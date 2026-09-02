module dscanner.imported_symbols_v2;

import dparse.ast;
import dparse.lexer;
import dparse.parser : parseModule, ParserConfig;
import dparse.rollback_allocator : RollbackAllocator;
import dscanner.analysis.base : BaseAnalyzerArguments, ScopedBaseAnalyzer;
import dscanner.utils : expandArgs, readFile;
import std.algorithm;
import std.container.rbtree;
import std.container.slist;
import std.conv : to;
import std.file : readText;
import std.format : f = format;
import std.meta;
import std.range;
import std.stdio : write, writef, writefln, writeln;
import std.string : representation, strip;
import std.traits;

// Note that "version = ..." declarations naturally work fine with this.

@safe:

struct Imports
{
	Import[Requirements] byRequirements;
}

struct Import
{
	string fqModuleName;
	string moduleRename;
	bool isStatic;

	string symbolName;
	string symbolRename;
	
	string visibility;
	string visibilityPackage;

	invariant
	{
		assert(fqModuleName.length);
		if (isStatic)
		{
			assert(moduleRename.empty);
			assert(symbolName.empty);
		}

		if (symbolRename.length)
			assert(symbolName.length);

		assert(visibility.empty || visibility.among("public", "protected", "package", "private"));
		if (visibility == "package")
			assert(visibilityPackage.length);
	}

pure nothrow:
scope const:
	bool isWildcard()
		=> symbolName.empty;
}

struct Requirements
{
	string[] versions;
	string[] debugSpecs;
	string[] staticIfs;
}

enum RequirementKind
{
	version_,
	debugSpec,
	staticIf,
}

Import[][Requirements] listImportsByRequirements(
	in ubyte[] sourceCode,
	StringCache* stringCache = null,
)
{
	if (stringCache is null)
		stringCache = new StringCache(StringCache.defaultBucketCount);

	const Token[] tokens = getTokensForParser(
		sourceCode: sourceCode,
		config: LexerConfig(
			stringBehavior: StringBehavior.source,
		),
		cache: stringCache,
	);

	const Module module_ = () @trusted {
		RollbackAllocator rba;
		return parseModule(ParserConfig(
			tokens: tokens,
			allocator: &rba,
		));
	}();

	Import[][Requirements] importsByRequirements;

	() @trusted {
		Visitor visitor = new Visitor(BaseAnalyzerArguments.init);
		visitor.visit(module_);
		importsByRequirements = visitor.m_importsByRequirements;
	}();

	return importsByRequirements;
}

private @system
class Visitor : ScopedBaseAnalyzer
{
	alias visit = typeof(super).visit;

	Import[][Requirements] m_importsByRequirements;

	Requirements m_requirements;
	bool m_attrStatic;
	string m_visibility;
	string m_visibilityPackage;

	this(BaseAnalyzerArguments args)
	{
		super(args);
	}

	protected override
	void pushScope()
	{
	}

	protected override
	void popScope()
	{
	}

	auto evaluateCondition(const CompileCondition node)
	{
		struct RaiiEffect
		{
			Visitor m_visitor;
			RequirementKind m_kind;

			@disable this();
			@disable this(scope ref typeof(this));

			this(Visitor visitor, RequirementKind kind, string value)
			{
				m_visitor = visitor;
				m_kind = kind;
				final switch (m_kind)
				{
				case RequirementKind.version_:  m_visitor.m_requirements.versions ~= value;   break;
				case RequirementKind.debugSpec: m_visitor.m_requirements.debugSpecs ~= value; break;
				case RequirementKind.staticIf:  m_visitor.m_requirements.staticIfs ~= value;  break;
				}
			}

			~this()
			{
				final switch (m_kind)
				{
				case RequirementKind.version_:  m_visitor.m_requirements.versions.popFront;   break;
				case RequirementKind.debugSpec: m_visitor.m_requirements.debugSpecs.popFront; break;
				case RequirementKind.staticIf:  m_visitor.m_requirements.staticIfs.popFront;  break;
				}
			}
		}
		
		if (node.versionCondition !is null)
			return RaiiEffect(this, RequirementKind.version_, node.versionCondition.token.text);
		else if (node.debugCondition !is null)
			return RaiiEffect(this, RequirementKind.debugSpec, node.debugCondition.identifierOrInteger.text);
		else if (node.staticIfCondition !is null)
			return RaiiEffect(this, RequirementKind.version_, node.staticIfCondition.assignExpression.tokens.to!string);
		else
			assert(false);
	}

	override
	void visit(const ConditionalDeclaration node)
	{
		super.visit(node.compileCondition);
		{
			const conditionEffect = evaluateCondition(node.compileCondition);
			foreach (decl; node.trueDeclarations)
				super.visit(decl);
		}
		if (node.hasElse)
		{
			foreach (decl; node.falseDeclarations)
				super.visit(decl);
		}
	}

	override
	void visit(const ConditionalStatement node)
	{
		super.visit(node.compileCondition);
		{
			const conditionEffect = evaluateCondition(node.compileCondition);
			super.visit(node.trueStatement);
		}
		if (node.falseStatement !is null)
		{
			super.visit(node.falseStatement);
		}
	}

	// Reset and restore m_attrStatic.
	// TODO: what other scopes reset static on entry? templates?
	static foreach (T; AliasSeq!(SpecifiedFunctionBody, StructBody))
	{
		override
		void visit(const T node)
		{
			const bool original = m_attrStatic;
			m_attrStatic = false;
			scope (exit) m_attrStatic = original;
			super.visit(node);
		}
	}

	override
	void visit(const Declaration node)
	{
		// Subtree has static attribute, set m_attrStatic to true for subtree.
		const bool original = m_attrStatic;
		if (node.attributes.any!(a => a.attribute == tok!"static"))
			m_attrStatic = true;
		scope (exit) m_attrStatic = original;
		super.visit(node);
	}

	override
	void visit(const ImportDeclaration node)
	{
		// An import declaration may have any number of wildcard (single) imports, separated by commas.
		foreach (const SingleImport im; node.singleImports)
		{
			m_importsByRequirements[m_requirements] ~= Import(
				fqModuleName: im.identifierChain.moduleIdentifierChainToString,
				moduleRename: im.rename.text,
				isStatic: im.rename.text.empty && m_attrStatic, // rename takes priority
				visibility: m_visibility,
				visibilityPackage: m_visibilityPackage,
			);
		}

		// If the last module is followed by a list of symbols (bindings), it will appear as the
		// `importBindings` field instead.
		if (node.importBindings !is null)
		{
			const SingleImport im = node.importBindings.singleImport;
			const string fqModuleName = im.identifierChain.moduleIdentifierChainToString;
			// This import can still be renamed, without affecting the symbols (bindings).
			// Note that static never applies here.
			if (im.rename.text.length)
			{
				m_importsByRequirements[m_requirements] ~= Import(
					fqModuleName: fqModuleName,
					moduleRename: im.rename.text,
					visibility: m_visibility,
					visibilityPackage: m_visibilityPackage,
				);
			}
			foreach (const ImportBind bind; node.importBindings.importBinds)
			{
				m_importsByRequirements[m_requirements] ~= Import(
					fqModuleName: fqModuleName,
					// With a rename, the name is in the `right` field.  Without a rename, the name is in the `left`
					// field, while `right` is empty.
					symbolName: bind.right.text.length ? bind.right.text : bind.left.text,
					symbolRename: bind.right.text.length ? bind.left.text : "",
					visibility: m_visibility,
					visibilityPackage: m_visibilityPackage,
				);
			}
		}
		super.visit(node);
	}
}

pure
string moduleIdentifierChainToString(const IdentifierChain identifierChain)
	=> identifierChain.identifiers.map!(id => id.text).join(".");

@("")
unittest
{
	///+
	const ubyte[] sourceCode = `
module example;

private import mod1 : a;
public import mod2 : sym2;
static import mod3;

import mod4 : sym4;
import mod5;
import mod5
:sym5;
import mod6, mod6 : sym6, mod6.submod : sym6, mod6.submod;

template A(T)
{
	import mod7;
	alias A = T;
}

mixin template B(T)
{
	import mod8;
	alias B = T;
}

version (none)
{
	import mod9;
}
	`.strip.representation;
	//+/

	// const ubyte[] sourceCode = "/home/jnms/projects/dlang/ldc/runtime/phobos/std/sumtype.d".readText.strip.representation;

	const Import[][Requirements] importsByRequirements = listImportsByRequirements(
		sourceCode: sourceCode,
		stringCache: new StringCache(StringCache.defaultBucketCount),
	);

	foreach (const Requirements reqs, const Import[] imports; importsByRequirements)
	{
		if (reqs.versions.empty)
			writeln("version (all)");
		else
		{
			foreach (version_; reqs.versions)
				writefln!"version (%s)"(version_);
		}
		foreach (debugSpec; reqs.debugSpecs)
		{
			if (debugSpec.empty)
				writeln("debug");
			else
				writefln!"debug (%s)"(debugSpec);
		}
		foreach (staticIf; reqs.staticIfs)
			writefln!"version (%s)"(staticIf);
		writeln("private");
		writeln("{");
		foreach (Import im; imports)
		{
			write("  ");
			write({
				switch (im.visibility)
				{
				case "public":
				case "protected": // has the same effect as public
					return "public";
				case "package":
					return f!"package(%s)"(im.visibilityPackage);
				case "private":
				default:
					return "";
				}
			}());
			if (im.isStatic)
				write(" static");
			write(" import ");
			if (im.moduleRename.length)
			{
				write(im.moduleRename);
				write(" = ");
			}
			write(im.fqModuleName);
			if (!im.isWildcard)
			{
				write(" : ");
				if (im.symbolRename.length)
				{
					write(im.symbolRename);
					write(" = ");
				}
				write(im.symbolName);
			}
			writeln(";");
		}
		writeln("}");
		writeln("");
	}
	/+
	assert(result[].array.sort.equal([
		"mod1.*",
		"mod2.sym2",
		"mod4.sym4",
		"mod5.*",
		"mod5.sym5",
		// "mod6.*", "mod6.submod.*", "mod6.submod.sym6", "mod6.sym6", // FIXME should appear
		"mod7.*",
		"mod8.*", // FIXME should not appear
		"mod9.*", // version (none) code appears with useVersions:false
	]));
	+/
}