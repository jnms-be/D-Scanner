module dscanner.imported_symbols_v2;

import dparse.ast;
import dparse.astprinter;
import dparse.lexer;
import dparse.parser : parseModule, ParserConfig;
import dparse.rollback_allocator : RollbackAllocator;
import dscanner.analysis.base : BaseAnalyzerArguments, ScopedBaseAnalyzer;
import dscanner.utils : expandArgs, readFile;
import std.algorithm;
import std.container.rbtree;
import std.container.slist;
import std.conv : to;
import std.exception : assumeWontThrow;
import std.file : readText;
import std.format : f = format;
import std.meta;
import std.range;
import std.stdio : write, writef, writefln, writeln;
import std.string : representation, strip, assumeUTF;
import std.sumtype;
import std.traits;

// TODO: Handling of version else-clause
// TODO: Don't emit static if's that reference template arguments (but process their contents).

// Note that "version = ..." declarations naturally work fine with this.

@safe:

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
		Visitor visitor = new Visitor(BaseAnalyzerArguments.init, sourceCode);
		visitor.visit(module_);
		importsByRequirements = visitor.m_importsByRequirements;
	}();

	return importsByRequirements;
}

private @system
class Visitor : ScopedBaseAnalyzer
{
	alias visit = typeof(super).visit;

	const(ubyte)[] m_sourceCode;
	Import[][Requirements] m_importsByRequirements;

	Requirements m_requirements;
	Attributes m_attributes;
	Attributes[] m_attributesScopeStack; /// See `pushScope` and `popScope`.

	this(BaseAnalyzerArguments args, const(ubyte)[] sourceCode)
	{
		super(args);
		m_sourceCode = sourceCode;
	}

	//
	// Tracking of m_requirements
	//

	auto evaluateCondition(const CompileCondition node)
	{
		alias Condition = SumType!(const VersionCondition, const DebugCondition, const StaticIfCondition);
		struct RaiiEffect
		{
			Visitor m_visitor;
			Condition m_condition;

			@disable this();
			@disable this(scope ref typeof(this));

			this(Visitor visitor, in typeof(m_condition) condition)
			{
				m_visitor = visitor;
				m_condition = condition;
				
				m_condition.match!(
					(in VersionCondition c) {
						m_visitor.m_requirements.versions
							~= c.token.tokenTo!string;
					},
					(in DebugCondition c) {
						m_visitor.m_requirements.debugSpecs
							~= c.identifierOrInteger.tokenTo!string;
					},
					(in StaticIfCondition c) {
						m_visitor.m_requirements.staticIfs
							~= c.assignExpression.tokens.tokensTo!string(m_visitor.m_sourceCode);
				},
				);
			}

			~this()
			{
				m_condition.match!(
					(in VersionCondition _) => m_visitor.m_requirements.versions.popFront,
					(in DebugCondition _) => m_visitor.m_requirements.debugSpecs.popFront,
					(in StaticIfCondition _) => m_visitor.m_requirements.staticIfs.popFront,
				);
			}
		}
		
		if (node.versionCondition !is null)
			return RaiiEffect(this, Condition(node.versionCondition));
		else if (node.debugCondition !is null)
			return RaiiEffect(this, Condition(node.debugCondition));
		else if (node.staticIfCondition !is null)
			return RaiiEffect(this, Condition(node.staticIfCondition));
		else
			assert(false);
	}

	/// Visit the node's children with the requirement applied.
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

	/// ditto
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

	//
	// Tracking of m_attributes
	//

	enum string saveAttributesMixin = q{
		const original = m_attributes;
		scope (exit) m_attributes = original;
	};

	/// Attributes are reset when entering these.
	static foreach (T; AliasSeq!(SpecifiedFunctionBody, StructBody))
	{
		override
		void visit(const T node)
		{
			mixin(saveAttributesMixin);
			m_attributes = Attributes.init;
			super.visit(node);
		}
	}

	/// Apply attributes on declarations.
	override
	void visit(const Declaration node)
	{
		mixin(saveAttributesMixin);
		foreach (const attribute; node.attributes)
			m_attributes.apply(attribute);
		super.visit(node);
	}

	/// Apply `attribute:` syntax for the rest of the scope.
	override
	void visit(const AttributeDeclaration node)
	{
		m_attributes.apply(node.attribute);
		super.visit(node);
	}

	/// See `visit(AttributeDeclaration)`.
	override
	void pushScope()
	{
		m_attributesScopeStack ~= m_attributes;
	}

	/// ditto
	override
	void popScope()
	{
		m_attributes = m_attributesScopeStack.front;
		m_attributesScopeStack.popFront;
	}

	/// Skip mixin templates.
	override
	void visit(const MixinTemplateDeclaration node)
	{
		cast(void) node;
	}

	//
	// Processing of imports
	//

	override
	void visit(const ImportDeclaration node)
	{
		// An import declaration may have any number of wildcard (single) imports, separated by commas.
		foreach (const SingleImport im; node.singleImports)
		{
			m_importsByRequirements[m_requirements] ~= Import(
				fqModuleName: im.identifierChain.identifierChainTo!string,
				moduleRename: im.rename.text,
				isStatic: im.rename.text.empty && m_attributes.static_, // rename takes priority
				visibility: m_attributes.visibility,
				visibilityPackage: m_attributes.visibilityPackage,
			);
		}

		// If the last module is followed by a list of symbols (bindings), it will appear as the
		// `importBindings` field instead.
		if (node.importBindings !is null)
		{
			const SingleImport im = node.importBindings.singleImport;
			const string fqModuleName = im.identifierChain.identifierChainTo!string;
			// This import can still be renamed, without affecting the symbols (bindings).
			// Note that static never applies here.
			if (im.rename.text.length)
			{
				m_importsByRequirements[m_requirements] ~= Import(
					fqModuleName: fqModuleName,
					moduleRename: im.rename.text,
					visibility: m_attributes.visibility,
					visibilityPackage: m_attributes.visibilityPackage,
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
					visibility: m_attributes.visibility,
					visibilityPackage: m_attributes.visibilityPackage,
				);
			}
		}
		super.visit(node);
	}
}

private
enum RequirementKind
{
	version_,
	debugSpec,
	staticIf,
}

private
struct Attributes
{
	bool static_;
	string visibility;
	string visibilityPackage;

scope:
pure nothrow:
	void apply(in Attribute attribute)
	{
		switch (attribute.attribute.type)
		{
			case tok!"public":
				visibility = "public";
				visibilityPackage = "";
				break;
			case tok!"protected":
				visibility = "protected";
				visibilityPackage = "";
				break;
			case tok!"package":
				visibility = "package";
				visibilityPackage = attribute.identifierChain.identifierChainTo!string;
				break;
			case tok!"private":
				visibility = "private";
				visibilityPackage = "";
				break;
			case tok!"static":
				static_ = true;
				break;
			default:
				break;
		}
	}
}

private pure nothrow
T identifierChainTo(T)(in IdentifierChain identifierChain)
if (isSomeString!T)
	=> identifierChain.identifiers.map!(id => id.text).join(".").to!T;

private pure nothrow
T tokenTo(T)(in Token token)
if (isSomeString!T)
	=> (token.text ? token.text : token.type.str).to!T;

private pure nothrow
T tokensTo(T)(in Token[] tokens, in ubyte[] sourceCode)
if (isSomeString!T)
{
	if (tokens.empty)
		return T.init;
	size_t begin = tokens[0].index;
	size_t end = tokens[$ - 1].index + tokens[$ - 1].tokenTo!string.representation.length;
	if (sourceCode.length < end)
		return T.init;
	return sourceCode[begin .. end].assumeUTF.to!T;
}

@("")
unittest
{
	/+
	const ubyte[] sourceCode = `
             import mod1;
private      import mod2;
package(pkg) import mod3;
package      import mod4;
protected    import mod5;
public       import mod6;
	`.strip.representation;
	+/

	const ubyte[] sourceCode = "/home/jnms/projects/dlang/ldc/runtime/phobos/std/sumtype.d".readText.strip.representation;

	const Import[][Requirements] importsByRequirements = listImportsByRequirements(
		sourceCode: sourceCode,
		stringCache: new StringCache(StringCache.defaultBucketCount),
	);

	foreach (const Requirements reqs, const Import[] imports; importsByRequirements)
	{
		foreach (version_; reqs.versions)
			writefln!"version (%s)"(version_);
		foreach (debugSpec; reqs.debugSpecs)
		{
			if (debugSpec.empty)
				writeln("debug");
			else
				writefln!"debug (%s)"(debugSpec);
		}
		foreach (staticIf; reqs.staticIfs)
			writefln!"static if (%s)"(staticIf);
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
					if (im.visibilityPackage.empty)
					 	return "package";
					else
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
}