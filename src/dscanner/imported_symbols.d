module dscanner.imported_symbols;

import dparse.ast;
import dparse.lexer;
import dparse.parser : parseModule, ParserConfig;
import dparse.rollback_allocator : RollbackAllocator;
import dscanner.analysis.base : BaseAnalyzerArguments, ScopedBaseAnalyzer;
import dscanner.utils : expandArgs, readFile;
import std.algorithm : any, each, map, splitter;
import std.array : join;
import std.container.rbtree : RedBlackTree;
import std.container.slist : SList;
import std.format : f = format;
import std.meta : AliasSeq;
import std.stdio : writefln, writeln;
import std.typecons : Rebindable;

void printImportedSymbols(
	string[] args,
	in bool useVersions, in string versionsCommaSeparated, in bool useDebugVersions, in string debugVersionsCommaSeparated,
	StringCache* cache,
)
{
	auto versions = new RedBlackTree!string(versionsCommaSeparated.splitter(","));
	auto debugVersions = new RedBlackTree!string(debugVersionsCommaSeparated.splitter(","));
	auto allImportedSymbols = new RedBlackTree!string;
	foreach (name; expandArgs(args))
		visitFile(name, useVersions, versions, useDebugVersions, debugVersions, allImportedSymbols, cache);
	allImportedSymbols.each!writeln;
}

private:

void visitFile(
	in string fileName,
	in bool useVersions, in RedBlackTree!string versions, in bool useDebugVersions, in RedBlackTree!string debugVersions,
	RedBlackTree!string allImportedSymbols,
	StringCache* stringCache,
)
{
	const ubyte[] sourceCode = readFile(fileName);

	const Token[] tokens = getTokensForParser(
		sourceCode: sourceCode,
		config: LexerConfig(
			fileName: fileName,
			stringBehavior: StringBehavior.source,
			whitespaceBehavior: WhitespaceBehavior.include,
		),
		cache: stringCache,
	);

	RollbackAllocator rba;
	const Module module_ = parseModule(
		ParserConfig(
			tokens: tokens,
			fileName: fileName,
			allocator: &rba,
		),
	);

	RedBlackTree!string fqSymbols = new RedBlackTree!string;
	analyze(module_, useVersions, versions, useDebugVersions, debugVersions, fqSymbols);
	allImportedSymbols.insert(fqSymbols[]);
}

void analyze(
	in Module module_,
	in bool useVersions, in RedBlackTree!string versions, in bool useDebugVersions, in RedBlackTree!string debugVersions,
	RedBlackTree!string fqSymbols,
)
in (module_ !is null)
in (versions !is null)
in (fqSymbols !is null)
{
	string[string] aliasFqMap = new string[string];
	RedBlackTree!string otherSymbols = new RedBlackTree!string;
	auto versionStack = SList!(RedBlackTree!string)(new RedBlackTree!string(versions[]));
	auto debugVersionStack = SList!(RedBlackTree!string)(new RedBlackTree!string(debugVersions[]));
	bool hasStaticAttribute;
	bool inIdentifier;

	bool hasVersion(string version_)
	{
		if (version_)
			foreach (RedBlackTree!string tree; versionStack)
				if (version_ in tree)
					return true;
		return false;
	}

	bool hasDebugVersion(string debugVersion)
	{
		if (debugVersion)
			foreach (RedBlackTree!string tree; debugVersionStack)
				if (debugVersion in tree)
					return true;
		return false;
	}

	void processImport(const SingleImport singleImport, const ImportBind[] importBinds)
	{
		const string fqModuleName = singleImport.identifierChain.identifiers
			.map!(id => id.text).join(".");
		const string moduleAlias = singleImport.rename.text;

		void addToFqAliasMap() { aliasFqMap[moduleAlias ? moduleAlias : fqModuleName] = fqModuleName; }

		if (hasStaticAttribute)
		{
			addToFqAliasMap;
		}
		else
		{
			// Don't need aliases of symbols, original symbol is stored in rightmost
			auto symbols = importBinds.map!(a => a.right.text ? a.right.text : a.left.text);

			if (symbols.length)
				foreach (string symbol; symbols)
					fqSymbols.insert(f!"%s.%s"(fqModuleName, symbol));
			else
			{
				addToFqAliasMap;
				if (!moduleAlias)
					fqSymbols.insert(f!"%s.*"(fqModuleName));
			}
		}
	}

	auto visitor = new class ScopedBaseAnalyzer {
		alias visit = typeof(super).visit;

		this()
		{
			super(BaseAnalyzerArguments.init);
		}

		protected override
		void pushScope()
		{
			versionStack.insertFront(new RedBlackTree!string);
			debugVersionStack.insertFront(new RedBlackTree!string);
		}

		protected override
		void popScope()
		{
			versionStack.removeFront;
			debugVersionStack.removeFront;
		}

		// TODO: what other scopes reset static on entry? templates?
		static foreach (BodyT; AliasSeq!(SpecifiedFunctionBody, StructBody))
		{
			override
			void visit(const BodyT node)
			{
				const bool tmp = hasStaticAttribute;
				hasStaticAttribute = false;
				scope (exit) hasStaticAttribute = tmp;
				super.visit(node);
			}
		}

		override
		void visit(const ConditionalDeclaration node)
		{
			visit(node.compileCondition);
			void visitTrue() { node.trueDeclarations.each!(d => this.visit(d)); }
			void visitFalse() { node.falseDeclarations.each!(d => this.visit(d)); }
			void visitBoth() { visitTrue; visitFalse; }
			if (node.compileCondition.versionCondition)
			{
				if (useVersions)
					hasVersion(node.compileCondition.versionCondition.token.text) ? visitTrue : visitFalse;
				else
					visitBoth;
			}
			else if (node.compileCondition.debugCondition)
			{
				if (useDebugVersions)
					hasDebugVersion(node.compileCondition.debugCondition.identifierOrInteger.text) ? visitTrue : visitFalse;
				else
					visitFalse;
			}
			else if (node.compileCondition.staticIfCondition)
			{
				visitBoth;
			}
		}

		override
		void visit(const ConditionalStatement node)
		{
			visit(node.compileCondition);
			void visitTrue() { node.trueStatement && visit(node.trueStatement); }
			void visitFalse() { node.falseStatement && visit(node.falseStatement); }
			void visitBoth() { visitTrue; visitFalse; }
			if (node.compileCondition.versionCondition)
			{
				if (useVersions)
					hasVersion(node.compileCondition.versionCondition.token.text) ? visitTrue : visitFalse;
				else
					visitBoth;
			}
			else if (node.compileCondition.debugCondition)
			{
				if (useDebugVersions)
					hasDebugVersion(node.compileCondition.debugCondition.identifierOrInteger.text) ? visitTrue : visitFalse;
				else
					visitFalse;
			}
			else if (node.compileCondition.staticIfCondition)
			{
				visitBoth;
			}
		}

		override
		void visit(const VersionSpecification node)
		{
			versionStack.front.insert(node.token.text);
			super.visit(node);
		}
		
		override
		void visit(const DebugSpecification node)
		{
			debugVersionStack.front.insert(node.identifierOrInteger.text);
			super.visit(node);
		}

		override
		void visit(const Declaration node)
		{
			// Subtree has static attribute, set hasStaticAttribute to true for subtree
			const bool tmp = hasStaticAttribute;
			if (node.attributes.any!(a => a.attribute == tok!"static"))
				hasStaticAttribute = true;
			scope (exit) hasStaticAttribute = tmp;
			super.visit(node);
		}

		override
		void visit(const ImportDeclaration node)
		{
			foreach (const SingleImport singleImport; node.singleImports)
				processImport(singleImport, []);
			if (node.importBindings !is null)
				processImport(node.importBindings.singleImport, node.importBindings.importBinds);
			super.visit(node);
		}

		override
		void visit(const TypeIdentifierPart node)
		{
			if (!inIdentifier)
			{
				string s;
				Rebindable!(const(TypeIdentifierPart)) curr = node;
				while (curr)
				{
					const next = curr.typeIdentifierPart;
					if (curr !is node)
						s ~= ".";
					s ~= curr.identifierOrTemplateInstance.identifier.text;
					if (next && s in aliasFqMap)
						fqSymbols.insert(s ~ "." ~ next.identifierOrTemplateInstance.identifier.text);
					curr = next;
				}
				inIdentifier = true;
				scope (exit) inIdentifier = false;
				super.visit(node);
			}
			else
			{
				super.visit(node);
			}
		}

		override
		void visit(const UnaryExpression node)
		{
			if (!inIdentifier && node.unaryExpression && node.identifierOrTemplateInstance)
			{
				string s;
				string rec(const UnaryExpression curr)
				{
					if (curr is null)
						return null;
					const string fq = rec(curr.unaryExpression);
					if (curr.unaryExpression && curr.identifierOrTemplateInstance)
					{
						string part = curr.identifierOrTemplateInstance.identifier.text;
						s ~= ".";
						s ~= part;
						if (fq)
							fqSymbols.insert(fq ~ "." ~ part);
					}
					else if (curr.primaryExpression && curr.identifierOrTemplateInstance)
						s ~= curr.primaryExpression.identifierOrTemplateInstance.identifier.text;
					const string* match = s in aliasFqMap;
					if (match)
						writeln(match);
					return match ? *match : null;
				}
				rec(node);
				inIdentifier = true;
				scope (exit) inIdentifier = false;
				super.visit(node);
			}
			else
			{
				super.visit(node);
			}
		}

		debug (lines) override
		void visit(const Token token)
		{
			writeln(token.line);
		}
	};
	visitor.visit(module_);
}
