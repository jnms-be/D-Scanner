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
import std.format : f = format;
import std.meta;
import std.range;
import std.stdio : writefln, writeln;
import std.traits;

@safe:

struct Imports
{
	Import[Requirements] byRequirements;
}

struct Import
{
	string fqModuleName;
	string moduleRename;

	bool isWildcard;
	string symbolName;
	string symbolRename;
	
	string visibility;
	string visibilityPackage;

	invariant
	{
		assert(fqModuleName.length);
		if (moduleRename.length)
			assert(isWildcard);

		if (isWildcard)
		{
			assert(symbolName.empty);
			assert(symbolRename.empty);
		}
		else
		{
			assert(symbolName.length);
		}

		assert(visibility.among("private", "package", "public"));
		if (visibility == "package")
			assert(visibilityPackage.length);
	}
}

struct Requirements
{
	string[] versions;
	string[] debugVersions;
	string[] ctConditions;
}
