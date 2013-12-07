#
#
#           The Nimrod Compiler
#        (c) Copyright 2012 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module contains a word recognizer, i.e. a simple
# procedure which maps special words to an enumeration.
# It is primarily needed because Pascal's case statement
# does not support strings. Without this the code would
# be slow and unreadable.

import 
  hashes, strutils, idents

# Keywords must be kept sorted and within a range

type
  TSpecialWord* = enum 
    wInvalid, 
    
    wAddr, wAnd, wAs, wAsm, wAtomic, 
    wBind, wBlock, wBreak, wCase, wCast, wConst, 
    wContinue, wConverter, wDiscard, wDistinct, wDiv, wDo, 
    wElif, wElse, wEnd, wEnum, wExcept, wExport,
    wFinally, wFor, wFrom, wGeneric, wIf, wImport, wIn, 
    wInclude, wInterface, wIs, wIsnot, wIterator, wLambda, wLet,
    wMacro, wMethod, wMixin, wUsing, wMod, wNil, 
    wNot, wNotin, wObject, wOf, wOr, wOut, wProc, wPtr, wRaise, wRef, wReturn, 
    wShared, wShl, wShr, wStatic, wTemplate, wTry, wTuple, wType, wVar, 
    wWhen, wWhile, wWith, wWithout, wXor, wYield,
    
    wColon, wColonColon, wEquals, wDot, wDotDot,
    wStar, wMinus,
    wMagic, wThread, wFinal, wProfiler, wObjChecks,

    wDestroy,
    
    wImmediate, wDestructor, wDelegator,
    wImportCpp, wImportObjC,
    wImportCompilerProc,
    wImportc, wExportc, wIncompleteStruct, wRequiresInit, wStaticCase,
    wAlign, wNodecl, wPure, wSideeffect, wHeader,
    wNosideeffect, wNoreturn, wMerge, wLib, wDynlib, wCompilerproc, wProcVar, 
    wFatal, wError, wWarning, wHint, wLine, wPush, wPop, wDefine, wUndef, 
    wLinedir, wStacktrace, wLinetrace, wLink, wCompile, 
    wLinksys, wDeprecated, wVarargs, wCallconv, wBreakpoint, wDebugger, 
    wNimcall, wStdcall, wCdecl, wSafecall, wSyscall, wInline, wNoInline, 
    wFastcall, wClosure, wNoconv, wOn, wOff, wChecks, wRangechecks, 
    wBoundchecks, wOverflowchecks, wNilchecks,
    wFloatchecks, wNanChecks, wInfChecks,
    wAssertions, wPatterns, wWarnings,
    wHints, wOptimization, wRaises, wWrites, wReads, wSize, wEffects, wTags,
    wDeadCodeElim, wSafecode, wNoForward,
    wPragma,
    wCompileTime, wNoInit,
    wPassc, wPassl, wBorrow, wDiscardable,
    wFieldChecks, 
    wWatchPoint, wSubsChar, 
    wAcyclic, wShallow, wUnroll, wLinearScanEnd, wComputedGoto,
    wWrite, wGensym, wInject, wDirty, wInheritable, wThreadVar, wEmit, 
    wNoStackFrame,
    wImplicitStatic, wGlobal, wCodegenDecl,

    wAuto, wBool, wCatch, wChar, wClass,
    wConst_cast, wDefault, wDelete, wDouble, wDynamic_cast,
    wExplicit, wExtern, wFalse, wFloat, wFriend,
    wGoto, wInt, wLong, wMutable, wNamespace, wNew, wOperator,
    wPrivate, wProtected, wPublic, wRegister, wReinterpret_cast,
    wShort, wSigned, wSizeof, wStatic_cast, wStruct, wSwitch,
    wThis, wThrow, wTrue, wTypedef, wTypeid, wTypename,
    wUnion, wUnsigned, wVirtual, wVoid, wVolatile, wWchar_t,

    wAlignas, wAlignof, wConstexpr, wDecltype, wNullptr, wNoexcept,
    wThread_local, wStatic_assert, wChar16_t, wChar32_t,

    wStdIn, wStdOut, wStdErr,

    wInOut, wByCopy, wByRef, wOneWay,
    
  TSpecialWords* = set[TSpecialWord]

const 
  oprLow* = ord(wColon)
  oprHigh* = ord(wDotDot)
  
  nimKeywordsLow* = ord(wAsm)
  nimKeywordsHigh* = ord(wYield)
  
  ccgKeywordsLow* = ord(wAuto)
  ccgKeywordsHigh* = ord(wOneWay)
  
  cppNimSharedKeywords* = {
    wAsm, wBreak, wCase, wConst, wContinue, wDo, wElse, wEnum, wExport,
    wFor, wIf, wReturn, wStatic, wTemplate, wTry, wWhile, wUsing }

  specialWords*: array[low(TSpecialWord)..high(TSpecialWord), string] = ["", 
    
    "addr", "and", "as", "asm", "atomic", 
    "bind", "block", "break", "case", "cast", 
    "const", "continue", "converter",
    "discard", "distinct", "div", "do",
    "elif", "else", "end", "enum", "except", "export", 
    "finally", "for", "from", "generic", "if", 
    "import", "in", "include", "interface", "is", "isnot", "iterator",
    "lambda", "let",
    "macro", "method", "mixin", "using", "mod", "nil", "not", "notin",
    "object", "of", "or", 
    "out", "proc", "ptr", "raise", "ref", "return",
    "shared", "shl", "shr", "static",
    "template", "try", "tuple", "type", "var", 
    "when", "while", "with", "without", "xor",
    "yield",

    ":", "::", "=", ".", "..",
    "*", "-",
    "magic", "thread", "final", "profiler", "objchecks",

    "destroy",
    
    "immediate", "destructor", "delegator",
    "importcpp", "importobjc",
    "importcompilerproc", "importc", "exportc", "incompletestruct",
    "requiresinit", "staticcase", "align", "nodecl", "pure", "sideeffect",
    "header", "nosideeffect", "noreturn", "merge", "lib", "dynlib", 
    "compilerproc", "procvar", "fatal", "error", "warning", "hint", "line", 
    "push", "pop", "define", "undef", "linedir", "stacktrace", "linetrace", 
    "link", "compile", "linksys", "deprecated", "varargs", 
    "callconv", "breakpoint", "debugger", "nimcall", "stdcall", 
    "cdecl", "safecall", "syscall", "inline", "noinline", "fastcall", "closure",
    "noconv", "on", "off", "checks", "rangechecks", "boundchecks", 
    "overflowchecks", "nilchecks",
    "floatchecks", "nanchecks", "infchecks",

    "assertions", "patterns", "warnings", "hints", 
    "optimization", "raises", "writes", "reads", "size", "effects", "tags",
    "deadcodeelim", "safecode", "noforward",
    "pragma",
    "compiletime", "noinit",
    "passc", "passl", "borrow", "discardable", "fieldchecks",
    "watchpoint",
    "subschar", "acyclic", "shallow", "unroll", "linearscanend", "computedgoto",
    "write", "gensym", "inject", "dirty", "inheritable", "threadvar", "emit",
    "nostackframe", "implicitstatic", "global", "codegendecl",
    
    "auto", "bool", "catch", "char", "class",
    "const_cast", "default", "delete", "double",
    "dynamic_cast", "explicit", "extern", "false",
    "float", "friend", "goto", "int", "long", "mutable",
    "namespace", "new", "operator",
    "private", "protected", "public", "register", "reinterpret_cast",
    "short", "signed", "sizeof", "static_cast", "struct", "switch",
    "this", "throw", "true", "typedef", "typeid",
    "typename", "union", "unsigned", "virtual", "void", "volatile",
    "wchar_t",

    "alignas", "alignof", "constexpr", "decltype", "nullptr", "noexcept",
    "thread_local", "static_assert", "char16_t", "char32_t",

    "stdin", "stdout", "stderr",

    "inout", "bycopy", "byref", "oneway",
    ]

proc findStr*(a: openarray[string], s: string): int = 
  for i in countup(low(a), high(a)): 
    if cmpIgnoreStyle(a[i], s) == 0: 
      return i
  result = - 1

proc whichKeyword*(id: PIdent): TSpecialWord = 
  if id.id < 0: result = wInvalid
  else: result = TSpecialWord(id.id)

proc whichKeyword*(id: String): TSpecialWord = 
  result = whichKeyword(getIdent(id))
  
proc initSpecials() = 
  # initialize the keywords:
  for s in countup(succ(low(specialWords)), high(specialWords)): 
    getIdent(specialWords[s], hashIgnoreStyle(specialWords[s])).id = ord(s)
  
initSpecials()
