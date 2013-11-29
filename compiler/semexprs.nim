#
#
#           The Nimrod Compiler
#        (c) Copyright 2013 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# this module does the semantic checking for expressions
# included from sem.nim

proc semTemplateExpr(c: PContext, n: PNode, s: PSym, semCheck = true): PNode = 
  markUsed(n, s)
  pushInfoContext(n.info)
  result = evalTemplate(n, s, getCurrOwner())
  if semCheck: result = semAfterMacroCall(c, result, s)
  popInfoContext()

proc semFieldAccess(c: PContext, n: PNode, flags: TExprFlags = {}): PNode

proc semOperand(c: PContext, n: PNode, flags: TExprFlags = {}): PNode =
  # same as 'semExprWithType' but doesn't check for proc vars
  result = semExpr(c, n, flags)
  if result.kind == nkEmpty: 
    # do not produce another redundant error message:
    #raiseRecoverableError("")
    result = errorNode(c, n)
  if result.typ != nil:
    # XXX tyGenericInst here?
    if result.typ.kind == tyVar: result = newDeref(result)
  else:
    LocalError(n.info, errExprXHasNoType, 
               renderTree(result, {renderNoComments}))
    result.typ = errorType(c)

proc semExprWithType(c: PContext, n: PNode, flags: TExprFlags = {}): PNode =
  result = semExpr(c, n, flags)
  if result.kind == nkEmpty: 
    # do not produce another redundant error message:
    #raiseRecoverableError("")
    result = errorNode(c, n)
  if result.typ == nil or result.typ == EnforceVoidContext:
    # we cannot check for 'void' in macros ...
    LocalError(n.info, errExprXHasNoType, 
               renderTree(result, {renderNoComments}))
    result.typ = errorType(c)
  else:
    # XXX tyGenericInst here?
    semProcvarCheck(c, result)
    if result.typ.kind == tyVar: result = newDeref(result)
    semDestructorCheck(c, result, flags)

proc semExprNoDeref(c: PContext, n: PNode, flags: TExprFlags = {}): PNode =
  result = semExpr(c, n, flags)
  if result.kind == nkEmpty:
    # do not produce another redundant error message:
    result = errorNode(c, n)
  if result.typ == nil:
    LocalError(n.info, errExprXHasNoType, 
               renderTree(result, {renderNoComments}))
    result.typ = errorType(c)
  else:
    semProcvarCheck(c, result)
    semDestructorCheck(c, result, flags)

proc semSymGenericInstantiation(c: PContext, n: PNode, s: PSym): PNode =
  result = symChoice(c, n, s, scClosed)
  
proc inlineConst(n: PNode, s: PSym): PNode {.inline.} =
  result = copyTree(s.ast)
  result.typ = s.typ
  result.info = n.info
  
proc semSym(c: PContext, n: PNode, s: PSym, flags: TExprFlags): PNode = 
  case s.kind
  of skConst:
    markUsed(n, s)
    case skipTypes(s.typ, abstractInst-{tyTypeDesc}).kind
    of  tyNil, tyChar, tyInt..tyInt64, tyFloat..tyFloat128, 
        tyTuple, tySet, tyUInt..tyUInt64:
      result = inlineConst(n, s)
    of tyArrayConstr, tySequence:
      # Consider::
      #     const x = []
      #     proc p(a: openarray[int])
      #     proc q(a: openarray[char])
      #     p(x)
      #     q(x)
      #
      # It is clear that ``[]`` means two totally different things. Thus, we
      # copy `x`'s AST into each context, so that the type fixup phase can
      # deal with two different ``[]``.
      if s.ast.len == 0: result = inlineConst(n, s)
      else: result = newSymNode(s, n.info)
    else:
      result = newSymNode(s, n.info)
  of skMacro: result = semMacroExpr(c, n, n, s)
  of skTemplate: result = semTemplateExpr(c, n, s)
  of skVar, skLet, skResult, skParam, skForVar:
    markUsed(n, s)
    # if a proc accesses a global variable, it is not side effect free:
    if sfGlobal in s.flags:
      incl(c.p.owner.flags, sfSideEffect)
    elif s.kind == skParam and s.typ.kind == tyExpr and s.typ.n != nil:
      # XXX see the hack in sigmatch.nim ...
      return s.typ.n
    result = newSymNode(s, n.info)
    # We cannot check for access to outer vars for example because it's still
    # not sure the symbol really ends up being used:
    # var len = 0 # but won't be called
    # genericThatUsesLen(x) # marked as taking a closure?
  of skGenericParam:
    if s.typ.kind == tyExpr:
      result = newSymNode(s, n.info)
      result.typ = s.typ
    elif s.ast != nil:
      result = semExpr(c, s.ast)
    else:
      InternalError(n.info, "no default for")
      result = emptyNode
  of skType:
    markUsed(n, s)
    result = newSymNode(s, n.info)
    result.typ = makeTypeDesc(c, s.typ)
  else:
    markUsed(n, s)
    result = newSymNode(s, n.info)

type
  TConvStatus = enum
    convOK,
    convNotNeedeed,
    convNotLegal

proc checkConversionBetweenObjects(castDest, src: PType): TConvStatus =
  return if inheritanceDiff(castDest, src) == high(int):
      convNotLegal
    else:
      convOK

const 
  IntegralTypes = {tyBool, tyEnum, tyChar, tyInt..tyUInt64}

proc checkConvertible(castDest, src: PType): TConvStatus =
  result = convOK
  if sameType(castDest, src) and castDest.sym == src.sym:
    # don't annoy conversions that may be needed on another processor:
    if castDest.kind notin IntegralTypes+{tyRange}:
      result = convNotNeedeed
    return
  var d = skipTypes(castDest, abstractVar)
  var s = skipTypes(src, abstractVar-{tyTypeDesc})
  while (d != nil) and (d.Kind in {tyPtr, tyRef}) and (d.Kind == s.Kind):
    d = base(d)
    s = base(s)
  if d == nil:
    result = convNotLegal
  elif d.Kind == tyObject and s.Kind == tyObject:
    result = checkConversionBetweenObjects(d, s)
  elif (skipTypes(castDest, abstractVarRange).Kind in IntegralTypes) and
      (skipTypes(src, abstractVarRange-{tyTypeDesc}).Kind in IntegralTypes):
    # accept conversion between integral types
  else:
    # we use d, s here to speed up that operation a bit:
    case cmpTypes(d, s)
    of isNone, isGeneric:
      if not compareTypes(castDest, src, dcEqIgnoreDistinct):
        result = convNotLegal
    else:
      nil

proc isCastable(dst, src: PType): bool = 
  #const
  #  castableTypeKinds = {tyInt, tyPtr, tyRef, tyCstring, tyString, 
  #                       tySequence, tyPointer, tyNil, tyOpenArray,
  #                       tyProc, tySet, tyEnum, tyBool, tyChar}
  var ds, ss: biggestInt
  # this is very unrestrictive; cast is allowed if castDest.size >= src.size
  ds = computeSize(dst)
  ss = computeSize(src)
  if ds < 0: 
    result = false
  elif ss < 0: 
    result = false
  else: 
    result = (ds >= ss) or
        (skipTypes(dst, abstractInst).kind in IntegralTypes) or
        (skipTypes(src, abstractInst-{tyTypeDesc}).kind in IntegralTypes)
  
proc isSymChoice(n: PNode): bool {.inline.} =
  result = n.kind in nkSymChoices

proc semConv(c: PContext, n: PNode, s: PSym): PNode =
  if sonsLen(n) != 2:
    LocalError(n.info, errConvNeedsOneArg)
    return n
  result = newNodeI(nkConv, n.info)
  result.typ = semTypeNode(c, n.sons[0], nil).skipTypes({tyGenericInst})
  addSon(result, copyTree(n.sons[0]))
  addSon(result, semExprWithType(c, n.sons[1]))
  var op = result.sons[1]
  
  if not isSymChoice(op):
    let status = checkConvertible(result.typ, op.typ)
    case status
    of convOK: nil
    of convNotNeedeed:
      Message(n.info, hintConvFromXtoItselfNotNeeded, result.typ.typeToString)
    of convNotLegal:
      LocalError(n.info, errGenerated, MsgKindToString(errIllegalConvFromXtoY)%
        [op.typ.typeToString, result.typ.typeToString])
  else:
    for i in countup(0, sonsLen(op) - 1):
      let it = op.sons[i]
      let status = checkConvertible(result.typ, it.typ)
      if status == convOK:
        markUsed(n, it.sym)
        markIndirect(c, it.sym)
        return it
    localError(n.info, errUseQualifier, op.sons[0].sym.name.s)

proc semCast(c: PContext, n: PNode): PNode = 
  if optSafeCode in gGlobalOptions: localError(n.info, errCastNotInSafeMode)
  #incl(c.p.owner.flags, sfSideEffect)
  checkSonsLen(n, 2)
  result = newNodeI(nkCast, n.info)
  result.typ = semTypeNode(c, n.sons[0], nil)
  addSon(result, copyTree(n.sons[0]))
  addSon(result, semExprWithType(c, n.sons[1]))
  if not isCastable(result.typ, result.sons[1].Typ): 
    LocalError(result.info, errExprCannotBeCastedToX, 
               typeToString(result.Typ))
  
proc semLowHigh(c: PContext, n: PNode, m: TMagic): PNode = 
  const 
    opToStr: array[mLow..mHigh, string] = ["low", "high"]
  if sonsLen(n) != 2: 
    LocalError(n.info, errXExpectsTypeOrValue, opToStr[m])
  else: 
    n.sons[1] = semExprWithType(c, n.sons[1], {efDetermineType})
    var typ = skipTypes(n.sons[1].typ, abstractVarRange)
    case typ.Kind
    of tySequence, tyString, tyOpenArray, tyVarargs: 
      n.typ = getSysType(tyInt)
    of tyArrayConstr, tyArray: 
      n.typ = typ.sons[0] # indextype
    of tyInt..tyInt64, tyChar, tyBool, tyEnum, tyUInt8, tyUInt16, tyUInt32: 
      # do not skip the range!
      n.typ = n.sons[1].typ.skipTypes(abstractVar)
    of tyGenericParam:
      # leave it for now, it will be resolved in semtypinst
      n.typ = getSysType(tyInt)
    else:
      LocalError(n.info, errInvalidArgForX, opToStr[m])
  result = n

proc semSizeof(c: PContext, n: PNode): PNode =
  if sonsLen(n) != 2:
    LocalError(n.info, errXExpectsTypeOrValue, "sizeof")
  else:
    n.sons[1] = semExprWithType(c, n.sons[1], {efDetermineType})
    #restoreOldStyleType(n.sons[1])
  n.typ = getSysType(tyInt)
  result = n

proc semOf(c: PContext, n: PNode): PNode = 
  if sonsLen(n) == 3: 
    n.sons[1] = semExprWithType(c, n.sons[1])
    n.sons[2] = semExprWithType(c, n.sons[2], {efDetermineType})
    #restoreOldStyleType(n.sons[1])
    #restoreOldStyleType(n.sons[2])
    let a = skipTypes(n.sons[1].typ, abstractPtrs)
    let b = skipTypes(n.sons[2].typ, abstractPtrs)
    let x = skipTypes(n.sons[1].typ, abstractPtrs-{tyTypeDesc})
    let y = skipTypes(n.sons[2].typ, abstractPtrs-{tyTypeDesc})

    if x.kind == tyTypeDesc or y.kind != tyTypeDesc:
      LocalError(n.info, errXExpectsObjectTypes, "of")
    elif b.kind != tyObject or a.kind != tyObject:
      LocalError(n.info, errXExpectsObjectTypes, "of")
    else:
      let diff = inheritanceDiff(a, b)
      # | returns: 0 iff `a` == `b`
      # | returns: -x iff `a` is the x'th direct superclass of `b`
      # | returns: +x iff `a` is the x'th direct subclass of `b`
      # | returns: `maxint` iff `a` and `b` are not compatible at all
      if diff <= 0:
        # optimize to true:
        Message(n.info, hintConditionAlwaysTrue, renderTree(n))
        result = newIntNode(nkIntLit, 1)
        result.info = n.info
        result.typ = getSysType(tyBool)
        return result
      elif diff == high(int):
        LocalError(n.info, errXcanNeverBeOfThisSubtype, typeToString(a))
  else:
    LocalError(n.info, errXExpectsTwoArguments, "of")
  n.typ = getSysType(tyBool)
  result = n

proc IsOpImpl(c: PContext, n: PNode): PNode =
  InternalAssert n.sonsLen == 3 and
    n[1].kind == nkSym and n[1].sym.kind == skType and
    n[2].kind in {nkStrLit..nkTripleStrLit, nkType}
  
  let t1 = n[1].sym.typ.skipTypes({tyTypeDesc})

  if n[2].kind in {nkStrLit..nkTripleStrLit}:
    case n[2].strVal.normalize
    of "closure":
      let t = skipTypes(t1, abstractRange)
      result = newIntNode(nkIntLit, ord(t.kind == tyProc and
                                        t.callConv == ccClosure and 
                                        tfIterator notin t.flags))
    of "iterator":
      let t = skipTypes(t1, abstractRange)
      result = newIntNode(nkIntLit, ord(t.kind == tyProc and
                                        t.callConv == ccClosure and 
                                        tfIterator in t.flags))
  else:
    var match: bool
    let t2 = n[2].typ
    if t2.kind == tyTypeClass:
      var m: TCandidate
      InitCandidate(m, t2)
      match = matchUserTypeClass(c, m, emptyNode, t2, t1) != nil
    else:
      match = sameType(t1, t2)
 
    result = newIntNode(nkIntLit, ord(match))

  result.typ = n.typ

proc semIs(c: PContext, n: PNode): PNode =
  if sonsLen(n) != 3:
    LocalError(n.info, errXExpectsTwoArguments, "is")

  result = n
  n.typ = getSysType(tyBool)
  
  n.sons[1] = semExprWithType(c, n[1], {efDetermineType})
  
  if n[2].kind notin {nkStrLit..nkTripleStrLit}:
    let t2 = semTypeNode(c, n[2], nil)
    n.sons[2] = newNodeIT(nkType, n[2].info, t2)

  if n[1].typ.kind != tyTypeDesc:
    n.sons[1] = makeTypeSymNode(c, n[1].typ, n[1].info)
  elif n[1].typ.sonsLen == 0:
    # this is a typedesc variable, leave for evals
    return

  let t1 = n[1].typ.sons[0]
  # BUGFIX: don't evaluate this too early: ``T is void``
  if not containsGenericType(t1): result = IsOpImpl(c, n)

proc semOpAux(c: PContext, n: PNode) =
  const flags = {efDetermineType}
  for i in countup(1, n.sonsLen-1):
    var a = n.sons[i]
    if a.kind == nkExprEqExpr and sonsLen(a) == 2: 
      var info = a.sons[0].info
      a.sons[0] = newIdentNode(considerAcc(a.sons[0]), info)
      a.sons[1] = semExprWithType(c, a.sons[1], flags)
      a.typ = a.sons[1].typ
    else:
      n.sons[i] = semExprWithType(c, a, flags)

proc overloadedCallOpr(c: PContext, n: PNode): PNode = 
  # quick check if there is *any* () operator overloaded:
  var par = getIdent("()")
  if searchInScopes(c, par) == nil:
    result = nil
  else:
    result = newNodeI(nkCall, n.info)
    addSon(result, newIdentNode(par, n.info))
    for i in countup(0, sonsLen(n) - 1): addSon(result, n.sons[i])
    result = semExpr(c, result)

proc changeType(n: PNode, newType: PType, check: bool) = 
  case n.kind
  of nkCurly, nkBracket: 
    for i in countup(0, sonsLen(n) - 1): 
      changeType(n.sons[i], elemType(newType), check)
  of nkPar: 
    if newType.kind != tyTuple: 
      InternalError(n.info, "changeType: no tuple type for constructor")
    elif newType.n == nil: nil
    elif sonsLen(n) > 0 and n.sons[0].kind == nkExprColonExpr: 
      for i in countup(0, sonsLen(n) - 1): 
        var m = n.sons[i].sons[0]
        if m.kind != nkSym: 
          internalError(m.info, "changeType(): invalid tuple constr")
          return
        var f = getSymFromList(newType.n, m.sym.name)
        if f == nil: 
          internalError(m.info, "changeType(): invalid identifier")
          return
        changeType(n.sons[i].sons[1], f.typ, check)
    else:
      for i in countup(0, sonsLen(n) - 1):
        var m = n.sons[i]
        var a = newNodeIT(nkExprColonExpr, m.info, newType.sons[i])
        addSon(a, newSymNode(newType.n.sons[i].sym))
        addSon(a, m)
        changeType(m, newType.sons[i], check)
        n.sons[i] = a
  of nkCharLit..nkUInt64Lit:
    if check:
      let value = n.intVal
      if value < firstOrd(newType) or value > lastOrd(newType):
        LocalError(n.info, errGenerated, "cannot convert " & $value &
                                         " to " & typeToString(newType))
  else: nil
  n.typ = newType

proc arrayConstrType(c: PContext, n: PNode): PType = 
  var typ = newTypeS(tyArrayConstr, c)
  rawAddSon(typ, nil)     # index type
  if sonsLen(n) == 0: 
    rawAddSon(typ, newTypeS(tyEmpty, c)) # needs an empty basetype!
  else:
    var x = n.sons[0]
    var lastIndex: biggestInt = sonsLen(n) - 1
    var t = skipTypes(n.sons[0].typ, {tyGenericInst, tyVar, tyOrdinal})
    addSonSkipIntLit(typ, t)
  typ.sons[0] = makeRangeType(c, 0, sonsLen(n) - 1, n.info)
  result = typ

proc semArrayConstr(c: PContext, n: PNode, flags: TExprFlags): PNode = 
  result = newNodeI(nkBracket, n.info)
  result.typ = newTypeS(tyArrayConstr, c)
  rawAddSon(result.typ, nil)     # index type
  if sonsLen(n) == 0: 
    rawAddSon(result.typ, newTypeS(tyEmpty, c)) # needs an empty basetype!
  else:
    var x = n.sons[0]
    var lastIndex: biggestInt = 0
    var indexType = getSysType(tyInt)
    if x.kind == nkExprColonExpr and sonsLen(x) == 2: 
      var idx = semConstExpr(c, x.sons[0])
      lastIndex = getOrdValue(idx)
      indexType = idx.typ
      x = x.sons[1]
    
    let yy = semExprWithType(c, x)
    var typ = yy.typ
    addSon(result, yy)
    #var typ = skipTypes(result.sons[0].typ, {tyGenericInst, tyVar, tyOrdinal})
    for i in countup(1, sonsLen(n) - 1): 
      x = n.sons[i]
      if x.kind == nkExprColonExpr and sonsLen(x) == 2: 
        var idx = semConstExpr(c, x.sons[0])
        idx = fitNode(c, indexType, idx)
        if lastIndex+1 != getOrdValue(idx):
          localError(x.info, errInvalidOrderInArrayConstructor)
        x = x.sons[1]
      
      let xx = semExprWithType(c, x, flags*{efAllowDestructor})
      result.add xx
      typ = commonType(typ, xx.typ)
      #n.sons[i] = semExprWithType(c, x, flags*{efAllowDestructor})
      #addSon(result, fitNode(c, typ, n.sons[i]))
      inc(lastIndex)
    addSonSkipIntLit(result.typ, typ)
    for i in 0 .. <result.len:
      result.sons[i] = fitNode(c, typ, result.sons[i])
  result.typ.sons[0] = makeRangeType(c, 0, sonsLen(result) - 1, n.info)

proc fixAbstractType(c: PContext, n: PNode) = 
  # XXX finally rewrite that crap!
  for i in countup(1, sonsLen(n) - 1): 
    var it = n.sons[i]
    case it.kind
    of nkHiddenStdConv, nkHiddenSubConv:
      if it.sons[1].kind == nkBracket:
        it.sons[1].typ = arrayConstrType(c, it.sons[1])
        #it.sons[1] = semArrayConstr(c, it.sons[1])
      if skipTypes(it.typ, abstractVar).kind in {tyOpenArray, tyVarargs}: 
        #if n.sons[0].kind == nkSym and IdentEq(n.sons[0].sym.name, "[]="):
        #  debug(n)
        
        var s = skipTypes(it.sons[1].typ, abstractVar)
        if s.kind == tyArrayConstr and s.sons[1].kind == tyEmpty: 
          s = copyType(s, getCurrOwner(), false)
          skipTypes(s, abstractVar).sons[1] = elemType(
              skipTypes(it.typ, abstractVar))
          it.sons[1].typ = s
        elif s.kind == tySequence and s.sons[0].kind == tyEmpty:
          s = copyType(s, getCurrOwner(), false)
          skipTypes(s, abstractVar).sons[0] = elemType(
              skipTypes(it.typ, abstractVar))
          it.sons[1].typ = s
          
      elif skipTypes(it.sons[1].typ, abstractVar).kind in
          {tyNil, tyArrayConstr, tyTuple, tySet}: 
        var s = skipTypes(it.typ, abstractVar)
        changeType(it.sons[1], s, check=true)
        n.sons[i] = it.sons[1]
    of nkBracket: 
      # an implicitely constructed array (passed to an open array):
      n.sons[i] = semArrayConstr(c, it, {})
    else: 
      nil
      #if (it.typ == nil): 
      #  InternalError(it.info, "fixAbstractType: " & renderTree(it))  
  
proc skipObjConv(n: PNode): PNode = 
  case n.kind
  of nkHiddenStdConv, nkHiddenSubConv, nkConv: 
    if skipTypes(n.sons[1].typ, abstractPtrs).kind in {tyTuple, tyObject}: 
      result = n.sons[1]
    else: 
      result = n
  of nkObjUpConv, nkObjDownConv: result = n.sons[0]
  else: result = n

proc isAssignable(c: PContext, n: PNode): TAssignableResult = 
  result = parampatterns.isAssignable(c.p.owner, n)

proc newHiddenAddrTaken(c: PContext, n: PNode): PNode = 
  if n.kind == nkHiddenDeref: 
    checkSonsLen(n, 1)
    result = n.sons[0]
  else: 
    result = newNodeIT(nkHiddenAddr, n.info, makeVarType(c, n.typ))
    addSon(result, n)
    if isAssignable(c, n) notin {arLValue, arLocalLValue}:
      localError(n.info, errVarForOutParamNeeded)

proc analyseIfAddressTaken(c: PContext, n: PNode): PNode = 
  result = n
  case n.kind
  of nkSym:
    # n.sym.typ can be nil in 'check' mode ...
    if n.sym.typ != nil and
        skipTypes(n.sym.typ, abstractInst-{tyTypeDesc}).kind != tyVar: 
      incl(n.sym.flags, sfAddrTaken)
      result = newHiddenAddrTaken(c, n)
  of nkDotExpr: 
    checkSonsLen(n, 2)
    if n.sons[1].kind != nkSym: 
      internalError(n.info, "analyseIfAddressTaken")
      return
    if skipTypes(n.sons[1].sym.typ, abstractInst-{tyTypeDesc}).kind != tyVar: 
      incl(n.sons[1].sym.flags, sfAddrTaken)
      result = newHiddenAddrTaken(c, n)
  of nkBracketExpr: 
    checkMinSonsLen(n, 1)
    if skipTypes(n.sons[0].typ, abstractInst-{tyTypeDesc}).kind != tyVar: 
      if n.sons[0].kind == nkSym: incl(n.sons[0].sym.flags, sfAddrTaken)
      result = newHiddenAddrTaken(c, n)
  else: 
    result = newHiddenAddrTaken(c, n)
  
proc analyseIfAddressTakenInCall(c: PContext, n: PNode) = 
  checkMinSonsLen(n, 1)
  const 
    FakeVarParams = {mNew, mNewFinalize, mInc, ast.mDec, mIncl, mExcl, 
      mSetLengthStr, mSetLengthSeq, mAppendStrCh, mAppendStrStr, mSwap, 
      mAppendSeqElem, mNewSeq, mReset, mShallowCopy}
  
  # get the real type of the callee
  # it may be a proc var with a generic alias type, so we skip over them
  var t = n.sons[0].typ.skipTypes({tyGenericInst})

  if n.sons[0].kind == nkSym and n.sons[0].sym.magic in FakeVarParams: 
    # BUGFIX: check for L-Value still needs to be done for the arguments!
    # note sometimes this is eval'ed twice so we check for nkHiddenAddr here:
    for i in countup(1, sonsLen(n) - 1): 
      if i < sonsLen(t) and t.sons[i] != nil and
          skipTypes(t.sons[i], abstractInst-{tyTypeDesc}).kind == tyVar: 
        if isAssignable(c, n.sons[i]) notin {arLValue, arLocalLValue}: 
          if n.sons[i].kind != nkHiddenAddr:
            LocalError(n.sons[i].info, errVarForOutParamNeeded)
    return
  for i in countup(1, sonsLen(n) - 1):
    if n.sons[i].kind == nkHiddenCallConv:
      # we need to recurse explicitly here as converters can create nested
      # calls and then they wouldn't be analysed otherwise
      analyseIfAddressTakenInCall(c, n.sons[i])
    semProcvarCheck(c, n.sons[i])
    if i < sonsLen(t) and
        skipTypes(t.sons[i], abstractInst-{tyTypeDesc}).kind == tyVar:
      if n.sons[i].kind != nkHiddenAddr:
        n.sons[i] = analyseIfAddressTaken(c, n.sons[i])
  
include semmagic

proc evalAtCompileTime(c: PContext, n: PNode): PNode =
  result = n
  if n.kind notin nkCallKinds or n.sons[0].kind != nkSym: return
  var callee = n.sons[0].sym
  
  # constant folding that is necessary for correctness of semantic pass:
  if callee.magic != mNone and callee.magic in ctfeWhitelist and n.typ != nil:
    var call = newNodeIT(nkCall, n.info, n.typ)
    call.add(n.sons[0])
    var allConst = true
    for i in 1 .. < n.len:
      var a = getConstExpr(c.module, n.sons[i])
      if a == nil:
        allConst = false
        a = n.sons[i]
        if a.kind == nkHiddenStdConv: a = a.sons[1]
      call.add(a)
    if allConst:
      result = semfold.getConstExpr(c.module, call)
      if result.isNil: result = n
      else: return result
    result.typ = semfold.getIntervalType(callee.magic, call)
    
  # optimization pass: not necessary for correctness of the semantic pass
  if {sfNoSideEffect, sfCompileTime} * callee.flags != {} and
     {sfForward, sfImportc} * callee.flags == {}:
    if sfCompileTime notin callee.flags and 
        optImplicitStatic notin gOptions: return

    if callee.magic notin ctfeWhitelist: return
    if callee.kind notin {skProc, skConverter} or callee.isGenericRoutine:
      return
    
    if n.typ != nil and not typeAllowed(n.typ, skConst): return
    
    var call = newNodeIT(nkCall, n.info, n.typ)
    call.add(n.sons[0])
    for i in 1 .. < n.len:
      let a = getConstExpr(c.module, n.sons[i])
      if a == nil: return n
      call.add(a)
    #echo "NOW evaluating at compile time: ", call.renderTree
    if sfCompileTime in callee.flags:
      result = evalStaticExpr(c, c.module, call, c.p.owner)
      if result.isNil: 
        LocalError(n.info, errCannotInterpretNodeX, renderTree(call))
    else:
      result = evalConstExpr(c, c.module, call)
      if result.isNil: result = n
    #if result != n:
    #  echo "SUCCESS evaluated at compile time: ", call.renderTree

proc semStaticExpr(c: PContext, n: PNode): PNode =
  let a = semExpr(c, n.sons[0])
  result = evalStaticExpr(c, c.module, a, c.p.owner)
  if result.isNil:
    LocalError(n.info, errCannotInterpretNodeX, renderTree(n))
    result = emptyNode

proc semOverloadedCallAnalyseEffects(c: PContext, n: PNode, nOrig: PNode,
                                     flags: TExprFlags): PNode =
  if flags*{efInTypeOf, efWantIterator} != {}:
    # consider: 'for x in pReturningArray()' --> we don't want the restriction
    # to 'skIterator' anymore; skIterator is preferred in sigmatch already for
    # typeof support.
    # for ``type(countup(1,3))``, see ``tests/ttoseq``.
    result = semOverloadedCall(c, n, nOrig,
      {skProc, skMethod, skConverter, skMacro, skTemplate, skIterator})  
  else:
    result = semOverloadedCall(c, n, nOrig, 
      {skProc, skMethod, skConverter, skMacro, skTemplate, skEnumField})
  if result != nil:
    if result.sons[0].kind != nkSym: 
      InternalError("semOverloadedCallAnalyseEffects")
      return
    let callee = result.sons[0].sym
    case callee.kind
    of skMacro, skTemplate: nil
    else:
      if (callee.kind == skIterator) and (callee.id == c.p.owner.id): 
        LocalError(n.info, errRecursiveDependencyX, callee.name.s)
      if sfNoSideEffect notin callee.flags: 
        if {sfImportc, sfSideEffect} * callee.flags != {}:
          incl(c.p.owner.flags, sfSideEffect)

proc semObjConstr(c: PContext, n: PNode, flags: TExprFlags): PNode
proc semIndirectOp(c: PContext, n: PNode, flags: TExprFlags): PNode = 
  result = nil
  checkMinSonsLen(n, 1)
  var prc = n.sons[0]
  if n.sons[0].kind == nkDotExpr: 
    checkSonsLen(n.sons[0], 2)
    n.sons[0] = semFieldAccess(c, n.sons[0])
    if n.sons[0].kind == nkDotCall: 
      # it is a static call!
      result = n.sons[0]
      result.kind = nkCall
      for i in countup(1, sonsLen(n) - 1): addSon(result, n.sons[i])
      return semDirectOp(c, result, flags)
  else: 
    n.sons[0] = semExpr(c, n.sons[0])
  let nOrig = n.copyTree
  semOpAux(c, n)
  var t: PType = nil
  if n.sons[0].typ != nil:
    t = skipTypes(n.sons[0].typ, abstractInst-{tyTypedesc})
  if t != nil and t.kind == tyProc:
    # This is a proc variable, apply normal overload resolution
    var m: TCandidate
    initCandidate(m, t)
    matches(c, n, nOrig, m)
    if m.state != csMatch:
      if c.inCompilesContext > 0:
        # speed up error generation:
        GlobalError(n.Info, errTypeMismatch, "")
        return emptyNode
      else:
        var hasErrorType = false
        var msg = msgKindToString(errTypeMismatch)
        for i in countup(1, sonsLen(n) - 1): 
          if i > 1: add(msg, ", ")
          let nt = n.sons[i].typ
          add(msg, typeToString(nt))
          if nt.kind == tyError: 
            hasErrorType = true
            break
        if not hasErrorType:
          add(msg, ")\n" & msgKindToString(errButExpected) & "\n" &
              typeToString(n.sons[0].typ))
          LocalError(n.Info, errGenerated, msg)
        return errorNode(c, n)
      result = nil
    else:
      result = m.call
      instGenericConvertersSons(c, result, m)
    # we assume that a procedure that calls something indirectly 
    # has side-effects:
    if tfNoSideEffect notin t.flags: incl(c.p.owner.flags, sfSideEffect)
  elif t != nil and t.kind == tyTypeDesc:
    if n.len == 1: return semObjConstr(c, n, flags)
    let destType = t.skipTypes({tyTypeDesc, tyGenericInst})
    result = semConv(c, n, symFromType(destType, n.info))
    return
  else:
    result = overloadedCallOpr(c, n)
    # Now that nkSym does not imply an iteration over the proc/iterator space,
    # the old ``prc`` (which is likely an nkIdent) has to be restored:
    if result == nil: 
      # XXX: hmm, what kind of symbols will end up here?
      # do we really need to try the overload resolution?
      n.sons[0] = prc
      nOrig.sons[0] = prc
      n.flags.incl nfExprCall
      result = semOverloadedCallAnalyseEffects(c, n, nOrig, flags)
      if result == nil: return errorNode(c, n)
  #result = afterCallActions(c, result, nOrig, flags)
  fixAbstractType(c, result)
  analyseIfAddressTakenInCall(c, result)
  if result.sons[0].kind == nkSym and result.sons[0].sym.magic != mNone:
    result = magicsAfterOverloadResolution(c, result, flags)
  result = evalAtCompileTime(c, result)

proc afterCallActions(c: PContext; n, orig: PNode, flags: TExprFlags): PNode =
  result = n
  let callee = result.sons[0].sym
  case callee.kind
  of skMacro: result = semMacroExpr(c, result, orig, callee)
  of skTemplate: result = semTemplateExpr(c, result, callee)
  else:
    semFinishOperands(c, result)
    activate(c, result)
    fixAbstractType(c, result)
    analyseIfAddressTakenInCall(c, result)
    if callee.magic != mNone:
      result = magicsAfterOverloadResolution(c, result, flags)
  result = evalAtCompileTime(c, result)

proc semDirectOp(c: PContext, n: PNode, flags: TExprFlags): PNode = 
  # this seems to be a hotspot in the compiler!
  let nOrig = n.copyTree
  #semLazyOpAux(c, n)
  result = semOverloadedCallAnalyseEffects(c, n, nOrig, flags)
  if result != nil: result = afterCallActions(c, result, nOrig, flags)
  #if n.info ?? "mac.nim":    
  #  debug(result) 

proc buildStringify(c: PContext, arg: PNode): PNode = 
  if arg.typ != nil and 
      skipTypes(arg.typ, abstractInst-{tyTypeDesc}).kind == tyString:
    result = arg
  else:
    result = newNodeI(nkCall, arg.info)
    addSon(result, newIdentNode(getIdent"$", arg.info))
    addSon(result, arg)

proc semEcho(c: PContext, n: PNode): PNode = 
  # this really is a macro
  checkMinSonsLen(n, 1)
  for i in countup(1, sonsLen(n) - 1): 
    var arg = semExprWithType(c, n.sons[i])
    n.sons[i] = semExprWithType(c, buildStringify(c, arg))
    let t = n.sons[i].typ
    if t == nil or t.skipTypes(abstractInst).kind != tyString:  
      LocalError(n.info, errGenerated,
                 "implicitly invoked '$' does not return string")
  let t = n.sons[0].typ
  if tfNoSideEffect notin t.flags: incl(c.p.owner.flags, sfSideEffect)
  result = n
  
proc buildEchoStmt(c: PContext, n: PNode): PNode = 
  # we MUST not check 'n' for semantics again here!
  result = newNodeI(nkCall, n.info)
  var e = StrTableGet(magicsys.systemModule.Tab, getIdent"echo")
  if e != nil:
    addSon(result, newSymNode(e))
  else:
    LocalError(n.info, errSystemNeeds, "echo")
    addSon(result, errorNode(c, n))
  var arg = buildStringify(c, n)
  # problem is: implicit '$' is not checked for semantics yet. So we give up
  # and check 'arg' for semantics again:
  addSon(result, semExpr(c, arg))

proc semExprNoType(c: PContext, n: PNode): PNode =
  result = semExpr(c, n, {efWantStmt})
  discardCheck(result)
  
proc isTypeExpr(n: PNode): bool = 
  case n.kind
  of nkType, nkTypeOfExpr: result = true
  of nkSym: result = n.sym.kind == skType
  else: result = false
  
proc lookupInRecordAndBuildCheck(c: PContext, n, r: PNode, field: PIdent, 
                                 check: var PNode): PSym = 
  # transform in a node that contains the runtime check for the
  # field, if it is in a case-part...
  result = nil
  case r.kind
  of nkRecList: 
    for i in countup(0, sonsLen(r) - 1): 
      result = lookupInRecordAndBuildCheck(c, n, r.sons[i], field, check)
      if result != nil: return 
  of nkRecCase: 
    checkMinSonsLen(r, 2)
    if (r.sons[0].kind != nkSym): IllFormedAst(r)
    result = lookupInRecordAndBuildCheck(c, n, r.sons[0], field, check)
    if result != nil: return 
    var s = newNodeI(nkCurly, r.info)
    for i in countup(1, sonsLen(r) - 1): 
      var it = r.sons[i]
      case it.kind
      of nkOfBranch: 
        result = lookupInRecordAndBuildCheck(c, n, lastSon(it), field, check)
        if result == nil: 
          for j in 0..sonsLen(it)-2: addSon(s, copyTree(it.sons[j]))
        else: 
          if check == nil: 
            check = newNodeI(nkCheckedFieldExpr, n.info)
            addSon(check, ast.emptyNode) # make space for access node
          s = newNodeI(nkCurly, n.info)
          for j in countup(0, sonsLen(it) - 2): addSon(s, copyTree(it.sons[j]))
          var inExpr = newNodeI(nkCall, n.info)
          addSon(inExpr, newIdentNode(getIdent("in"), n.info))
          addSon(inExpr, copyTree(r.sons[0]))
          addSon(inExpr, s)   #writeln(output, renderTree(inExpr));
          addSon(check, semExpr(c, inExpr))
          return 
      of nkElse: 
        result = lookupInRecordAndBuildCheck(c, n, lastSon(it), field, check)
        if result != nil: 
          if check == nil: 
            check = newNodeI(nkCheckedFieldExpr, n.info)
            addSon(check, ast.emptyNode) # make space for access node
          var inExpr = newNodeI(nkCall, n.info)
          addSon(inExpr, newIdentNode(getIdent("in"), n.info))
          addSon(inExpr, copyTree(r.sons[0]))
          addSon(inExpr, s)
          var notExpr = newNodeI(nkCall, n.info)
          addSon(notExpr, newIdentNode(getIdent("not"), n.info))
          addSon(notExpr, inExpr)
          addSon(check, semExpr(c, notExpr))
          return 
      else: illFormedAst(it)
  of nkSym: 
    if r.sym.name.id == field.id: result = r.sym
  else: illFormedAst(n)
  
proc makeDeref(n: PNode): PNode = 
  var t = skipTypes(n.typ, {tyGenericInst})
  result = n
  if t.kind == tyVar: 
    result = newNodeIT(nkHiddenDeref, n.info, t.sons[0])
    addSon(result, n)
    t = skipTypes(t.sons[0], {tyGenericInst})
  while t.kind in {tyPtr, tyRef, tyEnum}:
    var a = result
    result = newNodeIT(nkHiddenDeref, n.info, t.sons[0])
    addSon(result, a)
    t = skipTypes(t.sons[0], {tyGenericInst})

proc builtinFieldAccess(c: PContext, n: PNode, flags: TExprFlags): PNode =
  ## returns nil if it's not a built-in field access
  checkSonsLen(n, 2)
  # early exit for this; see tests/compile/tbindoverload.nim:
  if isSymChoice(n.sons[1]): return

  var s = qualifiedLookup(c, n, {checkAmbiguity, checkUndeclared})
  if s != nil:
    return semSym(c, n, s, flags)
  n.sons[0] = semExprWithType(c, n.sons[0], flags+{efDetermineType})
  #restoreOldStyleType(n.sons[0])
  var i = considerAcc(n.sons[1])  
  var ty = n.sons[0].typ
  var f: PSym = nil
  result = nil
  if isTypeExpr(n.sons[0]) or ty.kind == tyTypeDesc and ty.len == 1:
    if ty.kind == tyTypeDesc: ty = ty.sons[0]
    case ty.kind
    of tyEnum:
      # look up if the identifier belongs to the enum:
      while ty != nil:
        f = getSymFromList(ty.n, i)
        if f != nil: break 
        ty = ty.sons[0]         # enum inheritance
      if f != nil: 
        result = newSymNode(f)
        result.info = n.info
        result.typ = ty
        markUsed(n, f)
        return
    of tyGenericInst:
      assert ty.sons[0].kind == tyGenericBody
      let tbody = ty.sons[0]
      for s in countup(0, tbody.len-2):
        let tParam = tbody.sons[s]
        if tParam.sym.name == i:
          let rawTyp = ty.sons[s + 1]
          if rawTyp.kind == tyExpr:
            return rawTyp.n
          else:
            let foundTyp = makeTypeDesc(c, rawTyp)
            return newSymNode(copySym(tParam.sym).linkTo(foundTyp), n.info)
      return
    else:
      # echo "TYPE FIELD ACCESS"
      # debug ty
      return
    # XXX: This is probably not relevant any more
    # reset to prevent 'nil' bug: see "tests/reject/tenumitems.nim":
    ty = n.sons[0].Typ
    
  ty = skipTypes(ty, {tyGenericInst, tyVar, tyPtr, tyRef})    
  var check: PNode = nil  
  if ty.kind == tyObject: 
    while true: 
      check = nil
      f = lookupInRecordAndBuildCheck(c, n, ty.n, i, check)
      if f != nil: break 
      if ty.sons[0] == nil: break 
      ty = skipTypes(ty.sons[0], {tyGenericInst})
    if f != nil:
      if fieldVisible(c, f):
        # is the access to a public field or in the same module or in a friend?
        n.sons[0] = makeDeref(n.sons[0])
        n.sons[1] = newSymNode(f) # we now have the correct field
        n.typ = f.typ
        markUsed(n, f)
        if check == nil: 
          result = n
        else: 
          check.sons[0] = n
          check.typ = n.typ
          result = check
  elif ty.kind == tyTuple and ty.n != nil:      
    f = getSymFromList(ty.n, i)
    if f != nil:
      n.sons[0] = makeDeref(n.sons[0])
      n.sons[1] = newSymNode(f)
      n.typ = f.typ
      result = n
      markUsed(n, f)
  elif ty.kind == tyEnum and (tfEnumSumTyp in ty.flags):    
    ty = ty.sons[0]  
    f = getSymFromList(ty.n, i)      
    if f != nil:
      n.sons[0] = makeDeref(n.sons[0])
      n.sons[1] = newSymNode(f)
      n.typ = f.typ
      result = n
      markUsed(n, f)  
      echo("+++++++builtinFieldAccess")
      echo(renderTree(result))
      echo(renderTree(result))

proc dotTransformation(c: PContext, n: PNode): PNode =
  if isSymChoice(n.sons[1]):
    result = newNodeI(nkDotCall, n.info)
    addSon(result, n.sons[1])
    addSon(result, copyTree(n[0]))
  else:
    var i = considerAcc(n.sons[1])
    result = newNodeI(nkDotCall, n.info)
    result.flags.incl nfDelegate
    addSon(result, newIdentNode(i, n[1].info))
    addSon(result, copyTree(n[0]))
  
proc semFieldAccess(c: PContext, n: PNode, flags: TExprFlags): PNode = 
  # this is difficult, because the '.' is used in many different contexts
  # in Nimrod. We first allow types in the semantic checking.
  result = builtinFieldAccess(c, n, flags)
  if result == nil:
    result = dotTransformation(c, n)

proc buildOverloadedSubscripts(n: PNode, ident: PIdent): PNode =
  result = newNodeI(nkCall, n.info)
  result.add(newIdentNode(ident, n.info))
  for i in 0 .. n.len-1: result.add(n[i])
  
proc semDeref(c: PContext, n: PNode): PNode = 
  checkSonsLen(n, 1)
  n.sons[0] = semExprWithType(c, n.sons[0])     
  result = n
  var t = skipTypes(n.sons[0].typ, {tyGenericInst, tyVar})
  case t.kind
  of tyRef, tyPtr: 
    n.typ = t.sons[0]    
  of tyEnum:
    n.typ = getEnumType(c, n.sons[0]) 
    if n.info ?? "mac.nim":
      echo("+++++++ semDeref Enum++")
      debug(n.sons[0])      
      debug(n.typ)      
      echo("+++++++++++++++++++")     
  else: result = nil
  #GlobalError(n.sons[0].info, errCircumNeedsPointer) 

proc semSubscript(c: PContext, n: PNode, flags: TExprFlags): PNode =
  ## returns nil if not a built-in subscript operator; also called for the
  ## checking of assignments 
  if sonsLen(n) == 1: 
    var x = semDeref(c, n)
    if x == nil: return nil
    result = newNodeIT(nkDerefExpr, x.info, x.typ)
    result.add(x[0])
    return
  checkMinSonsLen(n, 2)
  n.sons[0] = semExprWithType(c, n.sons[0])
  var arr = skipTypes(n.sons[0].typ, {tyGenericInst, tyVar, tyPtr, tyRef})
  case arr.kind
  of tyArray, tyOpenArray, tyVarargs, tyArrayConstr, tySequence, tyString, 
     tyCString: 
    checkSonsLen(n, 2)
    n.sons[0] = makeDeref(n.sons[0])
    for i in countup(1, sonsLen(n) - 1): 
      n.sons[i] = semExprWithType(c, n.sons[i], 
                                  flags*{efInTypeof, efDetermineType})
    var indexType = if arr.kind == tyArray: arr.sons[0] else: getSysType(tyInt)
    var arg = IndexTypesMatch(c, indexType, n.sons[1].typ, n.sons[1])
    if arg != nil:
      n.sons[1] = arg
      result = n
      result.typ = elemType(arr)
    #GlobalError(n.info, errIndexTypesDoNotMatch)
  of tyTypeDesc:
    # The result so far is a tyTypeDesc bound 
    # a tyGenericBody. The line below will substitute
    # it with the instantiated type.
    result = symNodeFromType(c, semTypeNode(c, n, nil), n.info)
  of tyTuple: 
    checkSonsLen(n, 2)
    n.sons[0] = makeDeref(n.sons[0])
    # [] operator for tuples requires constant expression:
    n.sons[1] = semConstExpr(c, n.sons[1])
    if skipTypes(n.sons[1].typ, {tyGenericInst, tyRange, tyOrdinal}).kind in
        {tyInt..tyInt64}: 
      var idx = getOrdValue(n.sons[1])
      if idx >= 0 and idx < sonsLen(arr): n.typ = arr.sons[int(idx)]
      else: LocalError(n.info, errInvalidIndexValueForTuple)
    else: 
      LocalError(n.info, errIndexTypesDoNotMatch)
    result = n  
  else: nil
  
proc semArrayAccess(c: PContext, n: PNode, flags: TExprFlags): PNode = 
  result = semSubscript(c, n, flags)
  if result == nil:
    # overloaded [] operator:
    result = semExpr(c, buildOverloadedSubscripts(n, getIdent"[]"))

proc propertyWriteAccess(c: PContext, n, nOrig, a: PNode): PNode =
  var id = considerAcc(a[1])
  let setterId = newIdentNode(getIdent(id.s & '='), n.info)
  # a[0] is already checked for semantics, that does ``builtinFieldAccess``
  # this is ugly. XXX Semantic checking should use the ``nfSem`` flag for
  # nodes?
  let aOrig = nOrig[0]
  result = newNode(nkCall, n.info, sons = @[setterId, a[0], semExpr(c, n[1])])
  let orig = newNode(nkCall, n.info, sons = @[setterId, aOrig[0], nOrig[1]])
  result = semOverloadedCallAnalyseEffects(c, result, orig, {})
  
  if result != nil:
    result = afterCallActions(c, result, nOrig, {})
    #fixAbstractType(c, result)
    #analyseIfAddressTakenInCall(c, result)

proc takeImplicitAddr(c: PContext, n: PNode): PNode =
  case n.kind
  of nkHiddenAddr, nkAddr: return n
  of nkHiddenDeref, nkDerefExpr: return n.sons[0]
  of nkBracketExpr:
    if len(n) == 1: return n.sons[0]
  else: nil
  var valid = isAssignable(c, n)
  if valid != arLValue:
    if valid == arLocalLValue:
      LocalError(n.info, errXStackEscape, renderTree(n, {renderNoComments}))
    else:
      LocalError(n.info, errExprHasNoAddress)
  result = newNodeIT(nkHiddenAddr, n.info, makePtrType(c, n.typ))
  result.add(n)
  
proc asgnToResultVar(c: PContext, n, le, ri: PNode) {.inline.} =
  if le.kind == nkHiddenDeref:
    var x = le.sons[0]
    if x.typ.kind == tyVar and x.kind == nkSym and x.sym.kind == skResult:
      n.sons[0] = x # 'result[]' --> 'result'
      n.sons[1] = takeImplicitAddr(c, ri)

proc semAsgn(c: PContext, n: PNode): PNode =
  checkSonsLen(n, 2)
  var a = n.sons[0]
  case a.kind
  of nkDotExpr:
    # r.f = x
    # --> `f=` (r, x)
    let nOrig = n.copyTree
    a = builtinFieldAccess(c, a, {efLValue})
    if a == nil:
      a = propertyWriteAccess(c, n, nOrig, n[0])
      if a != nil: return a
      # we try without the '='; proc that return 'var' or macros are still
      # possible:
      a = dotTransformation(c, n[0])
      if a.kind == nkDotCall:
        a.kind = nkCall
        a = semExprWithType(c, a, {efLValue})
  of nkBracketExpr:
    # a[i] = x
    # --> `[]=`(a, i, x)
    a = semSubscript(c, a, {efLValue})
    if a == nil:
      result = buildOverloadedSubscripts(n.sons[0], getIdent"[]=")
      add(result, n[1])
      return semExprNoType(c, result)
  of nkCurlyExpr:
    # a{i} = x -->  `{}=`(a, i, x)
    result = buildOverloadedSubscripts(n.sons[0], getIdent"{}=")
    add(result, n[1])
    return semExprNoType(c, result)
  else:
    a = semExprWithType(c, a, {efLValue})
  n.sons[0] = a
  # a = b # both are vars, means: a[] = b[]
  # a = b # b no 'var T' means: a = addr(b)
  var le = a.typ
  if skipTypes(le, {tyGenericInst}).kind != tyVar and 
      IsAssignable(c, a) == arNone:
    # Direct assignment to a discriminant is allowed!
    localError(a.info, errXCannotBeAssignedTo,
               renderTree(a, {renderNoComments}))
  else:
    let
      lhs = n.sons[0]
      lhsIsResult = lhs.kind == nkSym and lhs.sym.kind == skResult
    var
      rhs = semExprWithType(c, n.sons[1], 
        if lhsIsResult: {efAllowDestructor} else: {})
    if lhsIsResult:
      n.typ = EnforceVoidContext
      if lhs.sym.typ.kind == tyGenericParam:
        if matchTypeClass(lhs.typ, rhs.typ):
          InternalAssert c.p.resultSym != nil
          lhs.typ = rhs.typ
          c.p.resultSym.typ = rhs.typ
          c.p.owner.typ.sons[0] = rhs.typ
        else:      
          typeMismatch(n, lhs.typ, rhs.typ)

    n.sons[1] = fitNode(c, le, rhs)
    fixAbstractType(c, n)
    asgnToResultVar(c, n, n.sons[0], n.sons[1])
  result = n

proc SemReturn(c: PContext, n: PNode): PNode =
  result = n
  checkSonsLen(n, 1)
  if c.p.owner.kind in {skConverter, skMethod, skProc, skMacro} or
     (c.p.owner.kind == skIterator and c.p.owner.typ.callConv == ccClosure):
    if n.sons[0].kind != nkEmpty:
      # transform ``return expr`` to ``result = expr; return``
      if c.p.resultSym != nil: 
        var a = newNodeI(nkAsgn, n.sons[0].info)
        addSon(a, newSymNode(c.p.resultSym))
        addSon(a, n.sons[0])
        n.sons[0] = semAsgn(c, a)
        # optimize away ``result = result``:
        if n[0][1].kind == nkSym and n[0][1].sym == c.p.resultSym: 
          n.sons[0] = ast.emptyNode
      else:
        LocalError(n.info, errNoReturnTypeDeclared)
  else:
    LocalError(n.info, errXNotAllowedHere, "\'return\'")

proc semProcBody(c: PContext, n: PNode): PNode =
  openScope(c)
  result = semExpr(c, n)
  if c.p.resultSym != nil and not isEmptyType(result.typ):
    # transform ``expr`` to ``result = expr``, but not if the expr is already
    # ``result``:
    if result.kind == nkSym and result.sym == c.p.resultSym:
      nil
    elif result.kind == nkNilLit:
      # or ImplicitlyDiscardable(result):
      # new semantic: 'result = x' triggers the void context
      result.typ = nil
    elif result.kind == nkStmtListExpr and result.typ.kind == tyNil:
      # to keep backwards compatibility bodies like:
      #   nil
      #   # comment
      # are not expressions:
      fixNilType(result)
    else:
      var a = newNodeI(nkAsgn, n.info, 2)
      a.sons[0] = newSymNode(c.p.resultSym)
      a.sons[1] = result
      result = semAsgn(c, a)
  else:
    discardCheck(result)
  closeScope(c)

proc SemYieldVarResult(c: PContext, n: PNode, restype: PType) =
  var t = skipTypes(restype, {tyGenericInst})
  case t.kind
  of tyVar:
    n.sons[0] = takeImplicitAddr(c, n.sons[0])
  of tyTuple:
    for i in 0.. <t.sonsLen:
      var e = skipTypes(t.sons[i], {tyGenericInst})
      if e.kind == tyVar:
        if n.sons[0].kind == nkPar:
          n.sons[0].sons[i] = takeImplicitAddr(c, n.sons[0].sons[i])
        elif n.sons[0].kind in {nkHiddenStdConv, nkHiddenSubConv} and 
             n.sons[0].sons[1].kind == nkPar:
          var a = n.sons[0].sons[1]
          a.sons[i] = takeImplicitAddr(c, a.sons[i])
        else:
          localError(n.sons[0].info, errXExpected, "tuple constructor")
  else: nil
  
proc SemYield(c: PContext, n: PNode): PNode =
  result = n
  checkSonsLen(n, 1)
  if c.p.owner == nil or c.p.owner.kind != skIterator:
    LocalError(n.info, errYieldNotAllowedHere)
  elif c.p.inTryStmt > 0 and c.p.owner.typ.callConv != ccInline:
    LocalError(n.info, errYieldNotAllowedInTryStmt)
  elif n.sons[0].kind != nkEmpty:
    n.sons[0] = SemExprWithType(c, n.sons[0]) # check for type compatibility:
    var restype = c.p.owner.typ.sons[0]
    if restype != nil:
      n.sons[0] = fitNode(c, restype, n.sons[0])
      if n.sons[0].typ == nil: InternalError(n.info, "semYield")
      SemYieldVarResult(c, n, restype)
    else:
      localError(n.info, errCannotReturnExpr)
  elif c.p.owner.typ.sons[0] != nil:
    localError(n.info, errGenerated, "yield statement must yield a value")

proc lookUpForDefined(c: PContext, i: PIdent, onlyCurrentScope: bool): PSym =
  if onlyCurrentScope: 
    result = localSearchInScope(c, i)
  else: 
    result = searchInScopes(c, i) # no need for stub loading

proc LookUpForDefined(c: PContext, n: PNode, onlyCurrentScope: bool): PSym = 
  case n.kind
  of nkIdent: 
    result = LookupForDefined(c, n.ident, onlyCurrentScope)
  of nkDotExpr:
    result = nil
    if onlyCurrentScope: return 
    checkSonsLen(n, 2)
    var m = LookupForDefined(c, n.sons[0], onlyCurrentScope)
    if (m != nil) and (m.kind == skModule): 
      if (n.sons[1].kind == nkIdent): 
        var ident = n.sons[1].ident
        if m == c.module: 
          result = StrTableGet(c.topLevelScope.symbols, ident)
        else: 
          result = StrTableGet(m.tab, ident)
      else: 
        LocalError(n.sons[1].info, errIdentifierExpected, "")
  of nkAccQuoted:
    result = lookupForDefined(c, considerAcc(n), onlyCurrentScope)
  of nkSym:
    result = n.sym
  else: 
    LocalError(n.info, errIdentifierExpected, renderTree(n))
    result = nil

proc semDefined(c: PContext, n: PNode, onlyCurrentScope: bool): PNode = 
  checkSonsLen(n, 2)
  # we replace this node by a 'true' or 'false' node:
  result = newIntNode(nkIntLit, 0)
  if LookUpForDefined(c, n.sons[1], onlyCurrentScope) != nil: 
    result.intVal = 1
  elif not onlyCurrentScope and (n.sons[1].kind == nkIdent) and
      condsyms.isDefined(n.sons[1].ident): 
    result.intVal = 1
  result.info = n.info
  result.typ = getSysType(tyBool)

proc setMs(n: PNode, s: PSym): PNode = 
  result = n
  n.sons[0] = newSymNode(s)
  n.sons[0].info = n.info

proc expectMacroOrTemplateCall(c: PContext, n: PNode): PSym =
  ## The argument to the proc should be nkCall(...) or similar
  ## Returns the macro/template symbol
  if isCallExpr(n):
    var expandedSym = qualifiedLookup(c, n[0], {checkUndeclared})
    if expandedSym == nil:
      LocalError(n.info, errUndeclaredIdentifier, n[0].renderTree)
      return errorSym(c, n[0])

    if expandedSym.kind notin {skMacro, skTemplate}:
      LocalError(n.info, errXisNoMacroOrTemplate, expandedSym.name.s)
      return errorSym(c, n[0])

    result = expandedSym
  else:
    LocalError(n.info, errXisNoMacroOrTemplate, n.renderTree)
    result = errorSym(c, n)

proc expectString(c: PContext, n: PNode): string =
  var n = semConstExpr(c, n)
  if n.kind in nkStrKinds:
    return n.strVal
  else:
    LocalError(n.info, errStringLiteralExpected)

proc getMagicSym(magic: TMagic): PSym =
  result = newSym(skProc, getIdent($magic), GetCurrOwner(), gCodegenLineInfo)
  result.magic = magic

proc newAnonSym(kind: TSymKind, info: TLineInfo,
                owner = getCurrOwner()): PSym =
  result = newSym(kind, idAnon, owner, info)
  result.flags = {sfGenSym}

proc semUsing(c: PContext, n: PNode): PNode =
  result = newNodeI(nkEmpty, n.info)
  for e in n.sons:
    let usedSym = semExpr(c, e)
    if usedSym.kind == nkSym:
      case usedSym.sym.kind
      of skLocalVars + {skConst}:
        c.currentScope.usingSyms.safeAdd(usedSym)
        continue
      of skProcKinds:
        addDeclAt(c.currentScope, usedSym.sym)
        continue
      else: nil

    LocalError(e.info, errUsingNoSymbol, e.renderTree)

proc semExpandToAst(c: PContext, n: PNode): PNode =
  var macroCall = n[1]
  var expandedSym = expectMacroOrTemplateCall(c, macroCall)
  if expandedSym.kind == skError: return n

  macroCall.sons[0] = newSymNode(expandedSym, macroCall.info)
  markUsed(n, expandedSym)

  for i in countup(1, macroCall.len-1):
    macroCall.sons[i] = semExprWithType(c, macroCall[i], {})

  # Preserve the magic symbol in order to be handled in evals.nim
  InternalAssert n.sons[0].sym.magic == mExpandToAst
  n.typ = getSysSym("PNimrodNode").typ # expandedSym.getReturnType
  result = n

proc semExpandToAst(c: PContext, n: PNode, magicSym: PSym,
                    flags: TExprFlags = {}): PNode =
  if sonsLen(n) == 2:
    n.sons[0] = newSymNode(magicSym, n.info)
    result = semExpandToAst(c, n)
  else:
    result = semDirectOp(c, n, flags)

proc processQuotations(n: var PNode, op: string,
                       quotes: var seq[PNode],
                       ids: var seq[PNode]) =
  template returnQuote(q) =
    quotes.add q
    n = newIdentNode(getIdent($quotes.len), n.info)
    ids.add n
    return

  if n.kind == nkPrefix:
    checkSonsLen(n, 2)
    if n[0].kind == nkIdent:
      var examinedOp = n[0].ident.s
      if examinedOp == op:
        returnQuote n[1]
      elif examinedOp.startsWith(op):
        n.sons[0] = newIdentNode(getIdent(examinedOp.substr(op.len)), n.info)
  elif n.kind == nkAccQuoted and op == "``":
    returnQuote n[0]
 
  if not n.isAtom:
    for i in 0 .. <n.len:
      processQuotations(n.sons[i], op, quotes, ids)

proc semQuoteAst(c: PContext, n: PNode): PNode =
  InternalAssert n.len == 2 or n.len == 3
  # We transform the do block into a template with a param for
  # each interpolation. We'll pass this template to getAst.
  var
    doBlk = n{-1}
    op = if n.len == 3: expectString(c, n[1]) else: "``"
    quotes = newSeq[PNode](1)
      # the quotes will be added to a nkCall statement 
      # leave some room for the callee symbol
    ids = newSeq[PNode]()
      # this will store the generated param names

  if doBlk.kind != nkDo:
    LocalError(n.info, errXExpected, "block")

  processQuotations(doBlk.sons[bodyPos], op, quotes, ids)
  
  doBlk.sons[namePos] = newAnonSym(skTemplate, n.info).newSymNode
  if ids.len > 0:
    doBlk[paramsPos].sons.setLen(2)
    doBlk[paramsPos].sons[0] = getSysSym("stmt").newSymNode # return type
    ids.add getSysSym("expr").newSymNode # params type
    ids.add emptyNode # no default value
    doBlk[paramsPos].sons[1] = newNode(nkIdentDefs, n.info, ids)
  
  var tmpl = semTemplateDef(c, doBlk)
  quotes[0] = tmpl[namePos]
  result = newNode(nkCall, n.info, @[
    getMagicSym(mExpandToAst).newSymNode,
    newNode(nkCall, n.info, quotes)])
  result = semExpandToAst(c, result)

proc tryExpr(c: PContext, n: PNode, flags: TExprFlags = {}): PNode =
  # watch out, hacks ahead:
  let oldErrorCount = msgs.gErrorCounter
  let oldErrorMax = msgs.gErrorMax
  inc c.InCompilesContext
  inc msgs.gSilence
  # do not halt after first error:
  msgs.gErrorMax = high(int)
  
  # open a scope for temporary symbol inclusions:
  let oldScope = c.currentScope
  openScope(c)
  let oldOwnerLen = len(gOwners)
  let oldGenerics = c.generics
  let oldContextLen = msgs.getInfoContextLen()
  
  let oldInGenericContext = c.InGenericContext
  let oldInUnrolledContext = c.InUnrolledContext
  let oldInGenericInst = c.InGenericInst
  let oldProcCon = c.p
  c.generics = @[]
  try:
    result = semExpr(c, n, flags)
    if msgs.gErrorCounter != oldErrorCount: result = nil
  except ERecoverableError:
    nil
  # undo symbol table changes (as far as it's possible):
  c.generics = oldGenerics
  c.InGenericContext = oldInGenericContext
  c.InUnrolledContext = oldInUnrolledContext
  c.InGenericInst = oldInGenericInst
  c.p = oldProcCon
  msgs.setInfoContextLen(oldContextLen)
  setlen(gOwners, oldOwnerLen)
  c.currentScope = oldScope
  dec c.InCompilesContext
  dec msgs.gSilence
  msgs.gErrorCounter = oldErrorCount
  msgs.gErrorMax = oldErrorMax

proc semCompiles(c: PContext, n: PNode, flags: TExprFlags): PNode =
  # we replace this node by a 'true' or 'false' node:
  if sonsLen(n) != 2: return semDirectOp(c, n, flags)
  
  result = newIntNode(nkIntLit, ord(tryExpr(c, n[1], flags) != nil))
  result.info = n.info
  result.typ = getSysType(tyBool)

proc semShallowCopy(c: PContext, n: PNode, flags: TExprFlags): PNode =
  if sonsLen(n) == 3:
    # XXX ugh this is really a hack: shallowCopy() can be overloaded only
    # with procs that take not 2 parameters:
    result = newNodeI(nkFastAsgn, n.info)
    result.add(n[1])
    result.add(n[2])
    result = semAsgn(c, result)
  else:
    result = semDirectOp(c, n, flags)

proc semMagic(c: PContext, n: PNode, s: PSym, flags: TExprFlags): PNode = 
  # this is a hotspot in the compiler!
  # DON'T forget to update ast.SpecialSemMagics if you add a magic here!
  result = n
  case s.magic # magics that need special treatment
  of mDefined: result = semDefined(c, setMs(n, s), false)
  of mDefinedInScope: result = semDefined(c, setMs(n, s), true)
  of mCompiles: result = semCompiles(c, setMs(n, s), flags)
  of mLow: result = semLowHigh(c, setMs(n, s), mLow)
  of mHigh: result = semLowHigh(c, setMs(n, s), mHigh)
  of mSizeOf: result = semSizeof(c, setMs(n, s))
  of mIs: result = semIs(c, setMs(n, s))
  of mOf: result = semOf(c, setMs(n, s))
  of mEcho: result = semEcho(c, setMs(n, s))
  of mShallowCopy: result = semShallowCopy(c, n, flags)
  of mExpandToAst: result = semExpandToAst(c, n, s, flags)
  of mQuoteAst: result = semQuoteAst(c, n)
  of mAstToStr:
    checkSonsLen(n, 2)
    result = newStrNodeT(renderTree(n[1], {renderNoComments}), n)
    result.typ = getSysType(tyString)
  else: result = semDirectOp(c, n, flags)

proc semWhen(c: PContext, n: PNode, semCheck = true): PNode =
  # If semCheck is set to false, ``when`` will return the verbatim AST of
  # the correct branch. Otherwise the AST will be passed through semStmt.
  result = nil
  
  template setResult(e: expr) =
    if semCheck: result = semStmt(c, e) # do not open a new scope!
    else: result = e

  for i in countup(0, sonsLen(n) - 1): 
    var it = n.sons[i]
    case it.kind
    of nkElifBranch, nkElifExpr: 
      checkSonsLen(it, 2)
      var e = semConstExpr(c, it.sons[0])
      if e.kind != nkIntLit: 
        # can happen for cascading errors, assume false
        # InternalError(n.info, "semWhen")
        discard
      elif e.intVal != 0 and result == nil:
        setResult(it.sons[1]) 
    of nkElse, nkElseExpr:
      checkSonsLen(it, 1)
      if result == nil: 
        setResult(it.sons[0])
    else: illFormedAst(n)
  if result == nil:
    result = newNodeI(nkEmpty, n.info) 
  # The ``when`` statement implements the mechanism for platform dependent
  # code. Thus we try to ensure here consistent ID allocation after the
  # ``when`` statement.
  IDsynchronizationPoint(200)

proc semSetConstr(c: PContext, n: PNode): PNode = 
  result = newNodeI(nkCurly, n.info)
  result.typ = newTypeS(tySet, c)
  if sonsLen(n) == 0: 
    rawAddSon(result.typ, newTypeS(tyEmpty, c))
  else: 
    # only semantic checking for all elements, later type checking:
    var typ: PType = nil
    for i in countup(0, sonsLen(n) - 1): 
      if isRange(n.sons[i]): 
        checkSonsLen(n.sons[i], 3)
        n.sons[i].sons[1] = semExprWithType(c, n.sons[i].sons[1])
        n.sons[i].sons[2] = semExprWithType(c, n.sons[i].sons[2])
        if typ == nil: 
          typ = skipTypes(n.sons[i].sons[1].typ, 
                          {tyGenericInst, tyVar, tyOrdinal})
        n.sons[i].typ = n.sons[i].sons[2].typ # range node needs type too
      elif n.sons[i].kind == nkRange:
        # already semchecked
        if typ == nil:
          typ = skipTypes(n.sons[i].sons[0].typ, 
                          {tyGenericInst, tyVar, tyOrdinal})
      else:
        n.sons[i] = semExprWithType(c, n.sons[i])
        if typ == nil: 
          typ = skipTypes(n.sons[i].typ, {tyGenericInst, tyVar, tyOrdinal})
    if not isOrdinalType(typ):
      LocalError(n.info, errOrdinalTypeExpected)
      typ = makeRangeType(c, 0, MaxSetElements - 1, n.info)
    elif lengthOrd(typ) > MaxSetElements: 
      typ = makeRangeType(c, 0, MaxSetElements - 1, n.info)
    addSonSkipIntLit(result.typ, typ)
    for i in countup(0, sonsLen(n) - 1): 
      var m: PNode
      if isRange(n.sons[i]):
        m = newNodeI(nkRange, n.sons[i].info)
        addSon(m, fitNode(c, typ, n.sons[i].sons[1]))
        addSon(m, fitNode(c, typ, n.sons[i].sons[2]))
      elif n.sons[i].kind == nkRange: m = n.sons[i] # already semchecked
      else:
        m = fitNode(c, typ, n.sons[i])
      addSon(result, m)

proc semTableConstr(c: PContext, n: PNode): PNode =
  # we simply transform ``{key: value, key2, key3: value}`` to 
  # ``[(key, value), (key2, value2), (key3, value2)]``
  result = newNodeI(nkBracket, n.info)
  var lastKey = 0
  for i in 0..n.len-1:
    var x = n.sons[i]
    if x.kind == nkExprColonExpr and sonsLen(x) == 2:
      for j in countup(lastKey, i-1):
        var pair = newNodeI(nkPar, x.info)
        pair.add(n.sons[j])
        pair.add(x[1])
        result.add(pair)

      var pair = newNodeI(nkPar, x.info)
      pair.add(x[0])
      pair.add(x[1])
      result.add(pair)

      lastKey = i+1

  if lastKey != n.len: illFormedAst(n)
  result = semExpr(c, result)

type 
  TParKind = enum 
    paNone, paSingle, paTupleFields, paTuplePositions

proc checkPar(n: PNode): TParKind = 
  var length = sonsLen(n)
  if length == 0: 
    result = paTuplePositions # ()
  elif length == 1: 
    result = paSingle         # (expr)
  else: 
    if n.sons[0].kind == nkExprColonExpr: result = paTupleFields
    else: result = paTuplePositions
    for i in countup(0, length - 1): 
      if result == paTupleFields: 
        if (n.sons[i].kind != nkExprColonExpr) or
            not (n.sons[i].sons[0].kind in {nkSym, nkIdent}): 
          LocalError(n.sons[i].info, errNamedExprExpected)
          return paNone
      else: 
        if n.sons[i].kind == nkExprColonExpr: 
          LocalError(n.sons[i].info, errNamedExprNotAllowed)
          return paNone

proc semTupleFieldsConstr(c: PContext, n: PNode, flags: TExprFlags): PNode =
  result = newNodeI(nkPar, n.info)
  var typ = newTypeS(tyTuple, c)
  typ.n = newNodeI(nkRecList, n.info) # nkIdentDefs
  var ids = initIntSet()
  for i in countup(0, sonsLen(n) - 1):
    if (n.sons[i].kind != nkExprColonExpr) or
        not (n.sons[i].sons[0].kind in {nkSym, nkIdent}):
      illFormedAst(n.sons[i])
    var id: PIdent
    if n.sons[i].sons[0].kind == nkIdent: id = n.sons[i].sons[0].ident
    else: id = n.sons[i].sons[0].sym.name
    if ContainsOrIncl(ids, id.id): 
      localError(n.sons[i].info, errFieldInitTwice, id.s)
    n.sons[i].sons[1] = semExprWithType(c, n.sons[i].sons[1],
                                        flags*{efAllowDestructor})
    var f = newSymS(skField, n.sons[i].sons[0], c)
    f.typ = skipIntLit(n.sons[i].sons[1].typ)
    f.position = i
    rawAddSon(typ, f.typ)
    addSon(typ.n, newSymNode(f))
    n.sons[i].sons[0] = newSymNode(f)
    addSon(result, n.sons[i])
  result.typ = typ

proc semTuplePositionsConstr(c: PContext, n: PNode, flags: TExprFlags): PNode = 
  result = n                  # we don't modify n, but compute the type:
  var typ = newTypeS(tyTuple, c)  # leave typ.n nil!
  for i in countup(0, sonsLen(n) - 1): 
    n.sons[i] = semExprWithType(c, n.sons[i], flags*{efAllowDestructor})
    addSonSkipIntLit(typ, n.sons[i].typ)
  result.typ = typ

proc checkInitialized(n: PNode, ids: TIntSet, info: TLineInfo) =
  case n.kind
  of nkRecList:
    for i in countup(0, sonsLen(n) - 1):
      checkInitialized(n.sons[i], ids, info)
  of nkRecCase:
    if (n.sons[0].kind != nkSym): InternalError(info, "checkInitialized")
    checkInitialized(n.sons[0], ids, info)
    when false:
      # XXX we cannot check here, as we don't know the branch!
      for i in countup(1, sonsLen(n) - 1):
        case n.sons[i].kind
        of nkOfBranch, nkElse: checkInitialized(lastSon(n.sons[i]), ids, info)
        else: internalError(info, "checkInitialized")
  of nkSym:
    if tfNeedsInit in n.sym.typ.flags and n.sym.name.id notin ids:
      Message(info, errGenerated, "field not initialized: " & n.sym.name.s)
  else: internalError(info, "checkInitialized")

proc semObjConstr(c: PContext, n: PNode, flags: TExprFlags): PNode =
  var t = semTypeNode(c, n.sons[0], nil)
  result = n
  result.typ = t
  result.kind = nkObjConstr
  t = skipTypes(t, abstractInst)
  if t.kind == tyRef: t = skipTypes(t.sons[0], abstractInst)
  if t.kind != tyObject:
    localError(n.info, errGenerated, "object constructor needs an object type")
    return
  var objType = t
  var ids = initIntSet()
  for i in 1.. <n.len:
    let it = n.sons[i]
    if it.kind != nkExprColonExpr or it.sons[0].kind notin {nkSym, nkIdent}:
      localError(n.info, errNamedExprExpected)
      break
    var id: PIdent
    if it.sons[0].kind == nkIdent: id = it.sons[0].ident
    else: id = it.sons[0].sym.name
    if ContainsOrIncl(ids, id.id):
      localError(it.info, errFieldInitTwice, id.s)
    var e = semExprWithType(c, it.sons[1], flags*{efAllowDestructor})
    var
      check: PNode = nil
      f: PSym
    t = objType
    while true:
      check = nil
      f = lookupInRecordAndBuildCheck(c, it, t.n, id, check)
      if f != nil: break
      if t.sons[0] == nil: break
      t = skipTypes(t.sons[0], {tyGenericInst})
    if f != nil and fieldVisible(c, f):
      it.sons[0] = newSymNode(f)
      e = fitNode(c, f.typ, e)
      # small hack here in a nkObjConstr the ``nkExprColonExpr`` node can have
      # 3 childen the last being the field check
      if check != nil:
        check.sons[0] = it.sons[0]
        it.add(check)
    else:
      localError(it.info, errUndeclaredFieldX, id.s)
    it.sons[1] = e
    # XXX object field name check for 'case objects' if the kind is static?
  if tfNeedsInit in objType.flags:
    while true:
      checkInitialized(objType.n, ids, n.info)
      if objType.sons[0] == nil: break
      objType = skipTypes(objType.sons[0], {tyGenericInst})

proc semBlock(c: PContext, n: PNode): PNode =
  result = n
  Inc(c.p.nestedBlockCounter)
  checkSonsLen(n, 2)
  openScope(c) # BUGFIX: label is in the scope of block!
  if n.sons[0].kind != nkEmpty:
    var labl = newSymG(skLabel, n.sons[0], c)
    if sfGenSym notin labl.flags:
      addDecl(c, labl)
      n.sons[0] = newSymNode(labl, n.sons[0].info)
    suggestSym(n.sons[0], labl)
  n.sons[1] = semExpr(c, n.sons[1])
  n.typ = n.sons[1].typ
  if isEmptyType(n.typ): n.kind = nkBlockStmt
  else: n.kind = nkBlockExpr
  closeScope(c)
  Dec(c.p.nestedBlockCounter)

proc buildCall(n: PNode): PNode =
  if n.kind == nkDotExpr and n.len == 2:
    # x.y --> y(x)
    result = newNodeI(nkCall, n.info, 2)
    result.sons[0] = n.sons[1]
    result.sons[1] = n.sons[0]
  elif n.kind in nkCallKinds and n.sons[0].kind == nkDotExpr:
    # x.y(a) -> y(x, a)
    let a = n.sons[0]
    result = newNodeI(nkCall, n.info, n.len+1)
    result.sons[0] = a.sons[1]
    result.sons[1] = a.sons[0]
    for i in 1 .. <n.len: result.sons[i+1] = n.sons[i]
  else:
    result = n

proc doBlockIsStmtList(n: PNode): bool =
  result = n.kind == nkDo and
           n[paramsPos].sonsLen == 1 and
           n[paramsPos][0].kind == nkEmpty

proc fixImmediateParams(n: PNode): PNode =
  # XXX: Temporary work-around until we carry out
  # the planned overload resolution reforms
  for i in 1 .. <safeLen(n):
    if doBlockIsStmtList(n[i]):
      n.sons[i] = n[i][bodyPos]
  result = n

proc semExport(c: PContext, n: PNode): PNode =
  var x = newNodeI(n.kind, n.info)
  #let L = if n.kind == nkExportExceptStmt: L = 1 else: n.len
  for i in 0.. <n.len:
    let a = n.sons[i]
    var o: TOverloadIter
    var s = initOverloadIter(o, c, a)
    if s == nil:
      localError(a.info, errGenerated, "invalid expr for 'export': " &
          renderTree(a))
    while s != nil:
      if s.kind in ExportableSymKinds+{skModule}:
        x.add(newSymNode(s, a.info))
      s = nextOverloadIter(o, c, a)
  if c.module.ast.isNil:
    c.module.ast = newNodeI(nkStmtList, n.info)
  assert c.module.ast.kind == nkStmtList
  c.module.ast.add x
  result = n

proc semExpr(c: PContext, n: PNode, flags: TExprFlags = {}): PNode = 
  result = n
  if gCmd == cmdIdeTools: suggestExpr(c, n)
  if nfSem in n.flags: return 
  case n.kind
  of nkIdent, nkAccQuoted:
    var s = lookUp(c, n)
    semCaptureSym(s, c.p.owner)
    result = semSym(c, n, s, flags)
    if s.kind in {skProc, skMethod, skIterator, skConverter}:
      #performProcvarCheck(c, n, s)
      result = symChoice(c, n, s, scClosed)
      if result.kind == nkSym:
        markIndirect(c, result.sym)
        if isGenericRoutine(result.sym):
          LocalError(n.info, errInstantiateXExplicitely, s.name.s)
  of nkSym:
    # because of the changed symbol binding, this does not mean that we
    # don't have to check the symbol for semantics here again!
    result = semSym(c, n, n.sym, flags)
  of nkEmpty, nkNone, nkCommentStmt: 
    nil
  of nkNilLit: 
    result.typ = getSysType(tyNil)
  of nkIntLit:
    if result.typ == nil: setIntLitType(result)
  of nkInt8Lit:
    if result.typ == nil: result.typ = getSysType(tyInt8)
  of nkInt16Lit: 
    if result.typ == nil: result.typ = getSysType(tyInt16)
  of nkInt32Lit: 
    if result.typ == nil: result.typ = getSysType(tyInt32)
  of nkInt64Lit: 
    if result.typ == nil: result.typ = getSysType(tyInt64)
  of nkUIntLit:
    if result.typ == nil: result.typ = getSysType(tyUInt)
  of nkUInt8Lit: 
    if result.typ == nil: result.typ = getSysType(tyUInt8)
  of nkUInt16Lit: 
    if result.typ == nil: result.typ = getSysType(tyUInt16)
  of nkUInt32Lit: 
    if result.typ == nil: result.typ = getSysType(tyUInt32)
  of nkUInt64Lit: 
    if result.typ == nil: result.typ = getSysType(tyUInt64)
  of nkFloatLit: 
    if result.typ == nil: result.typ = getFloatLitType(result)
  of nkFloat32Lit: 
    if result.typ == nil: result.typ = getSysType(tyFloat32)
  of nkFloat64Lit: 
    if result.typ == nil: result.typ = getSysType(tyFloat64)
  of nkFloat128Lit: 
    if result.typ == nil: result.typ = getSysType(tyFloat128)
  of nkStrLit..nkTripleStrLit: 
    if result.typ == nil: result.typ = getSysType(tyString)
  of nkCharLit: 
    if result.typ == nil: result.typ = getSysType(tyChar)
  of nkDotExpr: 
    result = semFieldAccess(c, n, flags)
    if result.kind == nkDotCall:
      result.kind = nkCall
      result = semExpr(c, result, flags)
  of nkBind:
    Message(n.info, warnDeprecated, "bind")
    result = semExpr(c, n.sons[0], flags)
  of nkTypeOfExpr, nkTupleTy, nkRefTy..nkEnumTy:
    var typ = semTypeNode(c, n, nil).skipTypes({tyTypeDesc})
    result = symNodeFromType(c, typ, n.info)
  of nkCall, nkInfix, nkPrefix, nkPostfix, nkCommand, nkCallStrLit: 
    # check if it is an expression macro:
    checkMinSonsLen(n, 1)
    let mode = if nfDelegate in n.flags: {} else: {checkUndeclared}
    var s = qualifiedLookup(c, n.sons[0], mode)
    if s != nil: 
      case s.kind
      of skMacro:
        if sfImmediate notin s.flags:
          result = semDirectOp(c, n, flags)
        else:
          var p = fixImmediateParams(n)
          result = semMacroExpr(c, p, p, s)
      of skTemplate:
        if sfImmediate notin s.flags:
          result = semDirectOp(c, n, flags)
        else:
          var p = fixImmediateParams(n)
          result = semTemplateExpr(c, p, s)
      of skType:
        # XXX think about this more (``set`` procs)
        if n.len == 2:
          result = semConv(c, n, s)
        elif n.len == 1:
          result = semObjConstr(c, n, flags)
        elif Contains(c.AmbiguousSymbols, s.id): 
          LocalError(n.info, errUseQualifier, s.name.s)
        elif s.magic == mNone: result = semDirectOp(c, n, flags)
        else: result = semMagic(c, n, s, flags)
      of skProc, skMethod, skConverter, skIterator: 
        if s.magic == mNone: result = semDirectOp(c, n, flags)
        else: result = semMagic(c, n, s, flags)
      else:
        #liMessage(n.info, warnUser, renderTree(n));
        result = semIndirectOp(c, n, flags)
    elif isSymChoice(n.sons[0]) or n[0].kind == nkBracketExpr and 
        isSymChoice(n[0][0]):
      result = semDirectOp(c, n, flags)
    elif nfDelegate in n.flags:
      result = semDirectOp(c, n, flags)
    else:
      result = semIndirectOp(c, n, flags)
  of nkWhen:
    if efWantStmt in flags:
      result = semWhen(c, n, true)
    else:
      result = semWhen(c, n, false)
      result = semExpr(c, result, flags)
  of nkBracketExpr:
    checkMinSonsLen(n, 1)
    var s = qualifiedLookup(c, n.sons[0], {checkUndeclared})
    if s != nil and s.kind in {skProc, skMethod, skConverter, skIterator}: 
      # type parameters: partial generic specialization
      n.sons[0] = semSymGenericInstantiation(c, n.sons[0], s)
      result = explicitGenericInstantiation(c, n, s)
    else: 
      result = semArrayAccess(c, n, flags)
  of nkCurlyExpr:
    result = semExpr(c, buildOverloadedSubscripts(n, getIdent"{}"), flags)
  of nkPragmaExpr: 
    # which pragmas are allowed for expressions? `likely`, `unlikely`
    internalError(n.info, "semExpr() to implement") # XXX: to implement
  of nkPar: 
    case checkPar(n)
    of paNone: result = errorNode(c, n)
    of paTuplePositions: result = semTuplePositionsConstr(c, n, flags)
    of paTupleFields: result = semTupleFieldsConstr(c, n, flags)
    of paSingle: result = semExpr(c, n.sons[0], flags)
  of nkCurly: result = semSetConstr(c, n)
  of nkBracket: result = semArrayConstr(c, n, flags)
  of nkObjConstr: result = semObjConstr(c, n, flags)
  of nkLambdaKinds: result = semLambda(c, n, flags)
  of nkDerefExpr: result = semDeref(c, n)
  of nkAddr:
    result = n
    checkSonsLen(n, 1)
    n.sons[0] = semExprWithType(c, n.sons[0])
    if isAssignable(c, n.sons[0]) notin {arLValue, arLocalLValue}: 
      LocalError(n.info, errExprHasNoAddress)
    n.typ = makePtrType(c, n.sons[0].typ)
  of nkHiddenAddr, nkHiddenDeref:
    checkSonsLen(n, 1)
    n.sons[0] = semExpr(c, n.sons[0], flags)
  of nkCast: result = semCast(c, n)
  of nkIfExpr, nkIfStmt: result = semIf(c, n)
  of nkHiddenStdConv, nkHiddenSubConv, nkConv, nkHiddenCallConv: 
    checkSonsLen(n, 2)
  of nkStringToCString, nkCStringToString, nkObjDownConv, nkObjUpConv: 
    checkSonsLen(n, 1)
  of nkChckRangeF, nkChckRange64, nkChckRange: 
    checkSonsLen(n, 3)
  of nkCheckedFieldExpr: 
    checkMinSonsLen(n, 2)
  of nkTableConstr:
    result = semTableConstr(c, n)
  of nkClosedSymChoice, nkOpenSymChoice:
    # handling of sym choices is context dependent
    # the node is left intact for now
  of nkStaticExpr:
    result = semStaticExpr(c, n)
  of nkAsgn: result = semAsgn(c, n)
  of nkBlockStmt, nkBlockExpr: result = semBlock(c, n)
  of nkStmtList, nkStmtListExpr: result = semStmtList(c, n)
  of nkRaiseStmt: result = semRaise(c, n)
  of nkVarSection: result = semVarOrLet(c, n, skVar)
  of nkLetSection: result = semVarOrLet(c, n, skLet)
  of nkConstSection: result = semConst(c, n)
  of nkTypeSection: result = SemTypeSection(c, n)
  of nkDiscardStmt: result = semDiscard(c, n)
  of nkWhileStmt: result = semWhile(c, n)
  of nkTryStmt: result = semTry(c, n)
  of nkBreakStmt, nkContinueStmt: result = semBreakOrContinue(c, n)
  of nkForStmt, nkParForStmt: result = semFor(c, n)
  of nkCaseStmt: result = semCase(c, n)
  of nkReturnStmt: result = semReturn(c, n)
  of nkUsingStmt: result = semUsing(c, n)
  of nkAsmStmt: result = semAsm(c, n)
  of nkYieldStmt: result = semYield(c, n)
  of nkPragma: pragma(c, c.p.owner, n, stmtPragmas)
  of nkIteratorDef: result = semIterator(c, n)
  of nkProcDef: result = semProc(c, n)
  of nkMethodDef: result = semMethod(c, n)
  of nkConverterDef: result = semConverterDef(c, n)
  of nkMacroDef: result = semMacroDef(c, n)
  of nkTemplateDef: result = semTemplateDef(c, n)
  of nkImportStmt: 
    if not isTopLevel(c): LocalError(n.info, errXOnlyAtModuleScope, "import")
    result = evalImport(c, n)
  of nkImportExceptStmt:
    if not isTopLevel(c): LocalError(n.info, errXOnlyAtModuleScope, "import")
    result = evalImportExcept(c, n)
  of nkFromStmt: 
    if not isTopLevel(c): LocalError(n.info, errXOnlyAtModuleScope, "from")
    result = evalFrom(c, n)
  of nkIncludeStmt: 
    if not isTopLevel(c): LocalError(n.info, errXOnlyAtModuleScope, "include")
    result = evalInclude(c, n)
  of nkExportStmt, nkExportExceptStmt:
    if not isTopLevel(c): LocalError(n.info, errXOnlyAtModuleScope, "export")
    result = semExport(c, n)
  of nkPragmaBlock:
    result = semPragmaBlock(c, n)
  of nkStaticStmt:
    result = semStaticStmt(c, n)
  else:
    LocalError(n.info, errInvalidExpressionX,
               renderTree(n, {renderNoComments}))
  if result != nil: incl(result.flags, nfSem)
