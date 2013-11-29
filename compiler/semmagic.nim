#
#
#           The Nimrod Compiler
#        (c) Copyright 2013 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This include file implements the semantic checking for magics.
# included from sem.nim

proc semIsPartOf(c: PContext, n: PNode, flags: TExprFlags): PNode =
  var r = isPartOf(n[1], n[2])
  result = newIntNodeT(ord(r), n)
  
proc expectIntLit(c: PContext, n: PNode): int =
  let x = c.semConstExpr(c, n)
  case x.kind
  of nkIntLit..nkInt64Lit: result = int(x.intVal)
  else: LocalError(n.info, errIntLiteralExpected)

proc semInstantiationInfo(c: PContext, n: PNode): PNode =
  result = newNodeIT(nkPar, n.info, n.typ)
  let idx = expectIntLit(c, n.sons[1])
  let useFullPaths = expectIntLit(c, n.sons[2])
  let info = getInfoContext(idx)
  var filename = newNodeIT(nkStrLit, n.info, getSysType(tyString))
  filename.strVal = if useFullPaths != 0: info.toFullPath else: info.ToFilename
  var line = newNodeIT(nkIntLit, n.info, getSysType(tyInt))
  line.intVal = ToLinenumber(info)
  result.add(filename)
  result.add(line)

proc semTypeTraits(c: PContext, n: PNode): PNode =
  checkMinSonsLen(n, 2)
  internalAssert n.sons[1].kind == nkSym
  let typArg = n.sons[1].sym
  if typArg.kind == skType or
    (typArg.kind == skParam and typArg.typ.sonsLen > 0):
    # This is either a type known to sem or a typedesc
    # param to a regular proc (again, known at instantiation)
    result = evalTypeTrait(n[0], n[1], GetCurrOwner())
  else:
    # a typedesc variable, pass unmodified to evals
    result = n

proc semOrd(c: PContext, n: PNode): PNode = 
  result = n
  result.typ = makeRangeType(c, firstOrd(n.sons[1].typ),
                                lastOrd(n.sons[1].typ), n.info)

proc semBindSym(c: PContext, n: PNode): PNode =
  result = copyNode(n)
  result.add(n.sons[0])
  
  let sl = semConstExpr(c, n.sons[1])
  if sl.kind notin {nkStrLit, nkRStrLit, nkTripleStrLit}: 
    LocalError(n.sons[1].info, errStringLiteralExpected)
    return errorNode(c, n)
  
  let isMixin = semConstExpr(c, n.sons[2])
  if isMixin.kind != nkIntLit or isMixin.intVal < 0 or
      isMixin.intVal > high(TSymChoiceRule).int:
    LocalError(n.sons[2].info, errConstExprExpected)
    return errorNode(c, n)
  
  let id = newIdentNode(getIdent(sl.strVal), n.info)
  let s = QualifiedLookUp(c, id)
  if s != nil:
    # we need to mark all symbols:
    var sc = symChoice(c, id, s, TSymChoiceRule(isMixin.intVal))
    result.add(sc)
  else:
    LocalError(n.sons[1].info, errUndeclaredIdentifier, sl.strVal)

proc semLocals(c: PContext, n: PNode): PNode =
  var counter = 0
  var tupleType = newTypeS(tyTuple, c)
  result = newNodeIT(nkPar, n.info, tupleType)
  tupleType.n = newNodeI(nkRecList, n.info)
  # for now we skip openarrays ...
  for scope in walkScopes(c.currentScope):
    if scope == c.topLevelScope: break
    for it in items(scope.symbols):
      # XXX parameters' owners are wrong for generics; this caused some pain
      # for closures too; we should finally fix it.
      #if it.owner != c.p.owner: return result
      if it.kind in skLocalVars and
          it.typ.skipTypes({tyGenericInst, tyVar}).kind notin
              {tyVarargs, tyOpenArray, tyTypeDesc, tyExpr, tyStmt, tyEmpty}:

        var field = newSym(skField, it.name, getCurrOwner(), n.info)
        field.typ = it.typ.skipTypes({tyGenericInst, tyVar})
        field.position = counter
        inc(counter)

        addSon(tupleType.n, newSymNode(field))
        addSonSkipIntLit(tupleType, field.typ)
        
        var a = newSymNode(it, result.info)
        if it.typ.skipTypes({tyGenericInst}).kind == tyVar: a = newDeref(a)
        result.add(a)


proc getEnumType(c: PContext, n: PNode): PType =   
  result = nil
  if n.typ.kind == tyEnum and (tfEnumSumTyp in n.typ.flags):    
    if n.kind == nkSym:   
      if n.sym.kind == skVar and n.sym.ast != nil:   
        if n.sym.ast.kind == nkSym and n.sym.ast.sym.ast != nil and         
          n.sym.ast.sym.ast.kind == nkSym and n.sym.ast.sym.ast.sym.kind == skType:        
          result = n.sym.ast.sym.ast.sym.typ
          return 
        elif n.sym.ast.kind in nkCallKinds:         
          debug(n.sym.ast.typ.sons[0])          
          result = n.sym.ast.typ.sons[0]
          return 
      else: 
        result = n.typ.sons[0]
        return             
  if n.info ?? "mac.nim":
    echo("--getEnumType needs to be extended to handle this case--")
    echo(renderTree(n))
    debug(n)  
    debug(n.sym.ast)
    debug(n.typ)        


#proc getEnumRef(c: PContext, n: PNode): PNode =
#  result = nil  
#  if n.typ.kind == tyEnum and n.kind == nkSym and (tfEnumSumTyp in n.typ.flags):   
#    if n.sym.kind == skVar and n.sym.ast != nil:    
#      if n.sym.ast.kind == nkSym:
#        var t = getEnumType(c, n) 
#        result = newNodeIT(nkCast, n.info, newType(tyPtr, n.sym))         
#        var p = newNodeIT(nkPtrTy, n.info, t)                   
#        p.addSon(newNodeIT(nkType, n.info, t))  

#        #var i = newIntNode(nkIntLit, n.sym.ast.sym.position and 0xFFFFFFFC) 
#        #echo(i.intVal)     

#        var i = newNodeI(nkInfix, n.info) 
#        i.addSon(newIdentNode(getIdent("and"), n.info))
#        #var x = newNodeI(nkConv, n.info)
#        #x.addSon(newIdentNode(getIdent("int"), n.info))
#        #x.addSon(n.sym.ast.sym.position)
#        var x = newIntNode(nkIntLit, n.sym.ast.sym.position)              
#        var y = newIntNode(nkIntLit, 0xFFFFFFFC)
#        x.info = n.info 
#        y.info = n.info        
#        x.typ = getSysType(tyInt)
#        y.typ = x.typ    
#        i.addSon(x)
#        i.addSon(y)                         
               
#        result.addSon(p)
#        result.addSon(i)
#        result.typ.newSons(1)
#        result.typ.sons[0] = t
#        result = semExpr(c, result) 
#      elif n.sym.ast.kind == nkCall: 
#        if n.info ?? "mac.nim": echo("getEnumRef ", n.sym.kind)
#        #result = newNodeI(nkInfix, n.info) 
#        #result.addSon(newIdentNode(getIdent("and"), n.info))
#        #var x = newNodeI(nkConv, n.info)
#        #x.addSon(newIdentNode(getIdent("int"), n.info))
#        #x.addSon(n.sym.ast)      
#        #var y = newIntNode(nkIntLit, platform.IntSize - 1)
#        #y.info = n.info
#        #x.typ = getSysType(tyInt)
#        #y.typ = x.typ    
#        #result.addSon(x)
#        #result.addSon(y)  
#        #if n.info ?? "mac.nim": echo(renderTree(result))
#        #result = semExpr(c, result)      
#    elif n.sym.kind == skEnumField: 
#      if n.info ?? "mac.nim": echo("getEnumRef ", n.sym.kind)
#      #if n.sym.typ == nil: n.sym.typ = n.typ
#      #result = newIntNode(nkIntLit, n.sym.position and (platform.IntSize - 1))
#      #result.info = n.info
#      #result.typ = n.typ         

proc getEnumOrd(c: PContext, n: PNode): PNode =
  result = n  
  if n.typ.kind == tyEnum and n.kind == nkSym and (tfEnumSumTyp in n.typ.flags):   
    if n.sym.kind == skVar and n.sym.ast != nil:    
      if n.sym.ast.kind == nkSym:       
        if n.info ?? "mac.nim": echo("Pop sym.typ ", n.sym.kind)
        result = newIntNode(nkIntLit, n.sym.ast.sym.position and (platform.IntSize - 1))
        result.info = n.info
        result.typ = n.typ
        return
      elif n.sym.ast.kind == nkCall: 
        if n.info ?? "mac.nim": echo("Pop sym.typ ", n.sym.kind)
        result = newNodeI(nkInfix, n.info) 
        result.addSon(newIdentNode(getIdent("and"), n.info))
        var x = newNodeI(nkConv, n.info)
        x.addSon(newIdentNode(getIdent("int"), n.info))
        x.addSon(n.sym.ast)      
        var y = newIntNode(nkIntLit, platform.IntSize - 1)
        y.info = n.info
        x.typ = getSysType(tyInt)
        y.typ = x.typ    
        result.addSon(x)
        result.addSon(y)  
        if n.info ?? "mac.nim": echo(renderTree(result))
        result = semExpr(c, result)
        return      
    elif n.sym.kind == skEnumField: 
      if n.info ?? "mac.nim": echo("Pop sym.typ ", n.sym.kind)
      if n.sym.typ == nil: n.sym.typ = n.typ
      result = newIntNode(nkIntLit, n.sym.position and (platform.IntSize - 1))
      result.info = n.info
      result.typ = n.typ 
      return
    else: 
      if n.info ?? "mac.nim": echo("Pop sym.typ ", n.sym.kind)
      result = newNodeI(nkInfix, n.info) 
      result.addSon(newIdentNode(getIdent("and"), n.info)) 
      var x = newNodeI(nkConv, n.info) 
      x.addSon(newIdentNode(getIdent("int"), n.info))
      x.addSon(n)         
      var y = newIntNode(nkIntLit, platform.IntSize - 1)
      y.info = n.info     
      x.typ = getSysType(tyInt)
      y.typ = x.typ     
      result.addSon(x)
      result.addSon(y)  
      if n.info ?? "mac.nim": echo(renderTree(result))
      result = semExpr(c, result)
      return    

  if n.info ?? "mac.nim":
    echo("--getEnumOrd needs to be extended to handle this case--")
    echo(renderTree(n))
    debug(n)    
    echo(n.sym.kind)
    debug(n.sym.ast) 
    echo("-------------------------------------------------------")


proc semEqEnum(c: PContext, n: PNode): PNode =
  if sonsLen(n) != 3: 
    LocalError(n.info, errXExpectsTypeOrValue, "mEqEnum")
  else:
    n.sons[1] = getEnumOrd(c, n.sons[1]) 
    n.sons[2] = getEnumOrd(c, n.sons[2])  
    result = n   

proc semShallowCopy(c: PContext, n: PNode, flags: TExprFlags): PNode

proc magicsAfterOverloadResolution(c: PContext, n: PNode, 
                                   flags: TExprFlags): PNode =                                    
  case n[0].sym.magic
  of mIsPartOf: result = semIsPartOf(c, n, flags)
  of mTypeTrait: result = semTypeTraits(c, n)
  of mAstToStr:
    result = newStrNodeT(renderTree(n[1], {renderNoComments}), n)
    result.typ = getSysType(tyString)
  of mInstantiationInfo: result = semInstantiationInfo(c, n)
  of mOrd: result = semOrd(c, n)
  of mHigh: result = semLowHigh(c, n, mHigh)
  of mShallowCopy: result = semShallowCopy(c, n, flags)
  of mNBindSym: result = semBindSym(c, n)
  of mLocals: result = semLocals(c, n)
  of mEqEnum: result = semEqEnum(c, n)
  else: result = n

