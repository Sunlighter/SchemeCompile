
type Symbol =
  | S_Interned of string
  | S_Uninterned of int

let nextSym = ref 0

let gensym () =
  let p = !nextSym
  nextSym := 1 + !nextSym
  (S_Uninterned p)

type Datum =
  | D_Unspecified
  | D_Bool of bool
  | D_Int of bigint
  | D_Float of float
  | D_Char of char
  | D_String of string
  | D_Symbol of Symbol
  | D_List of Datum list
  | D_Vector of Datum[]

type ParamSpecSrc =
  | PSS_Items of Symbol list
  | PSS_ItemsMore of Symbol list * Symbol

type ExprSrc =
  | ES_Literal of Datum
  | ES_VarRef of Symbol
  | ES_VarSet of Symbol * ExprSrc
  | ES_Begin of ExprSrc list
  | ES_IfThenElse of ExprSrc * ExprSrc * ExprSrc
  | ES_Lambda of ParamSpecSrc * ExprSrc
  | ES_Invoke of ExprSrc list
  | ES_And of ExprSrc list
  | ES_Or of ExprSrc list
  | ES_Catch of CatchRecordSrc
  | ES_Primitive of Symbol * ExprSrc list
  | ES_Let of LetClauseSrc list * ExprSrc
  | ES_LetStar of LetClauseSrc list * ExprSrc
  | ES_LetRec of LetClauseSrc list * ExprSrc
  | ES_LetLoop of Symbol * LetClauseSrc list * ExprSrc
and CatchRecordSrc = { crsrc_handler : ExprSrc ; crsrc_body : ExprSrc }
and LetClauseSrc = { lcsrc_name : Symbol ; lcsrc_value : ExprSrc }

let pssMinArity (pss : ParamSpecSrc) =
  match pss with
    | PSS_Items lst -> List.length lst
    | PSS_ItemsMore (lst, m) -> List.length lst

let pssMoreArity (pss : ParamSpecSrc) =
  match pss with
    | PSS_Items _ -> false
    | PSS_ItemsMore _ -> true

let captureInfo (envDesc : Map<Symbol, int>) (pss : ParamSpecSrc) (envSpecForLambda : Set<Symbol>) =
  let (captureListRev, captureLen, captureDesc) = List.fold (fun (cl, i, cd) sym -> (((Map.find sym envDesc) :: cl), (i + 1), (Map.add sym i cd))) ([], 0, Map.empty) (Set.toList envSpecForLambda)
  let itemsWithoutMore =
    match pss with
      | PSS_Items il -> il
      | PSS_ItemsMore (il, m) -> il
  let (capturePlusParamsLen, capturePlusParamsDesc) = List.fold (fun (i, cd) sym -> ((i + 1), (Map.add sym i cd))) (captureLen, captureDesc) itemsWithoutMore
  let finalCaptureDesc =
    match pss with
      | PSS_Items _ -> capturePlusParamsDesc
      | PSS_ItemsMore (_, m) -> Map.add m capturePlusParamsLen capturePlusParamsDesc
  let captureArray = captureListRev |> List.rev |> Array.ofList
  (captureArray, finalCaptureDesc)

let rec uninternedSymbolsDatum (d : Datum) =
  match d with
    | D_Symbol s ->
        match s with
          | S_Uninterned _ -> Set.singleton s
          | S_Interned _ -> Set.empty
    | D_List lst -> uninternedSymbolsDatumList lst
    | D_Vector v -> uninternedSymbolsDatumList (Array.toList v)
    | _ -> Set.empty
and uninternedSymbolsDatumList (lst : Datum list) =
  List.fold (fun s i -> Set.union s (uninternedSymbolsDatum i)) Set.empty lst

let rec uninternedSymbolLiteralsExpr (x : ExprSrc) =
  let formOfLet (lcs : LetClauseSrc list) (x : ExprSrc) =
    Set.union (uninternedSymbolLiteralsExprList (List.map (fun lc -> lc.lcsrc_value) lcs)) (uninternedSymbolLiteralsExpr x)
  match x with
    | ES_Literal d -> uninternedSymbolsDatum d
    | ES_VarRef _ -> Set.empty
    | ES_VarSet (s, e) -> uninternedSymbolLiteralsExpr e
    | ES_Begin lst -> uninternedSymbolLiteralsExprList lst
    | ES_IfThenElse (test, thenClause, elseClause) -> uninternedSymbolLiteralsExprList [ test ; thenClause; elseClause ]
    | ES_Lambda (pss, b) -> uninternedSymbolLiteralsExpr b
    | ES_Invoke lst -> uninternedSymbolLiteralsExprList lst
    | ES_And lst -> uninternedSymbolLiteralsExprList lst
    | ES_Or lst -> uninternedSymbolLiteralsExprList lst
    | ES_Catch { crsrc_handler = h ; crsrc_body = b } -> uninternedSymbolLiteralsExprList [ h ; b ]
    | ES_Primitive (s, lst) -> uninternedSymbolLiteralsExprList lst
    | ES_Let (lcs, x) -> formOfLet lcs x
    | ES_LetStar (lcs, x) -> formOfLet lcs x
    | ES_LetRec (lcs, x) -> formOfLet lcs x
    | ES_LetLoop (loop, lcs, x) -> formOfLet lcs x
and uninternedSymbolLiteralsExprList (xl : ExprSrc list) =
  List.fold (fun s x -> Set.union s (uninternedSymbolLiteralsExpr x)) Set.empty xl

let rec literalSlots (x : ExprSrc) =
  let formOfLet (lcs: LetClauseSrc list) (x : ExprSrc) =
    ((literalSlotsList (List.map (fun x -> x.lcsrc_value) lcs)) + (literalSlots x))
  match x with
    | ES_Literal d ->
        match d with
          | D_List [] -> 0
          | D_List _ -> 1
          | D_Vector _ -> 1
          | _ -> 0
    | ES_VarRef s -> 0
    | ES_VarSet (s, x2) -> literalSlots x2
    | ES_Begin xl -> literalSlotsList xl
    | ES_IfThenElse (test, thenClause, elseClause) -> (literalSlots test) + (literalSlots thenClause) + (literalSlots elseClause)
    | ES_Lambda (_, body) -> literalSlots body
    | ES_Invoke xl -> literalSlotsList xl
    | ES_And xl -> literalSlotsList xl
    | ES_Or xl -> literalSlotsList xl
    | ES_Catch { crsrc_handler = h ; crsrc_body = b } -> (literalSlots h) + (literalSlots b)
    | ES_Primitive (p, xl) -> literalSlotsList xl
    | ES_Let (lcs, x) -> formOfLet lcs x
    | ES_LetStar (lcs, x) -> formOfLet lcs x
    | ES_LetRec (lcs, x) -> formOfLet lcs x
    | ES_LetLoop (loop, lcs, x) -> formOfLet lcs x
and literalSlotsList (xl : ExprSrc list) =
  List.fold (fun a1 x1 -> a1 + literalSlots x1) 0 xl

let rec uninternedSymbolMap (s : Set<Symbol>) =
  s |> Set.toList |> List.mapi (fun i s -> (s, i)) |> Map.ofList

let rec envSpecPss (pss : ParamSpecSrc) =
  match pss with
    | PSS_Items i -> Set.ofList i
    | PSS_ItemsMore (i, j) -> Set.add j (Set.ofList i)

let rec envSpec (x : ExprSrc) =
  match x with
    | ES_Literal _ -> Set.empty
    | ES_VarRef s -> Set.singleton s
    | ES_VarSet (s, x2) -> Set.add s (envSpec x2)
    | ES_Begin xl -> envSpecList xl
    | ES_IfThenElse (test, thenClause, elseClause) -> Set.union (envSpec test) (Set.union (envSpec thenClause) (envSpec elseClause))
    | ES_Lambda (pss, x) -> Set.difference (envSpec x) (envSpecPss pss)
    | ES_Invoke xl -> envSpecList xl
    | ES_And xl -> envSpecList xl
    | ES_Or xl -> envSpecList xl
    | ES_Catch { crsrc_handler = h ; crsrc_body = b } -> Set.union (envSpec h) (envSpec b)
    | ES_Primitive (p, xl) -> envSpecList xl
    | ES_Let (clauses, body) ->
        Set.union
          (envSpecList (List.map (fun cl -> cl.lcsrc_value) clauses))
          (Set.difference (envSpec body) (Set.ofList (List.map (fun cl -> cl.lcsrc_name) clauses)))
    | ES_LetStar (clauses, body) ->
        match clauses with
          | [] -> envSpec body
          | { lcsrc_name = name ; lcsrc_value = value } :: t ->
              Set.union
                (envSpec value)
                (Set.remove name (envSpec (ES_LetStar (t, body))))
    | ES_LetRec (clauses, body) ->
        Set.difference
          (Set.union
            (envSpecList (List.map (fun cl -> cl.lcsrc_value) clauses))
            (envSpec body))
          (Set.ofList (List.map (fun cl -> cl.lcsrc_name) clauses))
    | ES_LetLoop (loop, clauses, body) ->
        Set.remove loop (envSpec (ES_Let (clauses, body)))
and envSpecList (xl : ExprSrc list) =
  List.fold (fun s1 x1 -> Set.union s1 (envSpec x1)) Set.empty xl

let rec primitives (x : ExprSrc) =
  let formOfLet (clauses : LetClauseSrc list) (body : ExprSrc) =
    Set.union
      (primitivesList (List.map (fun cl -> cl.lcsrc_value) clauses))
      (primitives body)
  match x with
    | ES_Literal _ -> Set.empty
    | ES_VarRef _ -> Set.empty
    | ES_VarSet (s, x2) -> primitives x2
    | ES_Begin xl -> primitivesList xl
    | ES_IfThenElse (test, thenClause, elseClause) -> Set.union (primitives test) (Set.union (primitives thenClause) (primitives elseClause))
    | ES_Lambda (_, x) -> primitives x
    | ES_Invoke xl -> primitivesList xl
    | ES_And xl -> primitivesList xl
    | ES_Or xl -> primitivesList xl
    | ES_Catch { crsrc_handler = h ; crsrc_body = b } -> Set.union (primitives h) (primitives b)
    | ES_Primitive (p, _) -> Set.singleton p
    | ES_Let (clauses, body) -> formOfLet clauses body
    | ES_LetStar (clauses, body) -> formOfLet clauses body
    | ES_LetRec (clauses, body) -> formOfLet clauses body
    | ES_LetLoop (loop, clauses, body) -> formOfLet clauses body
and primitivesList (xl : ExprSrc list) =
  List.fold (fun p1 x1 -> Set.union p1 (primitives x1)) Set.empty xl

type MakeProcedureArgs =
  { MPA_MinArity : int ;
    MPA_More : bool ;
    MPA_Captures : int[] ;
    MPA_Target : Symbol
  }

type LetArgs =
  { LA_Variables : int ;
    LA_Captures : int[] ;
  }

type Opcode =
  | O_CreateLiteralPool of int
  | O_LdBool of bool
  | O_LdInt of bigint
  | O_LdFloat of float
  | O_LdChar of char
  | O_LdStr of string
  | O_LdSymbol of Symbol
  | O_Gensym
  | O_LdEmptyList
  | O_ConsList
  | O_MkVector of int
  | O_SetVectorElement of int // vector val -> vector
  | O_StoreLiteral of int
  | O_LdLiteral of int
  | O_VarRef of int
  | O_VarSet of int // value -> unspecified-obj
  | O_Ret
  | O_LdUnspecified
  | O_Drop
  | O_JumpIfFalse of Symbol
  | O_Label of Symbol
  | O_Jump of Symbol
  | O_JumpIfTrue of Symbol
  | O_Dup
  | O_CallPrimitive of Symbol * int
  | O_TailCallPrimitive of Symbol * int
  | O_Call of int
  | O_TailCall of int
  | O_MkProcedure of MakeProcedureArgs
  | O_CallWithCatch of int
  | O_Swap
  | O_Let of LetArgs
  | O_LetRec of LetArgs
  | O_CallLetRec of int // pops 1 procedure from the stack, passes N dummy values to it

type CodeFragment =
  { CF_Init : Opcode list ;
    CF_Body : Opcode list ;
    CF_Deferral : Opcode list ;
  }

let rec buildLiteral (uninternedMap : Map<Symbol, int>) (d : Datum) =
  match d with
    | D_Unspecified -> [ O_LdUnspecified ]
    | D_Bool b -> [ (O_LdBool b) ]
    | D_Int i -> [ (O_LdInt i) ]
    | D_Float f -> [ (O_LdFloat f) ]
    | D_Char ch -> [ (O_LdChar ch) ]
    | D_String str -> [ (O_LdStr str) ]
    | D_Symbol sym ->
       match sym with
         | S_Interned _ -> [ (O_LdSymbol sym) ]
         | S_Uninterned _ -> [ (O_LdLiteral (Map.find sym uninternedMap)) ]
    | D_List [] -> [ O_LdEmptyList ]
    | D_List (h :: t) -> (buildLiteral uninternedMap (D_List t)) @ (buildLiteral uninternedMap h) @ [ O_ConsList ]
    | D_Vector v -> [ (O_MkVector (Array.length v)) ] @ List.concat (Array.mapi (fun i d -> (buildLiteral uninternedMap d) @ [ (O_SetVectorElement i) ]) v)

let rec retIfTail (tail: bool) (ol : Opcode list) =
  if tail then
    ol @ [ O_Ret ]
  else
    ol

let mapKeys (m : Map<'a, 'b>) =
  m |> Map.toList |> List.map (fun (x, y) -> x) |> Set.ofList

let mapUnion (d1 : Map<'a, 'b>) (d2 : Map<'a, 'b>) =
  let k = Set.union (mapKeys d1) (mapKeys d2)
  let result (v1 : 'b option) (v2 : 'b option) =
    match v1 with
      | Some v1s ->
          match v2 with
            | Some v2s -> raise (new System.InvalidOperationException("Item already added"))
            | None -> v1s
      | None ->
          match v2 with
            | Some v2s -> v2s
            | None -> raise (new System.InvalidOperationException("Key not found"))
  k |> Set.toList |> List.map (fun k -> (k, (result (Map.tryFind k d1) (Map.tryFind k d2)))) |> Map.ofList

let mapUnionMap (f : 'a -> Map<'b, 'c>) (g : 'a list) =
  List.fold (fun m i -> mapUnion m (f i)) Map.empty g

let rec compile (uninternedMap : Map<Symbol, int>) (lso : int) (envDesc : Map<Symbol, int>) (tail : bool) (x : ExprSrc) =
  match x with
    | ES_Literal d ->
        match d with
          | D_List [] -> { CF_Init = [] ; CF_Body = retIfTail tail (buildLiteral uninternedMap d) ; CF_Deferral = [] }
          | D_List (h :: t) -> { CF_Init = (buildLiteral uninternedMap d) @ [ (O_StoreLiteral lso) ] ; CF_Body = retIfTail tail [ (O_LdLiteral lso) ] ; CF_Deferral = [] }
          | D_Vector _ -> { CF_Init = (buildLiteral uninternedMap d) @ [ (O_StoreLiteral lso) ] ; CF_Body = retIfTail tail [ (O_LdLiteral lso) ] ; CF_Deferral = [] }
          | _ -> { CF_Init = [] ; CF_Body = retIfTail tail (buildLiteral uninternedMap d) ; CF_Deferral = [] }
    | ES_VarRef s -> { CF_Init = [] ; CF_Body = retIfTail tail [ (O_VarRef (Map.find s envDesc)) ] ; CF_Deferral = [] }
    | ES_VarSet (s, x) ->
        let { CF_Init = xi ; CF_Body = xb ; CF_Deferral = xd } = (compile uninternedMap lso envDesc false x)
        { CF_Init = xi ; CF_Body = retIfTail tail (xb @ [ (O_VarSet (Map.find s envDesc)) ]) ; CF_Deferral = xd }
    | ES_Begin [] ->
        { CF_Init = [] ; CF_Body = [ O_LdUnspecified ] ; CF_Deferral = [] }
    | ES_Begin (h :: []) ->
        compile uninternedMap lso envDesc tail h
    | ES_Begin (h :: t) ->
        let { CF_Init = xhi ; CF_Body = xhb ; CF_Deferral = xhd } = (compile uninternedMap lso envDesc false h)
        let { CF_Init = xti ; CF_Body = xtb ; CF_Deferral = xtd } = (compile uninternedMap (lso + literalSlots h) envDesc tail (ES_Begin t))
        { CF_Init = xhi @ xti ; CF_Body = xhb @ [ O_Drop ] @ xtb ; CF_Deferral = xhd @ xtd }
    | ES_IfThenElse (test, thenClause, elseClause) ->
        let { CF_Init = test_i ; CF_Body = test_b ; CF_Deferral = test_d } = (compile uninternedMap lso envDesc false test)
        let lso1 = literalSlots test
        let { CF_Init = thenClause_i ; CF_Body = thenClause_b ; CF_Deferral = thenClause_d } = (compile uninternedMap (lso + lso1) envDesc tail thenClause)
        let lso2 = lso1 + literalSlots thenClause
        let { CF_Init = elseClause_i ; CF_Body = elseClause_b ; CF_Deferral = elseClause_d } = (compile uninternedMap (lso + lso2) envDesc tail elseClause)
        let lbl1 = gensym ()
        { CF_Init = test_i @ thenClause_i @ elseClause_i ;
          CF_Body =
            if tail then
              test_b @ [ (O_JumpIfFalse lbl1) ] @ thenClause_b @ [ (O_Label lbl1) ] @ elseClause_b
            else
              let lbl2 = gensym ()
              test_b @ [ (O_JumpIfFalse lbl1) ] @ thenClause_b @ [ (O_Jump lbl2) ; (O_Label lbl1) ] @ elseClause_b @ [ (O_Label lbl2) ] ;
          CF_Deferral = test_d @ thenClause_d @ elseClause_d
        }
    | ES_And [] ->
        { CF_Init = [] ; CF_Body = retIfTail tail [ (O_LdBool true) ] ; CF_Deferral = [] }
    | ES_And (h :: []) ->
        compile uninternedMap lso envDesc tail h
    | ES_And (h :: t) ->
        let xLast :: xButLastRev = List.rev (h :: t)
        let xButLast = List.rev xButLastRev
        let (lsoFinal, cButLastRev) : int * (CodeFragment list) = List.fold (fun (lso, clist) x -> ((lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (lso, []) xButLast
        let cLast = compile uninternedMap lsoFinal envDesc tail xLast
        let cButLast = List.rev cButLastRev
        let lbl = gensym ()
        { CF_Init = (List.collect (fun b -> b.CF_Init) cButLast) @ (cLast.CF_Init) ;
          CF_Body = (List.collect (fun b -> b.CF_Body @ [ (O_JumpIfFalse lbl) ]) cButLast)
            @
            ( if tail then
                cLast.CF_Body @ [ (O_Label lbl) ; (O_LdBool false) ; O_Ret ]
              else
                let lbl2 = gensym()
                cLast.CF_Body @ [ (O_Jump lbl2) ; (O_Label lbl) ; (O_LdBool false) ; (O_Label lbl2) ]
            )
          CF_Deferral = List.concat (List.map (fun cf -> cf.CF_Deferral) (cButLast @ [ cLast ]))
        }
    | ES_Or [] ->
        { CF_Init = [] ; CF_Body = retIfTail tail [ (O_LdBool false) ] ; CF_Deferral = [] }
    | ES_Or (h :: []) ->
        compile uninternedMap lso envDesc tail h
    | ES_Or (h :: t) ->
        let xLast :: xButLastRev = List.rev (h :: t)
        let xButLast = List.rev xButLastRev
        let (lsoFinal, cButLastRev) : int * (CodeFragment list) = List.fold (fun (lso, clist) x -> ((lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (lso, []) xButLast
        let cLast = compile uninternedMap lsoFinal envDesc tail xLast
        let cButLast = List.rev cButLastRev
        let lbl = gensym ()
        { CF_Init = (List.collect (fun b -> b.CF_Init) cButLast) @ (cLast.CF_Init) ;
          CF_Body = retIfTail tail ((List.collect (fun b -> b.CF_Body @ [ O_Dup ; (O_JumpIfTrue lbl) ; O_Drop ]) cButLast) @ cLast.CF_Body @ [ (O_Label lbl) ])
          CF_Deferral = List.concat (List.map (fun cf -> cf.CF_Deferral) (cButLast @ [ cLast ]))
        }
    | ES_Invoke [] ->
        raise (new System.InvalidOperationException("Invoke requires a function"))
    | ES_Invoke xl ->
        let (count, lsoFinal, cRev) = List.fold (fun (count, lso, clist) x -> ((count + 1), (lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (0, lso, []) xl
        let c = List.rev cRev
        { CF_Init = (List.collect (fun b -> b.CF_Init) c) ;
          CF_Body = (List.collect (fun b -> b.CF_Body) c)
            @
            ( if tail then
                [ (O_TailCall count) ]
              else
                [ (O_Call count) ]
            ) ;
          CF_Deferral = List.concat (List.map (fun cf -> cf.CF_Deferral) c)
        }
    | ES_Primitive (p, xl) ->
        let (count, lsoFinal, cRev) = List.fold (fun (count, lso, clist) x -> ((count + 1), (lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (0, lso, []) xl
        let c = List.rev cRev
        { CF_Init = (List.collect (fun b -> b.CF_Init) c) ;
          CF_Body = (List.collect (fun b -> b.CF_Body) c)
            @
            ( if tail then
                [ (O_TailCallPrimitive (p, count)) ]
              else
                [ (O_CallPrimitive (p, count)) ]) ;
          CF_Deferral = List.concat (List.map (fun cf -> cf.CF_Deferral) c)
        }
    | ES_Lambda (pss, body) ->
        let lbl = gensym ()
        let (captureArray, envDescBody) = captureInfo envDesc pss (envSpec x)
        let cb = compile uninternedMap lso envDescBody true body
        { CF_Init = cb.CF_Init ;
          CF_Body =
            retIfTail tail
              [ ( O_MkProcedure
                    { MPA_MinArity = pssMinArity pss ;
                      MPA_More = pssMoreArity pss ;
                      MPA_Captures = captureArray ;
                      MPA_Target = lbl
                    } ) ] ;
          CF_Deferral =
            [ (O_Label lbl) ] @ cb.CF_Body @ cb.CF_Deferral
        }
    | ES_Catch { crsrc_handler = h ; crsrc_body = b } ->
        let ch = compile uninternedMap lso envDesc false h
        let cb = compile uninternedMap (lso + literalSlots h) envDesc false (ES_Lambda ((PSS_Items []), b))
        let lbl1 = gensym ()
        let lbl2 = gensym ()
        { CF_Init = ch.CF_Init @ cb.CF_Init ;
          CF_Body = retIfTail tail (cb.CF_Body @ [ (O_CallWithCatch 1) ; (O_JumpIfFalse lbl1) ] @ ch.CF_Body @ [ O_Swap ; (O_Call 2) ; (O_Label lbl1) ]) ;
          CF_Deferral = ch.CF_Deferral @ cb.CF_Deferral
        }
    | ES_Let (clauses, body) ->
        if List.isEmpty clauses then
          compile uninternedMap lso envDesc tail body
        else
          let vars = (List.map (fun lc -> lc.lcsrc_name) clauses)
          let compiledClauses = List.map (fun lc -> compile uninternedMap lso envDesc false lc.lcsrc_value) clauses
          let pss = (PSS_Items vars)
          if tail then
            let (captureArray, envDescBody) = captureInfo envDesc pss (Set.difference (envSpec body) (Set.ofList vars))
            let compiledBody = compile uninternedMap lso envDescBody true body
            { CF_Init = (List.collect (fun x -> x.CF_Init) compiledClauses) @ compiledBody.CF_Init ;
              CF_Body = (List.collect (fun x -> x.CF_Body) compiledClauses)
                        @
                        [ (O_Let { LA_Variables = (List.length vars) ; LA_Captures = captureArray }) ]
                        @
                        compiledBody.CF_Body ;
              CF_Deferral = (List.collect (fun x -> x.CF_Deferral) compiledClauses) @ compiledBody.CF_Deferral
            }
          else
            compile uninternedMap lso envDesc false
              (ES_Invoke
                ( (ES_Lambda (pss, body)) :: (List.map (fun lc -> lc.lcsrc_value) clauses)))
    | ES_LetStar (clauses, body) ->
        match clauses with
          | [] -> compile uninternedMap lso envDesc tail body
          | h :: t ->
              compile uninternedMap lso envDesc tail (ES_Let ([ h ], ES_LetStar(t, body)))
    | ES_LetRec (clauses, body) ->
        if List.isEmpty clauses then
          compile uninternedMap lso envDesc tail body
        else
          let vars = (List.map (fun lc -> lc.lcsrc_name) clauses)
          let envSpecInternal = (Set.union (envSpecList (List.map (fun lc -> lc.lcsrc_value) clauses)) (envSpec body))
          let envSpecExternal = Set.difference envSpecInternal (Set.ofList vars)
          let pss = (PSS_Items vars)
          let (captureArray, envDescInternal) = captureInfo envDesc pss envSpecExternal
          let compiledClauses = List.map (fun lc -> compile uninternedMap lso envDescInternal false lc.lcsrc_value) clauses
          let compiledBody = compile uninternedMap lso envDescInternal true body
          let compiledCombo =
            { CF_Init = (List.collect (fun x -> x.CF_Init) compiledClauses) @ compiledBody.CF_Init ;
              CF_Body = (List.concat (List.mapi (fun i x -> x.CF_Body @ [ (O_VarSet i) ; O_Drop ]) compiledClauses))
                        @
                        compiledBody.CF_Body ;
              CF_Deferral = (List.collect (fun x -> x.CF_Deferral) compiledClauses) @ compiledBody.CF_Deferral
            }
          if tail then
            { CF_Init = compiledCombo.CF_Init ;
              CF_Body = [ (O_LetRec { LA_Variables = (List.length vars) ; LA_Captures = captureArray }) ]
                        @
                        compiledCombo.CF_Body ;
              CF_Deferral = compiledCombo.CF_Deferral;
            }
          else
            let lbl = gensym ()
            { CF_Init = compiledCombo.CF_Init ;
              CF_Body = [ (O_MkProcedure
                            { MPA_MinArity = (List.length vars) ;
                              MPA_More = false ;
                              MPA_Captures = captureArray ;
                              MPA_Target = lbl
                            }) ;
                          (O_CallLetRec (List.length vars)) ] ;
              CF_Deferral = [ (O_Label lbl) ] @ compiledCombo.CF_Body @ compiledCombo.CF_Deferral
            }
    | ES_LetLoop (loop, clauses, body) ->
        compile uninternedMap lso envDesc tail
          (ES_LetRec
            ( [ { lcsrc_name = loop ;
                  lcsrc_value =
                    (ES_Lambda
                      ((PSS_Items (List.map (fun lc -> lc.lcsrc_name) clauses)), body)) } ],
              (ES_Invoke
                ((ES_VarRef loop) :: (List.map (fun lc -> lc.lcsrc_value) clauses)))))
    //| _ -> raise (new System.NotImplementedException("Cannot compile that yet"))

let compileFlat (x : ExprSrc) =
  let usls = uninternedSymbolLiteralsExpr x
  let um = uninternedSymbolMap usls
  let c = compile um (Set.count usls) Map.empty true x
  [ (O_CreateLiteralPool ((Set.count usls) + (literalSlots x))) ]
  @
  (List.collect (fun i -> [ O_Gensym ; (O_StoreLiteral i) ]) (List.init (Set.count usls) (fun i -> i)))
  @
  c.CF_Init @ c.CF_Body @ c.CF_Deferral

let test1 =
  (ES_Invoke
    [ (ES_Lambda
        ( (PSS_Items [ (S_Interned "x") ]),
          (ES_Primitive ((S_Interned "*"), [ (ES_VarRef (S_Interned "x")) ; (ES_VarRef (S_Interned "x")) ])))) ;
      (ES_Literal (D_Int 4I)) ] )

let test2 =
  (ES_Catch
    { crsrc_handler =
        (ES_Lambda
          ( (PSS_Items [ (S_Interned "ex") ]),
            (ES_Primitive ((S_Interned "println"), [ (ES_VarRef (S_Interned "ex")) ])))) ;
      crsrc_body = test1
    }
  )

let test3 =
  (ES_Let
    ( [ { lcsrc_name = (S_Interned "pi") ;
          lcsrc_value = (ES_Literal (D_Float 3.14159)) } ;
        { lcsrc_name = (S_Interned "r") ;
          lcsrc_value = (ES_Literal (D_Float 2.5)) }
      ],
      (ES_Primitive
        ( (S_Interned "*"),
          [ (ES_VarRef (S_Interned "pi")) ;
            (ES_Primitive
              ( (S_Interned "*"),
                [ (ES_VarRef (S_Interned "r")) ;
                  (ES_VarRef (S_Interned "r")) ]))]))))

let test4 =
  (ES_Let
    ( [ { lcsrc_name = (S_Interned "make-adder") ;
          lcsrc_value =
            (ES_Lambda
              ((PSS_Items [ (S_Interned "i") ]),
                (ES_Lambda
                  ((PSS_Items [ (S_Interned "x") ]),
                    (ES_Primitive
                      ( (S_Interned "+"),
                        [ (ES_VarRef (S_Interned "i")) ;
                          (ES_VarRef (S_Interned "x")) ])))))) } ;
        { lcsrc_name = (S_Interned "my-constant") ;
          lcsrc_value = (ES_Literal (D_Float 3.0)) } ;
        { lcsrc_name = (S_Interned "other-constant") ;
          lcsrc_value = (ES_Literal (D_Float 100.0)) } ],
      (ES_Let
        ( [ { lcsrc_name = (S_Interned "add-my-constant") ;
              lcsrc_value =
                (ES_Invoke [ (ES_VarRef (S_Interned "make-adder")) ; (ES_VarRef (S_Interned "my-constant")) ]) } ],
          (ES_Invoke [ (ES_VarRef (S_Interned "add-my-constant")) ; (ES_VarRef (S_Interned "other-constant")) ])))))

let test5 =
  (ES_LetStar
    ( [ { lcsrc_name = (S_Interned "sq") ;
          lcsrc_value =
            (ES_Lambda
              ((PSS_Items [ (S_Interned "x") ]),
                (ES_Primitive ((S_Interned "*"), [ (ES_VarRef (S_Interned "x")) ; (ES_VarRef (S_Interned "x")) ])))) } ;
        { lcsrc_name = (S_Interned "pi") ;
          lcsrc_value = (ES_Literal (D_Float 3.14159)) } ;
        { lcsrc_name = (S_Interned "circle-area") ;
          lcsrc_value =
            (ES_Lambda
              ((PSS_Items [ (S_Interned "r") ]),
                (ES_Primitive ((S_Interned "*"),
                  [ (ES_VarRef (S_Interned "pi")) ;
                    (ES_Invoke [ (ES_VarRef (S_Interned "sq")) ; (ES_VarRef (S_Interned "r")) ])])))) } ],
      (ES_Primitive ((S_Interned "print-float"),
        [ (ES_Invoke [ (ES_VarRef (S_Interned "circle-area")) ; (ES_Primitive ((S_Interned "read-float"), [])) ]) ]))))

let test6 =
  (ES_LetRec
    ( [ { lcsrc_name = (S_Interned "odd?") ;
          lcsrc_value =
            (ES_Lambda
              ((PSS_Items [ (S_Interned "i") ]),
                (ES_IfThenElse
                  ((ES_Primitive ((S_Interned "="),
                      [ (ES_VarRef (S_Interned "i")) ;
                        (ES_Literal (D_Int 0I)) ])),
                  (ES_Literal (D_Bool false)),
                  (ES_Invoke
                    [ (ES_VarRef (S_Interned "even?")) ;
                      (ES_Primitive ((S_Interned "-"),
                        [ (ES_VarRef (S_Interned "i")) ;
                          (ES_Literal (D_Int 1I)) ]))]))))) } ;
        { lcsrc_name = (S_Interned "even?") ;
          lcsrc_value =
            (ES_Lambda
              ((PSS_Items [ (S_Interned "i") ]),
                (ES_IfThenElse
                  ((ES_Primitive ((S_Interned "="),
                      [ (ES_VarRef (S_Interned "i")) ;
                        (ES_Literal (D_Int 0I)) ])),
                  (ES_Literal (D_Bool true)),
                  (ES_Invoke
                    [ (ES_VarRef (S_Interned "odd?")) ;
                      (ES_Primitive ((S_Interned "-"),
                        [ (ES_VarRef (S_Interned "i")) ;
                          (ES_Literal (D_Int 1I)) ]))]))))) } ],
      (ES_Primitive ((S_Interned "print-bool"),
        [ (ES_Invoke
            [ (ES_VarRef (S_Interned "odd?")) ;
              (ES_Primitive ((S_Interned "read-int"), []))]) ]))))

let test7 = (ES_Begin [ test6 ; (ES_Literal (D_Bool true)) ])

let test8 = (ES_Primitive ((S_Interned "transmit"), [ (ES_Literal (D_Symbol (gensym ()))) ]))

let test9 =
  (ES_LetLoop
    ( (S_Interned "loop"),
      [ { lcsrc_name = (S_Interned "i") ;
          lcsrc_value = (ES_Literal (D_Int 10I)) } ],
      (ES_IfThenElse
        ( (ES_Primitive ((S_Interned ">"), [ (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 0I)) ])),
          (ES_Begin
            [ (ES_Primitive ((S_Interned "print-int"), [ (ES_VarRef (S_Interned "i")) ])) ;
              (ES_Invoke
                [ (ES_VarRef (S_Interned "loop")) ;
                  (ES_Primitive ((S_Interned "-"), [ (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 1I)) ])) ]) ]),
          (ES_Literal (D_Bool true))))))

open System.IO

type WriteOpcode =
  | W_PushIndent of string
  | W_Write of string
  | W_NewLine
  | W_PopIndent
  
let write (out : TextWriter) (wol : WriteOpcode list) =
  let rec write1 (atBegin : bool) (indentStack : string list) (wol : WriteOpcode list) =
    match wol with
      | [] -> ()
      | h :: t ->
         match h with
           | W_PushIndent i ->
               write1 atBegin (((List.head indentStack) + i) :: indentStack) t
           | W_Write str ->
               if atBegin then
                 out.Write((List.head indentStack))
               out.Write(str)
               write1 false indentStack t
           | W_NewLine ->
               out.WriteLine()
               write1 true indentStack t
           | W_PopIndent ->
               write1 atBegin (List.tail indentStack) t
  write1 true [ "" ] wol

let codeToWrites (opl : Opcode list) =
  let (opCount, labelCount, labelToCaseMap, indexToCaseMap, _) =
    List.fold
      (fun (opNum, labelNum, labelToCaseMap, indexToCaseMap, prevLabel) op ->
        match op with
          | O_Label lbl ->
              match prevLabel with
                | None ->
                    ((opNum + 1), (labelNum + 1), (Map.add lbl labelNum labelToCaseMap), (Map.add opNum labelNum indexToCaseMap), (Some (lbl, labelNum)))
                | Some (pl, pln) ->
                    ((opNum + 1), labelNum, (Map.add lbl pln labelToCaseMap), indexToCaseMap, prevLabel)
          | O_Call _ | O_CallPrimitive _ | O_CallWithCatch _ | O_JumpIfTrue _ | O_JumpIfFalse _ ->
              let sym = gensym ()
              ((opNum + 1), (labelNum + 1), (Map.add sym labelNum labelToCaseMap), (Map.add opNum labelNum indexToCaseMap), (Some (sym, labelNum)))
          | _ ->
              ((opNum + 1), labelNum, labelToCaseMap, indexToCaseMap, None)
      )
      (0, 1, Map.empty, Map.empty, None)
      opl
  let doCapturesArray (arr : int[]) =
    assert ((Array.length arr) > 0)
    let iPtr = (sprintf "captures_%i" !nextSym)
    nextSym := 1 + !nextSym
    let code =
      [ (W_Write (sprintf "int %s[]" iPtr)) ; (W_Write (sprintf " = { %i" arr.[0])) ]
      @ List.map (fun j -> (W_Write (sprintf ", %i" j))) (List.tail (Array.toList arr))
      @ [ (W_Write " };") ; W_NewLine ]
    (iPtr, code)
  let writeInstruction (i : int) (op : Opcode) =
    match op with
      | O_CreateLiteralPool i ->
          [ (W_Write (sprintf "ms.CreateLiteralPool(%i);" i)) ; W_NewLine ]
      | O_LdBool b ->
          [ (W_Write (sprintf "ms.LoadBool(%b);" b)) ; W_NewLine ]
      | O_LdInt i ->
          [ (W_Write (sprintf "ms.LoadInt(%A);" i)) ; W_NewLine ]
      | O_LdFloat f ->
          [ (W_Write (sprintf "ms.LoadFloat(%g);" f)) ; W_NewLine ]
      | O_LdChar ch ->
          [ (W_Write (sprintf "ms.LoadChar('%s');" (new System.String(ch, 1)))) ; W_NewLine ]
      | O_LdStr str ->
          [ (W_Write (sprintf "ms.LoadString(\"%s\");" str)) ; W_NewLine ]
      | O_LdSymbol sym ->
          match sym with
            | S_Interned str ->
                [ (W_Write (sprintf "ms.LoadSymbol(\"%s\");" str)) ; W_NewLine ]
            | S_Uninterned i ->
                failwith "Unable to have a literal uninterned symbol"
      | O_Gensym ->
          [ (W_Write "ms.Gensym();") ; W_NewLine ]
      | O_LdEmptyList ->
          [ (W_Write "ms.LoadEmptyList();") ; W_NewLine ]
      | O_ConsList ->
          [ (W_Write "ms.ConsList();") ; W_NewLine ]
      | O_MkVector index ->
          [ (W_Write (sprintf "ms.MakeVector(%i);" index)) ; W_NewLine ]
      | O_SetVectorElement index ->
          [ (W_Write (sprintf "ms.SetVectorElement(%i);" index)) ; W_NewLine ]
      | O_StoreLiteral index ->
          [ (W_Write (sprintf "ms.StoreLiteral(%i);" index)) ; W_NewLine ]
      | O_LdLiteral index ->
          [ (W_Write (sprintf "ms.LoadLiteral(%i);" index)) ; W_NewLine ]
      | O_VarRef index ->
          [ (W_Write (sprintf "ms.VarRef(%i);" index)) ; W_NewLine ]
      | O_VarSet index ->
          [ (W_Write (sprintf "ms.VarSet(%i);" index)) ; W_NewLine ]
      | O_Ret ->
          [ (W_Write "ms.Ret();") ; W_NewLine ; (W_Write "break;") ; W_NewLine ]
      | O_LdUnspecified ->
          [ (W_Write "ms.LoadUnspecified();") ; W_NewLine ]
      | O_Drop ->
          [ (W_Write "ms.Drop();") ; W_NewLine ]
      | O_JumpIfFalse target ->
          [ (W_Write (sprintf "ms.JumpIfFalse(%i, /* else */ %i);" (Map.find target labelToCaseMap) (Map.find i indexToCaseMap))) ; W_NewLine ;
            (W_Write "break;") ; W_NewLine ;
            W_PopIndent ; (W_Write (sprintf "case %i:" (Map.find i indexToCaseMap))) ; (W_PushIndent "  ") ; W_NewLine ]
      | O_Label lbl ->
          match Map.tryFind i indexToCaseMap with
            | Some n ->
                [ W_PopIndent ; (W_Write (sprintf "case %i:" n)) ; (W_PushIndent "  ") ; W_NewLine ]
            | None ->
                [ ]
      | O_Jump target ->
          [ (W_Write (sprintf "ms.Jump(%i);" (Map.find target labelToCaseMap))) ; W_NewLine ]
      | O_JumpIfTrue target ->
          [ (W_Write (sprintf "ms.JumpIfTrue(%i, /* else */ %i);" (Map.find target labelToCaseMap) (Map.find i indexToCaseMap))) ; W_NewLine ;
            (W_Write "break;") ; W_NewLine ;
            W_PopIndent ; (W_Write (sprintf "case %i:" (Map.find i indexToCaseMap))) ; (W_PushIndent "  ") ; W_NewLine ]
      | O_Dup ->
          [ (W_Write "ms.Dup();") ; W_NewLine ]
      | O_CallPrimitive (sym, argCount) ->
          match sym with
            | S_Interned str ->
                [ (W_Write (sprintf "ms.CallPrimitive(\"%s\", %i, /* return to */ %i);" str argCount (Map.find i indexToCaseMap))) ; W_NewLine ;
                  (W_Write "break;") ; W_NewLine ;
                  W_PopIndent ; (W_Write (sprintf "case %i:" (Map.find i indexToCaseMap))) ; (W_PushIndent "  ") ; W_NewLine ]
            | S_Uninterned _ -> failwith "Unable to call uninterned primitive"
      | O_TailCallPrimitive (sym, argCount) ->
          match sym with
            | S_Interned str ->
                [ (W_Write (sprintf "ms.TailCallPrimitive(\"%s\", %i);" str argCount)) ; W_NewLine ;
                  (W_Write "break;") ; W_NewLine ]
            | S_Uninterned _ -> failwith "Unable to call uninterned primitive"
      | O_Call argCount ->
          [ (W_Write (sprintf "ms.Call(/* argsp1 */ %i, /* return to */ %i);" argCount (Map.find i indexToCaseMap))) ; W_NewLine ;
            (W_Write "break;") ; W_NewLine ;
            W_PopIndent ; (W_Write (sprintf "case %i:" (Map.find i indexToCaseMap))) ; (W_PushIndent "  ") ; W_NewLine ]
      | O_TailCall argCount ->
          [ (W_Write (sprintf "ms.TailCall(/* argsp1 */ %i);" argCount)) ; W_NewLine ;
            (W_Write "break;") ; W_NewLine ]
      | O_MkProcedure mpa ->
          if (Array.length mpa.MPA_Captures) = 0 then
            [ (W_Write (sprintf "ms.MakeProcedure(/* arity */ %i, /* more */ %b, /* arrCaptures */ NULL, /* nCaptures */ 0, /* target */ %i);" mpa.MPA_MinArity mpa.MPA_More (Map.find mpa.MPA_Target labelToCaseMap))) ; W_NewLine ]
          else
            let (iPtr, captureCode) = doCapturesArray mpa.MPA_Captures
            captureCode @ [ (W_Write (sprintf "ms.MakeProcedure(/* arity */ %i, /* more */ %b, /* arrCaptures */ %s, /* nCaptures */ %i, /* target */ %i);" mpa.MPA_MinArity mpa.MPA_More iPtr (Array.length mpa.MPA_Captures) (Map.find mpa.MPA_Target labelToCaseMap))) ; W_NewLine ]
      | O_CallWithCatch argCount ->
          [ (W_Write (sprintf "ms.CallWithCatch(/* argsp1 */ %i, /* return to */ %i);" argCount (Map.find i indexToCaseMap))) ; W_NewLine ;
            (W_Write "break;") ; W_NewLine ;
            W_PopIndent ; (W_Write (sprintf "case %i:" (Map.find i indexToCaseMap))) ; (W_PushIndent "  ") ; W_NewLine ]
      | O_Swap ->
          [ (W_Write "ms.Swap();") ; W_NewLine ]
      | O_Let la ->
          if (Array.length la.LA_Captures) = 0 then
            [ (W_Write (sprintf "ms.Let(%i, NULL, 0);" la.LA_Variables)) ; W_NewLine ]
          else
            let (iPtr, captureCode) = doCapturesArray la.LA_Captures
            captureCode @ [ (W_Write (sprintf "ms.Let(%i, %s, %i);" la.LA_Variables iPtr (Array.length la.LA_Captures))) ; W_NewLine ]
      | O_LetRec la ->
          if (Array.length la.LA_Captures) = 0 then
            [ (W_Write (sprintf "ms.LetRec(%i, NULL, 0);" la.LA_Variables)) ; W_NewLine ]
          else
            let (iPtr, captureCode) = doCapturesArray la.LA_Captures
            captureCode @ [ (W_Write (sprintf "ms.Let(%i, %s, %i);" la.LA_Variables iPtr (Array.length la.LA_Captures))) ; W_NewLine ]
      | O_CallLetRec vc ->
          [ (W_Write (sprintf "ms.CallLetRec(%i);" vc)) ; W_NewLine ]
  let wol = opl |> List.mapi (fun i x -> (i, x)) |> List.collect (fun (i, op) -> writeInstruction i op)
  [ (W_Write "switch(ms.PC)") ; W_NewLine ;
    (W_Write "{") ; W_NewLine ;
    (W_PushIndent "  ") ; (W_Write "case 0:") ; W_NewLine ; (W_PushIndent "  ") ]
  @
  wol
  @
  [ W_PopIndent ; W_PopIndent ; (W_Write "}") ; W_NewLine ]

let show (x : ExprSrc) = write (System.Console.Out) (codeToWrites (compileFlat x))

// ----- Packrat Parser Combinators -----

type StringComparison = System.StringComparison
type Regex = System.Text.RegularExpressions.Regex
type Match = System.Text.RegularExpressions.Match
type RegexOptions = System.Text.RegularExpressions.RegexOptions
type ObjectIDGenerator = System.Runtime.Serialization.ObjectIDGenerator

type ParseSuccess<'T> =
  { S_Value : 'T ;
    S_Length : int
  }

type ParseFailure =
  { F_Messages : Set<int * string>
  }

type ParseResult<'T> =
  | Success of ParseSuccess<'T>
  | Failure of ParseFailure

type System.Runtime.Serialization.ObjectIDGenerator with
  member this.GetId(o : obj) =
    let firstTime = ref false
    this.GetId(o, firstTime)

type ICharParser<'T> =
  interface
    abstract TryParse2 : int -> ICharParserContext -> ParseResult<'T>
  end

and ICharParserContext =
  interface
    abstract TryParse<'T> : ICharParser<'T> -> int -> ParseResult<'T>
    abstract Input : string
  end

type CharParserContext(input : string) =
  class
    let memos : Map<int64 * int, obj> ref = ref Map.empty
    let inProgress : Set<int64 * int> ref = ref Set.empty
    let idgen = new ObjectIDGenerator()
    interface ICharParserContext with
      member this.TryParse<'T> (parser : ICharParser<'T>) (pos : int) =
        let parserId = idgen.GetId(parser)
        match Map.tryFind (parserId, pos) !memos with
          | None ->
              if Set.contains (parserId, pos) !inProgress then
                failwith "Left recursion detected!"
              else
                inProgress := Set.add (parserId, pos) !inProgress
                let result = parser.TryParse2 pos this
                inProgress := Set.remove (parserId, pos) !inProgress
                memos := Map.add (parserId, pos) (result :> obj) !memos
                result
          | Some r ->
             r :?> ParseResult<'T>
      member this.Input
        with get () =
          input
  end

module Parser =
  begin

    let exact (cmp : System.StringComparison) (pat : string) =
      { new ICharParser<unit> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            if pos < 0 then
              Failure { F_Messages = Set.singleton (pos, "Position before beginning") }
            elif pos + pat.Length > context.Input.Length then
              Failure { F_Messages = Set.singleton (pos, sprintf "Expected \"%s\"" pat) }
            elif System.String.Compare(context.Input.Substring(pos, pat.Length), pat, cmp) = 0 then
              Success { S_Value = () ; S_Length = pat.Length }
            else
              Failure { F_Messages = Set.singleton (pos, sprintf "Expected \"%s\"" pat) }
      }

    let exactcs = exact StringComparison.InvariantCulture

    let regex (r : Regex) (desc : string) =
      { new ICharParser<System.Text.RegularExpressions.Match> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            let theMatch = r.Match(context.Input, pos)
            if theMatch.Success && theMatch.Index = pos then
              Success { S_Value = theMatch; S_Length = theMatch.Length }
            else
              Failure { F_Messages = Set.singleton (pos, sprintf "Expected %s" desc) }
      }     

    let convert (p : ICharParser<'T>) (cvt : 'T -> 'U) =
      { new ICharParser<'U> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            let r1 = context.TryParse p pos
            match r1 with
              | Success s ->
                  Success { S_Value = (cvt s.S_Value) ; S_Length = s.S_Length }
              | Failure f ->
                  Failure f
      }

    let tryConvert (p : ICharParser<'T>) (cvt : 'T -> 'U option) (desc : string) =
      { new ICharParser<'U> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            let r1 = context.TryParse p pos
            match r1 with
              | Success s ->
                  match cvt s.S_Value with
                    | Some r2 ->
                        Success { S_Value = r2 ; S_Length = s.S_Length }
                    | None ->
                        Failure { F_Messages = Set.singleton (pos, sprintf "Conversion Failure - %s" desc) }
              | Failure f ->
                  Failure f
      }

    let ignoreValue (t : ICharParser<'T>) = convert t (fun x -> ())

    let literal (t : ICharParser<unit>) (v : 'a) = convert t (fun () -> v)

    let ws = ignoreValue (regex (new Regex("\\G\\s*", RegexOptions.Compiled)) "ws")

    let wholeString (t : ICharParser<Match>) = convert t (fun m -> m.Value)

    let seq (t : ICharParser<'T>) (u : ICharParser<'U>) (cvt : 'T -> 'U -> 'V) =
      { new ICharParser<'V> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            match context.TryParse t pos with
              | Success ts ->
                  match context.TryParse u (pos + ts.S_Length) with
                    | Success us ->
                        Success { S_Value = (cvt ts.S_Value us.S_Value) ; S_Length = ts.S_Length + us.S_Length }
                    | Failure f ->
                        Failure f
              | Failure f ->
                  Failure f
      }

    let spaced (t : ICharParser<'T>) = seq t ws (fun x y -> x)

    let alt (t : ICharParser<'T>) (u : ICharParser<'T>) =
      { new ICharParser<'T> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            match context.TryParse t pos with
              | Success ts ->
                  Success ts
              | Failure tf ->
                  match context.TryParse u pos with
                    | Success us ->
                        Success us
                    | Failure uf ->
                        Failure { F_Messages = Set.union tf.F_Messages uf.F_Messages }
      }
     
    let succeed<'T> (v : 'T) =
      { new ICharParser<'T> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            Success { S_Value = v ; S_Length = 0 }
      }

    let fail<'T> (message : string) =
      { new ICharParser<'T> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            Failure { F_Messages = Set.singleton (pos, message) }
      }

    let rec altMany (tlist : ICharParser<'T> list) =
      match tlist with
        | [] -> fail<'T> "no alternatives"
        | h :: [] -> h
        | h :: t -> alt h (altMany t)

    let rec seqMany (tlist : ICharParser<'T> list) =
      match tlist with
        | [] -> succeed<'T list> []
        | h :: [] -> (convert h (fun item -> [item]))
        | h :: t -> seq h (seqMany t) (fun i l -> i :: l)

    let opt (t : ICharParser<'T>) =
      { new ICharParser<'T option> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            match context.TryParse t pos with
              | Success ts ->
                  Success { S_Value = Some (ts.S_Value); S_Length = ts.S_Length }
              | Failure tf ->
                  Success { S_Value = None; S_Length = 0 }
      }

    let zeroOrMore (t : ICharParser<'T>) =
      let rec p =
        { new ICharParser<'T list> with
            member this.TryParse2 (pos : int) (context : ICharParserContext) =
              match context.TryParse t pos with
                | Success ts ->
                    if ts.S_Length > 0 then
                      match context.TryParse p (pos + ts.S_Length) with
                        | Success ps ->
                            Success { S_Value = ts.S_Value :: ps.S_Value ; S_Length = ts.S_Length + ps.S_Length }
                        | Failure pf ->
                            Failure pf
                    else
                      Failure { F_Messages = Set.singleton (pos, "zeroOrMore of zero-length pattern") }
                | Failure tf ->
                    Success { S_Value = [] ; S_Length = 0 }
        }
      p

    let oneOrMore (t : ICharParser<'T>) = seq t (zeroOrMore t) (fun a b -> a :: b)

    let oneOrMoreJoined (t : ICharParser<'T>) (delim : ICharParser<unit>) =
      seq t (zeroOrMore (seq delim t (fun a b -> b))) (fun a b -> a :: b)

    let zeroOrMoreJoined (t : ICharParser<'T>) (delim : ICharParser<unit>) = convert (opt (oneOrMoreJoined t delim)) (fun x -> match x with | Some r -> r | None -> [])

    let name (f : ICharParser<'T> -> ICharParser<'T>) =
      let pref : ICharParser<'T> option ref = ref None
      let p =
        { new ICharParser<'T> with
            member this.TryParse2 (pos : int) (context : ICharParserContext) =
              match !pref with
                | None ->
                    Failure { F_Messages = Set.singleton (pos, "Unassigned parser") }
                | Some p2 ->
                    context.TryParse p2 pos
        }
      let p2 = (f p)
      pref := Some p2
      p2

    let ifFollowedBy (t : ICharParser<'T>) (u : ICharParser<unit>) =
      { new ICharParser<'T> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            match context.TryParse t pos with
              | Success ts ->
                  match context.TryParse u (pos + ts.S_Length) with
                    | Success us ->
                        Success ts
                    | Failure uf ->
                        Failure uf
              | Failure tf ->
                  Failure tf
      }

    let ifNotFollowedBy (t : ICharParser<'T>) (u : ICharParser<unit>) =
      { new ICharParser<'T> with
          member this.TryParse2 (pos : int) (context : ICharParserContext) =
            match context.TryParse t pos with
              | Success ts ->
                  match context.TryParse u (pos + ts.S_Length) with
                    | Success us ->
                        Failure { F_Messages = Set.singleton ((pos + ts.S_Length), "Lookahead assertion failed") }
                    | Failure uf ->
                        Success ts
              | Failure tf ->
                  Failure tf
      }

    let run (p : ICharParser<'T>) (i : string) =
      let context = new CharParserContext(i)
      (context :> ICharParserContext).TryParse p 0

  end

let parseTrue = Parser.spaced (Parser.literal (Parser.exactcs "#t") (D_Bool true))

let parseFalse = Parser.spaced (Parser.literal (Parser.exactcs "#f") (D_Bool false))

let parseListTail (parseDatum : ICharParser<Datum>) =
  Parser.name
    (fun parseListTail ->
      Parser.alt
        (Parser.literal (Parser.spaced (Parser.exactcs ")")) [])
        (Parser.seq parseDatum parseListTail (fun h t -> h :: t)))

let parseList (parseDatum : ICharParser<Datum>) =
  Parser.seq (Parser.spaced (Parser.exactcs "(")) (parseListTail parseDatum) (fun h t -> D_List t)

let parseVector (parseDatum : ICharParser<Datum>) =
  Parser.seq (Parser.spaced (Parser.exactcs "#(")) (parseListTail parseDatum) (fun h t -> D_Vector (Array.ofList t))

let parseIntDecimal =
  Parser.spaced
    (Parser.convert
      (Parser.regex (new Regex("\\G-?(?:0(?![0-9])|(?:[1-9][0-9]*))(?![\\.eE])", RegexOptions.Compiled)) "Base 10 Integer")
      (fun m -> System.Numerics.BigInteger.Parse(m.Value)))

let strcat (x : string) (y : string) = x + y

let strCatMany (l : string list) = List.fold strcat "" l

let parseFloat =
  Parser.spaced
    ( let intPart = Parser.wholeString (Parser.regex (new Regex("\\G-?(?:0(?![0-9])|(?:[1-9][0-9]*))(?=[\\.eE])", RegexOptions.Compiled)) "Base 10 Float (int part)")
      let fracPart = Parser.wholeString (Parser.regex (new Regex("\\G\\.[0-9]*", RegexOptions.Compiled)) "Base 10 Float (frac part)")
      let exptPart = Parser.wholeString (Parser.regex (new Regex("\\G[Ee]-?[1-9][0-9]*", RegexOptions.Compiled)) "Base 10 Float (expt part)")
      Parser.convert
        (Parser.seq intPart (Parser.alt (Parser.alt fracPart exptPart) (Parser.seq fracPart exptPart strcat)) strcat)
        (fun (x : string) -> System.Double.Parse(x)))

let escapeChars =
    Map.ofList
      [ ("\\", "\\") ;
        ("a", "\a") ;
        ("b", "\b") ;
        ("t", "\t") ;
        ("n", "\n") ;
        ("v", "\v") ;
        ("f", "\f") ;
        ("r", "\r")
      ]

let hexEscape =
  (Parser.convert (Parser.regex (new Regex("\\G\\\\x([0-9A-Fa-f]{2})", RegexOptions.Compiled)) "Hex escape (string)") (fun m -> new System.String((char (System.Int32.Parse(m.Groups.[1].Value, System.Globalization.NumberStyles.HexNumber))), 1)))

let parseStringPart =
  let escapeCharsStr = Map.add "\"" "\"" escapeChars
  let oneCharEscape = "Single char escape (string)"
  Parser.altMany
    [ (Parser.wholeString (Parser.regex (new Regex("\\G[^\\\\\"\\r\\n\\t]+", RegexOptions.Compiled)) "String chars")) ;
      (Parser.tryConvert (Parser.regex (new Regex("\\G\\\\([\\\\\"abtnvfr])", RegexOptions.Compiled)) oneCharEscape) (fun m -> Map.tryFind m.Groups.[1].Value escapeCharsStr) oneCharEscape) ;
      hexEscape
    ]

let parseString =
  let quote = Parser.exactcs "\""
  let parts = Parser.convert (Parser.zeroOrMore parseStringPart) strCatMany
  Parser.spaced
    (Parser.seq (Parser.seq quote parts (fun a b -> b)) quote (fun ab c -> ab))

let parseSymbolPart =
  let escapeCharsSym = Map.add "|" "|" escapeChars
  let oneCharEscape = "Single char escape (symbol)"
  Parser.altMany
    [ (Parser.wholeString (Parser.regex (new Regex("\\G[^\\\\|\\r\\n\\t]+", RegexOptions.Compiled)) "Symbol chars")) ;
      (Parser.tryConvert (Parser.regex (new Regex("\\G\\\\([\\\\|abtnvfr])", RegexOptions.Compiled)) oneCharEscape) (fun m -> Map.tryFind m.Groups.[1].Value escapeCharsSym) oneCharEscape) ;
      hexEscape
    ]

let parseSymbolUnquoted =
  Parser.alt
    (Parser.wholeString (Parser.regex (new Regex("\\G[A-Za-z!$%&*+./:<=>?@^_~][A-Za-z0-9!$%&*+\\-./:<=>?@^_~]*", RegexOptions.Compiled)) "Unquoted symbol chars"))
    (Parser.wholeString (Parser.regex (new Regex("\\G-+(?:[A-Za-z!$%&*+./:<=>?@^_~][A-Za-z0-9!$%&*+\\-./:<=>?@^_~]*)?", RegexOptions.Compiled)) "Minus unquoted symbol chars"))

let parseSymbol =
  let bar = Parser.exactcs "|"
  let parts = Parser.convert (Parser.zeroOrMore parseSymbolPart) strCatMany
  Parser.spaced
    (Parser.alt
      parseSymbolUnquoted
      (Parser.seq (Parser.seq bar parts (fun a b -> b)) bar (fun ab c -> ab)))

let parseDatum =
  Parser.name
    (fun parseDatum ->
      let quoteLike (qchar : string) (symname : string) =
        (Parser.seq (Parser.spaced (Parser.exactcs qchar)) parseDatum (fun x y -> D_List [ (D_Symbol (S_Interned symname)) ; y ]))
      Parser.altMany
        [ parseTrue ;
          parseFalse ;
          (Parser.convert parseFloat (fun f -> D_Float f)) ;
          (Parser.convert parseIntDecimal (fun bi -> D_Int bi)) ;
          (Parser.convert parseString (fun s -> D_String s)) ;
          (Parser.convert parseSymbol (fun s -> D_Symbol (S_Interned s))) ;
          (parseList parseDatum) ;
          (parseVector parseDatum) ;
          (quoteLike "'" "quote") ;
          (quoteLike "`" "quasiquote") ;
          (quoteLike "," "unquote") ;
          (quoteLike ",@" "unquote-splicing")
        ])

let rec analyze (d : Datum) =
  match d with
    | D_Bool _ | D_Int _ | D_Float _ | D_Char _ | D_String _ -> Some (ES_Literal d)
    | D_Symbol s -> Some (ES_VarRef s)
    | D_Vector _ -> None
    | D_List (D_Symbol (S_Interned kw) :: tail) ->
        match (kw, tail) with
          | ("quote", [ v ]) ->
              Some (ES_Literal v)
          | ("set!", [ D_Symbol var ; v] ) ->
              match (analyze v) with
                | Some vexpr -> Some (ES_VarSet (var, vexpr))
                | None -> None
          | ("begin", _) ->
              match (analyzeList tail) with
                | Some exprs2 -> Some (ES_Begin exprs2)
                | None -> None
          | ("if", [ cond; thenClause; elseClause ]) ->
              let acond = analyze cond
              let aThenClause = analyze thenClause
              let aElseClause = analyze elseClause
              match (acond, aThenClause, aElseClause) with
                | ((Some acond1), (Some aThenClause1), (Some aElseClause1)) ->
                    Some (ES_IfThenElse (acond1, aThenClause1, aElseClause1))
                | _ -> None
          | ("lambda", (D_List lParams) :: lBody) ->
              if List.forall (fun lp -> match lp with | D_Symbol s1 -> true | _ -> false) lParams then
                let aBody = analyzeList lBody
                match aBody with
                  | Some aBody2 ->
                      (Some (ES_Lambda ((PSS_Items (List.map (fun (D_Symbol s) -> s) lParams)), (ES_Begin aBody2))))
                  | None -> None
              else
                None
          | ("lambda*", (D_List lParams) :: (D_Symbol lParamMore) :: lBody) ->
              if List.forall (fun lp -> match lp with | D_Symbol s1 -> true | _ -> false) lParams then
                let aBody = analyzeList lBody
                match aBody with
                  | Some aBody2 ->
                      (Some (ES_Lambda ((PSS_ItemsMore ((List.map (fun (D_Symbol s) -> s) lParams), lParamMore)), (ES_Begin aBody2))))
                  | None -> None
              else
                None
          | ("and", _) ->
              match (analyzeList tail) with
                | Some exprs -> Some (ES_And exprs)
                | None -> None
          | ("or", _) ->
              match (analyzeList tail) with
                | Some exprs -> Some (ES_Or exprs)
                | None -> None
          | ("primitive", ((D_Symbol pName) :: args)) ->
              match (analyzeList args) with
                | Some exprs -> Some (ES_Primitive (pName, exprs))
                | None -> None
          | ("let", ((D_List clauses) :: body)) ->
              match ((analyzeLetClauses clauses), (analyzeList body)) with
                | ((Some clauses), (Some body)) ->
                    Some (ES_Let (clauses, (ES_Begin body)))
                | _ -> None
          | ("let", ((D_Symbol loopName) :: (D_List clauses) :: body)) ->
              match ((analyzeLetClauses clauses), (analyzeList body)) with
                | ((Some clauses), (Some body)) ->
                    Some (ES_LetLoop (loopName, clauses, (ES_Begin body)))
                | _ -> None
          | ("let*", ((D_List clauses) :: body)) ->
              match ((analyzeLetClauses clauses), (analyzeList body)) with
                | ((Some clauses), (Some body)) ->
                    Some (ES_LetStar (clauses, (ES_Begin body)))
                | _ -> None
          | ("letrec", ((D_List clauses) :: body)) ->
              match ((analyzeLetClauses clauses), (analyzeList body)) with
                | ((Some clauses), (Some body)) ->
                    Some (ES_LetRec (clauses, (ES_Begin body)))
                | _ -> None
          | ("catch", [ handler; body ]) ->
              match analyze handler with
                | Some handlerExpr ->
                    match analyze body with
                      | Some bodyExpr ->
                          Some (ES_Catch { crsrc_handler = handlerExpr ; crsrc_body = bodyExpr })
                      | None -> None
                | None -> None
          | _ ->
              match (analyzeList tail) with
                | Some tail -> Some (ES_Invoke ((ES_VarRef (S_Interned kw)) :: tail))
                | None -> None
    | D_List otherList ->
        match (analyzeList otherList) with
          | Some otherList -> Some (ES_Invoke otherList)
          | None -> None
    | _ -> None
and analyzeList (dl : Datum list) =
  let rec loop (results : ExprSrc list) (dlremain : Datum list) =
    match dlremain with
      | [] -> Some (List.rev results)
      | h :: t ->
          match (analyze h) with
            | None -> None
            | Some h2 -> loop (h2 :: results) t
  loop [] dl
and analyzeLetClause (dl : Datum) =
  match dl with
    | D_List [ D_Symbol v ; v2 ] ->
        match analyze v2 with
          | Some v3 -> Some { lcsrc_name = v ; lcsrc_value = v3 }
          | None -> None
    | _ -> None
and analyzeLetClauses (dl : Datum list) =
  let rec loop (results : LetClauseSrc list) (dlremain : Datum list) =
    match dlremain with
      | [] -> Some (List.rev results)
      | h :: t ->
          match (analyzeLetClause h) with
            | None -> None
            | Some h2 -> loop (h2 :: results) t
  loop [] dl

let parseExpr1 (st : string) =
  match (Parser.run parseDatum st) with
    | Success s -> analyze s.S_Value
    | Failure f -> None

let parseAndCompile (st : string) =
  match parseExpr1 st with
    | Some expr -> show expr
    | None -> ()

let pcTest1 = "((lambda (x) (primitive * x x)) 4)"

let pcTest2 = "(catch (lambda (ex) (primitive println ex)) ((lambda (x) (primitive * x x)) 4))"

let pcTest3 = "(let ((pi 3.14159) (r 2.5)) (primitive * pi (primitive * r r)))"

let pcTest4 =
  "(let ((make-adder (lambda (i) (lambda (x) (primitive + i x)))) " +
  "    (my-constant 3.0) " +
  "    (other-constant 100.0)) " +
  "  (let ((add-my-constant (make-adder my-constant))) " +
  "    (add-my-constant other-constant)))"
