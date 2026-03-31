
type Symbol =
  | S_Interned of string
  | S_Uninterned of int

let nextSym = ref 0

let gensym () =
  let p = nextSym.Value
  nextSym.Value <- 1 + nextSym.Value
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
        let (count, _lsoFinal, cRev) = List.fold (fun (count, lso, clist) x -> ((count + 1), (lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (0, lso, []) xl
        let c = List.rev cRev
        { CF_Init = (List.collect (fun b -> b.CF_Init) c) ;
          CF_Body = (List.collect (fun b -> b.CF_Body) c)
            @
            ( if tail then
                [ (O_TailCall (count - 1)) ]
              else
                [ (O_Call (count - 1)) ]
            ) ;
          CF_Deferral = List.concat (List.map (fun cf -> cf.CF_Deferral) c)
        }
    | ES_Primitive (p, xl) ->
        let (count, _lsoFinal, cRev) = List.fold (fun (count, lso, clist) x -> ((count + 1), (lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (0, lso, []) xl
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
        match b with
          | ES_Invoke funcArgs ->
              let (count, lsoFinal, cRev) = List.fold (fun (count, lso, clist) x -> ((count + 1), (lso + literalSlots x), ((compile uninternedMap lso envDesc false x) :: clist))) (0, lso, []) funcArgs
              let c = List.rev cRev
              let lbl1 = gensym ()
              { CF_Init = ch.CF_Init @ (List.collect (fun b -> b.CF_Init) c) ;
                CF_Body = retIfTail tail ((List.collect (fun b -> b.CF_Body) c) @ [ (O_CallWithCatch count) ; (O_JumpIfFalse lbl1) ] @ ch.CF_Body @ [ O_Swap ; (O_Call 1) ; (O_Label lbl1) ]) ;
                CF_Deferral = ch.CF_Deferral @ (List.concat (List.map (fun cf -> cf.CF_Deferral) c))
              }
          | _ ->
            let cb = compile uninternedMap (lso + literalSlots h) envDesc false (ES_Lambda ((PSS_Items []), b))
            let lbl1 = gensym ()
            { CF_Init = ch.CF_Init @ cb.CF_Init ;
              CF_Body = retIfTail tail (cb.CF_Body @ [ (O_CallWithCatch 0) ; (O_JumpIfFalse lbl1) ] @ ch.CF_Body @ [ O_Swap ; (O_Call 1) ; (O_Label lbl1) ]) ;
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
    let iPtr = (sprintf "captures_%i" nextSym.Value)
    nextSym.Value <- 1 + nextSym.Value
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
            captureCode @ [ (W_Write (sprintf "ms.LetRec(%i, %s, %i);" la.LA_Variables iPtr (Array.length la.LA_Captures))) ; W_NewLine ]
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

type ObjectIDGenerator2() =
  class
    let dict = new System.Collections.Generic.Dictionary<obj, int64>(System.Collections.Generic.ReferenceEqualityComparer.Instance)

    member this.GetId(o : obj) =
      match dict.TryGetValue(o) with
        | (true, id) -> id
        | (false, _) ->
            let id = int64 dict.Count
            dict.Add(o, id)
            id
  end

type StringComparison = System.StringComparison
type Regex = System.Text.RegularExpressions.Regex
type Match = System.Text.RegularExpressions.Match
type RegexOptions = System.Text.RegularExpressions.RegexOptions

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
    let idgen = new ObjectIDGenerator2()
    interface ICharParserContext with
      member this.TryParse<'T> (parser : ICharParser<'T>) (pos : int) =
        let parserId = idgen.GetId(parser)
        match Map.tryFind (parserId, pos) memos.Value with
          | None ->
              if Set.contains (parserId, pos) inProgress.Value then
                failwith "Left recursion detected!"
              else
                inProgress.Value <- Set.add (parserId, pos) inProgress.Value
                let result = parser.TryParse2 pos this
                inProgress.Value <- Set.remove (parserId, pos) inProgress.Value
                memos.Value <- Map.add (parserId, pos) (result :> obj) memos.Value
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
              match pref.Value with
                | None ->
                    Failure { F_Messages = Set.singleton (pos, "Unassigned parser") }
                | Some p2 ->
                    context.TryParse p2 pos
        }
      let p2 = (f p)
      pref.Value <- Some p2
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

type MachineState =
  { MS_Stack : RuntimeDatum list ;
    MS_NextStep : MachineStep ;
    MS_Literals : RuntimeDatum array ;
    MS_Env : (RuntimeDatum ref) array ;
    MS_ReturnTo : RuntimeContinuation ;
    MS_Done : bool
  }
and MachineStep =
  | M_Exec of int
  | M_Call of CallData
  | M_Halt of string // this is sort of a temporary measure until proper exception handling is implemented
and ContinuationData =
  { RD_Stack : RuntimeDatum list ;
    RD_PC : int ;
    RD_Env : (RuntimeDatum ref) array
    RD_ReturnTo : RuntimeContinuation
  }
and RuntimeContinuation =
  | RK_FinalContinuation
  | RK_Continuation of ContinuationData
  | RK_ContinuationWithCatch of ContinuationData
and StandardProcedureData =
  { RP_MinArity : int ;
    RP_More : bool ;
    RP_Captures : (RuntimeDatum ref) array ;
    RP_Target : int
  }
and RuntimeProcedure =
  | RP_StandardProcedure of StandardProcedureData
  | RP_CallCc
  | RP_ContinuationProcedure of RuntimeContinuation
and RuntimeDatum =
  | R_Unspecified
  | R_Bool of bool
  | R_Int of bigint
  | R_Float of float
  | R_Char of char
  | R_String of string
  | R_Symbol of Symbol
  | R_List of RuntimeDatum list
  | R_Vector of RuntimeDatum[]
  | R_Procedure of RuntimeProcedure
and CallData =
  { CD_Proc : RuntimeProcedure ;
    CD_Args : RuntimeDatum list ;
    CD_K : RuntimeContinuation
  }

let procArity (p : RuntimeProcedure) =
  match p with
    | RP_StandardProcedure spd -> spd.RP_MinArity
    | RP_CallCc -> 1
    | RP_ContinuationProcedure _ -> 1

let procMoreArity (p : RuntimeProcedure) =
  match p with
    | RP_StandardProcedure spd -> spd.RP_More
    | RP_CallCc -> false
    | RP_ContinuationProcedure _ -> false

type RuntimeMakeProcedureArgs =
  { RMPA_MinArity : int ;
    RMPA_More : bool ;
    RMPA_Captures : int array ;
    RMPA_Target : int
  }

type RuntimeOpcode =
  | RO_CreateLiteralPool of int
  | RO_LdBool of bool
  | RO_LdInt of bigint
  | RO_LdFloat of float
  | RO_LdChar of char
  | RO_LdStr of string
  | RO_LdSymbol of Symbol
  | RO_Gensym
  | RO_LdEmptyList
  | RO_ConsList
  | RO_MkVector of int
  | RO_SetVectorElement of int // vector val -> vector
  | RO_StoreLiteral of int
  | RO_LdLiteral of int
  | RO_VarRef of int
  | RO_VarSet of int // value -> unspecified-obj
  | RO_Ret
  | RO_LdUnspecified
  | RO_Drop
  | RO_JumpIfFalse of int
  | RO_Jump of int
  | RO_JumpIfTrue of int
  | RO_Dup
  | RO_CallPrimitive of Symbol * int
  | RO_TailCallPrimitive of Symbol * int
  | RO_Call of int
  | RO_TailCall of int
  | RO_MkProcedure of RuntimeMakeProcedureArgs
  | RO_CallWithCatch of int
  | RO_Swap
  | RO_Let of LetArgs
  | RO_LetRec of LetArgs
  | RO_CallLetRec of int // pops 1 procedure from the stack, passes N dummy values to it

let rec datumToRuntimeDatum (d : Datum) =
  match d with
    | D_Unspecified -> R_Unspecified
    | D_Bool b -> R_Bool b
    | D_Int i -> R_Int i
    | D_Float f -> R_Float f
    | D_Char c -> R_Char c
    | D_String s -> R_String s
    | D_Symbol sym -> R_Symbol sym
    | D_List l -> R_List (List.map datumToRuntimeDatum l)
    | D_Vector v -> R_Vector (Array.map datumToRuntimeDatum v)

let opcodeLength (o : Opcode) =
  match o with
    | O_Label _ -> 0
    | _ -> 1

let opcodeListLength (ol : Opcode list) = List.fold (fun acc o -> acc + opcodeLength o) 0 ol

let makeLabelMap (ol : Opcode list) =
  let rec loop (olremain : Opcode list) (currentIndex : int) (labelMap : Map<Symbol, int>) =
    match olremain with
      | [] -> labelMap
      | o :: t ->
          match o with
            | O_Label lbl ->
                loop t currentIndex (Map.add lbl currentIndex labelMap)
            | _ ->
                loop t (currentIndex + opcodeLength o) labelMap
  loop ol 0 Map.empty

let opcodeToRuntimeOpcode (labelMap : Map<Symbol, int>) (o : Opcode) =
  match o with
    | O_CreateLiteralPool i -> RO_CreateLiteralPool i
    | O_LdBool b -> RO_LdBool b
    | O_LdInt i -> RO_LdInt i
    | O_LdFloat f -> RO_LdFloat f
    | O_LdChar ch -> RO_LdChar ch
    | O_LdStr str -> RO_LdStr str
    | O_LdSymbol sym -> RO_LdSymbol sym
    | O_Gensym -> RO_Gensym
    | O_LdEmptyList -> RO_LdEmptyList
    | O_ConsList -> RO_ConsList
    | O_MkVector size -> RO_MkVector size
    | O_SetVectorElement index -> RO_SetVectorElement index // vector val -> vector
    | O_StoreLiteral index -> RO_StoreLiteral index
    | O_LdLiteral index -> RO_LdLiteral index
    | O_VarRef index -> RO_VarRef index
    | O_VarSet index -> RO_VarSet index // value -> unspecified-obj
    | O_Ret -> RO_Ret
    | O_LdUnspecified -> RO_LdUnspecified
    | O_Drop -> RO_Drop
    | O_JumpIfFalse sym -> RO_JumpIfFalse (Map.find sym labelMap)
    | O_Label _ -> failwith "Label not expected here"
    | O_Jump sym -> RO_Jump (Map.find sym labelMap)
    | O_JumpIfTrue sym -> RO_JumpIfTrue (Map.find sym labelMap)
    | O_Dup -> RO_Dup
    | O_CallPrimitive (name, args) -> RO_CallPrimitive (name, args)
    | O_TailCallPrimitive (name, args) -> RO_TailCallPrimitive (name, args)
    | O_Call args -> RO_Call args
    | O_TailCall args -> RO_TailCall args
    | O_MkProcedure mpa -> RO_MkProcedure { RMPA_MinArity = mpa.MPA_MinArity ; RMPA_More = mpa.MPA_More ; RMPA_Captures = mpa.MPA_Captures ; RMPA_Target = Map.find mpa.MPA_Target labelMap }
    | O_CallWithCatch args -> RO_CallWithCatch args
    | O_Swap -> RO_Swap
    | O_Let letArgs -> RO_Let letArgs
    | O_LetRec letArgs -> RO_LetRec letArgs
    | O_CallLetRec args -> RO_CallLetRec args // pops 1 procedure from the stack, passes N dummy values to it

let makeRuntimeOpcodeArray (ol : Opcode list) =
  let labelMap = makeLabelMap ol
  let arrayLen = opcodeListLength ol
  let rec loop (olremain : Opcode list) (currentIndex : int) (acc : RuntimeOpcode list) =
    match olremain with
      | [] -> List.rev acc |> List.toArray
      | o :: t ->
          match o with
            | O_Label _ ->
                loop t currentIndex acc
            | _ ->
                let ro = opcodeToRuntimeOpcode labelMap o
                loop t (currentIndex + opcodeLength o) (ro :: acc)
  loop ol 0 []


let initialMachineState =
  { MS_Stack = [] ;
    MS_NextStep = M_Exec 0 ;
    MS_Literals = [||] ;
    MS_Env = [||] ;
    MS_ReturnTo = RK_FinalContinuation ;
    MS_Done = false
  }

let parseForRunning (x : string) =
  let parseResult = Parser.run parseDatum x
  match Parser.run parseDatum x with
    | Success { S_Value = s ; S_Length = _ } ->
        match analyze s with
          | Some a -> compileFlat a |> makeRuntimeOpcodeArray |> Some
          | None ->
              printfn "Analysis failed"
              None
    | Failure f ->
        printfn "Parse failed"
        None

let isTruthy (v : RuntimeDatum) =
  match v with
    | R_Bool false -> false
    | _ -> true

let doCaptures (env : (RuntimeDatum ref array)) (captures : int array) =
  Array.map (fun i -> env[i]) captures

type DoExtendArgs =
  { DE_Stack : RuntimeDatum list ; // args should be [ arg0 ; arg1 ; arg2 ; ... ]
    DE_ActualArity : int ;
    DE_ExpectedArity : int ;
    DE_ExpectsMore : bool ;
    DE_Captures : RuntimeDatum ref array ;
  }

type ExtendResult =
  | ER_InsufficientArguments
  | ER_ExcessiveArguments
  | ER_ExtendSuccess of RuntimeDatum ref array

let tryArgSplit (i : int) (s : RuntimeDatum list) =
  if (List.length s) >= i then
    Some (List.take i s, List.skip i s)
  else
    None

let doExtend (a : DoExtendArgs) =
  if (a.DE_ActualArity < a.DE_ExpectedArity) then
    ER_InsufficientArguments
  elif a.DE_ExpectsMore then
    match tryArgSplit a.DE_ExpectedArity a.DE_Stack with
      | Some (args, rest) ->
          let argsWithRest = List.rev ((R_List rest) :: (List.rev args))
          ER_ExtendSuccess (Array.append a.DE_Captures (argsWithRest |> List.map (fun x -> ref x) |> List.toArray))
      | None ->
          ER_InsufficientArguments
  elif (a.DE_ActualArity > a.DE_ExpectedArity) then
    ER_ExcessiveArguments
  else
    ER_ExtendSuccess (Array.append a.DE_Captures (a.DE_Stack |> List.map (fun x -> ref x) |> List.toArray))

let doExtendLet (args : RuntimeDatum list) (captures : RuntimeDatum ref array) =
  Array.append captures (args |> List.rev |> List.map (fun x -> ref x) |> List.toArray)

let doExtendLetRec (argCount : int) (captures : RuntimeDatum ref array) =
  Array.append captures (Array.init argCount (fun _ -> ref R_Unspecified))

type ProcArgsSuccessRecord =
  { PASR_Proc : RuntimeProcedure ;
    PASR_Args : RuntimeDatum list ;
    PASR_Rest : RuntimeDatum list
  }

type ProcArgsResult =
  | PAR_Success of ProcArgsSuccessRecord
  | PAR_CallToNonProcedure
  | PAR_StackUnderflowPoppingProcedure

let handleProcArgs (argCount : int) (ms : MachineState) =
  match tryArgSplit (argCount + 1) ms.MS_Stack with
    | Some (procAndArgs, rest) ->
        match List.rev procAndArgs with
          | uProc :: args ->
              match uProc with
                | R_Procedure proc ->
                    PAR_Success { PASR_Proc = proc ; PASR_Args = args ; PASR_Rest = rest }
                | _ ->
                    PAR_CallToNonProcedure
          | _ ->
              failwith "argCount should have been at least zero"
    | None ->
        PAR_StackUnderflowPoppingProcedure

let runOpcode (ro : RuntimeOpcode) (ms : MachineState) =
  let nextPC =
    match ms.MS_NextStep with
      | M_Exec pc -> pc
      | _ -> failwith "Next step should have been M_Exec"
  match ro with
    | RO_CreateLiteralPool size ->
        { ms with MS_Literals = Array.init size (fun _ -> R_Unspecified) }
    | RO_LdBool b ->
        { ms with MS_Stack = (R_Bool b) :: ms.MS_Stack }
    | RO_LdInt i ->
        { ms with MS_Stack = (R_Int i) :: ms.MS_Stack }
    | RO_LdFloat f ->
        { ms with MS_Stack = (R_Float f) :: ms.MS_Stack }
    | RO_LdChar ch ->
        { ms with MS_Stack = (R_Char ch) :: ms.MS_Stack }
    | RO_LdStr str ->
        { ms with MS_Stack = (R_String str) :: ms.MS_Stack }
    | RO_LdSymbol sym ->
        { ms with MS_Stack = (R_Symbol sym) :: ms.MS_Stack }
    | RO_Gensym ->
        { ms with MS_Stack = (R_Symbol (gensym ())) :: ms.MS_Stack }
    | RO_LdEmptyList ->
        { ms with MS_Stack = (R_List []) :: ms.MS_Stack }
    | RO_ConsList ->
        match ms.MS_Stack with
          | v2 :: v1 :: rest ->
              { ms with MS_Stack = (R_List (v1 :: (match v2 with | R_List l -> l | _ -> failwith "RO_ConsList: type mismatch"))) :: rest }
          | _ -> failwith "RO_ConsList: stack underflow"
    | RO_MkVector size ->
        { ms with MS_Stack = (R_Vector (Array.init size (fun _ -> R_Unspecified))) :: ms.MS_Stack }
    | RO_SetVectorElement index ->
        match ms.MS_Stack with
          | vec :: theVal :: rest ->
              match vec with
                | R_Vector rvec ->
                    rvec[index] <- theVal
                    { ms with MS_Stack = vec :: rest }
                | _ -> failwith "RO_SetVectorElement: type mismatch"
          | _ -> failwith "RO_SetVectorElement: stack underflow"
    | RO_StoreLiteral index ->
        match ms.MS_Stack with
          | theVal :: rest ->
              ms.MS_Literals[index] <- theVal
              { ms with MS_Stack = rest }
          | _ -> failwith "RO_StoreLiteral: stack underflow"
    | RO_LdLiteral index ->
        { ms with MS_Stack = ms.MS_Literals[index] :: ms.MS_Stack }
    | RO_VarRef index ->
        { ms with MS_Stack = ms.MS_Env[index].Value :: ms.MS_Stack }
    | RO_VarSet index ->
        match ms.MS_Stack with
          | theVal :: rest ->
              ms.MS_Env[index].Value <- theVal
              { ms with MS_Stack = R_Unspecified :: rest }
          | _ -> failwith "RO_VarSet: stack underflow"
    | RO_Ret ->
        match ms.MS_Stack with
          | returnVal :: _ ->
              match ms.MS_ReturnTo with
                | RK_Continuation kd ->
                    { ms with
                        MS_Stack = returnVal :: kd.RD_Stack ;
                        MS_NextStep = M_Exec kd.RD_PC ;
                        MS_Env = Array.copy kd.RD_Env ;
                        MS_ReturnTo = kd.RD_ReturnTo
                    }
                | RK_ContinuationWithCatch kd ->
                    { ms with
                        MS_Stack = (R_Bool false) :: returnVal :: kd.RD_Stack ;
                        MS_NextStep = M_Exec kd.RD_PC ;
                        MS_Env = Array.copy kd.RD_Env ;
                        MS_ReturnTo = kd.RD_ReturnTo
                    }
                | RK_FinalContinuation ->
                    { ms with MS_Done = true }
          | _ -> failwith "RO_Ret: stack underflow"
    | RO_LdUnspecified ->
        { ms with MS_Stack = R_Unspecified :: ms.MS_Stack }
    | RO_Drop ->
        match ms.MS_Stack with
          | _ :: rest ->
              { ms with MS_Stack = rest }
          | _ -> failwith "RO_Drop: stack underflow"
    | RO_JumpIfFalse target ->
        match ms.MS_Stack with
          | v :: rest ->
              if isTruthy v then
                { ms with MS_Stack = rest }
              else
                { ms with MS_NextStep = M_Exec target ; MS_Stack = rest }
          | _ -> failwith "RO_JumpIfFalse: stack underflow"
    | RO_Jump target ->
        { ms with MS_NextStep = M_Exec target }
    | RO_JumpIfTrue target ->
        match ms.MS_Stack with
          | v :: rest ->
              if isTruthy v then
                { ms with MS_NextStep = M_Exec target ; MS_Stack = rest }
              else
                { ms with MS_Stack = rest }
          | _ -> failwith "RO_JumpIfTrue: stack underflow"
    | RO_Dup ->
        match ms.MS_Stack with
          | v :: rest ->
              { ms with MS_Stack = v :: v :: rest }
          | _ -> failwith "RO_Dup: stack underflow"
    // RO_CallPrimitive
    // RO_TailCallPrimitive
    | RO_Call argCount ->
        match handleProcArgs argCount ms with
          | PAR_Success { PASR_Proc = proc ; PASR_Args = args ; PASR_Rest = rest } ->
              { ms with
                  MS_NextStep = M_Call { CD_Proc = proc ; CD_Args = args ; CD_K = RK_Continuation { RD_Stack = rest ; RD_PC = nextPC ; RD_Env = ms.MS_Env ; RD_ReturnTo = ms.MS_ReturnTo } } ;
              }
          | PAR_CallToNonProcedure -> failwith "RO_Call: attempt to call non-procedure"
          | PAR_StackUnderflowPoppingProcedure -> failwith "RO_Call: stack underflow (attempting to pop procedure)"
    | RO_TailCall argCount ->
        match handleProcArgs argCount ms with
          | PAR_Success { PASR_Proc = proc ; PASR_Args = args ; PASR_Rest = rest } ->
              { ms with
                  MS_NextStep = M_Call { CD_Proc = proc ; CD_Args = args ; CD_K = ms.MS_ReturnTo }
              }
          | PAR_CallToNonProcedure -> failwith "RO_TailCall: attempt to call non-procedure"
          | PAR_StackUnderflowPoppingProcedure -> failwith "RO_TailCall: stack underflow (attempting to pop procedure)"
    | RO_MkProcedure rmpa ->
        let captures = doCaptures ms.MS_Env rmpa.RMPA_Captures
        let proc = R_Procedure (RP_StandardProcedure { RP_MinArity = rmpa.RMPA_MinArity ; RP_More = rmpa.RMPA_More ; RP_Captures = captures ; RP_Target = rmpa.RMPA_Target })
        { ms with MS_Stack = proc :: ms.MS_Stack }
    | RO_CallWithCatch argCount ->
        match handleProcArgs argCount ms with
          | PAR_Success { PASR_Proc = proc ; PASR_Args = args ; PASR_Rest = rest } ->
              { ms with
                  MS_NextStep = M_Call { CD_Proc = proc ; CD_Args = args ; CD_K = RK_ContinuationWithCatch { RD_Stack = rest ; RD_PC = nextPC ; RD_Env = ms.MS_Env ; RD_ReturnTo = ms.MS_ReturnTo } } ;
              }
          | PAR_CallToNonProcedure -> failwith "RO_TailCall: attempt to call non-procedure"
          | PAR_StackUnderflowPoppingProcedure -> failwith "RO_TailCall: stack underflow (attempting to pop procedure)"
    | RO_Swap ->
        match ms.MS_Stack with
          | v1 :: v2 :: rest ->
              { ms with MS_Stack = v2 :: v1 :: rest }
          | _ -> failwith "RO_Swap: stack underflow"
    | RO_Let letArgs ->
        match tryArgSplit letArgs.LA_Variables ms.MS_Stack with
          | Some (args, newStack) ->
              assert List.isEmpty newStack
              let newEnv = doExtendLet args (doCaptures ms.MS_Env letArgs.LA_Captures)
              { ms with MS_Stack = [] ; MS_Env = newEnv }
          | None -> failwith "RO_Let: stack underflow"
    | RO_LetRec letArgs ->
        let newEnv = doExtendLetRec letArgs.LA_Variables (doCaptures ms.MS_Env letArgs.LA_Captures)
        assert List.isEmpty ms.MS_Stack
        { ms with MS_Stack = [] ; MS_Env = newEnv }
    | RO_CallLetRec argCount ->
        match ms.MS_Stack with
          | uProc :: rest ->
              match uProc with
                | R_Procedure proc ->
                    { ms with
                        MS_NextStep = M_Call { CD_Proc = proc ; CD_Args = List.init argCount (fun _ -> R_Unspecified) ; CD_K = RK_Continuation { RD_Stack = rest ; RD_PC = nextPC ; RD_Env = ms.MS_Env ; RD_ReturnTo = ms.MS_ReturnTo } }
                    }
                | _ -> failwith "RO_CallLetRec: attempt to call non-procedure"
          | _ -> failwith "RO_CallLetRec: stack underflow (attempting to pop procedure)"
    | _ -> failwith "Opcode not implemented yet"

let nextStep (code : RuntimeOpcode array) (ms : MachineState) =
  match ms.MS_NextStep with
    | M_Exec pc ->
        if pc >= 0 && pc < code.Length then
          let ro = code[pc]
          let newMs = { ms with MS_NextStep = M_Exec (pc + 1) }
          runOpcode ro newMs
        else
          failwith "Program counter out of bounds"
    | M_Call { CD_Proc = proc ; CD_Args = args ; CD_K = k } ->
        match proc with
          | RP_StandardProcedure spd ->
              let extendResult = doExtend { DE_Stack = args ; DE_ActualArity = List.length args ; DE_ExpectedArity = spd.RP_MinArity ; DE_ExpectsMore = spd.RP_More ; DE_Captures = spd.RP_Captures }
              match extendResult with
                  | ER_InsufficientArguments -> failwith "RO_Call: insufficient arguments"
                  | ER_ExcessiveArguments -> failwith "RO_Call: excessive arguments"
                  | ER_ExtendSuccess newEnv ->
                      { ms with
                          MS_Stack = [] ;
                          MS_NextStep = M_Exec spd.RP_Target ;
                          MS_Env = newEnv ;
                          MS_ReturnTo = k
                      }
          | RP_CallCc ->
              match args with
                | [ uProc ] ->
                    match uProc with
                      | R_Procedure proc ->
                          { ms with
                              MS_NextStep = M_Call { CD_Proc = proc ; CD_Args = [ (R_Procedure (RP_ContinuationProcedure k)) ] ; CD_K = k } ;
                          }
                      | _ ->
                          failwith "Argument to call/cc was not a procedure"
                | _ :: _ ->
                    failwith "call/cc called with too many arguments"
                | [] ->
                    failwith "call/cc called with no arguments (expected exactly one)"
          | RP_ContinuationProcedure cont ->
              match args with
                | [ retval ] ->
                    match cont with
                      | RK_Continuation kd ->
                          { ms with
                              MS_Stack = retval :: kd.RD_Stack ;
                              MS_NextStep = M_Exec kd.RD_PC ;
                              MS_Env = Array.copy kd.RD_Env ;
                              MS_ReturnTo = kd.RD_ReturnTo
                          }
                      | RK_FinalContinuation ->
                          { ms with
                              MS_Stack = retval :: ms.MS_Stack ;
                              MS_NextStep = M_Halt "Returned to final continuation" ;
                              MS_Env = ms.MS_Env ;
                              MS_ReturnTo = RK_FinalContinuation
                          }
                      | RK_ContinuationWithCatch kd ->
                          { ms with
                              MS_Stack = (R_Bool true) :: retval :: kd.RD_Stack ;
                              MS_NextStep = M_Exec kd.RD_PC ;
                              MS_Env = Array.copy kd.RD_Env ;
                              MS_ReturnTo = kd.RD_ReturnTo
                          }
                | _ :: _ ->
                    failwith "Continuation procedure called with too many arguments (expected exactly one)"
                | [] ->
                    failwith "Continuation procedure called with no arguments (expected exactly one)"
    | M_Halt msg ->
        failwithf "Machine halted: %s" msg