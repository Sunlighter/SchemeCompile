// FScheme by Edward Kiser
// Copyright (c) 2011
// Licensed under the Apache License version 2.0

module FScheme

type RunnableStep =
  | RS_Eval of Expr * Env * Continuation
  | RS_Apply of Func * Datum list * Continuation
  | RS_Return of Continuation * Datum
  | RS_Throw of Continuation * Datum
and Datum =
  | D_Bool of bool
  | D_Int of bigint
  // | D_Float of float
  // | D_Char of char
  | D_String of string
  // | D_Symbol of Symbol
  | D_List of Datum list
  // | D_Vector of Datum array
  // | D_Expr of Expr
  // | D_ExprSrc of ExprSrc
  | D_Func of Func
  // | D_ParamInfoSrc of ParamSpecSrc
  // | D_Env of Env
  | D_Unspecified
and Expr =
  | E_Literal of Datum
  | E_VarRef of int
  | E_VarSet of int * Expr
  | E_Begin of Expr list
  | E_IfThenElse of Expr * Expr * Expr
  | E_Lambda of ParamSpec * CaptureMap * Expr
  | E_Invoke of Expr list
  | E_And of Expr list
  | E_Or of Expr list
  | E_Catch of CatchRecord
and CatchRecord = { cr_handler : Expr ; cr_body : Expr }
and ExprSrc =
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
and CatchRecordSrc = { crsrc_handler : ExprSrc ; crsrc_body : ExprSrc }
and EnvDesc = Map<Symbol, int>
and EnvSpec = Set<Symbol>
and Env = Ref<Datum> array
and InitialEnv = Map<Symbol, Datum>
and CaptureMap = int array
and Continuation =
  | K_Final
  | K_VarSet of Env * int * Continuation
  | K_Begin of Env * Expr list * Continuation
  | K_IfThenElse of Env * Expr * Expr * Continuation
  | K_Invoke of Env * Datum list * Expr list * Continuation
  | K_And of Env * Expr list * Continuation
  | K_Or of Env * Expr list * Continuation
  | K_Catch1 of Env * Expr * Continuation
  | K_Catch2 of Func * Continuation
and ParamSpec = int * bool
and ParamSpecSrc =
  | PSS_Items of Symbol list
  | PSS_ItemsMore of Symbol list * Symbol
and Func =
  | F_BuiltIn of string
  | F_UserDefined of ParamSpec * Env * Expr
  | F_Continuation of Continuation
and Symbol =
  | S_Interned of string
  | S_Uninterned of int ;;

let truthTest (x : Datum) =
  match x with
    | D_Bool false -> false
    | _ -> true ;;

let getSymbolSetFromParamSpecSrc (x : ParamSpecSrc) : EnvSpec =
  match x with
   | PSS_Items list -> Set.ofList list
   | PSS_ItemsMore (list, sym) -> Set.add sym (Set.ofList list) ;;

let getParamSpecFromParamSpecSrc (x : ParamSpecSrc) : ParamSpec =
  match x with
   | PSS_Items list -> ((List.length list), false)
   | PSS_ItemsMore (list, sym) -> ((List.length list), true) ;;

let getEnvDescFromParamSpecSrc (offset : int) (x : ParamSpecSrc) =
  match x with
   | PSS_Items list -> Seq.zip list [ offset .. ((List.length list) + offset - 1) ]
   | PSS_ItemsMore (list, sym) -> Seq.zip (Seq.append list (Seq.singleton sym)) [ offset .. ((List.length list) + offset) ] ;;

let varCount (ps : ParamSpec) =
  let (ac, more) = ps in
    if more then (ac + 1) else ac ;;

let acceptsArgs (ps : ParamSpec) (x : int) =
  match ps with
    | (a, false) -> (x = a)
    | (a, true) -> (x >= a) ;;

let rec getEnvSpec (x : ExprSrc) =
  match x with
   | ES_Literal m -> (Set.empty : Set<Symbol>)
   | ES_VarRef var -> Set.singleton var
   | ES_VarSet (var, expr) -> Set.union (Set.singleton var) (getEnvSpec expr)
   | ES_Begin list -> Set.unionMany (List.map getEnvSpec list)
   | ES_IfThenElse (cond, conseq, alt) -> Set.union (getEnvSpec cond) (Set.union (getEnvSpec conseq) (getEnvSpec alt))
   | ES_Lambda (argspec, expr) -> Set.difference (getEnvSpec expr) (getSymbolSetFromParamSpecSrc argspec)
   | ES_Invoke list -> Set.unionMany (List.map getEnvSpec list)
   | ES_And list -> Set.unionMany (List.map getEnvSpec list)
   | ES_Or list -> Set.unionMany (List.map getEnvSpec list)
   | ES_Catch { crsrc_handler = h ; crsrc_body = b } -> Set.union (getEnvSpec h) (getEnvSpec b) ;;

let makeEnvDesc (x : EnvSpec) =
   Map.ofSeq (Seq.zip x [ 0 .. Set.count x ]) ;;

//let makeEnvDesc2 (x : EnvSpec) (y : ParamSpecSrc) : EnvDesc =
//   Map.ofSeq (Seq.append (Seq.zip x [ 0 .. Set.count x ]) (getEnvDescFromParamSpecSrc (Set.count x) y)) ;;

let makeEnvDesc2 (z : EnvDesc) (x : EnvSpec) (y : ParamSpecSrc) : EnvDesc =
   Map.ofSeq (Seq.append (Seq.map (fun i -> (i, (Map.find i z))) x) (getEnvDescFromParamSpecSrc (Set.count x) y)) ;;

//let makeEnvDesc3 (z : EnvDesc) (x : EnvSpec) : EnvDesc =
//   Map.ofSeq (Seq.map (fun i -> (i, (Map.find i z))) x) ;;

let envSize (x : EnvDesc) =
   (Map.fold (fun maxv k v -> (max maxv v)) -1 x) + 1 ;;

let envGaps (x : EnvDesc) =
   Map.fold (fun gaps k v -> (Set.remove v gaps)) (Set.ofSeq [ 0 .. (envSize x) - 1 ]) x ;;

let makeEnv (x : EnvDesc) (y : InitialEnv) =
   let arr = (Array.zeroCreate (envSize x) : Env) in
   Map.iter (fun k v -> arr.[v] <- ref (Map.find k y)) x
   arr ;;

let runtimeCapture (env : Env) (capturemap : CaptureMap) : Env =
   let iEnd = (Array.length capturemap) in
   let newEnv = ((Array.zeroCreate iEnd) : Env) in
   for i = 0 to (iEnd - 1) do
     newEnv.[i] <- env.[capturemap.[i]]
   newEnv ;;

let runtimeExtend (env : Env) (ps : ParamSpec) (vals : Datum list) =
  let myVarCount = (varCount ps) in
    if myVarCount = 0
    then
      env
    else
      let (arity, more) = ps in
      let newEnv = ((Array.zeroCreate ((Array.length env) + myVarCount)) : Ref<Datum> array) in
        (Array.blit env 0 newEnv 0 (Array.length env)) ;
        let rec writeArg (ptr : int) (arity : int) (more: bool) (vals : Datum list) =
          match (arity, more, vals) with
            | (0, false, []) -> ()
            | (0, false, a) -> failwith "too many arguments"
            | (0, true, a) -> newEnv.[ptr] <- ref (D_List a) ; ()
            | (a1, m1, a :: b) -> newEnv.[ptr] <- ref a ; (writeArg (ptr + 1) (a1 - 1) m1 b)
            | (a1, m1, []) -> failwith "too few arguments"
        in
          (writeArg (Array.length env) arity more vals) ; newEnv ;;

let compileCapture (envdesc : EnvDesc) (pss : ParamSpecSrc) (bodyenvspec : EnvSpec) =
   let captureSpec = Set.difference bodyenvspec (getSymbolSetFromParamSpecSrc pss) in
   let captureMap = Array.ofSeq (Set.map (fun x -> Map.find x envdesc) captureSpec) in
   let captureDesc =
     let rmap = Map.ofList (List.map (fun (a, b) -> (b, a)) (Map.toList envdesc)) in
     Map.ofSeq (Array.mapi (fun i x -> ((Map.find x rmap), i)) captureMap) in
   let bodyEnvDesc = makeEnvDesc2 captureDesc captureSpec pss in
   (captureMap, bodyEnvDesc) ;;

let rec compile (envdesc : EnvDesc) (x : ExprSrc) =
  match x with
   | ES_Literal m -> E_Literal m
   | ES_VarRef var -> E_VarRef (Map.find var envdesc)
   | ES_VarSet (var, expr) -> E_VarSet ((Map.find var envdesc), (compile envdesc expr))
   | ES_Begin exprlist -> E_Begin (List.map (compile envdesc) exprlist)
   | ES_IfThenElse (cond, conseq, alt) -> E_IfThenElse ((compile envdesc cond), (compile envdesc conseq), (compile envdesc alt))
   | ES_Invoke exprlist -> E_Invoke (List.map (compile envdesc) exprlist)
   | ES_Lambda (paramspecsrc, body) ->
      let (captureMap, bodyEnvDesc) = compileCapture envdesc paramspecsrc (getEnvSpec body)
      in (E_Lambda ((getParamSpecFromParamSpecSrc paramspecsrc), captureMap, (compile bodyEnvDesc body)))
   | ES_And exprlist -> E_And (List.map (compile envdesc) exprlist)
   | ES_Or exprlist -> E_Or (List.map (compile envdesc) exprlist)
   | ES_Catch { crsrc_handler = h ; crsrc_body = b } -> E_Catch { cr_handler = (compile envdesc h) ; cr_body = (compile envdesc b) } ;;

type FunTabItem =
  { ft_fun : (Datum list -> Continuation -> RunnableStep) ; ft_arity : int ; ft_more : bool } ;;

let funtab : Map<string, FunTabItem> ref = ref Map.empty ;;

let funCallCc (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Func f) ] -> (RS_Apply (f, [ (D_Func (F_Continuation k)) ], k))
   | _ -> (RS_Throw (k, D_String "call/cc: bad arguments")) ;;

let funPlus (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Int a); (D_Int b) ] -> (RS_Return (k, (D_Int (a+b))))
   | _ -> (RS_Throw (k, D_String "+: bad arguments")) ;;

let funMinus (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Int a) ] -> (RS_Return (k, D_Int (-a)))
   | [ (D_Int a); (D_Int b) ] -> (RS_Return (k, (D_Int (a-b))))
   | _ -> (RS_Throw (k, D_String "-: bad arguments")) ;;

let funLessThan (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Int a); (D_Int b) ] -> (RS_Return (k, (D_Bool (a < b))))
   | _ -> (RS_Throw (k, D_String "<: bad arguments")) ;;

let funEquals (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Int a); (D_Int b) ] -> (RS_Return (k, (D_Bool (a = b))))
   | _ -> (RS_Throw (k, D_String "=: bad arguments")) ;;

let funNot (args : Datum list) (k : Continuation) =
  match args with
   | [ a ] -> (RS_Return (k, D_Bool (not (truthTest a))))
   | _ -> (RS_Throw (k, D_String "not: bad arguments")) ;;

let funPrint (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_String str) ] -> printf "%s" str ; (RS_Return (k, D_Unspecified))
   | [ (D_Int i) ] -> printf "%O" i ; (RS_Return (k, D_Unspecified))
   | [ (D_Bool b) ] -> printf "%s" (if b then "#t" else "#f") ; (RS_Return (k, D_Unspecified))
   | _ -> (RS_Throw (k, D_String "print: bad arguments")) ;;

let funThrow (args : Datum list) (k : Continuation) =
  match args with
   | [ x ] -> (RS_Throw (k, x))
   | _ -> (RS_Throw (k, D_String "throw: bad arguments")) ;;

let funArity (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Func func) ] ->
      match func with
          | (F_BuiltIn x) -> 
             match Map.tryFind x !funtab with
              | None -> (RS_Throw (k, D_String "arity: unknown built-in function"))
              | Some { ft_fun = _ ; ft_arity = a ; ft_more = _ } -> (RS_Return (k, D_Int (new System.Numerics.BigInteger(a))))
          | (F_Continuation _) -> (RS_Return (k, D_Int 1I))
          | (F_UserDefined (ps, _, _)) -> (RS_Return (k, D_Int (new System.Numerics.BigInteger(fst ps))))
   | _ -> (RS_Throw (k, D_String "arity: bad arguments")) ;;

let funMoreArity (args : Datum list) (k : Continuation) =
  match args with
   | [ (D_Func func) ] ->
      match func with
          | (F_BuiltIn x) -> 
             match Map.tryFind x !funtab with
              | None -> (RS_Throw (k, D_String "more-arity: unknown built-in function"))
              | Some { ft_fun = _ ; ft_arity = _ ; ft_more = a } -> (RS_Return (k, D_Bool a))
          | (F_Continuation _) -> (RS_Return (k, D_Bool false))
          | (F_UserDefined (ps, _, _)) -> (RS_Return (k, D_Bool (snd ps)))
   | _ -> (RS_Throw (k, D_String "more-arity: bad arguments")) ;;

funtab :=
  Map.ofList
   [ ("call/cc",    { ft_fun = funCallCc    ; ft_arity = 1 ; ft_more = false });
     ("+",          { ft_fun = funPlus      ; ft_arity = 2 ; ft_more = false });
     ("-",          { ft_fun = funMinus     ; ft_arity = 1 ; ft_more = true  });
     ("<",          { ft_fun = funLessThan  ; ft_arity = 2 ; ft_more = false });
     ("=",          { ft_fun = funEquals    ; ft_arity = 2 ; ft_more = false });
     ("not",        { ft_fun = funNot       ; ft_arity = 1 ; ft_more = false });
     ("print",      { ft_fun = funPrint     ; ft_arity = 1 ; ft_more = false });
     ("throw",      { ft_fun = funThrow     ; ft_arity = 1 ; ft_more = false });
     ("arity",      { ft_fun = funArity     ; ft_arity = 1 ; ft_more = false });
     ("more-arity", { ft_fun = funMoreArity ; ft_arity = 1 ; ft_more = false });
   ] ;;

let run (rs : RunnableStep) =
  match rs with
    | RS_Eval (expr, env, k) ->
       match expr with
        | E_Literal v -> (RS_Return (k, v))
        | E_VarRef i -> (RS_Return (k, !env.[i]))
        | E_VarSet (i, expr) -> (RS_Eval (expr, env, (K_VarSet (env, i, k))))
        | E_Begin list ->
           match list with
             | [] -> (RS_Return (k, D_Unspecified))
             | h :: [] -> (RS_Eval (h, env, k))
             | h :: t -> (RS_Eval (h, env, (K_Begin (env, t, k))))
        | E_IfThenElse (cond, conseq, alt) ->
           (RS_Eval (cond, env, (K_IfThenElse (env, conseq, alt, k))))
        | E_Lambda (args, capturemap, body) ->
           (RS_Return (k, (D_Func (F_UserDefined (args, (runtimeCapture env capturemap), body)))))
        | E_Invoke list ->
           match list with
             | [] -> (RS_Throw (k, D_String "invocation requires a function"))
             | h :: t -> (RS_Eval (h, env, (K_Invoke (env, [], t, k))))
        | E_And list ->
           match list with
             | [] -> (RS_Return (k, D_Bool true))
             | h :: t -> (RS_Eval (h, env, (K_And (env, t, k))))
        | E_Or list ->
           match list with
             | [] -> (RS_Return (k, D_Bool false))
             | h :: t -> (RS_Eval (h, env, (K_Or (env, t, k))))
        | E_Catch { cr_handler = h ; cr_body = b } -> (RS_Eval (h, env, K_Catch1 (env, b, k)))
    | RS_Apply (func, args, k) ->
       match func with
        | F_BuiltIn i ->
           match (Map.tryFind i !funtab) with
             | Some { ft_fun = theFun ; ft_arity = _ ; ft_more = _ } -> (theFun args k)
             | None -> (RS_Throw (k, D_String "unknown function"))
        | F_UserDefined (paramspec, env, expr) ->
           if (acceptsArgs paramspec (List.length args)) then
             (RS_Eval (expr, (runtimeExtend env paramspec args), k))
           else
             (RS_Throw (k, D_String "incorrect number of arguments"))
        | F_Continuation k2 ->
           match args with
             | [] -> (RS_Throw (k, D_String "too few arguments to continuation"))
             | a :: [] -> (RS_Return (k2, a))
             | _ -> (RS_Throw (k, D_String "too many arguments to continuation"))
    | RS_Return (k, result) ->
       match k with
        | K_Final _ -> failwith "ran amok"
        | K_VarSet (env, index, k) -> env.[index] := result ; (RS_Return (k, D_Unspecified))
        | K_Begin (env, exprlist, k) ->
           match exprlist with
             | [] -> (RS_Return (k, result))
             | h :: [] -> (RS_Eval (h, env, k))
             | h :: t -> (RS_Eval (h, env, (K_Begin (env, t, k))))
        | K_IfThenElse (env, conseq, alt, k) ->
           if truthTest result
           then (RS_Eval (conseq, env, k))
           else (RS_Eval (alt, env, k))
        | K_Invoke (env, resultlist, exprlist, k) ->
           match exprlist with
             | [] ->
                match (List.rev (result :: resultlist)) with
                | (D_Func rh) :: rt -> (RS_Apply (rh, rt, k))
                | rh :: rt -> (RS_Throw (k, D_String "invocation of a non-function"))
                | _ -> failwith "impossible"
             | h :: t -> (RS_Eval (h, env, (K_Invoke (env, result :: resultlist, t, k))))
        | K_And (env, exprlist, k) ->
           match ((truthTest result), exprlist) with
             | (false, _) -> (RS_Return (k, D_Bool false))
             | (true, []) -> (RS_Return (k, result))
             | (true, h :: []) -> (RS_Eval (h, env, k))
             | (true, h :: t) -> (RS_Eval (h, env, (K_And (env, t, k))))
        | K_Or (env, exprlist, k) ->
           match ((truthTest result), exprlist) with
             | (true, _) -> (RS_Return (k, result))
             | (false, []) -> (RS_Return (k, D_Bool false))
             | (false, h :: []) -> (RS_Eval (h, env, k))
             | (false, h :: t) -> (RS_Eval (h, env, (K_Or (env, t, k))))
        | K_Catch1 (env, b, k) -> 
           match result with
             | D_Func f -> (RS_Eval (b, env, (K_Catch2 (f, k))))
             | _ -> (RS_Throw (k, D_String "catch handler must be a function"))
        | K_Catch2 (f, k) -> (RS_Return (k, result))
    | RS_Throw (k, exc) ->
       match k with
        | K_Final _ -> failwith "ran amok (throwing)"
        | K_VarSet (_, _, k) -> (RS_Throw (k, exc))
        | K_Begin (_, _, k) -> (RS_Throw (k, exc))
        | K_IfThenElse (_, _, _, k) -> (RS_Throw (k, exc))
        | K_Invoke (_, _, _, k) -> (RS_Throw (k, exc))
        | K_And (_, _, k) -> (RS_Throw (k, exc))
        | K_Or (_, _, k) -> (RS_Throw (k, exc))
        | K_Catch1 (_, _, k) -> (RS_Throw (k, exc))
        | K_Catch2 (f, k) -> (RS_Apply (f, [ exc ], k))

let macroLet (vars : (Symbol * ExprSrc) list) (body : ExprSrc) =
  match vars with
   | [] -> body
   | _ -> (ES_Invoke ((ES_Lambda ((PSS_Items (List.map fst vars)), body)) :: (List.map snd vars))) ;;
  
let rec macroLetStar (vars : (Symbol * ExprSrc) list) (body : ExprSrc) =
  match vars with
   | [] -> body
   | h :: t -> (ES_Invoke [ (ES_Lambda ((PSS_Items [ fst h ]), (macroLetStar t body))) ; snd h ]) ;;

let macroLetRec (vars : (Symbol * ExprSrc) list) (body : ExprSrc) =
  match vars with
   | [] -> body
   | _ -> (ES_Invoke ((ES_Lambda ((PSS_Items (List.map fst vars)), (ES_Begin (List.append (List.map (fun (sym, expr) -> (ES_VarSet (sym, expr))) vars) [ body ])))) :: List.map (fun (sym, expr) -> ES_Literal (D_Unspecified)) vars)) ;;

let macroLetLoop (loopvar : Symbol) (vars : (Symbol * ExprSrc) list) (body : ExprSrc) =
  macroLetRec [ (loopvar, (ES_Lambda ((PSS_Items (List.map fst vars)), body))) ] (ES_Invoke ((ES_VarRef loopvar) :: List.map snd vars)) ;;
  
let expr1 =
  ES_Invoke
    [ ES_Lambda
        ( (PSS_Items [ S_Interned "x" ]),
          (ES_Invoke
            [ ES_VarRef (S_Interned "+") ;
              ES_VarRef (S_Interned "x") ;
              ES_VarRef (S_Interned "x")
            ]
          )
        ) ;
        ES_Literal (D_Int 3I)
    ]
  ;;

let expr2 =
  macroLet [ (S_Interned "a"), (ES_Literal (D_Int 3I)) ; (S_Interned "b"), (ES_Literal (D_Int 100I)) ]
    (ES_Invoke [ (ES_VarRef (S_Interned "+")) ; (ES_VarRef (S_Interned "a")) ; (ES_VarRef (S_Interned "b")) ]) ;;

let expr3 =
  macroLetLoop (S_Interned "loop") [ (S_Interned "i"), (ES_Literal (D_Int 10I)) ]
    (ES_IfThenElse ((ES_Invoke [ (ES_VarRef (S_Interned "<")) ; (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 0I)) ]),
      (ES_Begin [ (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_Literal (D_String "\n")) ]) ;
                  (ES_Literal (D_Bool true)) ]),
      (ES_Begin [ (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_VarRef (S_Interned "i")) ]) ;
                  (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_Literal (D_String " ")) ]) ;
                  (ES_Invoke [ (ES_VarRef (S_Interned "loop")) ;
                               (ES_Invoke [ (ES_VarRef (S_Interned "-")) ; (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 1I)) ]) ]) ]))) ;;

let expr4 =
  (ES_Catch
    { crsrc_handler =
        (ES_Lambda ((PSS_Items [ S_Interned "exc" ]),
          (ES_Begin [ (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_Literal (D_String "\n\n***** Exception! *****\n\n")) ]) ;
                      (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_VarRef (S_Interned "exc")) ]) ;
                      (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_Literal (D_String "\n")) ]) ]))) ;
      crsrc_body =
        macroLetLoop (S_Interned "loop") [ (S_Interned "i"), (ES_Literal (D_Int 10I)) ]
          (ES_IfThenElse (((ES_Invoke [ (ES_VarRef (S_Interned "<")) ; (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 0I)) ])),
            (ES_Begin [ (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_Literal (D_String "\n")) ]) ;
                        (ES_Literal (D_Bool true)) ]),
            (ES_IfThenElse ((ES_Invoke [ (ES_VarRef (S_Interned "=")) ; (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 3I)) ]),
              (ES_Invoke [ (ES_VarRef (S_Interned "throw")) ; (ES_Literal (D_String "-- value was 3")) ]),
              (ES_Begin [ (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_VarRef (S_Interned "i")) ]) ;
                          (ES_Invoke [ (ES_VarRef (S_Interned "print")) ; (ES_Literal (D_String " ")) ]) ;
                          (ES_Invoke [ (ES_VarRef (S_Interned "loop")) ;
                                       (ES_Invoke [ (ES_VarRef (S_Interned "-")) ; (ES_VarRef (S_Interned "i")) ; (ES_Literal (D_Int 1I)) ]) ]) ]))))) } ) ;;

let builtins = (List.map fst (Map.toList !funtab)) ;;

let envdesc1 = Map.ofList (List.mapi (fun i x -> ((S_Interned x), i)) (List.map fst (Map.toList !funtab))) ;;

let env1 = Array.ofList (List.map (fun x -> ref (D_Func (F_BuiltIn x))) builtins) ;;

let state = ref (RS_Return (K_Final, D_Unspecified)) ;;

let b (expr1 : ExprSrc) =
  state := (RS_Eval ((compile envdesc1 expr1), env1, K_Final)) ; !state ;;

let finished () =
  match !state with
    | (RS_Return (K_Final, v)) -> true
    | (RS_Throw (K_Final, v)) -> true
    | _ -> false

let a () =
  if finished() then
    !state
  else
    state := (run !state) ; !state ;;

let aa () =
  while (not (finished ())) do
    a () |> ignore ;
  !state
