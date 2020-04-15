(******************************************************************************)
(**                Retrieving the free variables from a term                 **)
(******************************************************************************)
let rec fv acc = function
| SVar x -> if (List.memq x acc) then [] else [x]
| SSequence l ->       remove_duplicates (List.flatten (List.map (fv acc) l))
| SCast(_,x) 
| SBolNeg(x) 
| SFracToIntBinOp(_,x) 
| SFracMonOp(_,x) 
| SLstCast(x) 
| SLstMonOp(_,x) 
| SFRemove(_,x)   
| SLstHead(x) ->       remove_duplicates(fv acc x)
| SBolBinOp(_,x,y) 
| SStrContains(x,y)
| SLstContains(x,y) 
| SFFuncContains(x,y) 
| SBinCompBool(_,x,y)
| SIntBinOp(_,x,y) 
| SFltBinOp(_,x,y) 
| SStrBinOp(_,x,y) 
| SStrIntBinOp(_,x,y) 
| SStrSplit(x,y) 
| SLstBinOp(_,x,y)
| SLstRemAt(x,y) 
| SLstRemVal(x,y) 
| SLstMap(x,y) 
| SLstFilter(x,y) 
| SFuncComp(x,y) 
| SFExtend(_,x,y) 
| SFFuncComp(x,y) 
| SLstAt(x,y) 
| SFunApply(x,y) 
| SFFunApply(x,y) ->   remove_duplicates ((fv acc x)@(fv acc y))
| SStrReplace(x,y,z) 
| SStrSet(x,y,z) 
| SLstSet(x,y,z) 
| SIfte(x,y,z)
| SLstLFold(x,y,z) ->  remove_duplicates ((fv acc x)@(fv acc y)@(fv acc z))
| SFunc(x,y) ->        fv (x::acc) y
| SFFunc(ls) ->        remove_duplicates (List.flatten (List.map (fun (x,y) -> (fv acc y)) ls))
| SLetIn(x,y,z) ->     remove_duplicates((fv acc y)@(fv (x::acc) z))
| _ -> []


(******************************************************************************)
(**      Substitutes the variable original in currnet with replacement       **)
(******************************************************************************)
let rec subst orig repl = function
| SVar x as t          -> if (x == orig) then repl else t
| SSequence l          -> SSequence (List.map (subst orig repl) l)
| SCast(t,x)           -> SCast(t, subst orig repl x)
| SBolNeg(x)           -> SBolNeg(subst orig repl x)
| SFracToIntBinOp(t,x) -> SFracToIntBinOp(t, subst orig repl x)
| SFracMonOp(t,x)      -> SFracMonOp(t, subst orig repl x)
| SLstCast(x)          -> SLstCast(subst orig repl x)
| SLstMonOp(t,x)       -> SLstMonOp(t, subst orig repl x) 
| SFRemove(t,x)        -> SFRemove(t, subst orig repl x) 
| SLstHead(x)          -> SLstHead(subst orig repl x)
| SStrContains(x,y)    -> SStrContains(subst orig repl x, subst orig repl y)
| SLstContains(x,y)    -> SLstContains(subst orig repl x, subst orig repl y)
| SFFuncContains(x,y)  -> SFFuncContains(subst orig repl x, subst orig repl y)
| SStrSplit(x,y)       -> SStrSplit(subst orig repl x, subst orig repl y)
| SFFuncComp(x,y)      -> SFFuncComp(subst orig repl x, subst orig repl y)
| SLstAt(x,y)          -> SLstAt(subst orig repl x, subst orig repl y)
| SFunApply(x,y)       -> SFunApply(subst orig repl x, subst orig repl y)
| SFFunApply(x,y)      -> SFFunApply(subst orig repl x, subst orig repl y)
| SLstRemAt(x,y)       -> SLstRemAt(subst orig repl x, subst orig repl y)
| SLstRemVal(x,y)      -> SLstRemVal(subst orig repl x, subst orig repl y)
| SLstMap(x,y)         -> SLstMap(subst orig repl x, subst orig repl y)
| SLstFilter(x,y)      -> SLstFilter(subst orig repl x, subst orig repl y)
| SFuncComp(x,y)       -> SFuncComp(subst orig repl x, subst orig repl y)
| SLstBinOp(t,x,y)     -> SLstBinOp(t, subst orig repl x, subst orig repl y)
| SBolBinOp(t,x,y)     -> SBolBinOp(t, subst orig repl x, subst orig repl y)
| SBinCompBool(t,x,y)  -> SBinCompBool(t, subst orig repl x, subst orig repl y)
| SIntBinOp(t,x,y)     -> SIntBinOp(t, subst orig repl x, subst orig repl y)
| SFltBinOp(t,x,y)     -> SFltBinOp(t, subst orig repl x, subst orig repl y)
| SStrBinOp(t,x,y)     -> SStrBinOp(t, subst orig repl x, subst orig repl y)
| SStrIntBinOp(t,x,y)  -> SStrIntBinOp(t, subst orig repl x, subst orig repl y)
| SFExtend(t,x,y)      -> SFExtend(t, subst orig repl x, subst orig repl y)
| SStrReplace(x,y,z)   -> SStrReplace(subst orig repl x, subst orig repl y, subst orig repl z)
| SStrSet(x,y,z)       -> SStrSet(subst orig repl x, subst orig repl y, subst orig repl z)
| SLstSet(x,y,z)       -> SLstSet(subst orig repl x, subst orig repl y, subst orig repl z)
| SIfte(x,y,z)         -> SIfte(subst orig repl x, subst orig repl y, subst orig repl z)
| SLstLFold(x,y,z)     -> SLstLFold(subst orig repl x, subst orig repl y, subst orig repl z)
| SFunc(x,y) as t      -> if (x==orig) then t else SFunc(x,subst orig repl y)
| SFFunc(ls)           -> SFFunc(List.map (fun (x,y) -> (x, subst orig repl y)) ls)
| SLetIn(x,y,z)        -> SLetIn(x,  subst orig repl y, if (x==orig) then z else (subst orig repl z))
| _ as t -> t


type env_variable = string list
type env_lets = (string * term2) list

(** - If the variable is binded by a function, returns the variable itself
    - If the variable is associated to a let definition, then it returns the associated value
    - Otherwise, it is a free variable: throw an exception (as it is undefined)
*)
let resolve_variable_if_possible (ev: env_variable) (el: env_lets) x = 
match (List.assoc_opt x el) with
| Some t -> t
| None -> if (List.memq x ev) then (SVar x) else raise(UnbondedVariable x)


(** This step optimizes the code, by rewriting it by expanding without necessairly "running" the code *)
let rec simplify_expression (ev: env_variable ref) (el: env_lets ref) = function
           | SFuncComp(f,g)             -> simplify_expression ev el (SFunc("x",SFunApply(f, SFunApply(g, SVar "x"))))
           | SLst(ls)                   -> SLst (List.map (simplify_expression ev el) ls)
           | SVar(x)                    -> resolve_variable_if_possible !ev !el x
           | SLetIn(x,y,z)              -> begin 
                                                 el := (x,y)::!el; 
                                                 simplify_expression ev el z
                                           end
           | SFunc(x,s)                 -> begin
                                                  ev := x::!ev;
                                                  SFunc(x,simplify_expression ev el s)
                                           end
           
           | SBolBinOp(BoolAnd,x,y) as t-> (match (simplify_expression ev el x,simplify_expression ev el y) with
                                            | (SBol true, x) 
                                            | (x, SBol true) -> x
                                            | (SBol false, x)
                                            | (x, SBol false)-> SBol false
                                            | _ -> t
                                           )
                                           
           | SBolBinOp(BoolOr,x,y)  as t-> (match (simplify_expression ev el x,simplify_expression ev el y) with
                                            | (SBol true, x) 
                                            | (x, SBol true) -> SBol true
                                            | (SBol false, x)
                                            | (x, SBol false)-> x
                                            | _ -> t
                                           )
                                           
           | SBolNeg(x) as t ->            (match (simplify_expression ev el x) with
                                            | SBol(b) -> SBol (not b)
                                            | _ -> t
                                           )
                                           
           | SCast(TInt,u) as t ->         (match (simplify_expression ev el u) with 
                                            | SFlt x     -> SInt (int_of_float x) 
                                            | SBol true  -> SInt 1
                                            | SBol false -> SInt 0
                                            | SStr t     -> SInt (String.length t)
                                            | SFunc(x,y) -> raise (UnexpectedCast "Function to Int")
                                            | SFFunc l   -> SInt (List.length l)
                                            | SLst l     -> SInt (List.length l)
                                            | SInt _ as u-> u
                                            | _ -> t)
                                           
                                          (* 
	 SBol of bool
           | SInt of int 
           | SFlt of float
           | SStr of string
           | SLst of term2 list 
           | SVar of string
           | SSequence of term2 list
           | SCast of basic_types * term2
           | SBolBinOp of bol_bin_op * term2 * term2
           | SBolNeg of term2
           | SStrContains of term2 * term2
           | SLstContains of term2 * term2
           | SFFuncContains of term2 * term2
           | SBinCompBool of bin_comp_to_bool * term2 * term2
           | SIntBinOp of int_bin_op * term2 * term2
           | SFracToIntBinOp of flt_to_int_mon_op * term2
           | SFltBinOp of flt_bin_op * term2 * term2
           | SFracMonOp of flt_mon_op * term2
           | SStrBinOp of str_bin_op * term2 * term2
           | SStrReplace of term2 * term2 * term2
           | SStrIntBinOp of str_int_bin_op * term2 * term2
           | SStrSet of term2 * term2 * term2
           | SLstCast of term2
           | SStrSplit of term2 * term2
           | SLstBinOp of list_bin_op * term2 * term2
           | SLstMonOp of list_mon_op * term2
           | SLstRemAt of term2 * term2
           | SLstRemVal of term2 * term2
           | SLstSet of term2 * term2 * term2
           | SLstMap of term2 * term2
           | SLstFilter of term2 * term2
           | SFunc of string * term2
           | SFuncComp of term2 * term2
           | SFFunc of (term2 * term2) list
           | SFExtend of term2 * term2 * term2
           | SFRemove of term2 * term2
           | SFFuncComp of term2 * term2    
           | SLstHead of term2
           | SLstLFold of term2 * term2 * term2
           | SLstAt of term2 * term2
           | SLetIn of string * term2 * term2
           | SFunApply of term2 * term2
           | SFFunApply of term2 * term2  
           | SIfte of term2* term2*term2*)                                        
                               
                                           
                                            
           | SCast(TLst,u) as t ->         (match (simplify_expression ev el u) with
                                            | SSequence v     -> SLst v
                                            | SLst _ as v     -> v
                                            | SStr l          -> SLst (List.init (String.length l) (fun x -> SStr (String.make 1 (String.get l x))))
                                            | SStrSplit _ as v -> v
                                            | SLstBinOp _ as v -> v
                                            | SLstMonOp _ as v -> v
                                            | SLstRemAt _ as v -> v
                                            | _ as u -> SLst [u] (* TODO: some other cases *)
                                            )
                                           
           | SCast(TBol,u) as t ->         (match (simplify_expression ev el u) with 
                                            | SFlt x     -> SBol ((Float.abs x) > Float.epsilon)
                                            | SBol _ as u-> u
                                            | SStr t     -> SBol ((String.length t) != 0)
                                            | SFunc(x,y) -> raise (UnexpectedCast "Function to Bool")
                                            | SFFunc l   -> SBol ((List.length l) != 0)
                                            | SLst l     -> SBol ((List.length l) != 0)
                                            | SInt l     -> SBol (l != 0)
                                            | _ -> t)
                                            
           | SCast(TFlt,u) as t ->         (match (simplify_expression ev el u) with 
                                            | SInt x     -> SFlt (float_of_int x)
                                            | SBol true  -> SFlt 1.0
                                            | SBol false -> SFlt 0.0
                                            | SStr t     -> SFlt (float_of_int (String.length t))
                                            | SFunc(x,y) -> raise (UnexpectedCast "Function to Float")
                                            | SFFunc l   -> SFlt (float_of_int (List.length l))
                                            | SLst l     -> SFlt (float_of_int (List.length l))
                                            | SFlt _ as u-> u
                                            | _ -> t)
                                            
           | SCast(TStr,u) as t ->         (match (simplify_expression ev el u) with 
                                            | SInt x     -> SStr (string_of_int x)
                                            | SBol b     -> SStr (if b then "true" else "false")
                                            | SStr _ as u-> u
                                            | SFunc(x,y) -> raise (UnexpectedCast "Missing Serialization") (* TODO: Serialization *)
                                            | SFFunc l   -> raise (UnexpectedCast "Missing Serialization") (* TODO: Serialization *)
                                            | SLst l     -> raise (UnexpectedCast "Missing Serialization") (* TODO: Serialization *)
                                            | SFlt l     -> SStr (string_of_float l)
                                            | _ -> t)
           
           | SIntBinOp(IntSum,x,y) as t -> (match (simplify_expression ev el x,simplify_expression ev el y) with
                                            | (SInt 0, j)
                                            | (j, SInt 0)         -> j
                                            | (SInt j, SInt (i)) -> if (i == -j) then SInt 0 else (if (i == j) then simplify_expression ev el (SIntBinOp(IntProd, SInt 2, SInt j)) else t)
                                            | (j, k)              -> if (j == k) then simplify_expression ev el (SIntBinOp(IntProd, SInt 2, j)) else t
                                           )
           | SIntBinOp(IntSub,x,y) as t -> (match (simplify_expression ev el x,simplify_expression ev el y) with
                                            | (SInt 0, SInt j)    -> SInt (-j)
                                            | (SInt 0, (SIntBinOp(IntSub,SInt 0,z))) -> simplify_expression ev el z
                                            | (j, SInt 0)         -> j
                                            | (SInt j, SInt i) -> if (i == -j) then simplify_expression ev el (SIntBinOp(IntProd, SInt 2, SInt j)) else (if (i == j) then (SInt 0) else t)
                                            | (j, k)              -> if (j == k) then SInt 0 else t
                                           )
           | SIntBinOp(IntProd,x,y) as t-> (match (simplify_expression ev el x,simplify_expression ev el y) with
                                            | (SInt 0, j)
                                            | (j, SInt 0)         -> SInt 0
                                            | (SInt 1, j)
                                            | (j, SInt 1)         -> j
                                            | (SInt j, SInt (i))  -> if (i == -j) then simplify_expression ev el (SFltBinOp(FltSub, SInt 0, (SFltBinOp(FltExp, SCast(TFlt,SInt j), SFlt 2.)))) else (if (i==j) then (simplify_expression ev el (SFltBinOp(FltExp, SCast(TFlt,SInt j), SFlt 2.))) else t)
                                            | (j,k)               -> if (j == k) then simplify_expression ev el (SFltBinOp(FltExp, SCast(TFlt,j), SFlt 2.)) else t
                                           )
           | SIntBinOp(IndDiv,x,y) as t-> (match (simplify_expression ev el x,simplify_expression ev el y) with
                                            | (SInt 0, j)         -> SInt 0
                                            | (j, SInt 0)         -> raise(DivisionByZero)
                                            | (j, SInt 1)         -> j
                                            | (SInt j, SInt (i)) -> if (i == -j) then SInt (-1) else (if (i ==j) then SInt 1 else t)
                                            | (j,k)               -> if (j ==k) then SInt 1 else t
                                           )
           (*| SFracToIntBinOp of flt_to_int_mon_op * term2
           | SFltBinOp of flt_bin_op * term2 * term2
           | SFracMonOp of flt_mon_op * term2
           | SStrBinOp of str_bin_op * term2 * term2
           | SStrReplace of term2 * term2 * term2
           | SStrIntBinOp of str_int_bin_op * term2 * term2
           | SStrSet of term2 * term2 * term2
           | SLstCast of term2
           | SStrSplit of term2 * term2
           | SLstBinOp of list_bin_op * term2 * term2
           | SLstMonOp of list_mon_op * term2
           | SLstRemAt of term2 * term2
           | SLstRemVal of term2 * term2
           | SLstSet of term2 * term2 * term2
           | SLstMap of term2 * term2
           | SLstFilter of term2 * term2
           | SFExtend of term2 * term2 * term2
           | SFRemove of term2 * term2
           | SFFuncComp of term2 * term2    
           | SLstHead of term2
           | SLstLFold of term2 * term2 * term2
           | SLstAt of term2 * term2
           | SFunApply of term2 * term2
           | SFFunApply of term2 * term2
           | SSequence of term2 list
           | SCast of basic_types * term2
           | SStrContains of term2 * term2
           | SLstContains of term2 * term2
           | SFFuncContains of term2 * term2
           | SBinCompBool of bin_comp_to_bool * term2 * term2*)
           | _ as t -> t 


(*
let get_environment_type (g:environment) x = List.fold_left (fun z -> fun  (s,t,b) -> if (s == x) then b else z) TObj g 
let get_environment_term (g:environment) x = List.fold_left (fun z -> fun  (s,t,b) -> if (s == x) then t else z) (SBol false) g 
let get_gamma_type (g:gamma) x = List.fold_left (fun z -> fun  (s,b) -> if (s == x) then b else z) TObj g 
*)


