open Basics
open Term
open Term2
open TermSemantics

exception UnexpectedCast of string
exception UnbondedVariable of string

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
| SVar x as t          -> if (x = orig) then repl else t
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
| SFunc(x,y) as t      -> if (x=orig) then t else SFunc(x,subst orig repl y)
| SFFunc(ls)           -> SFFunc(List.map (fun (x,y) -> (x, subst orig repl y)) ls)
| SLetIn(x,y,z)        -> SLetIn(x,  subst orig repl y, if (x=orig) then z else (subst orig repl z))
| _ as t -> t

let subst_var orig repl = subst orig (SVar repl)

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
           (* *************************************************************** *)
           (*                          SSequence                              *)
           (* *************************************************************** *)
           | SSequence []               -> SInt 0
           | SSequence (hd::[])         -> let ev2 = ref !ev in (*Copying the elements that are within the block, so that it could be popped any time at the end of it *)
                                           let el2 = ref !el in
                                                 simplify_expression ev2 el2 hd
           | SSequence (hd::tl)         -> let ev2 = ref !ev in (*Copying the elements that are within the block, so that it could be popped any time at the end of it *)
                                           let el2 = ref !el in
                                           begin
                                                 simplify_expression ev2 el2 hd;
                                                 simplify_expression ev2 el2 (SSequence tl)
                                           end
           (* *************************************************************** *)
           (* *************************************************************** *)



           (* *************************************************************** *)
           (*                            SCast                                *)
           (* *************************************************************** *)
           | SCast(TBol,u) ->         (let xx = (simplify_expression ev el u) in match xx with
                                            | SBol         _
                                            | SBolBinOp    _
                                            | SBolNeg      _
                                            | SStrContains _
                                            | SLstContains _
                                            | SBinCompBool _ as u -> u
                                            | SFlt x              -> SBol ((Float.abs x) > Float.epsilon)
                                            | SStr t              -> SBol ((String.length t) != 0)
                                            | SFunc(x,y)          -> raise (UnexpectedCast "Function to Bool")
                                            | SFFunc l            -> SBol ((List.length l) != 0)
                                            | SLst l              -> SBol ((List.length l) != 0)
                                            | SInt l              -> SBol (l != 0)
                                            | _ -> SCast(TBol,xx))

           | SCast(TInt,u) ->         (let xx = (simplify_expression ev el u) in match xx with
                                            | SIntBinOp       _
                                            | SFracToIntBinOp _
                                            | SInt            _ as u -> u
                                            | SFlt x                 -> SInt (int_of_float x)
                                            | SBol true              -> SInt 1
                                            | SBol false             -> SInt 0
                                            | SStr t                 -> SInt (String.length t)
                                            | SFunc(x,y)             -> raise (UnexpectedCast "Function to Int")
                                            | SFFunc l               -> SInt (List.length l)
                                            | SLst l                 -> SInt (List.length l)
                                            | _ -> SCast(TInt,xx))

           | SCast(TFlt,u)->         (let xx = (simplify_expression ev el u) in match xx with
                                            | SFltBinOp  _
                                            | SFracMonOp _
                                            | SFlt       _ as u -> u
                                            | SInt x            -> SFlt (float_of_int x)
                                            | SBol true         -> SFlt 1.0
                                            | SBol false        -> SFlt 0.0
                                            | SStr t            -> SFlt (float_of_int (String.length t))
                                            | SFunc(x,y)        -> raise (UnexpectedCast "Function to Float")
                                            | SFFunc l          -> SFlt (float_of_int (List.length l))
                                            | SLst l            -> SFlt (float_of_int (List.length l))
                                            | _ -> SCast(TFlt,xx))

           | SCast(TStr,u)  ->         (let xx = (simplify_expression ev el u) in match xx with
                                            | SStrBinOp    _
                                            | SStrReplace  _
                                            | SStr         _
                                            | SStrSet      _
                                            | SStrIntBinOp _ as u -> u
                                            | SInt x              -> SStr (string_of_int x)
                                            | SBol b              -> SStr (if b then "true" else "false")
                                            | SFunc(x,y)          -> raise (UnexpectedCast "Missing Serialization") (* TODO: Serialization *)
                                            | SFFunc l            -> raise (UnexpectedCast "Missing Serialization") (* TODO: Serialization *)
                                            | SLst l              -> raise (UnexpectedCast "Missing Serialization") (* TODO: Serialization *)
                                            | SFlt l              -> SStr (string_of_float l)
                                            | _ -> SCast(TStr,xx))

           | SCast(TLst,u)      ->         (match (simplify_expression ev el u) with
                                            | SLst          _
                                            | SStrSplit     _
                                            | SLstBinOp     _
                                            | SLstMonOp     _
                                            | SLstRemAt     _
                                            | SLstRemVal    _
                                            | SLstSet       _
                                            | SLstMap       _
                                            | SLstFilter    _ as v -> v
                                            | SFExtend(x,y,l)      -> let ll = SLst [simplify_expression ev el x;simplify_expression ev el y]         in
                                                                      let tt = (SLstBinOp(ListAppend, ll, simplify_expression ev el (SCast(TLst,u)))) in
                                                                                simplify_expression ev el tt

                                            | SFRemove(x,l)        -> let ll = simplify_expression ev el l                                                      in
                                                                      let hd = SLst [simplify_expression ev el x; simplify_expression ev el (SFFunApply(l, x))] in
                                                                      let tt = (SLstRemVal(hd, ll))                                                             in
                                                                                simplify_expression ev el tt

                                            | SFFunc l             -> SLst (List.map (fun (x,y) -> SLst [simplify_expression ev el x;simplify_expression ev el y]) l)
                                            | SSequence v          -> SLst v
                                            | SStr l               -> SLst (List.init (String.length l) (fun x -> SStr (String.make 1 (String.get l x))))
                                            | _ as u               -> SLst [u]
                                            )

           | SCast(TFnc,u)       ->         (match (simplify_expression ev el u) with
                                             | SFunc     _
                                             | SFRemove   _ as v -> v
                                             | SFFuncComp(f,g)   -> simplify_expression ev el (SFunc("x",SFunApply(f, SFunApply(g, SVar "x"))))
                                             | SLst       l
                                             | SSequence  l      -> SFFunc (enumerating l (fun x -> SInt x) 0)
                                             | _                 -> simplify_expression ev el (SCast(TFFnc,SCast(TLst,u)))
                                            )

           | SCast(TFFnc,u)      ->         (match (simplify_expression ev el u) with
                                             | SFFunc     _
                                             | SFExtend   _
                                             | SFRemove   _
                                             | SFFuncComp _ as v -> v
                                             | SLst       l
                                             | SSequence  l      -> SFFunc (enumerating l (fun x -> SInt x) 0)
                                             | _                 -> simplify_expression ev el (SCast(TFFnc,SCast(TLst,u)))
                                            )
           (* *************************************************************** *)
           (* *************************************************************** *)




           (* *************************************************************** *)
           (*                          SBolBinOp                              *)
           (* *************************************************************** *)
           | SBolBinOp(BoolAnd,x,y) -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SBolBinOp(BoolOr,xx,yy) in
                                            match (xx,yy) with
                                            | (SBol true, x)
                                            | (x, SBol true) -> x
                                            | (SBol false, x)
                                            | (x, SBol false)-> SBol false
                                            | _ -> tt
                                           )

           | SBolBinOp(BoolOr,x,y) -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SBolBinOp(BoolOr,xx,yy) in
                                            match (xx,yy) with
                                            | (SBol true, x)
                                            | (x, SBol true) -> SBol true
                                            | (SBol false, x)
                                            | (x, SBol false)-> x
                                            | _ -> tt
                                           )
           (* *************************************************************** *)
           (* *************************************************************** *)



           (* *************************************************************** *)
           (*                           SBolNeg                               *)
           (* *************************************************************** *)
           | SBolNeg(x) ->            (let xx = (simplify_expression ev el x) in match xx with
                                            | SBol(b) -> SBol (not b)
                                            | SBolBinOp(BoolAnd,a,b) -> simplify_expression ev el (SBolBinOp(BoolOr,SBolNeg(a),SBolNeg(b)))
                                            | SBolBinOp(BoolOr,a,b) -> simplify_expression ev el (SBolBinOp(BoolAnd,SBolNeg(a),SBolNeg(b)))
                                            | _ -> SBolNeg(xx)
                                           )
           (* *************************************************************** *)
           (* *************************************************************** *)




           (* *************************************************************** *)
           (*                        SStrContains                             *)
           (* *************************************************************** *)
           | SStrContains(str,elem) ->(let xx = simplify_expression ev el str in
                                            let yy = simplify_expression ev el elem in
                                            let tt = SLstContains(xx,yy) in
                                      match (xx,yy) with
                                            | (SStr x, SStr y) -> term_sem_to2 (sem_contains (TSStr x) (TSStr y))
                                            | _ -> tt
                                           )
           (* *************************************************************** *)
           (* *************************************************************** *)




           (* *************************************************************** *)
           (*                        SLstContains                             *)
           (* *************************************************************** *)
           | SLstContains(str,elem) ->(let xx = simplify_expression ev el str in
                                            let yy = simplify_expression ev el elem in
                                            let tt = SLstContains(xx,yy) in
                                      match (xx,yy) with
                                            | (SLst x, y) -> SBol (List.memq y x)
                                            | _ -> tt
                                           )
           (* *************************************************************** *)
           (* *************************************************************** *)



           (* *************************************************************** *)
           (*                        SFFuncContains                           *)
           (* *************************************************************** *)
           | SFFuncContains(ff,c) -> (let xx = simplify_expression ev el ff in
                                            let yy = simplify_expression ev el c in
                                            let tt = SFFuncContains(xx,yy) in
                                      match (xx,yy) with
                                            | (SFFuncComp(f,g), k) -> simplify_expression ev el (SBolBinOp(BoolOr,SFFuncContains(f,k),SFFuncContains(g,k)))
                                            | (SFFunc(l), k)       -> SBol (List.exists (fun (x,_) -> x=k) l)
                                            | (SFExtend(x,y,z),k)  -> simplify_expression ev el (SBolBinOp(BoolOr,SBol (x = k),SFFuncContains(z,k)))
                                            | (SFRemove(x,z),k)    -> if (x=k) then (SBol false) else simplify_expression ev el (SFFuncContains(z,k))
                                            | _ -> tt
                                           )
           (* *************************************************************** *)
           (* *************************************************************** *)




           (* *************************************************************** *)
           (*                        SBinCompBool                           *)
           (* *************************************************************** *)
           | SBinCompBool(Eq,x,y)      -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SBinCompBool(LEq,xx,yy) in
                                             match (xx,yy) with
                                            (* 1) Comparing basic types between each other *)
                                            | (SBol a, SBol b)           -> SBol (a=b)
                                            | (SInt a, SInt b)           -> SBol (a=b)
                                            | (SFlt a, SFlt b)           -> SBol (Float.abs(a-.b) <= Float.epsilon *. (Float.max (Float.max a b) 1.0))
                                            | (SStr a, SStr b)           -> SBol (a=b)
                                            | (SLst a, SLst b)           -> SBol (a=b)
                                            | (SFFunc a, SFFunc b)       -> SBol ((List.sort compare a)=(List.sort compare b))
                                            | (SFunc(x,y), SFunc(z,t))   -> let tt2 = subst_var x z t in simplify_expression ev el (SBinCompBool(Eq,y,tt2))
                                            | (SBol _, SInt _)
                                            | (SBol _, SFlt _)
                                            | (SBol _, SStr _)
                                            | (SBol _, SLst _)
                                            | (SBol _, SFunc  _)
                                            | (SBol _, SFFunc _)
                                            | (SInt _, SBol _)
                                            | (SInt _, SFlt _)
                                            | (SInt _, SStr _)
                                            | (SInt _, SLst _)
                                            | (SInt _, SFunc  _)
                                            | (SInt _, SFFunc _)
                                            | (SFlt _, SInt _)
                                            | (SFlt _, SBol _)
                                            | (SFlt _, SStr _)
                                            | (SFlt _, SLst _)
                                            | (SFlt _, SFunc  _)
                                            | (SFlt _, SFFunc _)
                                            | (SStr _, SInt _)
                                            | (SStr _, SBol _)
                                            | (SStr _, SFlt _)
                                            | (SStr _, SLst _)
                                            | (SStr _, SFunc  _)
                                            | (SStr _, SFFunc _)
                                            | (SLst _, SInt _)
                                            | (SLst _, SBol _)
                                            | (SLst _, SFlt _)
                                            | (SLst _, SStr _)
                                            | (SLst _, SFunc  _)
                                            | (SLst _, SFFunc _)
                                            | (SFFunc _, SInt _)
                                            | (SFFunc _, SBol _)
                                            | (SFFunc _, SFlt _)
                                            | (SFFunc _, SStr _)
                                            | (SFFunc _, SFunc  _)
                                            | (SFFunc _, SLst _)
                                            | (SFunc _, SInt _)
                                            | (SFunc _, SBol _)
                                            | (SFunc _, SFlt _)
                                            | (SFunc _, SStr _)
                                            | (SFunc _, SFFunc  _)
                                            | (SFunc _, SLst _)          -> SBol false
                                            | (k,j)             when k=j -> SBol true

                                            (* 2) Algebraic equivalences: commutativity *)
                                            | (SIntBinOp(IntSum,x,y),SIntBinOp(IntSum,z,t))                     when (x=t && y=z) -> SBol true
                                            | (SIntBinOp(IntProd,x,y),SIntBinOp(IntProd,z,t))                   when (x=t && y=z) -> SBol true
                                            | (SFltBinOp(FltSum,x,y),SFltBinOp(FltSum,z,t))                     when (x=t && y=z) -> SBol true
                                            | (SFltBinOp(FltProd,x,y),SFltBinOp(FltProd,z,t))                   when (x=t && y=z) -> SBol true
                                            | _ -> tt
             )
           | SBinCompBool(LEq,x,y)       -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SBinCompBool(LEq,xx,yy) in
                                             match (xx,yy) with
               (* 1) Comparing basic types between each other *)
               | (SBol a, SBol b)           -> SBol (not(a) || b)
               | (SInt a, SInt b)           -> SBol (a<=b)
               | (SFlt a, SFlt b)           -> SBol (a<=b)
               | (SStr a, SStr b)           -> SBol (supstring_of b a)
               | (SLst a, SLst b)           -> SBol (suplist_of b a)
               | (SFFunc a, SFFunc b)       -> let al =(List.sort compare a) in
                                               let bl = (List.sort compare b) in
                                               SBol (suplist_of bl al)
               | (SFunc(x,y), SFunc(z,t))   -> let tt2 = subst_var x z t in simplify_expression ev el (SBinCompBool(LEq,y,subst_var x z tt2))
                   (* | (SBol _, SInt _)
               | (SBol _, SFlt _)
               | (SBol _, SStr _)
               | (SBol _, SLst _)
               | (SBol _, SFunc  _)
               | (SBol _, SFFunc _)
               | (SInt _, SBol _)
               | (SInt _, SFlt _)
               | (SInt _, SStr _)
               | (SInt _, SLst _)
               | (SInt _, SFunc  _)
               | (SInt _, SFFunc _)
               | (SFlt _, SInt _)
               | (SFlt _, SBol _)
               | (SFlt _, SStr _)
               | (SFlt _, SLst _)
               | (SFlt _, SFunc  _)
               | (SFlt _, SFFunc _)
               | (SStr _, SInt _)
               | (SStr _, SBol _)
               | (SStr _, SFlt _)
               | (SStr _, SLst _)
               | (SStr _, SFunc  _)
               | (SStr _, SFFunc _)
               | (SLst _, SInt _)
               | (SLst _, SBol _)
               | (SLst _, SFlt _)
               | (SLst _, SStr _)
               | (SLst _, SFunc  _)
               | (SLst _, SFFunc _)
               | (SFFunc _, SInt _)
               | (SFFunc _, SBol _)
               | (SFFunc _, SFlt _)
               | (SFFunc _, SStr _)
               | (SFFunc _, SFunc  _)
               | (SFFunc _, SLst _)
               | (SFunc _, SInt _)
               | (SFunc _, SBol _)
               | (SFunc _, SFlt _)
               | (SFunc _, SStr _)
               | (SFunc _, SFFunc  _)
               | (SFunc _, SLst _)          -> SBol false
               | (k,j)             when k=j -> SBol true

               (* 2) Algebraic equivalences: commutativity *)
               | (SIntBinOp(IntSum,x,y),SIntBinOp(IntSum,z,t))                     when (x=t && y=z) -> SBol true
               | (SIntBinOp(IntProd,x,y),SIntBinOp(IntProd,z,t))                   when (x=t && y=z) -> SBol true
               | (SFltBinOp(FltSum,x,y),SFltBinOp(FltSum,z,t))                     when (x=t && y=z) -> SBol true
               | (SFltBinOp(FltProd,x,y),SFltBinOp(FltProd,z,t))                   when (x=t && y=z) -> SBol true*)
               | _ -> tt
             )
           | SBinCompBool(Lt,x,y) -> simplify_expression ev el (SBolBinOp(BoolAnd,SBinCompBool(LEq,x,y),SBolNeg(SBinCompBool(Eq,x,y))))
           | SBinCompBool(GEq,x,y) -> simplify_expression ev el (SBolNeg(SBinCompBool(Lt,x,y)))
           | SBinCompBool(Gt,x,y) -> simplify_expression ev el (SBolBinOp(BoolAnd,SBinCompBool(GEq,x,y),SBolNeg(SBinCompBool(Eq,x,y))))
                                             (* At the moment, I'm ignoring the other boolean operations: this is not the interpretation, but the reduction. In fact *)
           (* *************************************************************** *)
           (* *************************************************************** *)


           | SFuncComp(f,g)             -> simplify_expression ev el (SFunc("x",SFunApply(f, SFunApply(g, SVar "x"))))
           | SLst(ls)                   ->                          SLst (List.map (simplify_expression ev el) ls)
           | SVar(x)                    ->                          resolve_variable_if_possible !ev !el x
           | SLetIn(x,y,z)              -> begin
                                                 el := (x,y)::!el;
                                                 simplify_expression ev el z
                                           end
           | SFunc(x,s)                 -> begin
                                                  ev := x::!ev;
                                                  SFunc(x,simplify_expression ev el s)
                                           end

           (* *************************************************************** *)
           (*                           SIntBinOp                             *)
           (* *************************************************************** *)

           (* 1) Algebraic Equivalences: distributivity *)
           | SIntBinOp(IntProd,z,SIntBinOp(IntSum,x,y)) -> simplify_expression ev el (SIntBinOp(IntProd,SIntBinOp(IntSum,x,y),z))
           | SIntBinOp(IntProd,SIntBinOp(IntSum,x,y),z) -> simplify_expression ev el (SIntBinOp(IntSum,SIntBinOp(IntProd,z,x),SIntBinOp(IntProd,z,y)))
           | SIntBinOp(IntProd,z,SIntBinOp(IntSub,x,y)) -> simplify_expression ev el (SIntBinOp(IntProd,SIntBinOp(IntSub,x,y),z))
           | SIntBinOp(IntProd,SIntBinOp(IntSub,x,y),z) -> simplify_expression ev el (SIntBinOp(IntSub,SIntBinOp(IntProd,z,x),SIntBinOp(IntProd,z,y)))

           (* 2) Algebraic Equivalences: associativity *)
           | SIntBinOp(IntSum,SIntBinOp(IntSum,y,z),x)  -> simplify_expression ev el (SIntBinOp(IntSum,x,SIntBinOp(IntSum,y,z)))
           | SIntBinOp(IntProd,SIntBinOp(IntProd,y,z),x)  -> simplify_expression ev el (SIntBinOp(IntProd,x,SIntBinOp(IntProd,y,z)))


           (* 3) Operation related equivalences *)
           | SIntBinOp(IntSum,x,y)  -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SIntBinOp(IntSum,xx,yy) in
                                            match (xx,yy) with
                                            | (SInt 0, j)
                                            | (j, SInt 0)         -> j
                                            | (SInt j, SInt (i))  -> if (i = -j) then
                                                                       SInt 0
                                                                     else if (i = j) then
                                                                       simplify_expression ev el (SIntBinOp(IntProd, SInt 2, SInt j))
                                                                     else
                                                                       tt
                                            | (j, k)              -> if (j = k) then
                                                                        simplify_expression ev el (SIntBinOp(IntProd, SInt 2, j))
                                                                     else
                                                                        tt
                                           )
           | SIntBinOp(IntSub,x,y)-> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SIntBinOp(IntSub,xx,yy) in
                                            match (xx,yy) with
                                            | (SInt 0, SInt j)                       -> SInt (-j)
                                            | (SInt 0, (SIntBinOp(IntSub,SInt 0,z))) -> simplify_expression ev el z
                                            | (j, SInt 0)                            -> j
                                            | (SInt j, SInt i)                       -> if (i = -j) then
                                                                                            simplify_expression ev el (SIntBinOp(IntProd, SInt 2, SInt j))
                                                                                        else if (i = j) then
                                                                                            SInt 0
                                                                                        else
                                                                                            tt
                                            | (j, k)                                 -> if (j = k) then SInt 0 else tt
                                           )
           | SIntBinOp(IntProd,x,y)-> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SIntBinOp(IntProd,xx,yy) in
                                            match (xx,yy) with
                                            | (SInt 0, j)
                                            | (j, SInt 0)         -> SInt 0
                                            | (SInt 1, j)
                                            | (j, SInt 1)         -> j
                                            | (SInt j, SInt (i))  -> if (i = -j) then
                                                                        simplify_expression ev el (SFltBinOp(FltSub, SInt 0, (SFltBinOp(FltExp, SCast(TFlt,SInt j), SFlt 2.))))
                                                                     else if (i=j) then
                                                                        simplify_expression ev el (SFltBinOp(FltExp, SCast(TFlt,SInt j), SFlt 2.))
                                                                     else
                                                                        tt
                                            | (j,k)               -> if (j = k) then
                                                                        simplify_expression ev el (SFltBinOp(FltExp, SCast(TFlt,j), SFlt 2.))
                                                                     else
                                                                        tt
                                           )
           | SIntBinOp(IndDiv,x,y) -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SIntBinOp(IndDiv,xx,yy) in
                                            match (xx,yy) with
                                            | (SInt 0, j)         -> SInt 0
                                            | (j, SInt 0)         -> raise(DivisionByZero)
                                            | (j, SInt 1)         -> j
                                            | (SInt j, SInt (i)) -> if (i = -j) then SInt (-1) else (if (i =j) then SInt 1 else tt)
                                            | (j,k)               -> if (j =k) then SInt 1 else tt
                                           )
           (* *************************************************************** *)
           (* *************************************************************** *)




           (* *************************************************************** *)
           (*                           SFltBinOp                             *)
           (* *************************************************************** *)

          | SFltBinOp(FltProd,x,SFltBinOp(FltExp,y,z))  -> simplify_expression ev el (SFltBinOp(FltProd,SFltBinOp(FltExp,y,z),x))

           (* 1) Algebraic Equivalences: distributivity *)
           | SFltBinOp(FltProd,z,SFltBinOp(FltSum,x,y)) -> simplify_expression ev el (SFltBinOp(FltProd,SFltBinOp(FltSum,x,y),z))
           | SFltBinOp(FltProd,SFltBinOp(FltSum,x,y),z) -> simplify_expression ev el (SFltBinOp(FltSum,SFltBinOp(FltProd,z,x),SFltBinOp(FltProd,z,y)))
           | SFltBinOp(FltProd,z,SFltBinOp(FltSub,x,y)) -> simplify_expression ev el (SFltBinOp(FltProd,SFltBinOp(FltSub,x,y),z))
           | SFltBinOp(FltProd,SFltBinOp(FltSub,x,y),z) -> simplify_expression ev el (SFltBinOp(FltSub,SFltBinOp(FltProd,z,x),SFltBinOp(FltProd,z,y)))

           (* 2) Algebraic Equivalences: associativity *)
           | SFltBinOp(FltSum,SFltBinOp(FltSum,y,z),x)  -> simplify_expression ev el (SFltBinOp(FltSum,x,SFltBinOp(FltSum,y,z)))
           | SFltBinOp(FltProd,SFltBinOp(FltProd,y,z),x)-> simplify_expression ev el (SFltBinOp(FltProd,x,SFltBinOp(FltProd,y,z)))

           (* 3) Operation related equivalences *)
           | SFltBinOp(FltSum,x,y)  -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SFltBinOp(FltSum,xx,yy) in
                                            match (xx,yy) with
                                            | (SFlt 0., j)
                                            | (j, SFlt 0.)        -> j
                                            | (SFlt j, SFlt (i))  -> if (i = -.j) then
                                                                       SFlt 0.
                                                                     else if (i = j) then
                                                                       simplify_expression ev el (SFltBinOp(FltProd, SFlt 2., SFlt j))
                                                                     else
                                                                       tt
                                            | (j, k)              -> if (j = k) then
                                                                        simplify_expression ev el (SFltBinOp(FltProd, SFlt 2., j))
                                                                     else
                                                                        tt
                                           )
           | SFltBinOp(FltSub,x,y)  -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SFltBinOp(FltSub,xx,yy) in
                                            match (xx,yy) with
                                            | (SFlt 0., SFlt j)                       -> SFlt (-.j)
                                            | (SFlt 0., (SFltBinOp(FltSub,SFlt 0.,z)))-> simplify_expression ev el z
                                            | (j, SFlt 0.)                            -> j
                                            | (SFlt j, SFlt i)                        -> if (i = -.j) then
                                                                                            simplify_expression ev el (SFltBinOp(FltProd, SFlt 2., SFlt j))
                                                                                         else if (i = j) then
                                                                                            SFlt 0.
                                                                                         else
                                                                                            tt
                                            | (j, k)                                  -> if (j = k) then SFlt 0. else tt
                                           )
           | SFltBinOp(FltProd,x,y) -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SFltBinOp(FltProd,xx,yy) in
                                            match (xx,yy) with
                                            | (SFlt 0., j)
                                            | (j, SFlt 0.)         -> SFlt 0.
                                            | (SFlt 1., j)
                                            | (j, SFlt 1.)         -> j
                                            | (SFlt j, SFlt (i))   ->                          if (i = -.j) then
                                                                                                 simplify_expression ev el (SFltBinOp(FltSub, SFlt 0., (SFltBinOp(FltExp, SCast(TFlt,SFlt j), SFlt 2.))))
                                                                                               else if (i=j) then
                                                                                                 simplify_expression ev el (SFltBinOp(FltExp, SCast(TFlt,SFlt j), SFlt 2.))
                                                                                               else
                                                                                                 tt
                                            | (SFltBinOp(FltExp,a,b),SFltBinOp(FltExp,z,t)) -> if (a = z) then
                                                                                                 simplify_expression ev el (SFltBinOp(FltExp,z,SFltBinOp(FltSum,t,b)))
                                                                                               else if (b = t) then
                                                                                                 simplify_expression ev el (SFltBinOp(FltExp,SFltBinOp(FltProd,a,z),t))
                                                                                               else
                                                                                                 tt
                                            | (a,SFltBinOp(FltExp,b,c))
                                            | (SFltBinOp(FltExp,b,c),a) ->                     if (a=b) then
                                                                                                 simplify_expression ev el (SFltBinOp(FltExp,b,SFltBinOp(FltSum,c,SFlt 1.)))
                                                                                               else
                                                                                                 tt
                                            | (j,k)               ->                           if (j = k) then
                                                                                                 simplify_expression ev el (SFltBinOp(FltExp, SCast(TFlt,j), SFlt 2.))
                                                                                               else
                                                                                                 tt
                                           )
           | SFltBinOp(FltDiv,x,y) -> (let xx = simplify_expression ev el x in
                                            let yy = simplify_expression ev el y in
                                            let tt = SFltBinOp(FltDiv,xx,yy) in
                                            match (xx,yy) with
                                            | (SFlt 0., j)         -> SFlt 0.
                                            | (j, SFlt 0.)         -> raise(DivisionByZero)
                                            | (j, SFlt 1.)         -> j
                                            | (SFlt j, SFlt (i))  -> if (i = -.j) then SFlt (-.1.) else (if (i =j) then SFlt 1. else tt)
                                            | (j,k)               -> if (j =k) then SFlt 1. else simplify_expression ev el  (SFltBinOp(FltProd,x,SFltBinOp(FltDiv,(SFlt 1.),y)))
                                           )

           (* *************************************************************** *)
           (* *************************************************************** *)


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
           | SIfte(x,y,z) -> (match simplify_expression ev el x with
               | SBol true -> simplify_expression ev el y
               | SBol false -> simplify_expression ev el z
               | _ -> SIfte(x, simplify_expression ev el y, simplify_expression ev el z))
           | _ as t -> t


(*
let get_environment_type (g:environment) x = List.fold_left (fun z -> fun  (s,t,b) -> if (s = x) then b else z) TObj g
let get_environment_term (g:environment) x = List.fold_left (fun z -> fun  (s,t,b) -> if (s = x) then t else z) (SBol false) g
let get_gamma_type (g:gamma) x = List.fold_left (fun z -> fun  (s,b) -> if (s = x) then b else z) TObj g
*)
