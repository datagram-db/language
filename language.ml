(** ocamlc str.cma language.ml *)
open Str
exception UnexpectedType of string
exception UnbondedVariable of string
exception DivisionByZero
exception UnexpectedCast of string

let remove_elt e l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when e = x -> go xs acc
    | x::xs -> go xs (x::acc)
  in go l []

let remove_duplicates l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt x xs) (x::acc)
  in go l []

(*
   Defining the language's syntax
 *)

type bin_comp_to_bool = Eq | Lt | LEq | Gt | GEq
type bol_bin_op = BoolAnd | BoolOr
type int_bin_op = IntSum | IndDiv | IntSub | IntMod | IntProd
type flt_bin_op = FltSum | FltDiv | FltSub | FltProd | FltLog | FltExp
type flt_mon_op = FltSin | FltCos | FltTan | FltSqrt
type flt_to_int_mon_op = FltFloor | FltCeil | FltTrunc | FltRound 
type str_bin_op = StrAppend | StrSub
type str_int_bin_op = StrAt | RemAt
type list_bin_op = ListAppend | ListCross
type list_mon_op = ListTail | ListUnique

type basic_types = TBol | TInt | TFlt | TStr | TLst | TFnc | TFFnc (*| TObj *)

type variable = Variable of string


(** Defining the term system in such a way that the terms are type compliant (i.e., recognize at parser/lexer time and force a correct typing) *)
(* Terms that are always of type bool *)
type term_of_bol = Bol of bool
                 | BolCast of term
                 | BolBinOp of bol_bin_op * term_of_bol * term_of_bol
                 | BolNeg of term_of_bol
                 | StrContains of term_of_string * term_of_string
                 | LstContains of term_of_list * term
                 | FFuncContains of term_of_ffunc * term
                 | BinCompBool of bin_comp_to_bool * term * term
(* Terms that are always of type int *)
and term_of_int = Int of int 
                 | IntCast of term
                 | IntBinOp of int_bin_op * term_of_int * term_of_int
                 | FracToIntBinOp of flt_to_int_mon_op * term_of_flt
(* Terms that are always of type float *)                 
and term_of_flt = Flt of float
                | FltCast of term
                | FltBinOp of flt_bin_op * term_of_flt * term_of_flt
                | FracMonOp of flt_mon_op * term_of_flt

and term_of_string = Str of string
                   | StrCast of term
                   | StrBinOp of str_bin_op * term_of_string * term_of_string
                   | StrReplace of term_of_string * term_of_string * term_of_string
                   | StrIntBinOp of str_int_bin_op * term_of_string * term_of_int
                   | StrSet of term_of_string * term_of_int * term_of_string
             
and term_of_list = Lst of term list    
                 | LstCast of term
                 | StrSplit of term_of_string * term_of_string
                 | LstBinOp of list_bin_op * term_of_list * term_of_list
                 | LstMonOp of list_mon_op * term_of_list
                 | LstRemAt of term_of_list * term_of_int
                 | LstRemVal of term_of_list * term
                 | LstSet of term_of_list * term_of_int * term
                 | LstMap of term * term_of_list
                 | LstFilter of term * term_of_list
                        
and term_of_func = FunCast of term
                 | Func of variable (* * basic_types*) * term_of_func
                 | FuncBody of term   
                 | FuncComp of term_of_func * term_of_func
                 
and term_of_ffunc = FFuncCast of term
                 | FFunc of (term * term) list
                 | FExtend of term * term * term_of_ffunc
                 | FRemove of term * term_of_ffunc
                 | FFuncComp of term_of_ffunc * term_of_ffunc                   
(* TODO: Object definition, with phi, ell, and xi functions *)                                    
and term = Var of variable
         | Sequences of term list
	 | TermBol of term_of_bol
         | TermInt of term_of_int
         | TermFlt of term_of_flt
         | TermStr of term_of_string
         | TermLst of term_of_list
         | TermFnc of term_of_func
         | TermFFnc of term_of_ffunc
         | LstHead of term_of_list
         | LstLFold of term * term * term_of_list
         | LstAt of term_of_list * term_of_int
         | LetIn of variable * term * term
         | Ifte of term_of_bol * term * term 
         | FunApply of term_of_func * term
         | FFunApply of term_of_ffunc * term
         

(** Defining the semantics: the value will be the final value **)
type term_sem = SBol of bool 
              | SInt of int
              | SFlt of float
              | SStr of string
              | SFunc of (string * basic_types) list * term (* lazy function *)
              | SLst of term_sem list
              | SFFunc of (term_sem * term_sem) list

(******************************************************************************)
(**                Retrieving the free variables from a term                 **)
(******************************************************************************
let rec fv t = 
       let rec free_variable acc = function
	| Var x -> if (List.memq x acc) then [] else [x]
	| Sequences s -> remove_duplicates (List.flatten (List.map (free_variable acc) s))
	| TermBol x -> free_variable_bool acc x 
	| TermInt x -> free_variable_int acc x
	| TermFlt x -> free_variable_flt acc x
	| TermStr x -> free_variable_str acc x
	| TermLst x -> free_variable_lst acc x
	| TermFnc x -> free_variable_func acc x
	| TermFFnc x -> free_variable_ffunc acc x
	| LstHead x -> free_variable_lst acc x
	| LstLFold(t,f,l) -> (free_variable acc t)@(free_variable acc f)@(free_variable_lst acc l)
	| LstAt(l,i) -> (free_variable_lst acc l)@(free_variable_int acc i)
	| LetIn(v,t,m) -> (free_variable acc t)@(free_variable (v::acc) m)
	| FunApply(f,t) -> (free_variable acc t)@(free_variable_func acc f)
	| FFunApply(f,t) -> (free_variable acc t)@(free_variable_ffunc acc f)
       and free_variable_bool acc = function
	| BolCast x -> free_variable acc x
	| BolBinOp (_,y,x) -> (free_variable_bool acc y)@(free_variable_bool acc x)
	| BolNeg (x) -> free_variable_bool acc x
	| BinCompBool(_,x,y) -> (free_variable acc x)@(free_variable acc y)
	| StrContains(x,y) -> (free_variable_str acc x)@(free_variable_str acc y)
	| LstContains(x,y) -> (free_variable_lst acc x)@(free_variable acc y)
	| FFuncContains(x,y) -> (free_variable_ffunc acc x)@(free_variable acc y)
	| _ -> []
       and free_variable_int acc = function
	| IntCast (t) ->free_variable acc t
	| IntBinOp(_,x,y) -> (free_variable_int acc x)@(free_variable_int acc y)
	| FracToIntBinOp(_,x) -> free_variable_flt acc x
	| _ -> []
       and free_variable_flt acc = function
	| FltCast t -> free_variable acc t
	| FltBinOp(_,x,y) -> (free_variable_flt acc x)@(free_variable_flt acc y)
	| FracMonOp(_,x) -> (free_variable_flt acc x)
	| _ -> []
       and free_variable_str acc = function
	| StrCast  t -> free_variable acc t
	| StrBinOp(_,x,y) -> (free_variable_str acc x)@(free_variable_str acc y)
	| StrReplace(x,y,z) -> (free_variable_str acc x)@(free_variable_str acc y)@(free_variable_str acc z)
	| StrIntBinOp(_,x,y) -> (free_variable_str acc x)@(free_variable_int acc y)
	| StrSet(x,y,z) -> (free_variable_str acc x)@(free_variable_int acc y)@(free_variable_str acc z)
	| _ -> []
       and free_variable_lst acc = function
	| Lst x -> remove_duplicates (List.flatten (List.map (free_variable acc) x))
	| LstCast (t) ->free_variable acc t
	| StrSplit(x,y) -> (free_variable_str acc x)@(free_variable_str acc y)
	| LstBinOp(_,x,y) -> (free_variable_lst acc x)@(free_variable_lst acc y)
	| LstMonOp(_,x) -> (free_variable_lst acc x)
	| LstRemAt(x,y) -> (free_variable_lst acc x)@(free_variable_int acc y)
	| LstRemVal(x,y) -> (free_variable_lst acc x)@(free_variable acc y)
	| LstSet(x,y,z) -> (free_variable_lst acc x)@(free_variable_int acc y)@(free_variable acc z)
	| LstMap(x,y) -> (free_variable acc x)@(free_variable_lst acc y)
	| LstFilter(x,y) -> (free_variable acc x)@(free_variable_lst acc y)
       and free_variable_func acc = function
	| FunCast x -> free_variable acc x
	| Func(x,y) -> free_variable_func (x::acc) y
	| FuncBody(t) -> free_variable acc t
	| FuncComp(x,y) -> (free_variable_func acc x)@(free_variable_func acc y)
       and free_variable_ffunc acc = function
	| FFuncCast x -> free_variable acc x
	| FFunc(cpls) -> remove_duplicates (List.flatten (List.map (free_variable acc) (snd (List.split cpls)))) (* todo: the key should never be a variable *)
	| FExtend(_,x,y) -> (free_variable acc x)@(free_variable_ffunc acc y)
	| FRemove(x,y) -> (free_variable acc x)@(free_variable_ffunc acc y)
	| FFuncComp(x,y) -> (free_variable_ffunc acc x)@(free_variable_ffunc acc y)
in free_variable [] t
 
******************************************************************************)
(******************************************************************************)


(******************************************************************************)
(**      Substitutes the variable original in currnet with replacement       **)
(******************************************************************************
let subst current original replacement = 
       let rec substitution = function
        | Var (Variable x) -> if (x == original) then replacement else current
	| Sequences s -> Sequences (List.map substitution s)
	| TermBol x -> TermBol (substitution_bool x)
	| TermInt x -> TermInt (substitution_int x)
	| TermFlt x -> TermFlt (substitution_flt x)
	| TermStr x -> TermStr (substitution_str x)
	| TermLst x -> TermLst (substitution_lst x)
	| TermFnc x -> TermFnc (substitution_func x)
	| TermFFnc x -> TermFFnc (substitution_ffunc x)
	| LstHead x -> LstHead (substitution_lst x )
	| LstLFold(t,f,l) -> LstLFold((substitution t  ),(substitution f  ),(substitution_lst  l  ))
	| LstAt(l,i) -> LstAt((substitution_lst  l  ),(substitution_int  i )) 
	| FunApply(f,t) -> FunApply((substitution_func  f  ),(substitution  t  ))
	| FFunApply(f,t) -> FFunApply((substitution_ffunc f  ),(substitution  t))
	| LetIn(Variable v,t,m) -> LetIn(Variable v, (substitution  t  ), if (v == original) then m else (substitution  m))
       and substitution_bool : term_of_bol -> term_of_bol = function
	| BolCast x -> BolCast (substitution x)
	| BolBinOp (z,y,x) -> BolBinOp(z,(substitution_bool x),(substitution_bool y)) 
	| BolNeg (x) -> BolNeg(substitution_bool x)
	| StrContains(x,y) -> StrContains((substitution_str x),(substitution_str y))
	| LstContains(x,y) -> LstContains((substitution_lst x),(substitution y))
	| FFuncContains(x,y) -> FFuncContains((substitution_ffunc x),(substitution y))
	| BinCompBool(z,x,y) -> BinCompBool(z,substitution x, substitution y)
	| _ as t -> t
       and substitution_int : term_of_int -> term_of_int = function
	| IntCast (t) -> IntCast(substitution t)
	| IntBinOp(z,x,y) -> IntBinOp(z,(substitution_int x),(substitution_int y))
	| FracToIntBinOp(z,x) -> FracToIntBinOp(z,substitution_flt x)
	| _ as t -> t
       and substitution_flt: term_of_flt -> term_of_flt = function
	| FltCast t -> FltCast(substitution t)
	| FltBinOp(z,x,y) -> FltBinOp(z,(substitution_flt x),(substitution_flt y))
	| FracMonOp(z,x) -> FracMonOp(z,(substitution_flt x))
	| _ as t -> t
       and substitution_str: term_of_string -> term_of_string  = function
	| StrCast  t -> StrCast(substitution t)
	| StrBinOp(z,x,y) -> StrBinOp(z,(substitution_str x),(substitution_str y))
	| StrReplace(x,y,z) -> StrReplace((substitution_str x),(substitution_str y),(substitution_str z))
	| StrIntBinOp(z,x,y) -> StrIntBinOp(z,(substitution_str x),(substitution_int y))
	| StrSet(x,y,z) -> StrSet((substitution_str x),(substitution_int y),(substitution_str z))
	| _ as t -> t
       and substitution_lst : term_of_list -> term_of_list = function
	| Lst x -> Lst (List.map substitution x)
	| LstCast (t) ->LstCast(substitution t)
	| StrSplit(x,y) -> StrSplit(substitution_str x, substitution_str y)
	| LstBinOp(z,x,y) -> LstBinOp(z, substitution_lst x, substitution_lst y)
	| LstMonOp(z,x) -> LstMonOp(z, substitution_lst x)
	| LstRemAt(x,y) -> LstRemAt(substitution_lst x, substitution_int y)
	| LstRemVal(x,y) -> LstRemVal(substitution_lst x, substitution y)
	| LstSet(x,y,z) -> LstSet(substitution_lst x, substitution_int y, substitution z)
	| LstMap(x,y) -> LstMap(substitution x, substitution_lst y)
	| LstFilter(x,y) -> LstFilter(substitution x, substitution_lst y)
       and substitution_func : term_of_func -> term_of_func  = function
	| FunCast x -> FunCast(substitution x)
	| Func(Variable x,y) as t -> if (x==original) then t else Func(Variable x,substitution_func y)
	| FuncBody(t) -> FuncBody(substitution t)
	| FuncComp(x,y) -> FuncComp(substitution_func x, substitution_func y)
       and substitution_ffunc : term_of_ffunc -> term_of_ffunc  = function
	| FFuncCast x -> FFuncCast(substitution x)
	| FFunc(cpls) -> FFunc(List.map (fun (x,y) -> (x, substitution y)) cpls) (* todo: the key should never be a variable *)
	| FExtend(z,x,y) -> FExtend(z, substitution x, substitution_ffunc y)
	| FRemove(x,y) -> FRemove(substitution x, substitution_ffunc y)
	| FFuncComp(x,y) -> FFuncComp(substitution_ffunc x, substitution_ffunc y)
in substitution current
 
******************************************************************************)
(******************************************************************************)


type term2 = SBol of bool
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
           | SIfte of term2 * term2 * term2

(* Simplifying the term into a better representation, even though it is less typed *)
let to_term2 x = 
	let rec rewrite = function
        | Var (Variable x) -> SVar x
	| Sequences s -> SSequence (List.map rewrite s)
	| TermBol x -> (rewrite_bool x)
	| TermInt x -> (rewrite_int x)
	| TermFlt x -> (rewrite_flt x)
	| TermStr x -> (rewrite_str x)
	| TermLst x -> (rewrite_lst x)
	| TermFnc x -> (rewrite_func x)
	| TermFFnc x -> (rewrite_ffunc x)
	| LstHead x -> SLstHead (rewrite_lst x )
	| LstLFold(t,f,l) -> SLstLFold((rewrite t  ),(rewrite f  ),(rewrite_lst  l  ))
	| LstAt(l,i) -> SLstAt((rewrite_lst  l  ),(rewrite_int  i )) 
	| FunApply(f,t) -> SFunApply((rewrite_func  f  ),(rewrite  t  ))
	| FFunApply(f,t) -> SFFunApply((rewrite_ffunc f  ),(rewrite  t))
	| LetIn(Variable v,t,m) -> SLetIn(v, (rewrite  t  ), (rewrite  m))
	| Ifte(x,y,z) -> SIfte(rewrite_bool x, rewrite y, rewrite z)
       and rewrite_bool  = function
        | Bol x -> SBol x
	| BolCast x -> SCast (TBol, rewrite x)
	| BolBinOp (z,y,x) -> SBolBinOp(z,(rewrite_bool x),(rewrite_bool y)) 
	| BolNeg (x) -> SBolNeg(rewrite_bool x)
	| StrContains(x,y) -> SStrContains((rewrite_str x),(rewrite_str y))
	| LstContains(x,y) -> SLstContains((rewrite_lst x),(rewrite y))
	| FFuncContains(x,y) -> SFFuncContains((rewrite_ffunc x),(rewrite y))
	| BinCompBool(z,x,y) -> SBinCompBool(z,rewrite x, rewrite y)
       and rewrite_int  = function
        | Int t -> SInt t
	| IntCast (t) -> SCast(TInt, rewrite t)
	| IntBinOp(z,x,y) -> SIntBinOp(z,(rewrite_int x),(rewrite_int y))
	| FracToIntBinOp(z,x) -> SFracToIntBinOp(z,rewrite_flt x)
       and rewrite_flt  = function
        | Flt f -> SFlt f
	| FltCast t -> SCast(TFlt, rewrite t)
	| FltBinOp(z,x,y) -> SFltBinOp(z,(rewrite_flt x),(rewrite_flt y))
	| FracMonOp(z,x) -> SFracMonOp(z,(rewrite_flt x))
       and rewrite_str   = function
        | Str t -> SStr t
	| StrCast  t -> SCast(TStr, rewrite t)
	| StrBinOp(z,x,y) -> SStrBinOp(z,(rewrite_str x),(rewrite_str y))
	| StrReplace(x,y,z) -> SStrReplace((rewrite_str x),(rewrite_str y),(rewrite_str z))
	| StrIntBinOp(z,x,y) -> SStrIntBinOp(z,(rewrite_str x),(rewrite_int y))
	| StrSet(x,y,z) -> SStrSet((rewrite_str x),(rewrite_int y),(rewrite_str z))
       and rewrite_lst  = function
	| Lst x -> SLst (List.map rewrite x)
	| LstCast x -> SCast(TLst, rewrite x)
	| StrSplit(x,y) -> SStrSplit(rewrite_str x, rewrite_str y)
	| LstBinOp(z,x,y) -> SLstBinOp(z, rewrite_lst x, rewrite_lst y)
	| LstMonOp(z,x) -> SLstMonOp(z, rewrite_lst x)
	| LstRemAt(x,y) -> SLstRemAt(rewrite_lst x, rewrite_int y)
	| LstRemVal(x,y) -> SLstRemVal(rewrite_lst x, rewrite y)
	| LstSet(x,y,z) -> SLstSet(rewrite_lst x, rewrite_int y, rewrite z)
	| LstMap(x,y) -> SLstMap(rewrite x, rewrite_lst y)
	| LstFilter(x,y) -> SLstFilter(rewrite x, rewrite_lst y)
       and rewrite_func  = function
	| FunCast x -> SCast(TFnc, rewrite x)
	| Func(Variable x,y) -> SFunc(x,rewrite_func y)
	| FuncBody(t) -> (rewrite t)
	| FuncComp(x,y) -> SFuncComp(rewrite_func x, rewrite_func y)
       and rewrite_ffunc  = function
	| FFuncCast x -> SCast(TFFnc, rewrite x)
	| FFunc(cpls) -> SFFunc(List.map (fun (x,y) -> (rewrite x, rewrite y)) cpls) (* todo: the key should never be a variable *)
	| FExtend(z,x,y) -> SFExtend(rewrite z, rewrite x, rewrite_ffunc y)
	| FRemove(x,y) -> SFRemove(rewrite x, rewrite_ffunc y)
	| FFuncComp(x,y) -> SFFuncComp(rewrite_ffunc x, rewrite_ffunc y)
in rewrite x
    




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


(* Basic Semantic Functions *)

let sem_and x y = match (x,y) with
| (SBol true, SBol true) -> true
| (SBol _, SBol _) -> false
| _ -> raise (UnexpectedType "And function run over non-boolean elements")

let sem_or x y = match (x,y) with 
| (SBol false, SBol false) -> false
| (SBol _, SBol _) -> true
| _ -> raise (UnexpectedType "Or function run over non-boolean elements")

let sem_xor x y = match (x,y) with 
| (SBol true, SBol false) -> true
| (SBol false, SBol true) -> true
| (SBol _, SBol _) -> true
| _ -> raise (UnexpectedType "Or function run over non-boolean elements")

let getBolBinOpFunction = function
| BoolAnd -> sem_and 
| BoolOr -> sem_or

let sem_sum x y = match (x,y) with
| (SInt i, SInt j) -> SInt (i+j)
| (SFlt i, SFlt j) -> SFlt (i+.j)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_div x y = match (x,y) with
| (SInt i, SInt j) -> SInt (i/j)
| (SFlt i, SFlt j) -> SFlt (i/.j)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_sub x y = match (x,y) with
| (SInt i, SInt j) -> SInt (i-j)
| (SFlt i, SFlt j) -> SFlt (i-.j)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_mod x y = match (x,y) with
| (SInt i, SInt j) -> SInt (i mod j)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_prod x y = match (x,y) with
| (SInt i, SInt j) -> SInt (i * j)
| (SFlt i, SFlt j) -> SFlt (i/.j)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_pow x y = match (x,y) with
| (SFlt i, SFlt j) -> SFlt (Float.pow i j)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_log x y = match (x,y) with
| (SFlt i, SFlt j) -> SFlt ((Float.log i) /. (Float.log j))
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let getIntBinOpFunction = function
| IntSum -> sem_sum
| IndDiv -> sem_div
| IntSub -> sem_sub
| IntMod -> sem_mod 
| IntProd -> sem_prod

let getFltBinOpFunction = function
| FltSum -> sem_sum
| FltDiv -> sem_div 
| FltSub -> sem_sub
| FltProd -> sem_prod 
| FltLog -> sem_log 
| FltExp -> sem_pow


let sem_sin x = match (x) with
| (SFlt i) -> SFlt (Float.sin i)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_cos x = match (x) with
| (SFlt i) -> SFlt (Float.cos i)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_tan x = match (x) with
| (SFlt i) -> SFlt (Float.tan i)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_sqrt x = match (x) with
| (SFlt i) -> SFlt (Float.sqrt i)
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let getFltMonOpFunction = function
| FltSin -> sem_sin
| FltCos -> sem_cos
| FltTan -> sem_tan 
| FltSqrt -> sem_sqrt

let sem_floor x = match (x) with
| (SFlt i) -> SInt (int_of_float (floor i))
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_ceil x = match (x) with
| (SFlt i) -> SInt (int_of_float (ceil i))
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_trunc x = match (x) with
| (SFlt i) -> SInt (int_of_float (Float.trunc i))
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let sem_round x = match (x) with
| (SFlt i) -> SInt (int_of_float (Float.round i))
| _ -> raise (UnexpectedType "IntegerSum function run over non-integer elements")

let getFltMonToIntOpFunction = function
| FltFloor -> sem_floor
| FltCeil -> sem_ceil
| FltTrunc -> sem_trunc
| FltRound -> sem_round

let sem_append x y = match (x,y) with
| (SStr a, SStr b) -> SStr (a^b)
| (SLst a, SLst b) -> SLst (a@b)
| _ -> raise (UnexpectedType "Append function run over non-string elements")

let sem_replace x y z = match (x,y,z) with
| (SStr a, SStr b, SStr c) -> SStr (Str.global_replace (Str.regexp a) b c)
| _ -> raise (UnexpectedType "Replace function run over non-string elements")

let getStrBinOp = function
| StrAppend -> sem_append 
| StrSub -> fun x -> fun y-> sem_replace x (SStr "") y


let sem_get x y = match (x,y) with
| (SStr a, SInt b) -> SStr (String.make 1 (String.get a b))
| (SLst a, SInt b) -> List.nth a b
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let sem_rem x y = match (x,y) with
| (SStr a, SInt b) -> SStr 
                          (let len = String.length a in
                           if (b >= len) then a else (if (b == 0) then (String.sub a 1 ((String.length a)-1)) else 
                                                      (if (b == (len -1)) then (String.sub a 0 ((String.length a)-1)) else (String.sub a 0 b)^(String.sub a (b+1) (len-b-1)))
                                                     )
                          )
| (SLst a, SInt b) -> (let rec remnth i = function
                      | [] -> []
                      | a::b -> if (i <= 0) then b else a::(remnth (i-1) b) in
                      SLst (remnth b a))
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let sem_rem_val x y = match (x,y) with
| (SLst a, t) -> List.filter (fun z-> not (z == t)) a
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let getStrIntBinOPFunction = function
| StrAt -> sem_get
| RemAt -> sem_rem

let rec list_cross x = function
| [] -> []
| hd::tl -> (List.map (fun y-> [y;hd]) x)@(list_cross x tl)

let sem_cross x y = match (x,y) with
| (SLst a, SLst b) -> SLst (List.map (fun z -> SLst z) (list_cross a b))
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let getListBinOpFunction = function
| ListAppend -> sem_append 
| ListCross -> sem_cross

let sem_tail x = match x with
| SLst (hd::tl) -> SLst tl
| SLst _ -> SLst []
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let sem_uniq x = match x with
| SLst s -> SLst (remove_duplicates s)
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let getListMonOpFunction = function
| ListTail -> sem_tail
| ListUnique -> sem_uniq

let sem_contains x y = function
| (SLst a, y) -> SBol (List.memq y a)
| (SStr a, SStr b) -> SBol ((try Str.search_forward (Str.regexp b) a 0 with _ -> -1) >= 0)
| (SFFunc f, x) -> SBol (List.exists (fun (z,_) -> z == x) f)
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")


let sem_set x y t = match (x,y,t) with
| (SStr a, SInt b,SStr c) -> SStr 
                          (let len = String.length a in
                           let charo = (String.make 1 (String.get c 0)) in 
                           if (b >= len) then a else (if (b == 0) then charo^(String.sub a 1 ((String.length a)-1)) else 
                                                      (if (b == (len -1)) then (String.sub a 0 ((String.length a)-1))^charo else (String.sub a 0 b)^charo^(String.sub a (b+1) (len-b-1)))
                                                     )
                          )
| (SLst a, SInt b, c) -> (let rec remnth i = function
                      | [] -> []
                      | a::b -> if (i <= 0) then c::b else a::(remnth (i-1) b) in
                      SLst (remnth b a))
| _ -> raise (UnexpectedType "Replace function run over non-sequence elements")

let rec ffextend input output = function
	| []        -> [(input,output)]
	| (x,y)::tl -> if (x==input) then (input,output)::tl else (x,y)::(ffextend input output tl)

let ffremove input ls = 
	List.filter (fun (x,y) -> not (input==x)) ls

let rec ffcomp l1 l2 = 
	match l1 with
	| []        -> l2
	| (x,y)::tl -> ffcomp tl (ffextend x y l2)


(** TODO: implementare la interpretazione della semantica delle funzioni *) 

(** The object system is built on top of this other one *)
type database = {
	o: term_of_int;
	bigO: term_of_list;
	ell: term_of_ffunc;
	xi: term_of_ffunc;
	phi: term_of_ffunc;
}

(*
let rec function_length = function
| Var (Variable x) -> function_length (List.fold_left (fun z -> fun  (s,t,b) -> if (s == x) then t else z) (TermBol (Bol false)) g)
| _ -> 0

let explode s = List.init (String.length s) (fun x -> String.make 1 (String.get s x))

let rec bool_cast (g:environment) = function
| Var (Variable x) -> bool_cast g (get_environment_type g x)
| TermBol _ as t -> t
| TermInt 


let rec list_cast (g: environment) = function
| Var (Variable x) -> list_cast g (get_environment_type g x)
| TermStr x -> Termst (Lst (explode x))
| TermLst _ as t -> t
| _ as t -> TermLst (Lst t) 

let list_head (g: environment) = function
| Lst [] -> TermBol (Bol false)
| Lst (hd::tl) -> hd


let list_at (g: environment) i = function

let rec eval (g : environment) = function
| Var (Variable x) -> get_environment_term g x
| TermBol (Bol b) -> SBol b
| TermBol (t) -> eval g (TermBol (eval g t)) 
| TermBol (BolBinOp (op,x,y)) -> (match (eval g (TermBol x), eval g (TermBol y)) with
                                 | (SBol true, SBol true) -> 
                                             
                                             

 Bol of bool
                 | BolCast of term
                 | BolBinOp of bol_bin_op * term_of_bol * term_of_bol
                 | BolNeg of term_of_bol
                 | StrContains of term_of_string * term_of_string
                 | LstContains of term_of_list * term
                 | FFuncContains of term_of_ffunc * term

(* identity *)

(* ignore cast *)
| TermBol (BolCast (TermBol t)) -> eval g (TermBol t)
| TermBol (Bol b) ->  TermBol (Bol b)

| TermInt (IntCast (TermInt t)) -> eval g (TermInt t)
| TermInt (Int i) ->  TermInt (Int i)

| TermFlt (FltCast (TermFlt t)) -> eval g (TermFlt t)
| TermFlt (Flt f) ->  TermFlt (Flt f)

| TermStr (StrCast (TermStr t)) -> eval g (TermStr t)
| TermStr (Str t) -> TermStr (Str t)

| TermLst (LstCast (TermLst t)) -> eval g (TermLst t)
| TermLst (Lst l) -> TermLst (Lst l)

| TermFnc (FncCast (TermFnc t)) -> eval g (TermFnc t)
| TermFnc (Func (x,y,z)) ->  TermFnc (Func (x,y,z))
| TermFnc (FuncBody x) -> TermFnc (FuncBody x)

| TermFFnc (FFncCast (TermFFnc t)) -> eval g (TermFFnc t)

         
let rec typeof (g : environment) = function
| Var (Variable x) -> get_environment_type g x
| TermBol _ -> TBol
| TermInt _ -> TInt
| TermFlt _ -> TFlt
| TermStr _ -> TStr
| TermLst _ -> TLst
| TermFnc _ -> TFnc
| TermFFnc _ -> TFFnc
| LetIn (_,_,x) -> typeof g x
| _ as t (*LstHead, LstAt*) -> typeof g (eval t)


*)
