open Basics
open Term

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
    

