open Basics

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

