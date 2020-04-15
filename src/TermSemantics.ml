open Basics
open Term

(** Defining the semantics: the value will be the final value **)
type term_sem = SBol of bool 
              | SInt of int
              | SFlt of float
              | SStr of string
              | SFunc of (string * basic_types) list * term (* lazy function *)
              | SLst of term_sem list
              | SFFunc of (term_sem * term_sem) list
              

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
