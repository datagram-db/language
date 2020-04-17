exception DivisionByZero

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

let rec enumerating ls f i = match ls with
  | [] -> []
  | hd::tl -> (f i,hd)::(enumerating tl f (i+1));;

let supstring_of s1 s2 =
  let len1 = String.length s1
  and len2 = String.length s2 in
  if len1 < len2 then false else
    let sub = String.sub s1 0 len2 in
    (sub = s2)

let rec sublist l b e =
      match l with
      |  [] -> failwith "sublist"
      | h :: t ->
         let tail = if e=0 then [] else sublist t (b-1) (e-1) in
         if b>0 then tail else h :: tail



let suplist_of l1 l2 =
  let len1 = List.length l1 in
  let len2 = List.length l2 in
  if len1 < len2 then false else
    let sub = sublist l1 0 len2 in (sub = l2)
