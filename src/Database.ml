open Basics
open Term
open Term2

(** The object system is built on top of this other one *)
type database = {
	o: term_of_int;
	bigO: term_of_list;
	ell: term_of_ffunc;
	xi: term_of_ffunc;
	phi: term_of_ffunc;
}

type database2 = {
	o:    term2;
	bigO: term2;
	ell:  term2;
	xi:   term2;
	phi:  term2;
}


