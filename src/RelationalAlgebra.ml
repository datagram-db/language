open Term
open Term2
open Term2Operations

type 'a relational_algebra  = Empty | Relation of 'a
                                 | Union of 'a relational_algebra * 'a relational_algebra
                                 | Times of 'a relational_algebra * 'a relational_algebra
                                 | Difference of 'a relational_algebra * 'a relational_algebra
                                 | Selection of term2 * 'a relational_algebra
                                 | Projection of string list * 'a relational_algebra
                                 | Intersection of 'a relational_algebra * 'a relational_algebra
                                 | ThetaJoin of term2 * 'a relational_algebra * 'a relational_algebra

(** Using some relational algebra rexpression rewriting to enhance the computation *)
let rec rewrite_algebraic_expression = function
  | Empty as t -> t
  | Relation _ as t -> t
  | Union(a,b)      ->
    let (aa,bb) = (rewrite_algebraic_expression a, rewrite_algebraic_expression b) in
    if (aa = bb) then aa else
    if (aa > bb) then rewrite_algebraic_expression (Union(bb,aa)) else (
      match (aa,bb) with
      | (r,Empty)
      | (Empty,r)        -> r
      | (r,Union(s,t)) -> Union(Union(r,s),t)
      | (r,Difference(s,t)) -> rewrite_algebraic_expression (Difference(Union(r,s),Difference(t,r)))
      | (r,Intersection(s,t)) -> rewrite_algebraic_expression (Intersection(Union(r,s),Union(r,t)))
      | _                   -> Union(aa,bb)
    )
  | Intersection(a,b)      ->
    let (aa,bb) = (rewrite_algebraic_expression a, rewrite_algebraic_expression b) in
    if (aa=bb) then aa else
    if (aa > bb) then rewrite_algebraic_expression (Intersection(bb,aa)) else
      (match (aa,bb) with
       | (r,Empty)
       | (Empty,r) -> Empty
       | (r,Intersection(s,t)) -> Intersection(Intersection(r,s),t)
       | (r,Union(s,t)) -> rewrite_algebraic_expression (Union(Intersection(r,s),Intersection(r,t)))
       | (Times(r,s),Times(u,t)) when r=u -> rewrite_algebraic_expression (Times(r,Intersection(s,t)))
       | _ -> rewrite_algebraic_expression (Difference(aa,Difference(aa,bb)))
      )
  | Difference (a,b) ->
    let (aa,bb) = (rewrite_algebraic_expression a, rewrite_algebraic_expression b) in
    if (aa=bb) then Empty else
    if (aa > bb) then rewrite_algebraic_expression (Intersection(bb,aa)) else
      (match (aa,bb) with
       | (r,Empty)
       | (Empty,r) -> Empty
       | (r,Intersection(s,t)) -> rewrite_algebraic_expression (Union(Difference(r,s),Difference(r,t)))
       | (Intersection(s,t),r) -> rewrite_algebraic_expression (Intersection(Difference(s,r),Difference(t,r)))
       | (r,Union(s,t)) -> rewrite_algebraic_expression (Difference(Difference(r,s),t))
       | (Union(s,t),r) -> rewrite_algebraic_expression (Union(Difference(s,r),Difference(t,r)))
       | _ -> Difference(aa,bb)
      )
  | Times(a,b) ->
    let (aa,bb) = (rewrite_algebraic_expression a, rewrite_algebraic_expression b) in
    if (aa > bb) then rewrite_algebraic_expression (Times(bb,aa)) else
      (match (aa,bb) with
       | (r,Empty)
       | (Empty,r) -> Empty
       | (r,Times(s,t)) -> rewrite_algebraic_expression (Times(Times(r,s),t))
       | (r,Union(s,t)) -> rewrite_algebraic_expression (Union(Times(r,s),Times(r,t)))
       | _ -> Times(aa,bb)
      )
  | Selection(expr,b) ->
    let (bb,e1) = (rewrite_algebraic_expression b,resolve_and_ignore expr) in
    (match bb with
     | Empty -> Empty
     | Union(r,s) -> rewrite_algebraic_expression (Union(Selection(e1,r),Selection(e1,s)))
     | Difference(r,s) -> Difference(Selection(e1,r),Selection(e1,s))
     | Intersection(r,s) -> rewrite_algebraic_expression (Intersection(Selection(e1,r),Selection(e1,s)))
     | Selection(e1,Projection(l,r)) -> rewrite_algebraic_expression (Projection(l,Selection(e1,r)))
     | Selection(e2,r) -> rewrite_algebraic_expression (Selection(resolve_and_ignore (SFunc("x",SBolBinOp(BoolAnd,SFunApply(e1,SVar "x"),SFunApply(e2,SVar "x")))), r))
     | _ -> Selection(e1,bb)
    )
    
  | ThetaJoin(e,a,b) -> let (aa,bb) = (rewrite_algebraic_expression a, rewrite_algebraic_expression b) in
  if (aa < bb) then ThetaJoin(e,aa,bb) else rewrite_algebraic_expression (Selection(e,Times(aa,bb)))

| _ as t -> t
