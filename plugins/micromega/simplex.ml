(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A naive simplex *)
open Polynomial
open Util
open Mutils

let debug = false

type iset = unit IMap.t

type tableau = Vect.t IMap.t (** Mapping basic variables to their equation.
                                 All variables >= than a threshold rst are restricted.*)

module Restricted =
  struct
    type t =
  {
    base : int; (** All variables above [base] are restricted *)
    exc  : int option  (** Except [exc] which is currently optimised *)
  }

    let pp o {base;exc} =
      Printf.fprintf o ">= %a " LinPoly.pp_var base;
      match exc with
      | None ->Printf.fprintf o "-"
      | Some x ->Printf.fprintf o "-%a" LinPoly.pp_var base

    let is_exception (x:var) (r:t)  =
      match r.exc with
      | None -> false
      | Some x' -> x = x'

    let restrict x rst =
      if is_exception x rst
      then
        {base = rst.base;exc= None}
      else failwith (Printf.sprintf "Cannot restrict %i" x)


    let is_restricted x r0 =
      x >= r0.base && not (is_exception x r0)

    let make x = {base = x ; exc = None}

    let set_exc x rst = {base = rst.base ; exc = Some x}

    let fold rst f m acc =
      IMap.fold (fun k v acc ->
          if is_exception k rst then acc
          else f k v acc) (IMap.from rst.base m) acc

  end



let pp_row o v = LinPoly.pp o v

let output_tableau o  t =
  IMap.iter (fun k v ->
      Printf.fprintf o "%a = %a\n" LinPoly.pp_var k pp_row v) t

let output_vars o m =
  IMap.iter (fun k _ -> Printf.fprintf o "%a " LinPoly.pp_var k) m


(** A tableau is feasible iff for every basic restricted variable xi,
   we have ci>=0.

   When all the non-basic variables are set to 0, the value of a basic
   variable xi is necessarily ci.  If xi is restricted, it is feasible
   if ci>=0.
 *)


let unfeasible (rst:Restricted.t) tbl =
  Restricted.fold rst (fun k v m ->
      if Q.(leq zero) (Vect.get_cst v) then m
      else IMap.add k () m)  tbl IMap.empty


let is_feasible rst tb = IMap.is_empty (unfeasible rst tb)

(** Let a1.x1+...+an.xn be a vector of non-basic variables.
    It is maximised if all the xi are restricted
    and the ai are negative.

    If xi>= 0 (restricted)  and ai is negative,
    the maximum for ai.xi is obtained for xi = 0

    Otherwise, it is possible to make ai.xi arbitrarily big:
    - if xi is not restricted, take +/- oo depending on the sign of ai
    - if ai is positive, take +oo
 *)

let is_maximised_vect rst v =
  Vect.for_all (fun xi ai ->
      if Q.(lt zero) ai
      then false
      else Restricted.is_restricted xi rst) v


(** [is_maximised rst v]
    @return None if the variable is not maximised
    @return Some v where v is the maximal value
 *)
let is_maximised rst v =
  try
    let (vl,v) = Vect.decomp_cst v in
    if is_maximised_vect rst v
    then Some vl
    else None
  with Not_found -> None

(** A variable xi is unbounded if for every
    equation xj= ...ai.xi ...
    if ai < 0 then xj is not restricted.
    As a result, even if we
    increase the value of xi, it is always
    possible to adjust the value of xj without
    violating a restriction.
 *)

(* let is_unbounded rst  tbl vr =
  IMap.for_all (fun x v -> if Vect.get vr v </ Int 0
                           then not (IMap.mem vr rst)
                           else true
    ) tbl
 *)

type result =
  | Max of Q.t   (** Maximum is reached *)
  | Ubnd of var  (** Problem is unbounded *)
  | Feas         (** Problem is feasible *)

type pivot =
  | Done of result
  | Pivot of int * int * Q.t




type simplex =
  | Opt of tableau * result

(** For a row, x = ao.xo+...+ai.xi
    a valid pivot variable is such that it can improve the value of xi.
    it is the case, if xi is unrestricted (increase if ai> 0, decrease if ai < 0)
                    xi is restricted but ai > 0

This is the entering variable.
 *)

let rec find_pivot_column (rst:Restricted.t) (r:Vect.t)  =
  match Vect.choose r with
  | None -> failwith "find_pivot_column"
  | Some(xi,ai,r') -> if Q.lt ai Q.zero
                   then if Restricted.is_restricted xi rst
                        then find_pivot_column rst r' (* ai.xi cannot be improved *)
                        else  (xi, -1) (* r is not restricted, sign of ai does not matter *)
                   else (* ai is positive, xi can be increased *)
                     (xi,1)

(** Finding the variable leaving the basis is more subtle because we need to:
    - increase the objective function
    - make sure that the entering variable has a feasible value
    - but also that after pivoting all the other basic variables are still feasible.
    This explains why we choose the pivot with the smallest score
 *)

let min_score s (i1,sc1) =
  match s with
  | None  -> Some (i1,sc1)
  | Some(i0,sc0) ->
     if Q.lt sc0 sc1 then s
     else if Q.lt sc1 sc0 then Some (i1,sc1)
     else if i0 < i1 then s else Some(i1,sc1)

let find_pivot_row rst tbl j sgn =
  Restricted.fold rst
    (fun i' v res ->
      let aij = Vect.get j v in
      if Q.(lt (mul (of_int sgn) aij) zero)
      then (* This would improve *)
        let score' = Q.abs (Q.div (Vect.get_cst v) aij) in
        min_score res (i',score')
      else res) tbl None

let safe_find err x t =
  try
    IMap.find x t
  with Not_found ->
        if debug
        then Printf.fprintf stdout "safe_find %s x%i %a\n" err x output_tableau t;
        failwith err


(** [find_pivot vr t] aims at improving the objective function of the basic variable vr *)
let find_pivot vr (rst:Restricted.t) tbl =
  (* Get the objective of the basic variable vr *)
  let v = safe_find "find_pivot"  vr tbl in
  match is_maximised rst v with
  | Some mx -> Done (Max mx) (* Maximum is reached; we are done *)
  | None    ->
     (* Extract the vector *)
     let (_,v) = Vect.decomp_cst v in
     let (j',sgn) = find_pivot_column rst v  in
     match find_pivot_row rst (IMap.remove vr tbl) j' sgn with
     | None -> Done (Ubnd j')
     | Some (i',sc) -> Pivot(i', j', sc)

(** [solve_column c r e]
    @param c  is a non-basic variable
    @param r  is a basic variable
    @param e  is a vector such that r = e
     and e is of the form  ai.c+e'
    @return the vector (-r + e').-1/ai i.e
     c = (r - e')/ai
 *)

let solve_column (c : var) (r : var) (e : Vect.t) :  Vect.t =
  let a = Vect.get c e in
  if Q.(equal zero) a
  then failwith "Cannot solve column"
  else
    let a' = Q.(div minus_one a) in
    Vect.mul a' (Vect.set r Q.minus_one (Vect.set c Q.zero e))

(** [pivot_row r c e]
    @param c is such that c = e
    @param r is a vector r = g.c + r'
    @return g.e+r' *)

let pivot_row (row: Vect.t) (c : var) (e : Vect.t) : Vect.t =
  let g = Vect.get c row in
  if Q.(equal zero) g
  then row
  else Vect.mul_add g e Q.one (Vect.set c Q.zero row)

let pivot_with (m : tableau) (v: var) (p : Vect.t) =
  IMap.map (fun (r:Vect.t) -> pivot_row r v p) m

let pivot (m : tableau) (r : var) (c : var) =
  let row = safe_find "pivot" r m  in
  let piv = solve_column c r row in
  IMap.add c piv (pivot_with (IMap.remove r m) c piv)


let adapt_unbounded vr x rst tbl =
  if Q.geq (Vect.get_cst (IMap.find vr tbl)) Q.zero
  then tbl
  else pivot tbl vr x

module BaseSet = Set.Make(struct type t = iset let compare = IMap.compare (fun x y -> 0) end)

let get_base tbl = IMap.mapi (fun k _ -> ()) tbl

let simplex opt vr rst tbl =
  let b = ref BaseSet.empty in

let rec simplex opt vr rst tbl =

  if debug then begin
      let base = get_base tbl in
      if BaseSet.mem base !b
      then Printf.fprintf stdout "Cycling detected\n"
      else b := BaseSet.add base !b
    end;

  if debug && not (is_feasible rst tbl)
  then
    begin
      let m = unfeasible rst tbl in
      Printf.fprintf stdout "Simplex error\n";
      Printf.fprintf stdout "The current tableau is not feasible\n";
      Printf.fprintf stdout "Restricted >= %a\n" Restricted.pp rst ;
      output_tableau stdout tbl;
      Printf.fprintf stdout "Error for variables %a\n" output_vars m
    end;

  if not opt && Q.geq (Vect.get_cst (IMap.find vr tbl)) Q.zero
  then  Opt(tbl,Feas)
  else
    match find_pivot vr rst tbl with
    | Done r ->
       begin match r with
       | Max _ -> Opt(tbl, r)
       | Ubnd x ->
          let t' = adapt_unbounded vr x rst tbl in
          Opt(t',r)
       | Feas -> raise (Invalid_argument "find_pivot")
       end
    | Pivot(i,j,s) ->
       if debug then begin
           Printf.fprintf stdout "Find pivot for x%i(%s)\n" vr (Q.to_string s);
           Printf.fprintf stdout "Leaving variable x%i\n" i;
           Printf.fprintf stdout "Entering variable x%i\n" j;
         end;
       let m' = pivot tbl i j in
       simplex opt vr rst m' in

simplex opt vr rst tbl



type certificate =
  | Unsat of Vect.t
  | Sat of tableau * var option

(** [normalise_row t v]
    @return a row obtained by pivoting the basic variables of the vector v
 *)

let normalise_row (t : tableau) (v: Vect.t) =
  Vect.fold (fun acc vr ai -> try
        let e = IMap.find vr t in
        Vect.add (Vect.mul ai e) acc
      with Not_found -> Vect.add (Vect.set vr ai Vect.null) acc)
    Vect.null v

let normalise_row (t : tableau) (v: Vect.t) =
  let v' = normalise_row t v in
  if debug then Printf.fprintf stdout "Normalised Optimising %a\n" LinPoly.pp v';
  v'

let add_row (nw :var) (t : tableau) (v : Vect.t) : tableau =
  IMap.add nw (normalise_row t v) t

(** [push_real] performs reasoning over the rationals *)
let push_real (opt : bool) (nw : var) (v : Vect.t) (rst: Restricted.t) (t : tableau) : certificate  =
  if debug
  then begin Printf.fprintf stdout "Current Tableau\n%a\n" output_tableau t;
             Printf.fprintf stdout "Optimising %a=%a\n" LinPoly.pp_var nw LinPoly.pp v
       end;
  match simplex opt nw rst (add_row nw t v) with
  | Opt(t',r) -> (* Look at the optimal *)
     match r with
     | Ubnd x->
        if debug then Printf.printf "The objective is unbounded (variable %a)\n" LinPoly.pp_var x;
        Sat (t',Some x) (* This is sat and we can extract a value *)
     | Feas -> Sat (t',None)
     | Max n ->
        if debug then begin
          Printf.printf "The objective is maximised %s\n" (Q.to_string n);
          Printf.printf "%a = %a\n" LinPoly.pp_var nw pp_row (IMap.find nw t')
          end;

          if Q.(leq zero) n
        then Sat (t',None)
        else
          let v' = safe_find "push_real" nw t' in
          Unsat (Vect.set nw Q.one (Vect.set 0 Q.zero (Vect.mul Q.minus_one v')))


(** One complication is that equalities needs some pre-processing.contents
 *)
open Mutils
open Polynomial

let fresh_var l  =
  1 +
    try
      (ISet.max_elt  (List.fold_left (fun acc c -> ISet.union acc (Vect.variables c.coeffs)) ISet.empty  l))
    with Not_found -> 0


(*type varmap = (int * bool) IMap.t*)


let make_certificate vm l =
  Vect.normalise (Vect.fold (fun acc x n ->
                      let (x',b) = IMap.find x vm in
                      Vect.set x' (if b then  n else Q.neg n) acc) Vect.null l)





let eliminate_equalities (vr0:var) (l:Polynomial.cstr list) =
  let rec elim idx vr vm l acc =
    match l with
    | [] -> (vr,vm,acc)
    | c::l -> match c.op with
              | Ge -> let v = Vect.set 0 (Q.neg c.cst) c.coeffs in
                      elim (idx+1) (vr+1) (IMap.add vr (idx,true) vm) l ((vr,v)::acc)
              | Eq -> let v1 = Vect.set 0 (Q.neg c.cst) c.coeffs in
                      let v2 = Vect.mul Q.minus_one v1 in
                      let vm = IMap.add vr (idx,true) (IMap.add (vr+1) (idx,false) vm) in
                      elim (idx+1) (vr+2) vm l ((vr,v1)::(vr+1,v2)::acc)
              | Gt -> raise Strict in
  elim 0 vr0 IMap.empty l []

let find_solution rst tbl =
  IMap.fold (fun vr v res -> if Restricted.is_restricted vr rst
                             then res
                             else Vect.set vr (Vect.get_cst v) res) tbl Vect.null

let choose_conflict (sol:Vect.t) (l: (var * Vect.t) list) =
  let esol = Vect.set 0 Q.one sol in
  let is_conflict (x,v) =
    if Q.(leq zero) (Vect.dotproduct esol v)
    then None else Some(x,v) in
  let (c,r) = extract is_conflict l in
  match c with
  | Some (c,_) -> Some (c,r)
  | None   -> match l with
              | []   -> None
              | e::l -> Some(e,l)

(*let remove_redundant rst t =
  IMap.fold (fun k v m -> if Restricted.is_restricted k rst && Vect.for_all (fun x _ -> x == 0 || Restricted.is_restricted x rst) v
                          then begin
                              if debug then
                                Printf.printf "%a is redundant\n" LinPoly.pp_var k;
                              IMap.remove k m
                            end
                          else m) t t
 *)


let rec solve opt l (rst:Restricted.t) (t:tableau) =
  let sol = find_solution rst t in
  match choose_conflict sol l with
  | None ->  Inl (rst,t,None)
  | Some((vr,v),l) ->
     match push_real opt vr v (Restricted.set_exc vr rst) t with
     | Sat (t',x) ->
        (*        let t' = remove_redundant rst t' in*)
        begin
        match l with
        | [] -> Inl(rst,t', x)
        |  _ -> solve opt l rst t'
        end
     | Unsat c -> Inr c

let find_unsat_certificate (l : Polynomial.cstr list ) =
  let vr = fresh_var l in
  let (_,vm,l') =  eliminate_equalities vr l  in

  match  solve false l' (Restricted.make vr) IMap.empty  with
  | Inr c ->  Some  (make_certificate vm c)
  | Inl _ -> None



let find_point (l : Polynomial.cstr list) =
  let vr = fresh_var l in
  let (_,vm,l') =  eliminate_equalities vr l  in

  match solve false l' (Restricted.make vr) IMap.empty with
  | Inl (rst,t,_) -> Some (find_solution rst t)
  | _           -> None



let optimise obj l =
  let vr0 = fresh_var l in
  let (_,vm,l') = eliminate_equalities (vr0+1) l in

  let bound pos res =
    match res with
    | Opt(_,Max n) -> Some (if pos then n else Q.neg n)
    | Opt(_,Ubnd _)  -> None
    | Opt(_,Feas)    -> None
  in

  match solve false l' (Restricted.make vr0) IMap.empty with
  | Inl (rst,t,_) ->
     Some (bound false
             (simplex true vr0 rst (add_row vr0 t (Vect.uminus obj))),
           bound true
             (simplex true vr0 rst (add_row vr0 t obj)))
  | _  -> None



open Polynomial

let env_of_list l =
  List.fold_left (fun (i,m) l -> (i+1, IMap.add i l m)) (0,IMap.empty) l


open ProofFormat

let make_farkas_certificate (env: WithProof.t IMap.t) vm v =
  Vect.fold (fun acc x n ->
      add_proof acc
        begin
          try
            let (x',b) = IMap.find x vm in
            (mul_cst_proof
               (if b then n else (Q.neg n))
               (snd (IMap.find x' env)))
          with Not_found -> (* This is an introduced hypothesis *)
            (mul_cst_proof n (snd (IMap.find x env)))
        end) Zero v

let make_farkas_proof (env: WithProof.t IMap.t) vm v =
  Vect.fold (fun wp x n ->
      WithProof.addition wp   begin
          try
            let (x', b) = IMap.find x vm in
            let n =  if b then n else Q.neg n in
            WithProof.mult (Vect.cst n) (IMap.find x' env)
          with Not_found ->
            WithProof.mult (Vect.cst n) (IMap.find x env)
        end) WithProof.zero v

(*
let incr_cut rmin x =
  match rmin with
  | None -> true
  | Some r -> Int.compare x r = 1
 *)

let cut env rmin sol vm (rst:Restricted.t) (x,v) =
(*  if not (incr_cut rmin x)
  then None
  else *)
  let (n,r) = Vect.decomp_cst v in

  let nf = Sos_types.floorQ n in
  if Q.equal nf n
  then None (* The solution is integral *)
  else
    (* This is potentially a cut *)
    let cut = Vect.normalise
                (Vect.fold (fun acc x n ->
                     if Restricted.is_restricted x rst then
                       Vect.set x (Q.sub n (Sos_types.floorQ n)) acc
                     else acc
                   ) Vect.null r) in
    if debug then Printf.fprintf stdout "Cut vector for %a : %a\n" LinPoly.pp_var x LinPoly.pp cut ;
    let cut = make_farkas_proof env vm cut in

    match WithProof.cutting_plane cut  with
    | None ->  None
    | Some (v,prf) ->
       if debug then begin
           Printf.printf "This is a cutting plane:\n" ;
           Printf.printf "%a -> %a\n" WithProof.output cut WithProof.output (v,prf);
         end;
       if Pervasives.(=) (snd v) Eq
       then (* Unsat *) Some (x,(v,prf))
       else if eval_op Ge (Vect.dotproduct (fst v) (Vect.set 0 Q.one sol)) Q.zero
       then begin
           (* Can this happen? *)
           if debug then  Printf.printf "The cut is feasible - drop it\n";
           None
         end
       else Some(x,(v,prf))

let find_cut env u sol vm rst tbl =
  (* find first *)
  IMap.fold (fun x v acc ->
      match acc with
      | None -> cut env u sol  vm rst (x,v)
      | Some c -> acc) tbl None

(*
let find_cut env u sol vm rst tbl =
  IMap.fold (fun x v acc ->
      match acc with
      | Some c -> Some c
      |  None  ->  cut env u sol  vm rst (x,v)
    ) tbl None
 *)

let integer_solver lp =
  let (l,_) = List.split lp in
  let vr0 = fresh_var l in
  let (vr,vm,l') =  eliminate_equalities vr0 l  in

  let _,env = env_of_list (List.map WithProof.of_cstr lp) in

  let insert_row vr v rst tbl =
    match push_real true vr v rst tbl with
    | Sat (t',x) -> Inl (Restricted.restrict vr rst,t',x)
    | Unsat c -> Inr c in

  let rec isolve env cr vr res =
    match res with
    | Inr c -> Some (Step (vr, make_farkas_certificate env vm (Vect.normalise c),Done))
    | Inl (rst,tbl,x) ->
       if debug then begin
           Printf.fprintf stdout "Looking for a cut\n";
           Printf.fprintf stdout "Restricted %a ...\n" Restricted.pp rst;
           Printf.fprintf stdout "Current Tableau\n%a\n" output_tableau tbl;
         end;
       let sol = find_solution rst tbl in

       match find_cut env cr (*x*) sol vm rst tbl with
       | None -> None
       | Some(cr,((v,op),cut)) ->
          if Pervasives.(=) op Eq
          then (* This is a contradiction *)
            Some(Step(vr,CutPrf cut, Done))
          else
            let res = insert_row vr v (Restricted.set_exc vr rst) tbl in
            let prf = isolve (IMap.add vr ((v,op),Def vr) env) (Some cr) (vr+1) res in
            match prf with
            | None -> None
            | Some p -> Some (Step(vr,CutPrf cut,p)) in

  let res = solve true l' (Restricted.make vr0) IMap.empty in
  isolve env None vr res

let integer_solver lp =
  match integer_solver lp with
  | None -> None
  | Some prf -> if debug
                then Printf.fprintf stdout "Proof %a\n" ProofFormat.output_proof prf ;
                Some prf
