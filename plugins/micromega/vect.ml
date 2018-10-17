(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Mutils

(** [t] is the type of vectors.
        A vector [(x1,v1) ; ... ; (xn,vn)] is such that:
        - variables indexes are ordered (x1 < ... < xn
        - values are all non-zero
 *)
type var = int
type t = (var * Q.t) list

(** [equal v1 v2 = true] if the vectors are syntactically equal. *)

let rec equal v1 v2 =
  match v1 , v2 with
  | [] , []   -> true
  | [] , _    -> false
  | _::_ , [] -> false
  | (i1,n1)::v1 , (i2,n2)::v2 ->
     (Int.equal i1 i2) && Q.equal n1 n2 && equal v1 v2

let hash v =
  let rec hash i = function
    | [] -> i
    | (vr,vl)::l ->  hash (i + (Hashtbl.hash (vr, Q.to_float vl))) l in
  Hashtbl.hash (hash 0 v )


let null = []

let is_null v =
  match v with
  | [] -> true
  | [0, z] when Q.(equal zero) z -> true
  | _  -> false

let pp_var_num pp_var o (v,n) =
  if Int.equal v 0
  then if Q.(equal zero) n then ()
       else Printf.fprintf o "%s" (Q.to_string n)
  else
    match n with
    | n when Q.(equal one) n -> pp_var o v
    | n when Q.(equal minus_one) n -> Printf.fprintf o "-%a" pp_var v
    | n when Q.(equal zero) n -> ()
    |  _     -> Printf.fprintf o "%s*%a" (Q.to_string n) pp_var v


let rec pp_gen pp_var o v =
  match v with
  | [] -> output_string o "0"
  | [e] -> pp_var_num pp_var o e
  | e::l -> Printf.fprintf o "%a + %a" (pp_var_num pp_var) e (pp_gen pp_var) l


let pp_var o v = Printf.fprintf o "x%i" v

let pp o v = pp_gen pp_var o v


let from_list (l: Q.t list) =
  let rec xfrom_list i l =
    match l with
    | [] -> []
    | e::l ->
       if not (Q.(equal zero) e)
       then (i,e)::(xfrom_list (i+1) l)
       else xfrom_list (i+1) l in

  xfrom_list 0 l

let to_list m =
  let rec xto_list i l =
    match l with
    | [] -> []
    |	(x,v)::l' ->
         if i = x then v::(xto_list (i+1) l') else Q.zero ::(xto_list (i+1) l) in
  xto_list 0 m


let cons i v rst = if Q.(equal zero) v then rst else (i,v)::rst

let rec update i f t =
  match t with
  | [] -> cons i (f Q.zero) []
  | (k,v)::l ->
     match Int.compare i k with
     | 0 -> cons k (f v) l
     | -1 -> cons i (f Q.zero) t
     |  1 -> (k,v) ::(update i f l)
     |  _  -> failwith "compare_num"

let rec set i n t =
  match t with
  | [] -> cons i n []
  | (k,v)::l ->
     match Int.compare i k with
     | 0 -> cons k n l
     | -1 -> cons i n t
     |  1 -> (k,v) :: (set i n l)
     |  _  -> failwith "compare_num"

let cst n = if Q.(equal zero) n then [] else [0,n]


let mul z t =
  match z with
  | z when Q.(equal zero) z -> []
  | z when Q.(equal one) z -> t
  |  _    -> List.map (fun (i,n) -> (i, Q.mul z n)) t

let div z t =
  if Q.(equal one) z
  then t
  else List.map (fun (x,nx) -> (x, Q.div nx z)) t


let uminus t = List.map (fun (i,n) -> i, Q.neg n) t


let rec add (ve1:t) (ve2:t)  =
  match ve1 , ve2 with
  | [] , v | v , [] -> v
  | (v1,c1)::l1 , (v2,c2)::l2 ->
     let cmp = Pervasives.compare v1 v2 in
     if cmp == 0 then
       let s = Q.add c1 c2 in
       if Q.(equal zero) s
       then add l1 l2
       else (v1,s)::(add l1 l2)
     else if cmp < 0 then (v1,c1) :: (add l1 ve2)
     else (v2,c2) :: (add l2 ve1)


let rec xmul_add (n1: Q.t) (ve1:t) (n2: Q.t) (ve2:t) =
  match ve1 , ve2 with
  | [] , _ -> mul n2 ve2
  | _ , [] -> mul n1 ve1
  | (v1,c1)::l1 , (v2,c2)::l2 ->
     let cmp = Pervasives.compare v1 v2 in
     if cmp == 0 then
       let s = Q.(add (mul n1 c1) (mul n2 c2)) in
       if Q.(equal zero) s
       then xmul_add n1 l1 n2 l2
       else (v1,s)::(xmul_add n1 l1 n2 l2)
     else if cmp < 0 then (v1, Q.mul n1 c1) :: (xmul_add n1 l1 n2 ve2)
     else (v2, Q.mul n2 c2) :: (xmul_add n1 ve1 n2 l2)

let mul_add n1 ve1 n2 ve2 =
  if Q.(equal one) n1 && Q.(equal one) n2
  then add ve1 ve2
  else xmul_add n1 ve1 n2 ve2


let compare : t -> t -> int = Mutils.Cmp.compare_list (fun x y -> Mutils.Cmp.compare_lexical
                                                                    [
                                                                      (fun () -> Int.compare (fst x) (fst y));
                                                                      (fun () -> Q.compare (snd x) (snd y))])

(** [tail v vect] returns
        - [None] if [v] is not a variable of the vector [vect]
        - [Some(vl,rst)]  where [vl] is the value of [v] in vector [vect]
        and [rst] is the remaining of the vector
        We exploit that vectors are ordered lists
 *)
let rec tail (v:var) (vect:t) =
  match vect with
  | [] -> None
  | (v',vl)::vect' ->
     match Int.compare v' v with
     | 0 -> Some (vl,vect) (* Ok, found *)
     | -1 -> tail v vect' (* Might be in the tail *)
     | _  -> None (* Hopeless *)

let get v vect =
  match tail v vect with
  | None       -> Q.zero
  | Some(vl,_) -> vl

let is_constant v =
  match v with
  | [] | [0,_] -> true
  | _ -> false



let get_cst vect =
  match vect with
  | (0,v)::_ -> v
  |   _      -> Q.zero

let choose v =
  match v with
  |  [] -> None
  | (vr,vl)::rst -> Some (vr,vl,rst)


let rec fresh v =
  match v with
  | [] -> 1
  | [v,_] -> v + 1
  | _::v  -> fresh v


let variables v =
  List.fold_left (fun acc (x,_) ->  ISet.add x acc) ISet.empty v

let decomp_cst v =
  match v with
  | (0,vl)::v -> vl,v
  | _  -> Q.zero ,v

let fold f acc v =
  List.fold_left (fun acc (v,i) -> f acc v i) acc v

let fold_error f acc v =
  let rec fold acc v =
    match v with
    | [] -> Some acc
    | (x,i)::v' -> match f acc x i with
                  | None -> None
                  | Some acc' -> fold acc' v' in
  fold acc v



let rec find p v =
  match v with
  | [] -> None
  | (v,n)::v' -> match p v n with
                 | None -> find p v'
                 | Some r -> Some r


let for_all p l =
  List.for_all (fun (v,n) -> p v n) l


let decr_var i v = List.map (fun (v,n) -> (v-i,n)) v
let incr_var i v = List.map (fun (v,n) -> (v+i,n)) v

open Big_int_Z

(* Workaround to removed once https://github.com/ocaml/Zarith/pull/39
   is fixed *)
let fix_gcd c n =
  if Z.(equal c zero) then
    if Z.(equal n zero) then Z.(div zero zero) else n
  else gcd_big_int c n

let gcd v =
  let res = fold (fun c _ n  ->
                assert (Int.equal (compare_big_int (Q.den n) unit_big_int) 0);
                fix_gcd c (Q.num n)) zero_big_int v in
  if Int.equal (compare_big_int res zero_big_int) 0
  then unit_big_int else res

let normalise v =
  let ppcm = fold (fun c _ n -> ppcm c (Q.den n)) unit_big_int v in
  let gcd =
    let gcd = fold (fun c _ n -> fix_gcd c (Q.num n)) unit_big_int v in
    if Int.equal (compare_big_int gcd zero_big_int) 0 then unit_big_int else gcd in
  List.map (fun (x,v) -> (x, Q.(mul v (div (of_bigint ppcm) (of_bigint gcd))))) v

let rec exists2 p vect1 vect2 =
      match vect1 , vect2 with
    | _ , [] | [], _ -> None
    | (v1,n1)::vect1' , (v2, n2) :: vect2' ->
       if Int.equal v1 v2
       then
         if p n1 n2
         then Some (v1,n1,n2)
         else
           exists2 p vect1' vect2'
       else
         if v1 < v2
         then exists2 p vect1' vect2
         else exists2 p vect1 vect2'

let dotproduct v1 v2 =
  let rec dot acc v1 v2 =
    match v1, v2 with
    | [] , _ | _ , [] -> acc
    | (x1,n1)::v1', (x2,n2)::v2' ->
       if x1 == x2
       then dot Q.(add acc (mul n1 n2)) v1' v2'
       else if x1 < x2
       then dot acc v1' v2
       else dot acc v1  v2' in
  dot Q.zero v1 v2
