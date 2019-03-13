(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module ISet : Set.S with type elt = int

module IMap :
sig
  include Map.S with type key = int

  (** [from k  m] returns the submap of [m] with keys greater or equal k *)
  val from : key -> 'elt t -> 'elt t

end

module Cmp : sig

  val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int
  val compare_lexical : (unit -> int) list -> int

end

module Tag : sig

  type t

  val pp : out_channel -> t -> unit
  val next : t -> t
  val from : int -> t

end

module TagSet : CSig.SetS with type elt = Tag.t

val pp_list : string -> (out_channel -> 'a -> unit) -> out_channel -> 'a list -> unit

module CamlToCoq : sig

  val positive : int -> Micromega.positive
  val bigint : Z.t -> Micromega.z
  val n : int -> Micromega.n
  val nat : int -> Micromega.nat
  val q : Q.t -> Micromega.q
  val index : int -> Micromega.positive
  val z : int -> Micromega.z
  val positive_big_int : Z.t -> Micromega.positive

end

module CoqToCaml : sig

  val z_big_int : Micromega.z -> Z.t
  val q_to_num : Micromega.q -> Q.t
  val positive : Micromega.positive -> int
  val n : Micromega.n -> int
  val nat : Micromega.nat -> int
  val index : Micromega.positive -> int

end

val ppcm : Z.t -> Z.t -> Z.t

val all_pairs : ('a -> 'a -> 'b) -> 'a list -> 'b list
val try_any : (('a -> 'b option) * 'c) list -> 'a -> 'b option
val is_sublist : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val extract : ('a -> 'b option) -> 'a list -> ('b * 'a) option * 'a list

val extract_all : ('a -> 'b option) -> 'a list -> ('b * 'a) list * 'a list

val iterate_until_stable : ('a -> 'a option) -> 'a -> 'a

val app_funs : ('a -> 'b option) list -> 'a -> 'b option

val command : string -> string array -> 'a -> 'b
