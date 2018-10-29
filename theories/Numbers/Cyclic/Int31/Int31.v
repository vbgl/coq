(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Fondation Inria, 2018 *)
(************************************************************************)

(** Compatibility layer for CompCert,
      waiting for an update of Menhir using (63- bit) primitive integers. *)

From Coq
Require Export Int63.

Import BinInt.

Local Open Scope int63_scope.

From Coq
Require Extraction.

Extract Constant int => "Uint63.t".
Extract Constant lsl => "Uint63.l_sl".
Extract Constant lsr => "Uint63.l_sr".
Extract Constant Int63.land => "Uint63.l_and".
Extract Constant add => "Uint63.add".
Extract Constant sub => "Uint63.sub".
Extract Constant mul => "Uint63.mul".
Extract Constant eqb => "Uint63.equal".
Extract Constant compare => "(fun x y -> match Uint63.compare x y with 0 -> Eq | n when 0 < n -> Lt | _ -> Gt)".

Variant digits := D0 | D1.

Notation int31 := int.

Notation "'phi' n" := (φ n) (at level 0, only parsing) : int63_scope.
Definition phi_inv n := of_Z n.

Definition incr n : int31 := succ n.

Definition compare31 (n m : int31) := Z.compare (φ n) (φ m).

Definition iter_int31 i A (f: A -> A) a := Wf_nat.iter_nat (Z.abs_nat (φ i)) A f a.

Definition twice n : int31 := mul n 2.
Definition twice_plus_one n : int31 := add (mul n 2) 1.
Definition On : int31 := 0.
Definition In : int31 := 1.

Delimit Scope int63_scope with int31.

(** Not needed with menhir > 20181105 *)
Definition nat_of_int31 (n: int31) : nat := Z.to_nat (φ n).
Global Coercion nat_of_int31 : int31 >-> nat.
