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

From Coq Require Import ssreflect.
From Coq Require Import Int31.
Import BinInt.
Export Zdiv.

Open Scope int63_scope.
Global Open Scope nat_scope.

Lemma phi_bounded x : (0 <= phi x < 2 ^ (Z.of_nat size))%Z.
Proof. exact: to_Z_bounded. Qed.

Lemma phi_inv_phi x : phi_inv (φ x) = x.
Proof. exact: of_to_Z. Qed.

Lemma spec_0 : φ 0 = 0%Z.
Proof. by []. Qed.

Lemma phi_incr x :
  phi (incr x) = ((Z.succ (phi x)) mod 2^(Z.of_nat size))%Z.
Proof. exact: succ_spec. Qed.

Lemma iter_int31_iter_nat A f i a :
  iter_int31 i A f a = Wf_nat.iter_nat (Z.abs_nat [|i|]) A f a.
Proof. by []. Qed.
