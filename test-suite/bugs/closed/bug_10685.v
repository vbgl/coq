From Coq Require Import ssreflect.

Structure box (T: Type) := Box { sort :> Type ; projector : sort -> T }.

Lemma property T (B: box T) (x: B) :
  projector T B x = projector T B x.
Proof. exact eq_refl. Qed.

Record boxed_nat := BoxNat { unbox_nat : nat }.

Canonical box_nat_box : box nat :=
  {| projector := unbox_nat |}.

Check BoxNat 4 : sort _ (_ : box nat).

Goal forall n : boxed_nat, 0 <= unbox_nat n.
Proof.
  intros [n].
  rewrite property.
  apply le_0_n.
Qed.

Set Primitive Projections.

Record boxed_bool := BoxBool { unbox_bool : bool }.

Canonical box_bool_box : box bool :=
  {| projector := unbox_bool |}.

Check BoxBool true : sort _ (_ : box bool).

Goal forall b : boxed_bool, is_true (unbox_bool b || true).
Proof.
  intros [b].
  rewrite property.
  apply Bool.orb_true_r.
Qed.
