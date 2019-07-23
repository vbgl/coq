Require Import Int63.

Lemma foo : False.
Proof.
set (v := fst (diveucl_21 9305446873517 1793572051078448654 4930380657631323783)).
generalize (eq_refl v) (eqb_refl v).
unfold v at 1 3.
clearbody v.
intros H1.
cbv in H1.
elim H1.
vm_compute.
Fail discriminate.
Abort.
