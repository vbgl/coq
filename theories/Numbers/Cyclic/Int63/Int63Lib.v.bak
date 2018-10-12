(*
Require Int63.
Import BinInt.
Import Bool.
Export Int63.
Import Zdiv.
Import Lia.
Import Zpow_facts.
Import Znumtheory.
Import Zcomplements.
Import Utf8.

Local Open Scope int63_scope.
Local Open Scope Z_scope.

Import Znumtheory.
Require Import Zgcd_alt.

(* Subtraction and comparison. *)
Lemma sub_leb x y :
  x ≤ y = true -> 0 ≤ y - x = true.
Proof.
  assert (hx := to_Z_bounded x).
  assert (hy := to_Z_bounded y).
  rewrite !leb_spec, sub_spec.
  intros hle.
  rewrite Z.mod_small by lia.
  change [| 0 |] with 0%Z; lia.
Qed.

Definition int63rw := (leb_spec, sub_spec).

Require Import Znumtheory Zpow_facts Zgcd_alt.
Import Bool.
Import ZArith.

Section UPWARDS_WF.
  From Coq Require Import ssreflect ssrbool.
  Context (ceiling: int).

  Local Lemma rw y : y = ceiling - (ceiling - y).
  Proof.
    apply to_Z_inj.
    rewrite !int63rw.
    z. rewrite !sub_spec.

  Definition bounded_gt (x y: int) := andb (y < x) (x <= ceiling) = true.

  Lemma upwards_wf : well_founded bounded_gt.
  Proof.
    move => x; constructor => y /andP [] _ /sub_leb; clear x.
    rewrite {2} (rw y).
    elim/(well_founded_induction wf): (ceiling - y) => {y} x ih hx; constructor => y /andP [] hy hy'.
    rewrite (rw y).
    apply: ih.
      admit.
    exact: sub_leb.
  Admitted.

End UPWARDS_WF.

Variant isLt x y : Type :=
| NotLt
| IsLt `(x < y = true).

Arguments NotLt {x y}.
Arguments IsLt {x y} _.

Definition isLt_dec x y : isLt x y :=
  (if x < y then IsLt else fun _ => NotLt) eq_refl.

Section FORALLB.
  Context (f: int -> bool) (to: int).

  Axiom argument : forall from, from < to = true -> bounded_gt to (succ from) from.

  Fixpoint forallb_rec (from: int) (h: Acc (bounded_gt to) from) : bool :=
    if f from
    then match isLt_dec from to with
      | NotLt => true
      | IsLt hlt =>
        let 'Acc_intro _ rec := h in
        let x := succ from in
        forallb_rec x (rec _ (argument _ hlt))
      end else false.

  Fixpoint existsb_rec (from: int) (h: Acc (bounded_gt to) from) : bool :=
    if f from
    then true
    else match isLt_dec from to with
      | NotLt => false
      | IsLt hlt =>
        let 'Acc_intro _ rec := h in
        let x := succ from in
        existsb_rec x (rec _ (argument _ hlt))
      end.

End FORALLB.

Definition forallb (f: int -> bool) (from to: int) : bool :=
  forallb_rec f to from (Acc_intro_generator 20 (upwards_wf to) from).

Time Compute forallb (fun b => b ≤ 10000) 1 10000.

Definition existsb (f: int -> bool) (from to: int) : bool :=
  existsb_rec f to from (Acc_intro_generator 20 (upwards_wf to) from).

Local Open Scope int63_scope.
Local Open Scope Z_scope.

Local Open Scope int63_scope.
Local Open Scope Z_scope.

(** translation with Z *)

Lemma Z_of_N_double : forall n, Z_of_N (N.double n) = Z.double (Z_of_N n).
Proof.
 destruct n;simpl;trivial.
Qed.

Lemma Z_of_N_double_plus_one : forall n, Z_of_N (Ndouble_plus_one n) = Zdouble_plus_one (Z_of_N n).
Proof.
 destruct n;simpl;trivial.
Qed.

(* TODO: move_this *)
Lemma orb_true_iff : forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
 split;intros;[apply orb_prop | apply orb_true_intro];trivial.
Qed.

Lemma leb_ltb_eqb : forall x y, ((x <= y) = (x < y) || (x == y))%int63.
Proof.
 intros.
 apply eq_true_iff_eq.
 rewrite -> leb_spec, orb_true_iff, ltb_spec, eqb_spec, <- to_Z_eq;omega.
Qed.


Lemma zn2z_to_Z_pos ih il : 0 <= [||WW ih il||].
Proof.
 simpl zn2z_to_Z;destruct (to_Z_bounded ih);destruct (to_Z_bounded il);auto with zarith.
Qed.



(* lsr lsl *)
Lemma lsl_0_r i: i << 0 = i.
Proof.
 apply to_Z_inj.
 rewrite lsl_spec to_Z_0 Zmult_1_r.
 apply Zmod_small; apply (to_Z_bounded i).
Qed.

Lemma lsl_M_r x i (H: (digits <= i = true)%int63) : x << i = 0%int63.
Proof.
 apply to_Z_inj.
 rewrite lsl_spec to_Z_0.
 rewrite -> leb_spec in H.
 unfold wB; change (Z_of_nat size) with [|digits|].
 replace [|i|] with (([|i|] - [|digits|]) + [|digits|])%Z; try ring.
 rewrite -> Zpower_exp, Zmult_assoc, Z_mod_mult; auto with arith.
 apply Z.le_ge; auto with zarith.
 case (to_Z_bounded digits); auto with zarith.
Qed.

Lemma lsl_add i m n: ((i << m) << n = if n <= m + n then i << (m + n) else 0)%int63.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (to_Z_bounded i); intros H1i H2i.
 generalize (add_le_r m n); case (n <= m + n)%int63; intros H.
   apply to_Z_inj; rewrite -> !lsl_spec, Zmult_mod, Zmod_mod, <- Zmult_mod.
   rewrite <-Zmult_assoc, <- Zpower_exp; auto with zarith.
   apply f_equal2 with (f := Zmod); auto.
   rewrite add_spec Zmod_small; auto with zarith.
 apply to_Z_inj; rewrite -> !lsl_spec, Zmult_mod, Zmod_mod, <- Zmult_mod.
 rewrite <-Zmult_assoc, <- Zpower_exp; auto with zarith.
 unfold wB.
 replace ([|m|] + [|n|])%Z with
         ((([|m|] + [|n|]) - Z_of_nat size) + Z_of_nat size)%Z.
 2: ring.
 rewrite -> Zpower_exp, Zmult_assoc, Z_mod_mult; auto with zarith.
 assert (Z_of_nat size < wB)%Z; auto with zarith.
 apply Zpower2_lt_lin; auto with zarith.
Qed.

Lemma bit_or_split i : (i = (i>>1)<<1 lor bit i 0)%int63.
Proof.
 rewrite bit_eq.
 intros n; rewrite lor_spec.
 rewrite bit_lsl bit_lsr bit_b2i.
 case (to_Z_bounded n); intros Hi _.
 case (Zle_lt_or_eq _ _ Hi).
 2: replace 0%Z with [|0|]; auto; rewrite to_Z_eq.
 2: intros H; rewrite <-H.
 2: replace (0 < 1)%int63 with true; auto.
 intros H; clear Hi.
 case_eq (n == 0).
 rewrite eqb_spec; intros H1; generalize H; rewrite H1; discriminate.
 intros _; rewrite orb_false_r.
 case_eq (n < 1)%int63.
 rewrite ltb_spec to_Z_1; intros HH; contradict HH; auto with zarith.
 intros _.
 generalize (@bit_M i n); case Int63.leb.
 intros H1; rewrite H1; auto.
 intros _.
 case (to_Z_bounded n); intros H1n H2n.
 assert (F1: [|n - 1|] = ([|n|] - 1)%Z).
 rewrite sub_spec Zmod_small; rewrite to_Z_1; auto with zarith.
 generalize (add_le_r 1 (n - 1)); case Int63.leb; rewrite F1 to_Z_1; intros HH.
 replace (1 + (n -1))%int63 with n; auto.
 apply to_Z_inj; rewrite add_spec F1 Zmod_small; rewrite to_Z_1;
  auto with zarith.
 rewrite bit_M; auto; rewrite leb_spec.
 replace [|n|] with wB; try discriminate; auto with zarith.
Qed.

(* is_zero *)
Lemma is_zero_0: is_zero 0 = true.
Proof. apply refl_equal. Qed.

Lemma is_even_0: is_even 0 = true.
Proof. apply refl_equal. Qed.

Lemma is_even_lsl_1 i: is_even (i << 1) = true.
Proof.
 rewrite is_even_bit bit_lsl; auto.
Qed.

(* More land *)

Lemma land_0_l i: 0 land i = 0%int63.
Proof.
 apply bit_eq; intros n.
 rewrite land_spec bit_0; auto.
Qed.

Lemma land_0_r i: i land 0 = 0%int63.
Proof.
 apply bit_eq; intros n.
 rewrite land_spec bit_0 andb_false_r; auto.
Qed.

Lemma land_assoc i1 i2 i3 :
  i1 land (i2 land i3) = i1 land i2 land i3.
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec andb_assoc; auto.
Qed.

Lemma land_comm i j : i land j = j land i.
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec andb_comm; auto.
Qed.

Lemma lor_comm i1 i2 : i1 lor i2 = i2 lor i1.
Proof.
 apply bit_eq; intros n.
 rewrite !lor_spec orb_comm; auto.
Qed.

Lemma lor_assoc i1 i2 i3 :
  i1 lor (i2 lor i3) = i1 lor i2 lor i3.
Proof.
 apply bit_eq; intros n.
 rewrite !lor_spec orb_assoc; auto.
Qed.

Lemma land_lor_distrib_r i1 i2 i3 :
 i1 land (i2 lor i3) = (i1 land i2) lor (i1 land i3).
Proof.
 apply bit_eq; intros n.
 rewrite -> !land_spec, !lor_spec, !land_spec, andb_orb_distrib_r; auto.
Qed.

Lemma land_lor_distrib_l i1 i2 i3 :
 (i1 lor i2) land i3 = (i1 land i3) lor (i2 land i3).
Proof.
 apply bit_eq; intros n.
 rewrite -> !land_spec, !lor_spec, !land_spec, andb_orb_distrib_l; auto.
Qed.

Lemma lor_land_distrib_r i1 i2 i3:
  i1 lor (i2 land i3) = (i1 lor i2) land (i1 lor i3).
Proof.
 apply bit_eq; intros n.
 rewrite -> !land_spec, !lor_spec, !land_spec, orb_andb_distrib_r; auto.
Qed.

Lemma lor_land_distrib_l i1 i2 i3:
  (i1 land i2) lor i3 = (i1 lor i3) land (i2 lor i3).
Proof.
 apply bit_eq; intros n.
 rewrite -> !land_spec, !lor_spec, !land_spec, orb_andb_distrib_l; auto.
Qed.

Lemma absoption_land i1 i2 : i1 land (i1 lor i2) = i1.
Proof.
 apply bit_eq; intros n.
 rewrite -> land_spec, lor_spec, absoption_andb; auto.
Qed.

Lemma absoption_lor i1 i2: i1 lor (i1 land i2) = i1.
Proof.
 apply bit_eq; intros n.
 rewrite -> lor_spec, land_spec, absoption_orb; auto.
Qed.

Lemma land_lsl i1 i2 i: (i1 land i2) << i = (i1 << i) land (i2 << i).
Proof.
 apply bit_eq; intros n.
 rewrite -> land_spec, !bit_lsl, land_spec.
 case (_ || _); auto.
Qed.

Lemma lor_lsl i1 i2 i: (i1 lor i2) << i = (i1 << i) lor (i2 << i).
Proof.
 apply bit_eq; intros n.
 rewrite -> lor_spec, !bit_lsl, lor_spec.
 case (_ || _); auto.
Qed.

Lemma lxor_lsl i1 i2 i: (i1 lxor i2) << i = (i1 << i) lxor (i2 << i).
Proof.
 apply bit_eq; intros n.
 rewrite -> lxor_spec, !bit_lsl, lxor_spec.
 case (_ || _); auto.
Qed.

Lemma land_lsr i1 i2 i: (i1 land i2) >> i = (i1 >> i) land (i2 >> i).
Proof.
 apply bit_eq; intros n.
 rewrite -> land_spec, !bit_lsr, land_spec.
 case (_ <= _)%int63; auto.
Qed.

Lemma lxor_lsr i1 i2 i: (i1 lxor i2) >> i = (i1 >> i) lxor (i2 >> i).
Proof.
 apply bit_eq; intros n.
 rewrite -> lxor_spec, !bit_lsr, lxor_spec.
 case (_ <= _)%int63; auto.
Qed.

Lemma is_even_and i j : is_even (i land j) = is_even i || is_even j.
Proof.
 rewrite -> !is_even_bit, land_spec; case bit; auto.
Qed.

Lemma is_even_or i j : is_even (i lor j) = is_even i && is_even j.
Proof.
 rewrite -> !is_even_bit, lor_spec; case bit; auto.
Qed.

Lemma is_even_xor i j : is_even (i lxor j) = negb (xorb (is_even i) (is_even j)).
Proof.
 rewrite -> !is_even_bit, lxor_spec; do 2 case bit; auto.
Qed.

Lemma is_even_add x y :
  is_even (x + y) = negb (xorb (negb (is_even x)) (negb (is_even y))).
Proof.
 assert (F : [|x + y|] mod 2 = ([|x|] mod 2 + [|y|] mod 2) mod 2).
  assert (F1: (2 | wB)) by (apply Zpower_divide; apply refl_equal).
  assert (F2: 0 < wB) by (apply refl_equal).
  case (to_Z_bounded x); intros H1x H2x.
  case (to_Z_bounded y); intros H1y H2y.
  rewrite -> add_spec, <-Zmod_div_mod; auto with zarith.
  rewrite -> (Z_div_mod_eq [|x|] 2) at 1; auto with zarith.
  rewrite -> (Z_div_mod_eq [|y|] 2) at 1; auto with zarith.
  rewrite Zplus_mod.
  rewrite -> Zmult_comm, (fun x => Zplus_comm (x * 2)), Z_mod_plus; auto with zarith.
  rewrite -> Zmult_comm, (fun x => Zplus_comm (x * 2)), Z_mod_plus; auto with zarith.
  rewrite -> !Zmod_mod, <-Zplus_mod; auto.
 generalize (is_even_spec (x + y)) (is_even_spec x) (is_even_spec y).
 do 3 case is_even; auto; rewrite F; intros H1 H2 H3;
  generalize H1; rewrite H2 H3; try discriminate.
Qed.

Lemma bit_add_0 x y: bit (x + y) 0 = xorb (bit x 0) (bit y 0).
Proof.
 rewrite <-(fun x => (negb_involutive (bit x 0))).
 rewrite <-is_even_bit, is_even_add, !is_even_bit.
 do 2 case bit; auto.
Qed.



Lemma lxor_comm: forall i1 i2 : int, i1 lxor i2 = i2 lxor i1.
Proof.
 intros;apply bit_eq;intros.
 rewrite !lxor_spec;apply xorb_comm.
Qed.

Lemma lxor_assoc: forall i1 i2 i3 : int, i1 lxor (i2 lxor i3) = i1 lxor i2 lxor i3.
Proof.
 intros;apply bit_eq;intros.
 rewrite -> !lxor_spec, xorb_assoc;trivial.
Qed.

Lemma lxor_0_l : forall i, 0 lxor i = i.
Proof.
  intros;apply bit_eq;intros.
  rewrite -> lxor_spec, bit_0, xorb_false_l;trivial.
Qed.

Lemma lxor_0_r : forall i, i lxor 0 = i.
Proof.
 intros;rewrite lxor_comm;apply lxor_0_l.
Qed.

Lemma lxor_nilpotent: forall i, i lxor i = 0%int63.
Proof.
 intros;apply bit_eq;intros.
 rewrite -> lxor_spec, xorb_nilpotent, bit_0;trivial.
Qed.

Lemma lor_0_l : forall i, 0 lor i = i.
Proof.
  intros;apply bit_eq;intros.
  rewrite -> lor_spec, bit_0, orb_false_l;trivial.
Qed.

Lemma lor_0_r : forall i, i lor 0 = i.
Proof.
 intros;rewrite lor_comm;apply lor_0_l.
Qed.

Lemma reflect_leb : forall i j, reflect ([|i|] <= [|j|])%Z (i <= j)%int63.
Proof.
 intros; apply iff_reflect.
 symmetry;apply leb_spec.
Qed.

Lemma reflect_eqb : forall i j, reflect (i = j)%Z (i == j).
Proof.
 intros; apply iff_reflect.
 symmetry;apply eqb_spec.
Qed.

Lemma reflect_ltb : forall i j, reflect ([|i|] < [|j|])%Z (i < j)%int63.
Proof.
 intros; apply iff_reflect.
 symmetry;apply ltb_spec.
Qed.

Lemma lsr_is_even_eq : forall i j,
  i >> 1 = j >> 1 ->
  is_even i = is_even j ->
  i = j.
Proof.
 intros;apply bit_eq.
 intros n;destruct (reflect_eqb n 0).
 rewrite <- (negb_involutive (bit i n)), <- (negb_involutive (bit j n)).
 rewrite -> e, <- !is_even_bit, H0;trivial.
 assert (W1 : [|n|] <> 0) by (intros Heq;apply n0;apply to_Z_inj;trivial).
 assert (W2 := to_Z_bounded n);clear n0.
 assert (W3 : [|n-1|] = [|n|] - 1).
   rewrite -> sub_spec, to_Z_1, Zmod_small;trivial;omega.
 assert (H1 : n = ((n-1)+1)%int63).
   apply to_Z_inj;rewrite -> add_spec, W3.
   rewrite Zmod_small;rewrite to_Z_1; omega.
 destruct (reflect_ltb (n-1) digits).
  rewrite <- ltb_spec in l.
  rewrite -> H1, <- !bit_half, H;trivial.
 assert ((digits <= n)%int63 = true).
  rewrite leb_spec;omega.
 rewrite !bit_M;trivial.
Qed.

Lemma lsr1_bit : forall i k, (bit i k >> 1 = 0)%int63.
Proof.
 intros;destruct (bit i k);trivial.
Qed.

Lemma bit_xor_split: forall i : int, i = (i >> 1) << 1 lxor bit i 0.
Proof.
 intros.
 rewrite -> bit_or_split at 1.
 apply lsr_is_even_eq.
 rewrite -> lxor_lsr, lor_lsr, lsr1_bit, lxor_0_r, lor_0_r;trivial.
 rewrite -> is_even_or, is_even_xor.
 rewrite is_even_lsl_1;trivial.
 rewrite -> (xorb_true_l (is_even (bit i 0))), negb_involutive;trivial.
Qed.

(** Order *)
Local Open Scope int63_scope.

Lemma succ_max_int : forall x,
  (x < max_int)%int63 = true -> (0 < x + 1)%int63 = true.
Proof.
 intros x;rewrite -> ltb_spec, ltb_spec, add_spec.
 intros; assert (W:= to_Z_bounded x); assert (W1:= to_Z_bounded max_int).
 change [|0|] with 0%Z;change [|1|] with 1%Z.
 rewrite Zmod_small;omega.
Qed.

Lemma leb_max_int : forall x, (x <= max_int)%int63 = true.
Proof.
 intros x;rewrite leb_spec;assert (W:= to_Z_bounded x).
 change [|max_int|] with (wB - 1)%Z;omega.
Qed.

Lemma leb_0 : forall x, 0 <= x = true.
Proof.
 intros x;rewrite leb_spec;destruct (to_Z_bounded x);trivial.
Qed.

Lemma ltb_0 : forall x, ~ (x < 0 = true).
Proof.
 intros x;rewrite -> ltb_spec, to_Z_0;destruct (to_Z_bounded x);omega.
Qed.

Lemma leb_trans : forall x y z, x <= y = true ->  y <= z = true -> x <= z = true.
Proof.
 intros x y z;rewrite !leb_spec;apply Z.le_trans.
Qed.

Lemma ltb_trans : forall x y z, x < y = true ->  y < z = true -> x < z = true.
Proof.
 intros x y z;rewrite !ltb_spec;apply Zlt_trans.
Qed.

Lemma ltb_leb_trans : forall x y z, x < y = true ->  y <= z = true -> x < z = true.
Proof.
 intros x y z;rewrite -> leb_spec, !ltb_spec;apply Z.lt_le_trans.
Qed.

Lemma leb_ltb_trans : forall x y z, x <= y = true ->  y < z = true -> x < z = true.
Proof.
 intros x y z;rewrite -> leb_spec, !ltb_spec;apply Z.le_lt_trans.
Qed.

Lemma gtb_not_leb : forall n m, m < n = true -> ~(n <= m = true).
Proof.
 intros n m; rewrite -> ltb_spec, leb_spec;omega.
Qed.

Lemma leb_not_gtb : forall n m, m <= n = true -> ~(n < m = true).
Proof.
 intros n m; rewrite -> ltb_spec, leb_spec;omega.
Qed.

Lemma leb_refl : forall n, n <= n = true.
Proof.
 intros n;rewrite leb_spec;apply Zle_refl.
Qed.

Lemma leb_negb_gtb : forall x y, x <= y = negb (y < x).
Proof.
 intros x y;apply Bool.eq_true_iff_eq;split;intros.
 apply Bool.eq_true_not_negb;apply leb_not_gtb;trivial.
 rewrite -> Bool.negb_true_iff, <- Bool.not_true_iff_false in H.
 rewrite leb_spec; rewrite -> ltb_spec in H;omega.
Qed.

Lemma ltb_negb_geb : forall x y, x < y = negb (y <= x).
Proof.
 intros;rewrite -> leb_negb_gtb, Bool.negb_involutive;trivial.
Qed.

Lemma to_Z_sub_gt : forall x y, y <= x = true -> [|x - y|] = ([|x|] - [|y|])%Z.
Proof.
 intros x y;assert (W:= to_Z_bounded x);assert (W0:= to_Z_bounded y);
   rewrite leb_spec;intros;rewrite -> sub_spec, Zmod_small;omega.
Qed.

Lemma not_0_ltb : forall x, x <> 0 <-> 0 < x = true.
Proof.
 intros x;rewrite -> ltb_spec, to_Z_0;assert (W:=to_Z_bounded x);split.
 intros Hd;assert ([|x|] <> 0)%Z;[ | omega].
   intros Heq;elim Hd;apply to_Z_inj;trivial.
 intros Hlt Heq;elimtype False.
 assert ([|x|] = 0)%Z;[ rewrite -> Heq, to_Z_0;trivial | omega].
Qed.

Lemma not_ltb_refl : forall i, ~(i < i = true).
Proof.
 intros;rewrite ltb_spec;omega.
Qed.

Lemma to_Z_sub_1 : forall x y, y < x = true -> ([| x - 1|] = [|x|] - 1)%Z.
Proof.
 intros;apply to_Z_sub_gt.
 generalize (leb_ltb_trans _ _ _ (leb_0 y) H).
 rewrite -> ltb_spec, leb_spec, to_Z_0, to_Z_1;auto with zarith.
Qed.

Lemma to_Z_sub_1_diff : forall x, x <> 0 -> ([| x - 1|] = [|x|] - 1)%Z.
Proof.
  intros x;rewrite not_0_ltb;apply to_Z_sub_1.
Qed.

Lemma to_Z_add_1 : forall x y, x < y = true -> [|x+1|] = ([|x|] + 1)%Z.
Proof.
  intros x y;assert (W:= to_Z_bounded x);assert (W0:= to_Z_bounded y);
   rewrite ltb_spec;intros;rewrite -> add_spec, to_Z_1, Zmod_small;omega.
Qed.

Lemma ltb_leb_sub1 : forall x i,  x <> 0 -> (i < x = true <-> i <= x - 1 = true).
Proof.
 intros x i Hdiff.
 rewrite -> ltb_spec, leb_spec, to_Z_sub_1_diff;trivial.
 split;auto with zarith.
Qed.

Lemma ltb_leb_add1 : forall x y i, i < y = true -> (i < x = true <-> i + 1 <= x = true).
Proof.
 intros x y i Hlt.
 rewrite -> ltb_spec, leb_spec.
 rewrite (to_Z_add_1 i y);trivial.
 split;auto with zarith.
Qed.

Lemma int_ind : forall (P:int -> Type),
  P 0%int63 ->
  (forall i, (i < max_int)%int63 = true -> P i -> P (i + 1)%int63) ->
  forall i, P i.
Proof.
 intros P HP0 Hrec.
 assert (forall z, (0 <= z)%Z -> forall i, z = [|i|] -> P i).
 intros z H;pattern z;apply natlike_rec2;intros;trivial.
 rewrite <- (of_to_Z i), <- H0;exact HP0.
 assert (W:= to_Z_bounded i).
 assert ([|i - 1|] = [|i|] - 1)%Z.
  rewrite -> sub_spec, Zmod_small;rewrite to_Z_1;auto with zarith.
 assert (i = i - 1 + 1)%int63.
  apply to_Z_inj.
  rewrite -> add_spec, H2.
  rewrite Zmod_small;rewrite to_Z_1;auto with zarith.
 rewrite H3;apply Hrec.
 rewrite -> ltb_spec, H2;change [|max_int|] with (wB - 1)%Z;auto with zarith.
 apply X;auto with zarith.
 intros;apply (X [|i|]);trivial.
 destruct (to_Z_bounded i);trivial.
Qed.

Lemma int_ind_bounded : forall (P:int-> Type) min max,
  min <= max =true ->
  P max ->
  (forall i, min <= i + 1 = true-> i < max =true-> P (i + 1) -> P i) ->
  P min.
Proof.
 intros P min max Hle.
 intros Hmax Hrec.
 assert (W1:= to_Z_bounded max);assert (W2:= to_Z_bounded min).
 assert (forall z, (0 <= z)%Z -> (z <= [|max|] - [|min|])%Z  -> forall i, z = [|i|] -> P (max - i)%int63).
 intros z H1;pattern z;apply natlike_rec2;intros;trivial.
 assert (max - i = max)%int63.
  apply to_Z_inj;rewrite -> sub_spec, <- H0, Zminus_0_r, Zmod_small;auto using to_Z_bounded.
 rewrite H2;trivial.
 assert (W3:= to_Z_bounded i);apply Hrec.
 rewrite -> leb_spec,add_spec, sub_spec, to_Z_1, (Zmod_small ([|max|] - [|i|])), Zmod_small;auto with zarith.
 rewrite -> ltb_spec, sub_spec, Zmod_small;auto with zarith.
 assert (max - i + 1 = max - (i - 1))%int63.
  apply to_Z_inj;rewrite -> add_spec, !sub_spec, to_Z_1.
  rewrite (Zmod_small ([|max|] - [|i|]));auto with zarith.
  rewrite (Zmod_small ([|i|] - 1));auto with zarith.
  apply f_equal2;auto with zarith.
 rewrite H3;apply X;auto with zarith.
 rewrite -> sub_spec, to_Z_1, <- H2, Zmod_small;auto with zarith.
 rewrite -> leb_spec in Hle;assert (min = max - (max - min))%int63.
  apply to_Z_inj.
  rewrite -> !sub_spec, !Zmod_small;auto with zarith.
  rewrite Zmod_small;auto with zarith.
 rewrite H;apply (X [| max - min |]);trivial;rewrite -> sub_spec, Zmod_small;auto with zarith.
Qed.

(*
Lemma foldi_cont_ZInd : forall A B (P: Z -> (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) min max cont,
   (forall z, ([|max|] < z)%Z -> P z cont) ->
   (forall i cont, min <= i = true -> i <= max = true -> P ([|i|] + 1)%Z cont -> P [|i|] (f i cont)) ->
   P [|min|] (foldi_cont f min max cont).
Proof.
 intros A B P f min max cont Ha Hf.
 assert (Bmax:= to_Z_bounded max);assert (Bmin:= to_Z_bounded min).
 case_eq (min <= max);intros Heq.
 generalize (leb_refl min).
 assert (P ([|max|] + 1)%Z cont) by (apply Ha;auto with zarith).
 clear Ha;revert cont H.
 pattern min at 2 3 4;apply int_ind_bounded with max;trivial.
 intros;rewrite foldi_cont_eq;auto using leb_refl.
 intros i Hle Hlt Hr cont Hcont Hle'.
 rewrite foldi_cont_lt;[ | trivial].
 apply Hf;trivial. rewrite leb_spec;rewrite ltb_spec in Hlt;auto with zarith.
 assert ([|i|] + 1 = [|i + 1|])%Z.
  rewrite ltb_spec in Hlt;assert (W:= to_Z_bounded i);rewrite add_spec, to_Z_1, Zmod_small;omega.
 rewrite H;apply Hr;trivial.
 assert (max < min = true) by (rewrite ltb_negb_geb,Heq;trivial).
 rewrite foldi_cont_gt;trivial;apply Ha;rewrite <- ltb_spec;trivial.
Qed.
*)

Lemma of_Z_spec : forall z, [|of_Z z|] = z mod wB.
Proof.
 unfold of_Z;destruct z.
 assert (W:= to_Z_bounded 0);rewrite Zmod_small;trivial.
 apply of_pos_spec.
 rewrite opp_spec, of_pos_spec.
 rewrite <- Zmod_opp_opp.
 change (- Zpos p)%Z with (Zneg p).
 destruct (Z_eq_dec (Zneg p mod wB) 0).
 rewrite e, Z_mod_zero_opp_r;trivial.
 rewrite Z_mod_nz_opp_r, Zminus_mod, Z_mod_same_full, Zmod_mod, Zminus_0_r, Zmod_mod;trivial.
Qed.

Lemma foldi_cont_Ind : forall A B (P: int -> (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) min max cont,
   max < max_int = true ->
   (forall z, max < z = true -> P z cont) ->
   (forall i cont, min <= i = true -> i <= max = true -> P (i + 1) cont -> P i (f i cont)) ->
   P min (foldi_cont f min max cont).
Proof.
 intros.
 set (P' z cont := (0 <= z < wB)%Z -> P (of_Z z) cont).
 assert (P' [|min|] (foldi_cont f min max cont)).
 apply foldi_cont_ZInd;unfold P';intros.
 assert ([|(of_Z z)|] = z).
  rewrite of_Z_spec, Zmod_small;trivial.
 apply H0;rewrite ltb_spec, H4;trivial.
 rewrite of_to_Z;apply H1;trivial.
 assert (i < max_int = true).
   apply leb_ltb_trans with max;trivial.
 rewrite <- (to_Z_add_1 _ _ H6), of_to_Z in H4;apply H4.
 apply to_Z_bounded.
 unfold P' in H2;rewrite of_to_Z in H2;apply H2;apply to_Z_bounded.
Qed.

Lemma foldi_cont_ind : forall A B (P: (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) min max cont,
   P cont ->
   (forall i cont, min <= i = true -> i <= max = true -> P cont -> P (f i cont)) ->
   P (foldi_cont f min max cont).
Proof.
 intros A B P f min max cont Ha Hf.
 set (P2 := fun (z:Z) b => P b);change (P2 [|min|] (foldi_cont f min max cont)).
 apply foldi_cont_ZInd;trivial.
Qed.

Lemma foldi_ZInd : forall A (P : Z -> A -> Prop) f min max a,
  (max < min = true -> P ([|max|] + 1)%Z a) ->
  P [|min|] a ->
  (forall i a, min <= i = true -> i <= max = true ->
      P [|i|] a -> P ([|i|] + 1)%Z (f i a)) ->
  P ([|max|]+1)%Z (foldi f min max a).
Proof.
 unfold foldi;intros A P f min max a Hlt;intros.
 set (P' z cont :=
       if Zlt_bool [|max|] z then cont = (fun a0 : A => a0)
       else forall a, P z a -> P ([|max|]+1)%Z (cont a)).
 assert (P' [|min|] (foldi_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f i a0)) min
                       max (fun a0 : A => a0))).
 apply foldi_cont_ZInd;intros;red.
 rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
 case_eq (Zlt_bool [|max|] [|i|]);intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H2;elimtype False;omega.
 clear H4; revert H3;unfold P'.
 case_eq (Zlt_bool [|max|] ([|i|] + 1));intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|max|]) by (rewrite leb_spec in H2;omega).
  rewrite H4, <- H6;apply H0;trivial.
 revert H1;unfold P'.
 case_eq (Zlt_bool [|max|] [|min|]);auto.
 rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite foldi_cont_gt;auto.
Qed.

Lemma foldi_Ind : forall A (P : int -> A -> Prop) f min max a,
  (max < max_int = true) ->
  (max < min = true -> P (max + 1) a) ->
  P min a ->
  (forall i a, min <= i = true -> i <= max = true ->
      P i a -> P (i + 1) (f i a)) ->
  P (max+1) (foldi f min max a).
Proof.
 intros.
 set (P' z a := (0 <= z < wB)%Z -> P (of_Z z) a).
 assert (W:= to_Z_add_1 _ _ H).
 assert (P' ([|max|]+1)%Z (foldi f min max a)).
 apply foldi_ZInd;unfold P';intros.
 rewrite <- W, of_to_Z;auto.
 rewrite of_to_Z;trivial.
 assert (i < max_int = true).
   apply leb_ltb_trans with max;trivial.
 rewrite <- (to_Z_add_1 _ _ H7), of_to_Z;apply H2;trivial.
 rewrite of_to_Z in H5;apply H5;apply to_Z_bounded.
 unfold P' in H3;rewrite <- W, of_to_Z in H3;apply H3;apply to_Z_bounded.
Qed.

Lemma foldi_ind : forall A (P: A -> Prop) (f:int -> A -> A) min max a,
   P a ->
   (forall i a, min <= i = true -> i <= max = true -> P a -> P (f i a)) ->
   P (foldi f min max a).
Proof.
 unfold foldi;intros A P f min max a Ha Hr;revert a Ha.
 apply foldi_cont_ind;auto.
Qed.

Lemma fold_ind : forall A (P: A -> Prop) (f: A -> A) min max a,
   P a -> (forall a, P a -> P (f a)) -> P (fold f min max a).
Proof.
 unfold fold;intros A P f min max a Ha Hr;revert a Ha.
 apply foldi_cont_ind;auto.
Qed.

Lemma foldi_down_cont_ZInd :
   forall A B (P: Z -> (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) max min cont,
   (forall z, (z < [|min|])%Z -> P z cont) ->
   (forall i cont, min <= i = true -> i <= max = true -> P ([|i|] - 1)%Z cont -> P [|i|] (f i cont)) ->
   P [|max|] (foldi_down_cont f max min cont).
Proof.
 intros A B P f max min cont Ha Hf.
 assert (Bmax:= to_Z_bounded max);assert (Bmin:= to_Z_bounded min).
 case_eq (min <= max);intros Heq.
 generalize (leb_refl max).
 assert (P ([|min|] -1)%Z cont) by (apply Ha;auto with zarith).
 clear Ha;revert cont H Heq.
 pattern max at 1 2 4 5;apply int_ind;trivial.
 intros; assert (0 = min).
   apply to_Z_inj;revert Heq;rewrite leb_spec, to_Z_0;omega.
 rewrite foldi_down_cont_eq;subst;auto.
 intros i Hmaxi Hr cont Hcont Hmin Hmax.
 generalize Hmin;rewrite leb_ltb_eqb;case_eq (min < i+1);simpl;intros Hlt Hmin'.
 rewrite foldi_down_cont_gt;[ | trivial].
 apply Hf;trivial.
 assert ([|i|] + 1 = [|i + 1|])%Z.
   assert (W:= to_Z_bounded i);rewrite ltb_spec in Hmaxi;
    assert (W2 := to_Z_bounded max_int);rewrite add_spec, to_Z_1, Zmod_small;auto with zarith.
 assert (i + 1 - 1 = i).
  rewrite leb_spec in *;rewrite ltb_spec in *.
  assert (W1:= to_Z_bounded i); apply to_Z_inj;rewrite sub_spec,to_Z_1, Zmod_small;try omega.
 assert ([|i|] = [|i+1|]-1)%Z.
   rewrite <- H;ring.
 rewrite <- H1, H0;apply Hr;trivial.
 rewrite ltb_spec in Hlt;rewrite leb_spec;omega.
 rewrite leb_spec in Hmax |- *;omega.
 rewrite eqb_spec in Hmin';subst;rewrite foldi_down_cont_eq;auto.
 assert (max < min = true) by (rewrite ltb_negb_geb,Heq;trivial).
 rewrite foldi_down_cont_lt;trivial.
 apply Ha;rewrite <- ltb_spec;trivial.
Qed.

Lemma foldi_down_cont_ind : forall A B (P: (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) max min cont,
   P cont ->
   (forall i cont, min <= i = true -> i <= max = true -> P cont -> P (f i cont)) ->
   P (foldi_down_cont f max min cont).
Proof.
 intros A B P f max min cont Ha Hf.
 set (P2 := fun (z:Z) b => P b);change (P2 [|max|] (foldi_down_cont f max min cont)).
 apply foldi_down_cont_ZInd;trivial.
Qed.

Lemma foldi_down_ZInd :
   forall A (P: Z -> A -> Prop) (f:int -> A -> A) max min a,
   (max < min = true -> P ([|min|] - 1)%Z a) ->
   (P [|max|] a) ->
   (forall i a, min <= i = true -> i <= max = true -> P [|i|]%Z a -> P ([|i|]-1)%Z (f i a)) ->
   P ([|min|] - 1)%Z (foldi_down f max min a).
Proof.
 unfold foldi_down;intros A P f max min a Hlt;intros.
 set (P' z cont :=
       if Zlt_bool z [|min|] then cont = (fun a0 : A => a0)
       else forall a, P z a -> P ([|min|] - 1)%Z (cont a)).
 assert (P' [|max|] (foldi_down_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f i a0)) max
                       min (fun a0 : A => a0))).
 apply foldi_down_cont_ZInd;intros;red.
 rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
 case_eq (Zlt_bool [|i|] [|min|]);intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H1;elimtype False;omega.
 clear H4;revert H3;unfold P'.
 case_eq (Zlt_bool ([|i|] - 1) [|min|]);intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|min|]) by (rewrite leb_spec in H1;omega).
  rewrite H4, <- H6. apply H0;trivial.
 revert H1;unfold P'.
 case_eq (Zlt_bool [|max|] [|min|]);auto.
 rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite foldi_down_cont_lt;auto.
Qed.

Lemma foldi_down_ind : forall A (P: A -> Prop) (f:int -> A -> A) max min a,
   P a ->
   (forall i a, min <= i = true -> i <= max = true -> P a -> P (f i a)) ->
   P (foldi_down f max min a).
Proof.
 unfold foldi_down;intros A P f max min a Ha Hr;revert a Ha.
 apply foldi_down_cont_ind;auto.
Qed.

Lemma fold_down_ind : forall A (P: A -> Prop) (f: A -> A) max min a,
   P a -> (forall a, P a -> P (f a)) -> P (fold_down f max min a).
Proof.
 unfold fold_down;intros A P f max min a Ha Hr;revert a Ha.
 apply foldi_down_cont_ind;auto.
Qed.

Lemma foldi_down_Ind :
   forall A (P: int -> A -> Prop) (f:int -> A -> A) max min a,
   0 < min = true ->
   (max < min = true -> P (min - 1) a) ->
   (P max a) ->
   (forall i a, min <= i = true -> i <= max = true -> P i a -> P (i - 1) (f i a)) ->
   P (min - 1) (foldi_down f max min a).
Proof.
 intros.
 set (P' z a := (0 <= z < wB)%Z -> P (of_Z z) a).
 assert (W:= to_Z_sub_1 _ _ H).
 assert (P' ([|min|]-1)%Z (foldi_down f max min a)).
 apply foldi_down_ZInd;unfold P';intros.
 rewrite <- W, of_to_Z;auto.
 rewrite of_to_Z;trivial.
 assert (0 < i = true).
   apply ltb_leb_trans with min;trivial.
 rewrite <- (to_Z_sub_1 _ _ H7), of_to_Z;apply H2;trivial.
 rewrite of_to_Z in H5;apply H5;apply to_Z_bounded.
 unfold P' in H3;rewrite <- W, of_to_Z in H3;apply H3;apply to_Z_bounded.
Qed.

Lemma foldi_down_min :
  forall A f min max (a:A),
  min < max_int = true->
  (min <= max) = true ->
  foldi_down f max min a = f min (foldi_down f max (min + 1) a).
Proof.
  intros.
  set (P:= fun i => i <= max - min = true ->
       forall a, foldi_down f (min + i) min a = f min (foldi_down f (min + i) (min + 1) a)).
  assert (min < min + 1 = true).
   rewrite ltb_leb_add1 with (y:=max_int), leb_refl;trivial.
  assert (P (max - min)).
    apply int_ind;unfold P.
      replace (min + 0) with min.
      intros _ a'; rewrite foldi_down_eq, foldi_down_lt;trivial.
      apply to_Z_inj;rewrite add_spec, to_Z_0, Zplus_0_r, Zmod_small;auto using to_Z_bounded.
    intros i Hi Hrec Hi1 a'.
    rewrite add_assoc.
    assert (Wi:= to_Z_add_1 _ _ Hi).
    assert (Wmin:= to_Z_add_1 _ _ H).
    assert ((min + 1) <= (min + i + 1) = true).
      assert (W1 := to_Z_bounded min); assert (W2:= to_Z_bounded max); assert (W3:= to_Z_bounded i).
      replace (min + i + 1) with (min + 1 + i).
      rewrite leb_spec, (add_spec (min+1)).
      unfold is_true in Hi1;rewrite leb_spec in *; rewrite ltb_spec in *.
      rewrite sub_spec in Hi1;rewrite Zmod_small in Hi1;[ | omega].
      rewrite Zmod_small;omega.
      rewrite <- !add_assoc, (add_comm 1 i);trivial.
    rewrite leb_ltb_eqb in H2;revert H2.
    case_eq (min + 1 < min + i + 1).
      intros Hlt _;rewrite foldi_down_gt.
      rewrite foldi_down_gt with (from := min + i + 1);trivial.
      replace (min + i + 1 - 1) with (min + i).
      apply Hrec.
      apply leb_trans with (i+1);[rewrite leb_spec;omega | trivial].
      apply to_Z_inj;rewrite sub_spec, (add_spec (min + i)), to_Z_1, Zminus_mod_idemp_l.
      replace ([|min + i|] + 1 - 1)%Z with [|min + i|] by ring.
      rewrite Zmod_small;auto using to_Z_bounded.
      apply leb_ltb_trans with (2:= Hlt).
      rewrite leb_spec;omega.
    simpl;rewrite eqb_spec;intros _ Heq.
    rewrite <- Heq.
    rewrite foldi_down_gt.
     replace (min + 1 - 1) with min.
     rewrite !foldi_down_eq;trivial.
     apply to_Z_inj;rewrite sub_spec, add_spec, to_Z_1, Zminus_mod_idemp_l.
     replace ([|min|] + 1 - 1)%Z with [|min|] by ring.
     rewrite Zmod_small;auto using to_Z_bounded.
     rewrite ltb_spec;omega.
  generalize (H2 (leb_refl _) a).
  replace (min + (max - min)) with max;trivial.
  apply to_Z_inj;rewrite add_spec, sub_spec, Zplus_mod_idemp_r.
  ring_simplify ([|min|] + ([|max|] - [|min|]))%Z.
  rewrite Zmod_small;auto using to_Z_bounded.
Qed.

Definition foldi_ntr A f min max (a:A) :=
  foldi_cont (fun i cont _ => f i (cont tt)) min max (fun _ => a) tt.

Lemma foldi_ntr_foldi_down : forall A f min max (a:A),
  max < max_int = true ->
  foldi_down f max min a = foldi_ntr _ f min max a.
Proof.
 intros;unfold foldi_ntr.
 apply foldi_cont_Ind;trivial.
   intros;apply foldi_down_lt;trivial.
 intros i cont Hmin Hmax Heq;rewrite <- Heq;clear Heq.
 apply foldi_down_min;trivial.
 apply leb_ltb_trans with (1:= Hmax);trivial.
Qed.


(** Two iterators *)

Lemma foldi_cont_ZInd2 : forall A B C D (P: Z -> (A -> B) -> (C -> D) -> Prop) (f1 : int -> (A -> B) -> (A -> B)) (f2 : int -> (C -> D) -> (C -> D)) min max cont1 cont2,
  (forall z, ([|max|] < z)%Z -> P z cont1 cont2) ->
  (forall i cont1 cont2, min <= i = true -> i <= max = true -> P ([|i|] + 1)%Z cont1 cont2 ->
    P [|i|] (f1 i cont1) (f2 i cont2)) ->
  P [|min|] (foldi_cont f1 min max cont1) (foldi_cont f2 min max cont2).
Proof.
  intros.
  set (P' z cont :=
    if Zlt_bool [|max|] z then cont = cont1
      else P z cont (foldi_cont f2 (of_Z z) max cont2)).
  assert (P' [|min|] (foldi_cont f1 min max cont1)).
  apply foldi_cont_ZInd;unfold P';intros.
  rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
  case_eq (Zlt_bool [|max|] [|i|]);intros.
  rewrite <- Zlt_is_lt_bool, <- ltb_spec in H4.
  elim (not_ltb_refl max);apply ltb_leb_trans with i;trivial.
  rewrite of_to_Z;generalize H2;rewrite leb_ltb_eqb, orb_true_iff;intros [Hlt | Heq].
  rewrite foldi_cont_lt;[apply H0 | ];trivial.
  revert H3;case_eq (Zlt_bool [|max|] ([|i|] + 1)).
  rewrite <- Zlt_is_lt_bool;rewrite ltb_spec in Hlt;intros;elimtype False;omega.
  rewrite <- (to_Z_add_1 _ _ Hlt), of_to_Z; intros _ W;exact W.
  rewrite eqb_spec in Heq;subst.
  rewrite foldi_cont_eq;[apply H0 | ];trivial.
  assert ([|max|] < [|max|] + 1)%Z by auto with zarith.
  rewrite Zlt_is_lt_bool in H5;rewrite H5 in H3;rewrite H3.
  apply H;rewrite Zlt_is_lt_bool;trivial.
  revert H1;unfold P';case_eq (Zlt_bool [|max|] [|min|]).
  rewrite <- Zlt_is_lt_bool;intros.
  rewrite H2;rewrite foldi_cont_gt;[ | rewrite ltb_spec];auto.
  rewrite of_to_Z;auto.
Qed.


Lemma foldi_cont_ind2 : forall A B C D (P: (A -> B) -> (C -> D) -> Prop) (f:int -> (A -> B) -> (A -> B)) (g:int -> (C -> D) -> (C -> D)) min max cont1 cont2,
  P cont1 cont2 ->
  (forall i cont1 cont2, min <= i = true -> i <= max = true -> P cont1 cont2 -> P (f i cont1) (g i cont2)) ->
  P (foldi_cont f min max cont1) (foldi_cont g min max cont2).
Proof.
  intros A B C D P f g min max cont1 cont2 Ha Hf.
  set (P2 := fun (z:Z) b c => P b c);change (P2 [|min|] (foldi_cont f min max cont1) (foldi_cont g min max cont2)).
  apply foldi_cont_ZInd2;trivial.
Qed.


Lemma foldi_ZInd2 : forall A B (P : Z -> A -> B -> Prop) f g min max a b,
  (max < min = true -> P ([|max|] + 1)%Z a b) ->
  P [|min|] a b ->
  (forall i a b, min <= i = true -> i <= max = true ->
    P [|i|] a b -> P ([|i|] + 1)%Z (f i a) (g i b)) ->
  P ([|max|]+1)%Z (foldi f min max a) (foldi g min max b).
Proof.
  unfold foldi;intros A B P f g min max a b Hlt;intros.
  set (P' z cont1 cont2 :=
    if Zlt_bool [|max|] z then cont1 = (fun a : A => a) /\ cont2 = (fun b : B => b)
      else forall a b, P z a b -> P ([|max|]+1)%Z (cont1 a) (cont2 b)).
  assert (P' [|min|] (foldi_cont (fun (i : int) (cont : A -> A) (a : A) => cont (f i a)) min
    max (fun a : A => a))
  (foldi_cont (fun (i : int) (cont : B -> B) (b : B) => cont (g i b)) min
    max (fun b : B => b))).
  apply foldi_cont_ZInd2;intros;red.
  rewrite Zlt_is_lt_bool in H1;rewrite H1;auto.
  case_eq (Zlt_bool [|max|] [|i|]);intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H2;elimtype False;omega.
  clear H4; revert H3;unfold P'.
  case_eq (Zlt_bool [|max|] ([|i|] + 1));intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|max|]) by (rewrite leb_spec in H2;omega).
  destruct H4;subst;rewrite <- H6;apply H0;trivial.
  revert H1;unfold P'.
  case_eq (Zlt_bool [|max|] [|min|]);auto.
  rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite !foldi_cont_gt;auto.
Qed.


Lemma foldi_Ind2 : forall A B (P : int -> A -> B -> Prop) f g min max a b,
  (max < max_int = true) ->
  (max < min = true -> P (max + 1) a b) ->
  P min a b ->
  (forall i a b, min <= i = true -> i <= max = true ->
    P i a b -> P (i + 1) (f i a) (g i b)) ->
  P (max+1) (foldi f min max a) (foldi g min max b).
Proof.
  intros.
  set (P' z a b := (0 <= z < wB)%Z -> P (of_Z z) a b).
  assert (W:= to_Z_add_1 _ _ H).
  assert (P' ([|max|]+1)%Z (foldi f min max a) (foldi g min max b)).
  apply foldi_ZInd2;unfold P';intros.
  rewrite <- W, of_to_Z;auto.
  rewrite of_to_Z;trivial.
  assert (i < max_int = true).
  apply leb_ltb_trans with max;trivial.
  rewrite <- (to_Z_add_1 _ _ H7), of_to_Z;apply H2;trivial.
  rewrite of_to_Z in H5;apply H5;apply to_Z_bounded.
  unfold P' in H3;rewrite <- W, of_to_Z in H3;apply H3;apply to_Z_bounded.
Qed.


Lemma foldi_ind2 : forall A B (P: A -> B -> Prop) (f:int -> A -> A) (g:int -> B -> B) min max a b,
  P a b ->
  (forall i a b, min <= i = true -> i <= max = true -> P a b -> P (f i a) (g i b)) ->
  P (foldi f min max a) (foldi g min max b).
Proof.
  unfold foldi;intros A B P f g min max a b Ha Hr; revert a b Ha.
  apply (foldi_cont_ind2 _ _ _ _ (fun cont1 cont2 => forall a b, P a b -> P (cont1 a) (cont2 b))); auto.
Qed.


Lemma fold_ind2 : forall A B (P: A -> B -> Prop) (f: A -> A) (g: B -> B) min max a b,
  P a b -> (forall a b, P a b -> P (f a) (g b)) -> P (fold f min max a) (fold g min max b).
Proof.
  unfold fold;intros A B P f g min max a b Ha Hr;revert a b Ha.
  apply (foldi_cont_ind2 _ _ _ _ (fun cont1 cont2 => forall a b, P a b -> P (cont1 a) (cont2 b)));auto.
Qed.

Lemma foldi_eq_compat : forall A (f1 f2:int -> A -> A) min max a,
  (forall i a, min <= i = true -> i <= max = true -> f1 i a = f2 i a) ->
  foldi f1 min max a = foldi f2 min max a.
Proof.
 intros; set (P' (z:Z) (a1 a2:A) := a1 = a2).
 assert (P' ([|max|] + 1)%Z (foldi f1 min max a) (foldi f2 min max a)).
 apply foldi_ZInd2;unfold P';intros;subst;auto.
 apply H0.
Qed.

Lemma foldi_down_cont_ZInd2 :
  forall A B C D (P: Z -> (A -> B) -> (C -> D) -> Prop) (f1:int -> (A -> B) -> (A -> B)) (f2:int -> (C -> D) -> (C -> D)) max min cont1 cont2,
    (forall z, (z < [|min|])%Z -> P z cont1 cont2) ->
    (forall i cont1 cont2, min <= i = true -> i <= max = true -> P ([|i|] - 1)%Z cont1 cont2 ->
      P [|i|] (f1 i cont1) (f2 i cont2)) ->
    P [|max|] (foldi_down_cont f1 max min cont1) (foldi_down_cont f2 max min cont2).
Proof.
  intros.
  set (P' z cont :=
    if Zlt_bool z [|min|] then cont = cont1
      else P z cont (foldi_down_cont f2 (of_Z z) min cont2)).
  assert (P' [|max|] (foldi_down_cont f1 max min cont1)).
  apply foldi_down_cont_ZInd;unfold P';intros.
  rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
  case_eq (Zlt_bool [|i|] [|min|]);intros.
  rewrite <- Zlt_is_lt_bool, <- ltb_spec in H4.
  elim (not_ltb_refl min);apply leb_ltb_trans with i;trivial.
  rewrite of_to_Z;generalize H1;rewrite leb_ltb_eqb, orb_true_iff;intros [Hlt | Heq].
  rewrite foldi_down_cont_gt;[apply H0 | ];trivial.
  revert H3;case_eq (Zlt_bool ([|i|] - 1) [|min|]).
  rewrite <- Zlt_is_lt_bool;rewrite ltb_spec in Hlt;intros;elimtype False;omega.
  rewrite <- (to_Z_sub_1 _ _ Hlt), of_to_Z; intros _ W;exact W.
  rewrite eqb_spec in Heq;subst.
  rewrite foldi_down_cont_eq;[apply H0 | ];trivial.
  assert ([|i|] - 1 < [|i|])%Z by auto with zarith.
  rewrite Zlt_is_lt_bool in H5;rewrite H5 in H3;rewrite H3.
  apply H;rewrite Zlt_is_lt_bool;trivial.
  revert H1;unfold P';case_eq (Zlt_bool [|max|] [|min|]).
  rewrite <- Zlt_is_lt_bool;intros.
  rewrite H2;rewrite foldi_down_cont_lt;[ | rewrite ltb_spec];auto.
  rewrite of_to_Z;auto.
Qed.


Lemma foldi_down_cont_ind2 : forall A B C D (P: (A -> B) -> (C -> D) -> Prop) (f:int -> (A -> B) -> (A -> B)) (g:int -> (C -> D) -> (C -> D)) max min cont1 cont2,
  P cont1 cont2 ->
  (forall i cont1 cont2, min <= i = true -> i <= max = true -> P cont1 cont2 -> P (f i cont1) (g i cont2)) ->
  P (foldi_down_cont f max min cont1) (foldi_down_cont g max min cont2).
Proof.
  intros A B C D P f g max min cont1 cont2 Ha Hf.
  set (P2 := fun (z:Z) b c => P b c);change (P2 [|max|] (foldi_down_cont f max min cont1) (foldi_down_cont g max min cont2)).
  apply foldi_down_cont_ZInd2;trivial.
Qed.


Lemma foldi_down_ZInd2 :
  forall A B (P: Z -> A -> B -> Prop) (f1:int -> A -> A) (f2:int -> B -> B) max min a1 a2,
    (max < min = true -> P ([|min|] - 1)%Z a1 a2) ->
    (P [|max|] a1 a2) ->
    (forall z, (z < [|min|])%Z -> P z a1 a2) ->
    (forall i a1 a2, min <= i = true -> i <= max = true -> P [|i|] a1 a2 ->
      P ([|i|] - 1)%Z (f1 i a1) (f2 i a2)) ->
    P ([|min|] - 1)%Z (foldi_down f1 max min a1) (foldi_down f2 max min a2).
Proof.
  unfold foldi_down;intros A B P f1 f2 max min a1 a2 Hlt;intros.
  set (P' z cont1 cont2 :=
    if Zlt_bool z [|min|] then cont1 = (fun a0 : A => a0) /\ cont2 = (fun a0 : B => a0)
      else forall a1 a2, P z a1 a2 -> P ([|min|] - 1)%Z (cont1 a1) (cont2 a2)).
  assert (P' [|max|] (foldi_down_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f1 i a0)) max
    min (fun a0 : A => a0))
  (foldi_down_cont (fun (i : int) (cont : B -> B) (a0 : B) => cont (f2 i a0)) max
    min (fun a0 : B => a0))).
  apply foldi_down_cont_ZInd2;intros;red.
  rewrite Zlt_is_lt_bool in H2;rewrite H2;auto.
  case_eq (Zlt_bool [|i|] [|min|]);intros.
  rewrite <- Zlt_is_lt_bool in H5;rewrite leb_spec in H2;elimtype False;omega.
  clear H5;revert H4;unfold P'.
  case_eq (Zlt_bool ([|i|] - 1) [|min|]);intros;auto.
  rewrite <- Zlt_is_lt_bool in H4; assert ([|i|] = [|min|]) by (rewrite leb_spec in H2;omega).
  destruct H5;subst;rewrite <- H7;apply H1;trivial.
  revert H2;unfold P'.
  case_eq (Zlt_bool [|max|] [|min|]);auto.
  rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite foldi_down_cont_lt;auto.
  destruct H3. rewrite H4;auto.
Qed.


Lemma foldi_down_ind2 : forall A B (P: A -> B -> Prop) (f:int -> A -> A) (g:int -> B -> B) max min a b,
  P a b ->
  (forall i a b, min <= i = true -> i <= max = true -> P a b -> P (f i a) (g i b)) ->
  P (foldi_down f max min a) (foldi_down g max min b).
Proof.
  unfold foldi_down;intros A B P f g max min a b Ha Hr;revert a b Ha.
  apply (foldi_down_cont_ind2 _ _ _ _ (fun cont1 cont2 => forall a b, P a b -> P (cont1 a) (cont2 b)));auto.
Qed.


Lemma fold_down_ind2 : forall A B (P: A -> B -> Prop) (f: A -> A) (g: B -> B) max min a b,
  P a b -> (forall a b, P a b -> P (f a) (g b)) -> P (fold_down f max min a) (fold_down g max min b).
Proof.
  unfold fold_down;intros A B P f g max min a b Ha Hr;revert a b Ha.
  apply (foldi_down_cont_ind2 _ _ _ _ (fun cont1 cont2 => forall a b, P a b -> P (cont1 a) (cont2 b)));auto.
Qed.

Lemma foldi_down_eq_compat : forall A (f1 f2:int -> A -> A) max min a,
  (forall i a, min <= i = true -> i <= max = true -> f1 i a = f2 i a) ->
  foldi_down f1 max min a = foldi_down f2 max min a.
Proof.
  intros; set (P' (z:Z) (a1 a2:A) := a1 = a2).
  assert (P' ([|min|] - 1)%Z (foldi_down f1 max min a) (foldi_down f2 max min a)).
  apply foldi_down_ZInd2;unfold P';intros;subst;auto.
  apply H0.
Qed.


Lemma forallb_spec : forall f from to,
  forallb f from to = true <->
  forall i, from <= i = true -> i <= to = true -> f i = true.
Proof.
 unfold forallb;intros f from to.
 setoid_rewrite leb_spec.
 apply foldi_cont_ZInd.
 intros;split;[intros;elimtype False;omega | trivial].
 intros i cont Hfr Hto Hcont.
 case_eq (f i);intros Heq.
 rewrite Hcont;clear Hcont;split;auto with zarith;intros.
 assert (H2 : ([|i0|] = [|i|] \/ [|i|] + 1 <= [|i0|])%Z) by omega; destruct H2;auto with zarith.
 apply to_Z_inj in H2;rewrite H2;trivial.
 split;[discriminate | intros].
 rewrite leb_spec in Hto;rewrite <- Heq;auto with zarith.
Qed.

Lemma forallb_eq_compat : forall f1 f2 from to,
  (forall i, from <= i = true -> i <= to = true -> f1 i = f2 i) ->
  forallb f1 from to = forallb f2 from to.
Proof.
 unfold forallb;intros.
 set (P' (z:Z) (cont1 cont2:unit -> bool) := cont1 tt = cont2 tt).
 refine (foldi_cont_ZInd2 _ _ _ _ P' _ _ from to _ _ _ _);unfold P';intros;trivial.
 rewrite H2, H;trivial.
Qed.

Lemma existsb_spec : forall f from to,
  existsb f from to = true <->
  exists i, ((from <= i) && (i <= to) && (f i)) = true .
Proof.
 unfold existsb;intros.
 repeat setoid_rewrite andb_true_iff;setoid_rewrite leb_spec.
 apply foldi_cont_ZInd.
 intros;split;[discriminate | intros [i [W1 W2]];elimtype False;omega].
 intros i cont Hfr Hto Hcont.
 case_eq (f i);intros Heq.
  split;trivial.
  exists i;rewrite leb_spec in Hto;auto with zarith.
 rewrite Hcont;clear Hcont;split;intros [i0 [W1 W2]];
  exists i0;split;auto with zarith.
 assert (~ [|i|] = [|i0|]);[ | auto with zarith].
 intros W;apply to_Z_inj in W;rewrite W in Heq;rewrite Heq in W2;discriminate.
Qed.

Lemma existsb_eq_compat : forall f1 f2 from to,
  (forall i, from <= i = true -> i <= to = true -> f1 i = f2 i) ->
  existsb f1 from to = existsb f2 from to.
Proof.
 unfold existsb;intros.
 set (P' (z:Z) (cont1 cont2:unit -> bool) := cont1 tt = cont2 tt).
 refine (foldi_cont_ZInd2 _ _ _ _ P' _ _ from to _ _ _ _);unfold P';intros;trivial.
 rewrite H2, H;trivial.
Qed.

Lemma bit_max_int : forall i, (i < digits)%int63 = true -> bit max_int i = true.
Proof.
 intros;apply (forallb_spec (bit max_int) 0 (digits - 1)).
 lazy (* compute FIXME *); trivial.
 apply leb_0.
 rewrite ltb_spec in H.
 destruct (to_Z_bounded i);rewrite leb_spec.
 change [|digits - 1 |] with ([|digits|] - 1)%Z;omega.
Qed.

Lemma land_max_int_l : forall i, max_int land i = i.
Proof.
  intros;apply bit_eq;intros.
  rewrite land_spec.
  destruct (reflect_leb digits i0).
  rewrite <- leb_spec in l.
  rewrite !bit_M;trivial.
  rewrite bit_max_int;trivial.
  rewrite ltb_spec;omega.
Qed.

Lemma land_max_int_r : forall i, i land max_int = i.
Proof.
 intros;rewrite land_comm;apply land_max_int_l.
Qed.
*)
