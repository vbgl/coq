Require Import ZArith.
Require Import Lia Psatz.
Open Scope Z_scope.

(* From fiat-crypto Toplevel1.v *)

Goal forall
    (x1 x2 x3 x4 x5 x7 : Z)
    (H0 : x1 + x2 - x3 = 0) (* substitute x1, nothing happens *)
    (H1 : 2 * x2 - x4 - 1 >= 0)
    (H2 : - x2 + x4 >= 0)
    (H3 : 2 * x2 - x5 - 1 >= 0)
    (H5 : x2 - 4 >= 0)
    (H7 : - x2 * x7 + x4 * x5 >= 0)
    (H6 : x2 * x7 + x2 - x4 * x5 - 1 >= 0)
    (H9 : x7 - x2 ^ 2 >= 0), (* x2^2 is *visibly* positive *)
  False.
Proof.
  intros.
  nia.
Qed.

Goal forall
    (x1 x2 x3 x4 x5 x7 : Z)
    (H0 : x2 + x1 - x3 = 0) (* substitute x2= x3 -x1 ... *)
    (H1 : 2 * x2 - x4 - 1 >= 0)
    (H2 : - x2 + x4 >= 0)
    (H3 : 2 * x2 - x5 - 1 >= 0)
    (H5 : x2 - 4 >= 0)
    (H7 : - x2 * x7 + x4 * x5 >= 0)
    (H6 : x2 * x7 + x2 - x4 * x5 - 1 >= 0)
    (H9 : x7 - x2 ^ 2 >= 0), (* (x3 - x1)^2 is not visibly positive *)
  False.
Proof.
  intros.
  nia.
Qed.

(* From bedrock2 FlatToRisc.v *)

(* Variant of the following - omega fails (bad linearisation?)*)
Goal forall
    (PXLEN XLEN r : Z)
    (q q0 r0 a : Z)
    (H3 : 4 * a = 4 * PXLEN * q0 + (4 * q + r))
    (H6 : 0 <= 4 * q + r)
    (H7 : 4 * q + r < 4 * PXLEN)
    (H8 : r <= 3)
    (H4 : r >= 1),
  False.
Proof.
  intros.
  Time lia.
Qed.

Goal forall
    (PXLEN XLEN r : Z)
    (q q0 r0 a : Z)
    (H3 : 4 * a = 4 * PXLEN * q0 + (4 * q + r))
    (H6 : 0 <= 4 * q + r)
    (H7 : 4 * q + r < 4 * PXLEN)
    (H8 : r <= 3)
    (H4 : r >= 1),
  False.
Proof.
  intros.
  Time nia.
Qed.


(** Very slow *)
Goal forall
    (XLEN r : Z)
    (H : 4 < 2 ^ XLEN)
    (H0 : 8 <= XLEN)
    (q q0 r0 a : Z)
    (H3 : 4 * a = 4 * 2 ^ (XLEN - 2) * q0 + r0)
    (H5 : r0 = 4 * q + r)
    (H6 : 0 <= r0)
    (H7 : r0 < 4 * 2 ^ (XLEN - 2))
    (H2 : 0 <= r)
    (H8 : r < 4)
    (H4 : r > 0)
    (H9 : 0 < 2 ^ (XLEN - 2)),
    False.
Proof.
  intros.
  Time nia.
Qed.

Goal forall
    (XLEN r : Z)
    (R : r > 0 \/ r < 0)
    (H : 4 < 2 ^ XLEN)
    (H0 : 8 <= XLEN)
    (H1 : ~ (0 <= XLEN - 2) \/ 0 < 2 ^ (XLEN - 2))
     (q  q0 r0 a : Z)
    (H2 : 0 <= r0 < 4 * 2 ^ (XLEN - 2))
    (H3 : 4 *  a = 4 * 2 ^ (XLEN - 2) * q0 + r0)
    (H4 : 0 <= r < 4)
    (H5 : r0 = 4 * q + r),
    False.
Proof.
  intros.
  Time nia.
Qed.

Goal forall
    (XLEN r : Z)
    (R : r > 0 \/ r < 0)
    (H : 4 < 2 ^ XLEN)
    (H0 : 8 <= XLEN)
    (H1 : ~ (0 <= XLEN - 2) \/ 0 < 2 ^ (XLEN - 2))
     (q  q0 r0 a : Z)
    (H2 : 0 <= r0 < 4 * 2 ^ (XLEN - 2))
    (H3 : 4 *  a = 4 * 2 ^ (XLEN - 2) * q0 + r0)
    (H4 : 0 <= r < 4)
    (H5 : r0 = 4 * q + r),
    False.
Proof.
  intros.
  intuition idtac.
  Time   all:nia.
Qed.



Goal forall
    (XLEN a q q0 z : Z)
    (HR : 4 * a - 4 * z * q0 - 4 * q > 0)
    (H0 : 8 <= XLEN)
    (H1 : 0 < z)
    (H : 0 <= 4 * a - 4 * z * q0 - 4 * q)
    (H3 : 4 * a - 4 * z * q0 - 4 * q < 4)
    (H4 : 4 * a - 4 * z * q0 < 4 * z),
  False.
Proof.
  intros.
  Time nia.
Qed.


(* From fiat-crypto Generalized.v *)
Goal
  forall (__x1 __x2 __x3 __x4 __x5 __x6 __x7 __x8 __x9 __x10 __x11 __x12 __x13
  __x14 __x15 __x16 : Z)
         (H6 : __x8 < __x10 ^ 2 * __x15 ^ 2 + 2 * __x10 * __x15 * __x14 + __x14 ^ 2)
         (H7 : 0 <= __x8)
         (H12 : 0 <= __x14)
         (H0 : __x8 = __x15 * __x11 + __x9)
         (H14 : __x10 ^ 2 * __x15 + __x10 * __x14 < __x16)
         (H17 : __x16 <= 0)
         (H15 : 0 <= __x9)
         (H18 : __x9 < __x15)
         (H16 : 0 <= __x12)
         (H19 : __x12 < (__x10 * __x15 + __x14) * __x10)
  , False.
Proof.
  intros.
  Time nia.
Qed.


(* From Sozeau's plugin Equations *)
Goal forall z z0 z1 m
            (Heqz0 : z0 = ((1 + z) * z1)%Z)
            (H0 : (0 <= m)%Z)
            (H3 : z = m)
            (H1 : (0 <= z0)%Z)
            (H4 : z1 = z0)
            (H2 : (z1 > 0)%Z),
  (z1 > z)%Z.
Proof.
  intros.
  Time nia.
Qed.

Goal forall x p2 p1 m,
    x <> 0%Z  ->
    (Z.abs (x *  p2 ) > Z.abs (Z.abs p1 + Z.abs m))%Z ->
    (Z.abs (x * (p1 + x * p2 )) > Z.abs m)%Z.
Proof.
  intros.
  Time nia.
Qed.

(* From fiat-crypto Modulo.v *)

Goal forall  (b : Z)
             (H : 0 <> b)
             (c  r q1 q2 r2 : Z)
             (H2 : r2 < c)
             (q0 : Z)
             (H7 : r < b)
             (H5 : 0 <= r)
             (H6 : r < b)
             (H12 : 0 < c)
             (H13 : 0 <> c)
             (H0 : 0 <> c * b)
             (H1 : 0 <= r2)
             (H14 : 0 <= q0)
             (H9 : c * q1 + q0 = c * q2 + r2)
             (H4 : 0 <= b * q0 + - r)
             (H10 : b * q0 + - r < c * b),
  q1 = q2.
Proof.
  intros.
  Fail nia.
Abort.

(* Known issues.

  - Found proof may violate  Proof using ...
    There may be a compliant proof but lia has no way to know.
    Proofs could be optimised to minimise the number of hypotheses,
    but this seems to costly.
Section S.
  Variable z z0 z1 z2 : Z.
  Variable H2 : 0 <= z2.
  Variable H3 : z2 < z1.
  Variable H4 : 0 <= z0.
  Variable H5 : z0 < z1.
  Variable H6 : z = - z2.

  Goal -z1 -z2  >= 0 -> False.
  Proof using  H2 H3  H6.
    intros.
    lia.
  Qed.
*)
