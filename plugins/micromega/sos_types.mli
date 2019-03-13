(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The type of positivstellensatz -- used to communicate with sos *)

type vname = string

type term =
| Zero
| Const of Q.t
| Var of vname
| Opp of term
| Add of (term * term)
| Sub of (term * term)
| Mul of (term * term)
| Pow of (term * int)

val output_term : out_channel -> term -> unit

type positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of Q.t
 | Rational_le of Q.t
 | Rational_lt of Q.t
 | Square of term
 | Monoid of int list
 | Eqmul of term * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz

val output_psatz : out_channel -> positivstellensatz -> unit
