(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Target language for extraction: a core ML called MiniML. *)

open Pp
open Names
open Term
open Libnames
open Util

(*s ML type expressions. *)

type ml_type = 
  | Tarr  of ml_type * ml_type
  | Tglob of global_reference * ml_type list 
  | Tvar  of int
  | Tvar' of int (* same as Tvar, used to avoid clash *)
  | Tmeta of ml_meta (* used during ML type reconstruction *)
  | Tdummy
  | Tunknown

and ml_meta = { id : int; mutable contents : ml_type option}

(* ML type schema. 
   The integer is the number of variable in the schema. *)

type ml_schema = int * ml_type 

(*s ML inductive types. *)

type ml_ind = 
  identifier list * global_reference * (global_reference * ml_type list) list

(*s ML terms. *)

type ml_ast = 
  | MLrel   of int
  | MLapp   of ml_ast * ml_ast list
  | MLlam   of identifier * ml_ast
  | MLletin of identifier * ml_ast * ml_ast
  | MLglob  of global_reference
  | MLcons  of global_reference * ml_ast list
  | MLcase  of ml_ast * (global_reference * identifier list * ml_ast) array
  | MLfix   of int * identifier array * ml_ast array
  | MLexn   of string
  | MLdummy
  | MLcast  of ml_ast * ml_type
  | MLmagic of ml_ast

(*s ML declarations. *)

type ml_decl = 
  | Dind  of ml_ind list * bool (* cofix *)
  | Dtype of global_reference * identifier list * ml_type
  | Dterm   of global_reference * ml_ast * ml_type
  | DcustomTerm of global_reference * string
  | DcustomType of global_reference * string
  | Dfix    of global_reference array * ml_ast array * ml_type array

(*s Pretty-printing of MiniML in a given concrete syntax is parameterized
    by a function [pp_global] that pretty-prints global references. 
    The resulting pretty-printer is a module of type [Mlpp] providing
    functions to print types, terms and declarations. *)

type extraction_params =  
  { modular : bool; 
    mod_name : identifier; 
    to_appear : global_reference list }

module type Mlpp_param = sig
  val globals : unit -> Idset.t
  val pp_global : global_reference -> std_ppcmds
end

module type Mlpp = sig
  val pp_decl : ml_decl -> std_ppcmds
end

