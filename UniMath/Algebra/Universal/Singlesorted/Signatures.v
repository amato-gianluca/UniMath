(** * Signatures for universal algebra. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)
(*
This file contains a formalization of single-sorted signatures.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Export UniMath.Combinatorics.DecSet.
Require Import UniMath.Combinatorics.MoreLists.

Local Open Scope stn.

(** A _signature_ is given by a set of operation symbols and a map from operations to their arity *)

Definition signature : UU := ∑ (O: hSet), O → nat.

Definition names (σ: signature) := pr1 σ.

Definition arity {σ: signature} := pr2 σ.

(** Helper functions for creating signatures. *)

Definition make_signature (O: hSet) (arity: O → nat) : signature
  := O,,  arity.

(** A signature may be alternatively specified trough a sequence of arities. In this
case, the operation symbols are just element of stnset *)

Definition signature_simple: UU := list nat.

Definition make_signature_simple: list nat → signature_simple := idfun _.

Coercion signature_simple_compile (σ: signature_simple) : signature
  := make_signature  (stnset (length σ)) (nth σ).
