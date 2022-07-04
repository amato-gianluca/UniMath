(** * Signatures for universal algebra. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(*
This file contains a formalization of multi-sorted signatures.
*)

Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Export UniMath.Combinatorics.DecSet.
Require Import UniMath.Combinatorics.MoreLists.
Require Import UniMath.Algebra.Universal.SortedTypes.

Local Open Scope stn.

(** A _signature_ is given by a decidable set of sorts, a set of of operation symbols and a map
from operation symbols to pair [(l,, s)] where [l] is the _arity_ (or _domain_) and [s] is
the _sort_ (or _range_).
*)

Definition signature : UU := ∑ (S: hSet) (O: S → hSet), ∏ (s: S), O s → list S.

Definition sorts (σ: signature): hSet := pr1 σ.

Definition names {σ: signature}: (sorts σ) → hSet := pr12 σ.

Definition arity {σ: signature} {s: sorts σ}: names s → list (sorts σ) := pr22 σ s.

Definition sort {σ: signature} {s: sorts σ}: names s → sorts σ := λ _, s.

(** Helper functions for creating signatures. *)
 
Definition make_signature (S: hSet) (O: S → hSet) (ar: ∏ (s: S), O s → list S): signature
  := S ,, (O ,, ar).

Definition make_signature_single_sorted (O: hSet) (ar: O → nat) : signature
  := make_signature unitset (λ _, O) (λ _ op, fill tt (ar op)).

(** Helper functions for creating signatures according to the old definition. *)

Definition make_signature' (S: hSet) (O: hSet) (ar: O → list S × S) : signature.
Proof.
  exists S.
  use tpair.
  - intro s.
    exists (∑ o: O,  pr2 (ar o) = s).
    apply isaset_total2.
    + exact (setproperty O).
    + intro o.
      apply isasetaprop.
      apply (setproperty S).
 - cbn.
   intros s o'.
   exact (pr1 (ar (pr1 o'))).
Defined.


(** A signature may be alternatively specified trough a [signature_simple]. In a simple
signature, the types for sorts and operation symbols are standard finite sets, and
the map from operations symbols to domain and range is replaced by a list. In this way,
the definition of a new signature is made simpler.

We have decided to define new types for simple signatures instead of only defining helper
functions, since this make it simpler to define simplified means of defining a new algebra,
too.
*)

Definition signature_simple : UU := ∑ (ns: nat), list (list (⟦ ns ⟧) × ⟦ ns ⟧).

Definition make_signature_simple {ns: nat} (ar: list (list (⟦ ns ⟧) × ⟦ ns ⟧))
  : signature_simple := ns ,, ar.

Coercion signature_simple_compile (σ: signature_simple) : signature
  := make_signature' (stnset (pr1 σ)) (stnset (length (pr2 σ))) (nth (pr2 σ)).

Definition signature_simple_single_sorted : UU := list nat.

Definition make_signature_simple_single_sorted (ar: list nat) : signature_simple_single_sorted := ar.

Coercion signature_simple_single_sorted_compile (σ: signature_simple_single_sorted): signature
  := make_signature_single_sorted (stnset (length σ)) (nth σ).
