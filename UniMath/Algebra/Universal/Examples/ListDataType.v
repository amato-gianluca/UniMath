(** * Example of lists *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HLists.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.

Local Open Scope stn.

Definition data_sort: ⟦ 2 ⟧ := ●0.
Definition list_sort: ⟦ 2 ⟧ := ●1.

Definition list_signature: signature_simple
  := make_signature_simple [ (nil ,, list_sort) ;  ( [data_sort ; list_sort] ,, list_sort ) ]%list.

Definition nil_op: list_signature := ●0.
Definition cons_op: list_signature := ●1.

Definition list_algebra (A: hSet) := make_algebra_simple list_signature
    [ A ; listset A ]
    [ λ _, nil ; λ p, cons (pr1 p) (pr12 p) ].
