(** * Algebra for a given signature. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Require Export UniMath.Algebra.Universal.Multisorted.HVectors.
Require Export UniMath.Algebra.Universal.Singlesorted.Signatures.

(** ** Basic definitions. *)

Definition algebra (σ: signature): UU
  := ∑ A: UU, ∏ nm: names σ, vec A (arity nm) → A.

Definition carrier {σ: signature} (A: algebra σ): UU := pr1 A.

Coercion carrier: algebra >-> UU.

Definition ops {σ: signature} (A: algebra σ) := pr2 A.

Definition make_algebra {σ: signature} (A: UU) (ops: ∏ nm: names σ, vec A (arity nm) → A)
  : algebra σ := A ,, ops.

Definition dom {σ: signature} (A: algebra σ) (nm: names σ): UU := vec A (arity nm).

Definition rng {σ: signature} (A: algebra σ) (nm: names σ): UU := A.

Definition has_supportsets {σ: signature} (A: algebra σ): UU
  := isaset (carrier A).

(** ** Helper for building an algebra starting from a simple signature.

A simple signature is either a [signature_simple_single_sorted] for the single-sorted case or
a [signature_single] for the multi-sorted case.
*)

Definition make_algebra_simple
    (σ : signature_simple)
    (A : UU)
    (ops: hvec (vec_map (λ n: nat, vec A n → A) (list_to_vec σ)))
  : algebra σ.
Proof.
  exists A.
  revert σ ops.
  refine (list_ind _ _ _).
  - intros.
    cbn in nm.
    apply fromstn0.
    assumption.
  - intros x xs IHxs ops nm.
    induction nm as [nm nmproof].
    induction nm.
    + exact (pr1 ops).
    + exact (IHxs (pr2 ops) (nm ,, nmproof)).
Defined.

(** ** Homomorphisms of algebras. *)

Definition ishom {σ: signature} {A1 A2: algebra σ} (h: A1 → A2) : UU
  := ∏ (nm: names σ) (x: dom A1 nm), h (ops A1 nm x) = ops A2 nm (vec_map h x).

Definition hom {σ: signature} (A1 A2: algebra σ): UU := ∑ (h: A1 → A2), ishom h.

Declare Scope hom_scope.

Notation "a1 ↷ a2" := (hom a1 a2) (at level 80, right associativity): hom_scope.

Delimit Scope hom_scope with hom.

Bind Scope hom_scope with hom.

Local Open Scope hom.

Definition hom2fun {σ: signature} {A1 A2: algebra σ} (f: A1 ↷ A2): A1 → A2 := pr1 f.

Coercion hom2fun: hom >-> Funclass.

Definition hom2axiom {σ: signature} {A1 A2: algebra σ} (f: A1 ↷ A2) := pr2 f.

Definition make_hom {σ: signature} {A1 A2: algebra σ} {f: A1 → A2} (ish: ishom f): A1 ↷ A2 := f ,, ish.

Theorem isapropishom {σ: signature} {A1 A2: algebra σ} (f: A1 → A2)
   (setprop: has_supportsets A2): isaprop (ishom f).
Proof.
  red.
  apply impred_isaprop.
  intros.
  apply impred_isaprop.
  intros.
  apply setprop.
Defined.

Theorem isasethom {σ: signature} (A1 A2: algebra σ) (setprop: has_supportsets A2)
  : isaset (A1 ↷ A2).
Proof.
  red.
  apply isaset_total2.
  - apply impred_isaset.
    intros.
    apply setprop.
  - intros.
    apply isasetaprop.
    apply isapropishom.
    exact setprop.
Defined.

(** ** Identity and composition of homomorphisms. *)

Lemma ishomid {σ: signature} (A: algebra σ): ishom (idfun A).
Proof.
  red.
  intros.
  rewrite vec_map_id.
  apply idpath.
Defined.

Definition homid {σ: signature} (A: algebra σ): A ↷ A := make_hom (ishomid A).

Lemma ishomcomp {σ: signature} {A1 A2 A3: algebra σ} (h1: A1 ↷ A2) (h2: A2 ↷ A3): ishom (h2 ∘ h1).
Proof.
  red.
  intros.
  induction h1 as [h1 ishomh1].
  induction h2 as [h2 ishomh2].
  cbn.
  rewrite vec_map_comp.
  rewrite ishomh1.
  rewrite ishomh2.
  apply idpath.
Defined.

Definition homcomp {σ: signature} {a1 a2 a3: algebra σ} (h1: a1 ↷ a2) (h2: a2 ↷ a3) : a1 ↷ a3
  := make_hom (ishomcomp h1 h2).

(** ** The unit algebra and the proof it is final. *)

Definition unitalgebra (σ: signature): algebra σ
  := make_algebra unit (λ _, tounit).

Lemma ishomtounit {σ: signature} (A: algebra σ): @ishom σ A (unitalgebra σ) tounit.
Proof.
  red.
  intros.
  apply iscontrunit.
Defined.

Definition unithom {σ: signature} (A : algebra σ): hom A (unitalgebra σ)
  := make_hom (ishomtounit A).

Theorem iscontrhomstounit {σ: signature} (A: algebra σ): iscontr (hom A (unitalgebra σ)).
Proof.
  exists (unithom A).
  intro.
  apply subtypePairEquality'.
  - apply proofirrelevancecontr.
    apply iscontrfuntounit.
  - apply isapropishom.
    unfold has_supportsets.
    intros.
    apply isasetunit.
Defined.

(** ** Helpers for working with curried functions *)

Definition ops' {σ: signature} (A: algebra σ) (nm: names σ) := Vectors.currify (ops A nm).

Definition make_algebra'
    {σ: signature}
    (A : UU)
    (ops: ∏ nm: names σ, Vectors.iterfun (arity nm) A A)
  : algebra σ := A ,, λ nm, Vectors.uncurrify (ops nm).

Definition make_algebra_simple'
    (σ : signature_simple)
    (A : UU)
    (ops : hvec (vec_map (λ n: nat, Vectors.iterfun n A A) (list_to_vec σ)))
  : algebra σ.
Proof.
  refine (make_algebra_simple σ A _).
  refine (h1map _ ops).
  intro a.
  exact Vectors.uncurrify.
Defined.

(** ** Algebras with hSets as carriers *)

Definition hSetalgebra (σ : signature) : UU
  := ∑ A: hSet, ∏ nm: names σ, vec A (arity nm) → A.

Definition make_hSetalgebra {σ : signature} {A: algebra σ} (setproperty: has_supportsets A): hSetalgebra σ
  := (make_hSet (carrier A) setproperty,, ops A).

Definition hSetalgebra_to_algebra {σ : signature} (A: hSetalgebra σ): algebra σ
  := (pr1 (pr1 A),, pr2 A).

Definition has_supportsets_hSetalgebra {σ : signature} (A: hSetalgebra σ): has_supportsets (hSetalgebra_to_algebra A)
:= setproperty (pr1 A).
