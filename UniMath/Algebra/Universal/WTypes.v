Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.Type.Core.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.W.Core.

Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.TermAlgebras.

Local Open Scope stn.
Local Open Scope cat.

Context (σ: signature_simple_single_sorted).

Definition A := names σ.

Definition B (a: A) := ⟦ length (arity a) ⟧.

Definition W := W B.

Definition h1const_is_vec' {A: UU} {n: nat} (B: A) (P: A → UU)
  : hvec (vec_map P (vec_fill B n)) = vec (P B) n.
Proof.
  induction n.
  - apply idpath.
  - simpl.
    apply maponpaths.
    apply IHn.
Defined.

Definition algebra_to_functoralgebra (Alg: algebra σ):  algebra_ob (polynomial_functor A B).
Proof.
  unfold algebra_ob.
  exists (support Alg tt).
  simpl.
  unfold polynomial_functor_obj, A, B.
  intro.
  induction X as [nm subterms].
  refine (ops Alg nm _).
  unfold star, arity.
  simpl.
  rewrite h1const_is_vec'.
  exact (make_vec subterms).
Defined.

Definition functoralgebra_to_algebra (FAlg: algebra_ob (polynomial_functor A B)) 
  (carrierSet: isaset (alg_carrier _ FAlg)): algebra σ.
Proof.
  induction FAlg as [carrier ops].
  exists (λ _, make_hSet carrier carrierSet).
  intro.
  unfold star, arity.
  simpl.
  rewrite h1const_is_vec'.
  simpl in ops.
    unfold polynomial_functor_obj, A, B in ops.
  intro subterms.
  exact (ops (nm ,, el subterms)).
Defined.

(* Definition is_iso_algebra_to_functoralgebra: is_iso algebra_to_functoralgebra. *)

Definition termalgebra_as_wtype: W.
Proof.
  unfold W, Core.W.
  exists (algebra_to_functoralgebra (term_algebra σ)).
  unfold is_initial.
  intro Y.
Abort.
 