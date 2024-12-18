Require Import UniMath.Foundations.All.
Require Import UniMath.Foundations.All.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Export UniMath.Algebra.Universal.SortedTypes.
Require Export UniMath.Algebra.Universal.Signatures.
Require Export UniMath.Algebra.Universal.Algebras.

Open Scope sorted.

Section Embedding.

Definition embedding {σ : signature} (B A : algebra σ) :=
  ∑ (i : B s→ A), (∏ s, isincl (i s)) × (ishom i).

Definition embedding_pr1 {σ : signature} (B A : algebra σ) 
  (i:embedding B A) : B s→ A := pr1 i.
Coercion embedding_pr1 : embedding >-> sfun.
Identity Coercion embedding_Id : sfun >-> Funclass.
Definition embedding_isincl {σ : signature} (B A : algebra σ) 
  (i:embedding B A) : ∏ s, isincl (i s) := pr12 i.
Definition embedding_ishom {σ : signature} (B A : algebra σ) 
  (i:embedding B A) : ishom i := pr22 i.

End Embedding.

Section SubUniverse.

Definition issubuniverse {σ : signature} (A : algebra σ) (B : shsubtype A): UU
  := ∏(nm : names σ) (xs : B⋆ (arity nm)),
    B (sort nm) (ops A nm ((λ s, pr1carrier (B s))⋆⋆ (arity nm) xs)).
(*TODO: proof it is a prop*)

End SubUniverse.


Section HomAndSubUniverse.

  Context {σ : signature} (A B: algebra σ) (f : B s→ A).

  Theorem issubuniverse_image : issubuniverse A (simage_shsubtype f).
  Proof.
    intros nm xs.
    cbn in xs.
    cbn.


    (*IDEA: "bring out" ishinh in h12map (λ s, pr2) xs*)

    Print simage_shsubtype.

    Check h1map (λ s, pr1) xs.
    Check h12map (λ s, pr2) xs.
    Check h12map (λ s, pr2) xs
      : hvec (h1map_vec
          (λ (s:sorts σ) (t : ∑ x : A s, ishinh_UU (∑ y : B s, f s y = x)), 
              ishinh_UU (∑ y' : B s, f s y' = (pr1 t)))
          xs).
    Check h12map (λ s, pr2) xs
      : hvec (h1map_vec
          ( ishinh_UU ∘
            λ (s:sorts σ) (t : ∑ x : A s, ishinh_UU (∑ y : B s, f s y = x)), 
              ishinh_UU (∑ y' : B s, f s y' = (pr1 t)))
          xs).

    

    assert (B⋆ (arity nm)).
    {

    }

  Qed.




End HomAndSubUniverse.
