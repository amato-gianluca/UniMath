
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Definition of the Yoneda functor
           [yoneda(C) : [C, [C^op, HSET]]]

           Proof that [yoneda(C)] is fully faithful


TODO: this file needs cleanup

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Export UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.whiskering.

Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).

Ltac unf := unfold identity,
                   compose,
                   precategory_morphisms;
                   simpl.

(** * Yoneda functor *)

(** ** On objects *)

Definition yoneda_objects_ob (C : category) (c : C)
          (d : C) := hom C d c.

Definition yoneda_objects_mor (C : category) (c : C)
    (d d' : C) (f : hom C d  d') :
   yoneda_objects_ob C c d' -> yoneda_objects_ob C c d :=
    λ g, f · g.

Definition yoneda_ob_functor_data (C : category) (c : C) :
    functor_data C^op HSET.
Proof.
  exists (λ c', make_hSet (yoneda_objects_ob C c c') (homset_property C _ _ ) ).
  intros a b f g. unfold yoneda_objects_ob in *. simpl in *.
  exact (f · g).
Defined.


Lemma is_functor_yoneda_functor_data (C : category) (c : C) :
  is_functor (yoneda_ob_functor_data C c).
Proof.
  repeat split; unf; simpl.
  unfold functor_idax .
  intros.
  apply funextsec.
  intro f. unf. apply id_left.
  intros a b d f g.
  apply funextsec. intro h.
  apply (! assoc _ _ _ ).
Qed.

Definition yoneda_objects (C : category) (c : C) :
             functor C^op HSET :=
    tpair _ _ (is_functor_yoneda_functor_data C c).


(** ** On morphisms *)

Definition yoneda_morphisms_data (C : category) (c c' : C)
    (f : hom C c c') : ∏ a : ob C^op,
         hom _ (yoneda_objects C c a) ( yoneda_objects C c' a) :=
            λ a g, g · f.

Lemma is_nat_trans_yoneda_morphisms_data (C : category)
     (c c' : ob C) (f : hom C c c') :
  is_nat_trans (yoneda_objects C c) (yoneda_objects C c')
    (yoneda_morphisms_data C c c' f).
Proof.
  unfold is_nat_trans; simpl.
  unfold yoneda_morphisms_data; simpl.
  intros d d' g.
  apply funextsec; simpl in *.
  unfold yoneda_objects_ob; simpl.
  unf; intro;
  apply  ( ! assoc _ _ _ ).
Qed.

Definition yoneda_morphisms (C : category) (c c' : C)
   (f : hom C c c') : nat_trans (yoneda_objects C c) (yoneda_objects C c') :=
   tpair _ _ (is_nat_trans_yoneda_morphisms_data C c c' f).


Definition yoneda_functor_data (C : category) :
   functor_data C [C^op , HSET, (has_homsets_HSET) ] :=
   tpair _ (yoneda_objects C) (yoneda_morphisms C).


(** ** Functorial properties of the yoneda assignments *)

Lemma is_functor_yoneda (C : category) :
  is_functor (yoneda_functor_data C).
Proof.
  unfold is_functor.
  repeat split; simpl.
  intro a.
  set (T:= nat_trans_eq (C:=C^op) (has_homsets_HSET)). simpl.
  apply T.
  intro c; apply funextsec; intro f.
  apply id_right.
  intros a b c f g.
  set (T:=nat_trans_eq (C:=C^op) (has_homsets_HSET)).
  apply T.
  simpl; intro d; apply funextsec; intro h.
  apply assoc.
Qed.


Definition yoneda (C : category) :
  functor C (functor_category C^op hset_category) :=
   tpair _ _ (is_functor_yoneda C).

(* Notation "'ob' F" := (precategory_ob_mor_fun_objects F)(at level 4). *)

(** ** Yoneda lemma: natural transformations from [yoneda C c] to [F]
         are isomorphic to [F c] *)


Definition yoneda_map_1 (C : category) (c : C)
   (F : functor C^op HSET) :
       hom _ (yoneda C c) F -> pr1 (F c) :=
   λ h,  pr1 h c (identity c).



Lemma yoneda_map_2_ax (C : category) (c : C)
       (F : functor C^op HSET) (x : pr1 (F c)) :
  is_nat_trans (pr1 (yoneda C c)) F
         (fun (d : C) (f : hom (C ^op) c d) => #F f x).
Proof.
  intros a b f; simpl in *.
  apply funextsec.
  unfold yoneda_objects_ob; intro g.
  set (H:= @functor_comp _ _ F  _ _  b g).
  unfold functor_comp in H;
  unfold opp_precat_data in H;
  simpl in *.
  apply (toforallpaths _ _ _ (H f) x).
Qed.

Definition yoneda_map_2 (C : category) (c : C)
   (F : functor C^op HSET) :
       pr1 (F c) -> hom _ (yoneda C c) F.
Proof.
  intro x.
  exists (λ d : ob C, λ f, #F f x).
  apply yoneda_map_2_ax.
Defined.

Lemma yoneda_map_1_2 (C : category) (c : C)
  (F : functor C^op HSET)
  (alpha : hom _ (yoneda C c) F) :
      yoneda_map_2 _ _ _ (yoneda_map_1 _ _ _ alpha) = alpha.
Proof.
  simpl in *.
  set (T:=nat_trans_eq (C:=C^op) (has_homsets_HSET)).
  apply T.
  intro a'; simpl.
  apply funextsec; intro f.
  unfold yoneda_map_1.
  intermediate_path ((alpha c · #F f) (identity c)).
    apply idpath.
  rewrite <- nat_trans_ax.
  unf; apply maponpaths.
  apply (id_right f ).
Qed.


Lemma yoneda_map_2_1 (C : category) (c : C)
   (F : functor C^op HSET) (x : pr1 (F c)) :
   yoneda_map_1 _ _ _ (yoneda_map_2 _  _ _ x) = x.
Proof.
  simpl.
  rewrite (functor_id F).
  apply idpath.
Qed.

Lemma isaset_nat_trans_yoneda (C: category) (c : C)
  (F : functor C^op HSET) :
 isaset (nat_trans (yoneda_ob_functor_data C c) F).
Proof.
  apply isaset_nat_trans.
  apply (has_homsets_HSET).
Qed.



Lemma yoneda_iso_sets (C : category) (c : C)
   (F : functor C^op HSET) :
   is_z_isomorphism (C:=HSET)
     (a := make_hSet (hom _ ((yoneda C) c) F) (isaset_nat_trans_yoneda C c F))
     (b := F c)
     (yoneda_map_1 C c F).
Proof.
  set (T:=yoneda_map_2 C c F). simpl in T.
  set (T':= T : hom HSET (F c) (make_hSet (hom _ ((yoneda C) c) F)
                                  (isaset_nat_trans_yoneda C c F))).
  exists T'.
  split; simpl.
  - apply funextsec; intro alpha.
    unf; simpl.
    apply (yoneda_map_1_2 C c F).
  - apply funextsec; intro x.
    unf; rewrite (functor_id F).
    apply idpath.
Defined.



Definition yoneda_iso_target (C : category)
           (F : [C^op, HSET])
  : functor C^op HSET.
Proof.
  use (@functor_composite _ [C^op, HSET]^op).
  - apply functor_opp.
    apply yoneda.
  - apply (yoneda _  F).
Defined.

Lemma is_natural_yoneda_iso (C : category) (F : functor C^op HSET):
  is_nat_trans (yoneda_iso_target C F) F
  (λ c, yoneda_map_1 C c F).
Proof.
  unfold is_nat_trans.
  intros c c' f. cbn in *.
  apply funextsec.
  unfold yoneda_ob_functor_data. cbn.
  unfold yoneda_morphisms_data.
  unfold yoneda_map_1.
  intro X.
  assert (XH := nat_trans_ax X).
  cbn in XH. unfold yoneda_objects_ob in XH.
  assert (XH' := XH c' c' (identity _ )).
  assert (XH2 := toforallpaths _ _ _ XH').
  rewrite XH2.
  rewrite (functor_id F).
  cbn.
  clear XH2 XH'.
  assert (XH' := XH _ _ f).
  assert (XH2 := toforallpaths _ _ _ XH').
  eapply pathscomp0. 2: apply XH2.
  rewrite id_right.
  apply idpath.
Qed.

Definition natural_trans_yoneda_iso (C : category)
  (F : functor C^op HSET)
  : nat_trans (yoneda_iso_target C F) F
  := tpair _ _ (is_natural_yoneda_iso C F).



Lemma is_natural_yoneda_iso_inv (C : category) (F : functor C^op HSET):
  is_nat_trans F (yoneda_iso_target C F)
  (λ c, yoneda_map_2 C c F).
Proof.
  unfold is_nat_trans.
  intros c c' f. cbn in *.
  apply funextsec.
  unfold yoneda_ob_functor_data. cbn.
  unfold yoneda_map_2.
  intro A.
  apply nat_trans_eq. { apply (has_homsets_HSET). }
  cbn. intro d.
  apply funextfun.
  unfold yoneda_objects_ob. intro g.
  unfold yoneda_morphisms_data.
  apply (! toforallpaths _ _ _ (functor_comp F _ _ ) A).
Qed.

Definition natural_trans_yoneda_iso_inv (C : category)
  (F : functor C^op HSET)
  : nat_trans (yoneda_iso_target C F) F
  := tpair _ _ (is_natural_yoneda_iso C F).


Lemma isweq_yoneda_map_1 (C : category) (c : C)
   (F : functor C^op HSET) :
  isweq
     (*a := make_hSet (hom _ ((yoneda C) hs c) F) (isaset_nat_trans_yoneda C hs c F)*)
     (*b := F c*)
     (yoneda_map_1 C c F).
Proof.
  set (T:=yoneda_map_2 C c F). simpl in T.
  use isweq_iso.
  - apply T.
  - apply yoneda_map_1_2.
  - apply yoneda_map_2_1.
Defined.

Definition yoneda_weq (C : category) (c : C)
   (F : functor C^op HSET)
  :  hom [C^op, HSET, has_homsets_HSET] (yoneda C c) F ≃ pr1hSet (F c)
  := make_weq _ (isweq_yoneda_map_1 C c F).


(** ** The Yoneda embedding is fully faithful *)

Lemma yoneda_fully_faithful (C : category) : fully_faithful (yoneda C).
Proof.
  intros a b; simpl.
  apply (isweq_iso _
      (yoneda_map_1 C a (pr1 (yoneda C) b))).
  - intro; simpl in *.
    apply id_left.
  - intro gamma.
    simpl in *.
    apply nat_trans_eq. apply (has_homsets_HSET).
    intro x. simpl in *.
    apply funextsec; intro f.
    unfold yoneda_map_1.
    unfold yoneda_morphisms_data.
    assert (T:= toforallpaths _ _ _ (nat_trans_ax gamma a x f) (identity _ )).
    cbn in T.
    eapply pathscomp0; [apply (!T) |].
    apply maponpaths.
    apply id_right.
Defined.


Section yoneda_functor_precomp.

Variables C D : category.
Variable F : functor C D.

Section fix_object.

Variable c : C.

Definition yoneda_functor_precomp' : nat_trans (yoneda_objects C c)
      (functor_composite (functor_opp F) (yoneda_objects D (F c))).
Proof.
  use tpair.
  - intros d f ; simpl.
    apply (#F f).
  - abstract (intros d d' f ;
              apply funextsec; intro t; simpl;
              apply functor_comp).
Defined.

Definition yoneda_functor_precomp :  _ ⟦ yoneda C c, functor_composite (functor_opp F) (yoneda_objects D (F c))⟧.
Proof.
  exact yoneda_functor_precomp'.
Defined.

Variable Fff : fully_faithful F.

Lemma is_z_iso_yoneda_functor_precomp : is_z_isomorphism yoneda_functor_precomp.
Proof.
  apply nat_trafo_z_iso_if_pointwise_z_iso.
  intro a. simpl.
  set (T:= make_weq _ (Fff a c)).
  set (TA := make_hSet (hom C a c) (homset_property C _ _)).
  set (TB := make_hSet (hom D (F a) (F c)) (homset_property _ _ _ )).
  apply (hset_equiv_is_z_iso TA TB T).
Defined.

End fix_object.


Let A : C ⟶ [D^op, HSET] := functor_composite F (yoneda D).
Let B : [D^op, HSET] ⟶ [C^op, HSET]
    := pre_composition_functor _ _ HSET (functor_opp F : [C^op, D^op]).

Definition yoneda_functor_precomp_nat_trans :
    @nat_trans
      C
      [C^op, HSET, (has_homsets_HSET)]
      (yoneda C)
      (functor_composite A B).
Proof.
  use tpair.
  - intro c; simpl.
    apply yoneda_functor_precomp.
  - abstract (
        intros c c' f;
        apply nat_trans_eq; [apply (has_homsets_HSET) |];
        intro d; apply funextsec; intro t;
        cbn;
        apply functor_comp).
Defined.

End yoneda_functor_precomp.
