(** * Terms for a given signature. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)
(**
This file contains a formalization of terms over a signature, implemented as a sequence of
operation symbols. This sequence is though to be executed by a stack machine: each
symbol of arity _n_ virtually pops _n_ elements from the stack and pushes a new element.
A sequence of function symbols is a term when the result of the execution is a stack
with a single element and no stack underflow or type errors occur.

Here we only define ground terms, while terms with variables will be defined in <<VTerms.v>>.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.Combinatorics.Maybe.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.MoreLists.
Require Export UniMath.Algebra.Universal.HVectors.
Require Export UniMath.Algebra.Universal.Singlesorted.Signatures.

Local Open Scope list.

(** ** Definition of [oplist] (operations list). *)
(**
An [oplist] is a list of operation symbols, interpreted as commands to be executed by a stack
machine. Elements of the stack are sorts. When an operation symbol is executed  its arity is
popped out from the stack and replaced by its range. When a stack underflow occurs,
or when the sorts present in the stack are not the ones expected by the operator, the stack goes into an
error condition which is propagated by successive operations. A term is an [oplist] that produces
a stack of length one, when execution starts from the empty stack. Operation symbols are executed in
order from the last element of the [oplist] to the first.
*)

Local Definition oplist (σ: signature):= list (names σ).

Bind Scope list_scope with oplist.

Identity Coercion oplistislist: oplist >-> list.

Local Corollary isasetoplist (σ: signature): isaset (oplist σ).
Proof.
  apply isofhlevellist.
  apply setproperty.
Defined.

Local Definition stackstatus: UU := maybe nat.

Local Lemma isasetstackstatus: isaset stackstatus.
Proof.
  apply isasetmaybe.
  apply isasetnat.
Defined.

Section Oplists.

  Context {σ: signature}.

  (** *** The [opexec] and [oplistexec] functions. *)
  (**
     The function [opexec nm] is the stack transformation corresponding to the execution of
     the operation symbol [nm], while [oplistexec l] returns the stack corresponding to the
     execution of the entire oplist [l] starting from the empty stack. The list is executed from the last
     to the first operation symbol. Finally [isaterm l] holds when the result of [oplistexec l]
     is a stack of length one.
   *)

  Local Definition opexec (nm: names σ): stackstatus → stackstatus.
  Proof.
    apply flatmap.
    intro sl.
    induction (isdecrelnatgth (arity nm) sl) as [arityerr | arityok].
    - exact nothing.
    - exact (just (S (sl - (arity nm)))).
  Defined.

  Local Definition oplistexec (l: oplist σ): stackstatus := foldr opexec (just 0) l.

  Local Definition isaterm (l: oplist σ): UU := oplistexec l = just 1.

  Local Lemma isapropisaterm (l: oplist σ): isaprop (isaterm l).
  Proof.
    apply isasetstackstatus.
  Defined.

  Local Lemma opexec_dec (nm: names σ) (sl: nat)
    : (opexec nm (just sl) = nothing × arity nm > sl)
        ⨿  (opexec nm (just sl) = just (S (sl - arity nm )) × arity nm ≤ sl).
  Proof.
    unfold opexec, just.
    simpl.
    induction (isdecrelnatgth (arity nm) sl) as [arityerr | arityok].
    - apply ii1.
      split.
      + apply idpath.
      + assumption.
    - simpl.
      apply ii2.
      split.
      + apply idpath.
      + apply negnatgthtoleh.
        assumption.
  Defined.

  Local Lemma opexec_just_f (nm: names σ) (sl: nat) (arityok: arity nm ≤ sl)
    : opexec nm (just sl) = just (S (sl - arity nm)).
  Proof.
    induction (opexec_dec nm sl) as [execdecerr | execdecok].
    - induction execdecerr as [_  arityerr].
      apply natlehneggth in arityok.
      contradiction.
    - exact (pr1 execdecok).
  Defined.

  Local Lemma opexec_just_b (nm: names σ) (st: stackstatus) (sl': nat)
   : opexec nm st = just sl' → st = just (sl' - 1 + arity nm).
  Proof.
    intro execok.
    induction st as [sl | serror].
    - induction (opexec_dec nm sl) as [execdecerr | execdecok].
      + induction execdecerr as [execerr _].
        set (C := ! execok @ execerr).
        contradiction (negpathsii1ii2 _ _ C).
      + induction execdecok as [execok1 arityok].
        set (H := ! execok @ execok1).
        apply ii1_injectivity in H.
        apply maponpaths.
        rewrite H.
        change (sl = 1 + (sl - arity nm) - 1 + arity nm).
        rewrite (natpluscomm 1 (sl - arity nm)).
        rewrite plusminusnmm.
        rewrite (minusplusnmm _ _ arityok).
        apply idpath.
    - simpl in execok.
      apply negpathsii2ii1 in execok.
      contradiction.
  Defined.

  Local Lemma opexec_zero_b (nm: names σ) (st: stackstatus)
    : ¬ (opexec nm st = just 0).
  Proof.
    induction st as [sl | sterror].
    - simpl.
      induction (isdecrelnatgth (arity nm) sl).
      + simpl.
        apply negpathsii2ii1.
      + simpl.
        intro C.
        apply ii1_injectivity in C.
        apply negpathssx0 in C.
        assumption.
    - simpl.
      apply negpathsii2ii1.
Defined.

  Local Lemma oplistexec_nil
    : oplistexec (nil: oplist σ) = just 0.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistexec_cons (nm: names σ) (l: oplist σ)
    : oplistexec (nm :: l) = opexec nm (oplistexec l).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistexec_zero_b (l: oplist σ): oplistexec l = just 0 → l = nil.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs _ lstack.
      apply opexec_zero_b in lstack.
      contradiction.
  Defined.

  Local Lemma oplistexec_positive_b (l: oplist σ) (sl: nat)
    : oplistexec l = just (S sl) → ∑ (x: names σ) (xs: oplist σ), l = x :: xs.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - intro nilstack.
      cbn in nilstack.
      apply ii1_injectivity in nilstack.
      apply negpaths0sx in nilstack.
      contradiction.
    - intros x xs _ lstack.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  (** *** Lemmas on natural numbers. *)

  Local Lemma natlehsntolrhn (a b: nat): S b ≤ a → b ≤ a.
  Proof.
    intro H.
    apply natlthtoleh.
    apply natlehsntolth.
    assumption.
  Defined.

  Local Lemma natlemma1 (a b: nat): a ≥ b → S (a - b) = S a - b.
  Proof.
    revert b.
    induction a.
    - intro b.
      intro H.
      apply nat0gehtois0 in H.
      rewrite H.
      apply idpath.
    -  induction b.
      + intro. apply idpath.
      + intro H.
        change (S (a - b) = S a - b).
        apply (IHa b H).
  Defined.

  Local Lemma natminuscomm (a b c: nat) (ok: a ≥ b): (a - b) + c = (a + c) - b.
  Proof.
    induction c.
    - repeat rewrite natplusr0.
      apply idpath.
    - repeat rewrite <- plus_n_Sm.
      rewrite IHc.
      apply natlemma1.
      eapply istransnatgeh.
      + apply natgehplusnmn.
      + assumption.
  Defined.

  (** *** The [stackconcatenate] function. *)

  (**
  [stackconcatenate] simply sum two stacks, possibly propagating  erroneous states.
  *)

  Local Definition stackconcatenate (st1 st2: stackstatus): stackstatus
    := flatmap (λ st2', flatmap (λ st1', just (st1' + st2')) st1) st2.

  Local Lemma stackconcatenate_opexec (nm: names σ) (st1 st2: stackstatus)
    : opexec nm st1 != nothing
      → stackconcatenate (opexec nm st1) st2 = opexec nm (stackconcatenate st1 st2).
  Proof.
    intro opexecok1.
    induction st1 as [sl1 | ].
    2: contradiction.
    induction st2 as [sl2 | ].
    2: reflexivity.
    induction (opexec_dec nm sl1) as [opexecdecerr1 | opexecdecok1].
    - induction opexecdecerr1 as [opexecerr1  _].
      contradiction.
    - induction opexecdecok1 as [opexecok1' arityok1].
      unfold just in opexecok1'.
      rewrite opexecok1'.
      change (just (S (sl1 - arity nm + sl2)) = opexec nm (just (sl1 + sl2))).
      rewrite opexec_just_f.
      + apply maponpaths.
        apply maponpaths.
        apply natminuscomm.
        assumption.
      + eapply istransnatleh.
        * exact arityok1.
        * apply natlehnplusnm.
  Defined.

  Local Lemma oplistexec_concatenate (l1 l2: oplist σ)
  : oplistexec l1 != nothing
    → oplistexec (concatenate l1 l2)
      = stackconcatenate (oplistexec l1) (oplistexec l2).
  Proof.
  revert l1.
  refine (list_ind _ _ _).
  - intros.
    change ([] ++ l2) with (l2).
    induction (oplistexec l2) as [l2ok | l2error].
    + apply idpath.
    + induction l2error.
      apply idpath.
  - intros x xs IHxs noerror.
    change (oplistexec (x :: xs)) with (opexec x (oplistexec xs))  in *.
    rewrite stackconcatenate_opexec by (assumption).
    rewrite <- IHxs.
    + apply idpath.
    + intro error.
      rewrite error in noerror.
      contradiction.
  Defined.

  (** *** The [oplistsplit] function. *)

  (**
     [oplistsplit] splits an oplist into an oplist of up to [n] terms and an oplist of the remaining
     terms.
   *)

  Local Definition oplistsplit (l: oplist σ) (n: nat): oplist σ × oplist σ.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - intros.
      exact (nil ,, nil).
    - intros x xs IHxs n.
      induction n.
      + exact (nil,, (x :: xs)).
      + induction (IHxs (arity x + n)) as [IHfirst IHsecond].
        exact ((x :: IHfirst) ,, IHsecond).
  Defined.

  Local Lemma oplistsplit_zero (l: oplist σ): oplistsplit l 0 = nil,, l.
  Proof.
    revert l.
    refine (list_ind _ _ _) ; reflexivity.
  Defined.

  Local Lemma oplistsplit_nil (n: nat): oplistsplit nil n = nil,, nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_cons (x: names σ) (xs: oplist σ) (n: nat)
    : oplistsplit (x :: xs) (S n)
      = (x :: (pr1 (oplistsplit xs (arity x + n)))) ,, (pr2 (oplistsplit xs (arity x + n))).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_concatenate (l1 l2: oplist σ) (n sl: nat)
    : oplistexec l1 = just sl → n ≤ sl
      → oplistsplit (l1 ++ l2) n
        = make_dirprod (pr1 (oplistsplit l1 n)) (pr2 (oplistsplit l1 n) ++ l2).
  Proof.
    revert l1 sl n.
    refine (list_ind _ _ _).
    - intros sl n oplistexecnil nlehsl.
      apply ii1_injectivity in oplistexecnil.
      rewrite <- oplistexecnil in nlehsl.
      apply natleh0tois0 in nlehsl.
      rewrite nlehsl.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x1 xs1 IHxs1 ss n oplistexec1 nlehsl.
      change ((x1 :: xs1) ++ l2) with (x1 :: (xs1 ++ l2)).
      induction n.
      + apply idpath.
      + change (oplistexec (x1 :: xs1)) with (opexec x1 (oplistexec xs1)) in oplistexec1.
        apply opexec_just_b in oplistexec1.
        eset (IHinst := IHxs1 (ss - 1 + arity x1) ((arity x1) + n) oplistexec1 _).
        do 2 rewrite oplistsplit_cons.
        apply pathsdirprod.
        * cbn.
          apply maponpaths.
          apply (maponpaths pr1) in IHinst.
          cbn in IHinst.
          assumption.
        * apply (maponpaths dirprod_pr2) in IHinst.
          assumption.
     Unshelve.
     rewrite natpluscomm.
     apply natlehandplusr.
     apply natltminus1.
     exact nlehsl.
  Defined.

  Local Lemma concatenate_oplistsplit (l: oplist σ) (n: nat): pr1 (oplistsplit l n) ++ pr2 (oplistsplit l n) = l.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs IHxs n.
      induction n.
      + apply idpath.
      + rewrite oplistsplit_cons.
        simpl.
        rewrite concatenateStep.
        apply maponpaths.
        apply IHxs.
  Defined.

  Local Lemma oplistexec_oplistsplit (l: oplist σ) {sl: nat} (n: nat)
    : oplistexec l = just sl → n ≤ sl
      →  oplistexec (pr1 (oplistsplit l n)) = just n
         × oplistexec (pr2 (oplistsplit l n)) = just (sl - n).
    Proof.
    revert l sl n.
    refine (list_ind _ _ _).
    - intros sl n oplistexecnil nlehsl.
      apply ii1_injectivity in oplistexecnil.
      rewrite <- oplistexecnil in *.
      apply natleh0tois0 in nlehsl.
      rewrite nlehsl.
      repeat split.
    - intros x xs IHxs sl n oplistexecl nlehsl.
      induction n.
      + rewrite oplistsplit_zero.
        repeat split.
        rewrite natminuseqn.
        assumption.
      + rewrite oplistsplit_cons.
        simpl.
        change (oplistexec (x :: xs)) with (opexec x (oplistexec xs)) in oplistexecl.
        apply opexec_just_b in oplistexecl.
        eset (IHinst := IHxs (sl - 1 + arity x) (arity x + n) oplistexecl _).
        induction IHinst as  [ t1def t2def ] .
        split.
        * rewrite oplistexec_cons.
          rewrite t1def.
          rewrite opexec_just_f.
          -- do 2 apply maponpaths.
             rewrite <- natminuscomm.
             ++ rewrite minuseq0'.
                apply idpath.
             ++ apply isreflnatgeh.
          -- apply natlehnplusnm.
        * rewrite t2def.
          apply maponpaths.
          rewrite <- natminusminusassoc.
          rewrite plusminusnmm.
          rewrite natminusminusassoc.
          apply idpath.
   Unshelve.
   rewrite natpluscomm.
   apply natlehandplusr.
   apply natltminus1.
   exact nlehsl.
  Defined.

  Local Corollary oplistsplit_self {l: oplist σ} {sl: nat}
    : oplistexec l = just sl → oplistsplit l sl = l ,, nil.
  Proof.
    intro lstack.
    set (H := oplistexec_oplistsplit l sl lstack (isreflnatleh sl)).
    induction H as [t1def t2def].
    set (normalization := concatenate_oplistsplit l sl).
    rewrite minuseq0' in t2def.
    apply oplistexec_zero_b in t2def.
    rewrite t2def in normalization.
    rewrite concatenate_nil in normalization.
    induction (oplistsplit l sl) as [l1 l2].
    apply total2_paths2.
    - assumption.
    - assumption.
  Defined.

End Oplists.

Section Term.

  (** ** Terms and related constructors and destructors. *)

  (**  A [term] is an oplist together with the proof it is a term. *)

  Local Definition term (σ: signature): UU
    := ∑ t: oplist σ, isaterm t.

  Definition make_term {σ: signature} {l: oplist σ} (lstack: isaterm l)
    : term σ := l ,, lstack.

  Coercion term2oplist {σ: signature}: term σ → oplist σ := pr1.

  Definition term2proof {σ: signature}: ∏ t: term σ, isaterm t := pr2.

  Lemma isasetterm (σ: signature): isaset (term σ).
  Proof.
    apply isaset_total2.
    - apply isasetoplist.
    - intros.
      apply isasetaprop.
      apply isasetstackstatus.
  Defined.

  Local Definition termset (σ: signature): hSet
    := make_hSet (term σ) (isasetterm σ).

  Context {σ: signature}.

  Lemma term_extens {t1 t2 : term σ} (p : term2oplist t1 = term2oplist t2)
    : t1 = t2.
  Proof.
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    assumption.
  Defined.

  (** *** The [vecoplist2oplist] and [oplist2vecoplist] functions *)
  (**
  These functions transform a vec of [n] oplists into an oplists of stack [n]
  ([vecoplist2oplist]) and viceversa ([oplist2vecoplist]).
  *)

  Local Definition vecoplist2oplist {n: nat} (v: vec (oplist σ) n): oplist σ
    := vec_foldr concatenate nil v.

  Local Lemma vecoplist2oplist_vcons {n: nat} (x: oplist σ) (v: vec (oplist σ) n)
    : vecoplist2oplist (x ::: v) = concatenate x (vecoplist2oplist v).
  Proof.
    apply idpath.
  Defined.

  Local Lemma vecoplist2oplist_inj {n: nat} {v1 v2: vec (term σ) n}
    : vecoplist2oplist (vec_map term2oplist v1) = vecoplist2oplist (vec_map term2oplist v2)
      → v1 = v2.
  Proof.
    induction n.
    - intros.
      induction v1.
      induction v2.
      apply idpath.
    - intro eq.
      induction v1 as [v1x v1xs].
      induction v2 as [v2x v2xs].
      simpl in eq.
      apply (maponpaths (λ l, oplistsplit l 1)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 1 (term2proof v1x) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 1 (term2proof v2x) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_self (term2proof v1x)) in eq.
      rewrite (oplistsplit_self (term2proof v2x)) in eq.
      cbn in eq.
      simpl.
      apply map_on_two_paths.
      + apply subtypePairEquality'.
        * apply (maponpaths pr1 eq).
        * apply isapropisaterm.
      + apply IHn.
        apply (maponpaths (λ l, pr2 l: oplist σ) eq).
  Defined.

  Local Lemma oplistexec_vecoplist2oplist {n: nat} {v: vec (term σ) n}
    : oplistexec (vecoplist2oplist (vec_map term2oplist v)) = just n.
  Proof.
    induction n.
    - induction v.
      reflexivity.
    - induction v as [vx vxs].
      simpl in *.
      rewrite oplistexec_concatenate.
      + rewrite IHn.
        rewrite (term2proof vx).
        apply idpath.
      + rewrite (term2proof vx).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist {n: nat} (l: oplist σ) (lstack: oplistexec l = just n)
    : ∑ (v: vec (term σ) n)
        , (hvec (vec_map (λ t, hProptoType (length (term2oplist t) ≤ length l)) v))
          × vecoplist2oplist (vec_map  term2oplist v) = l.
  Proof.
    revert n l lstack.
    induction n.
    - intros.
      exists vnil.
      exists hnil.
      apply oplistexec_zero_b in lstack.
      rewrite lstack.
      apply idpath.
    - intros l lstack.
      induction (oplistexec_oplistsplit l 1 lstack (natleh0n 0)) as [firststackp reststackp].
      set (first := pr1 (oplistsplit l 1)) in *.
      set (rest := pr2 (oplistsplit l 1)) in *.
      change (S n) with (1 + n) in reststackp.
      rewrite <- (natminuscomm _ _ _ (isreflnatgeh 1)) in reststackp.
      rewrite minuseq0' in reststackp.
      induction (IHn rest reststackp) as [v [vlen vflatten]].
      exists (vcons (make_term firststackp) v).
      repeat split.
      + change (length first ≤ length l).
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist1.
      + change (hvec (vec_map (λ (t: term σ), hProptoType (length (term2oplist t) ≤ length l)) v)).
        eapply (h1map (λ  _ p, istransnatleh p _) vlen).
        Unshelve.
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist2.
      + simpl.
        unfold h1map_vec in vflatten.
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  (** ** Constructors and destuctors. *)

  (** [build_term] builds a term starting from principal operation symbol and subterms, while
  [princop] and [subterms] are the corresponding destructors. *)

  Local Definition oplist_build (nm: names σ) (v: vec (oplist σ) (arity nm))
    : oplist σ := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_isaterm (nm: names σ) (v: vec (term σ) (arity nm))
    : isaterm (oplist_build nm (vec_map term2oplist v)).
  Proof.
    unfold oplist_build, isaterm.
    rewrite oplistexec_cons.
    rewrite oplistexec_vecoplist2oplist.
    rewrite opexec_just_f.
    - rewrite minuseq0'.
      apply idpath.
    - apply isreflnatleh.
  Defined.

  Local Definition build_term (nm: names σ) (v: vec (term σ) (arity nm)): term σ.
  Proof.
    exists (oplist_build nm (vec_map term2oplist v)).
    apply oplist_build_isaterm.
  Defined.

  Local Definition term_decompose (t: term σ) :
    ∑ (nm:names σ) (v: vec (term σ) (arity nm))
      , (hvec (vec_map (λ t', hProptoType (length (term2oplist t') < length t)) v))
         × oplist_build nm (vec_map term2oplist v) = t.
  Proof.
    induction t as [l lstack].
    cbv [pr1 term2oplist].
    revert l lstack.
    refine (list_ind _ _ _).
    - intro lstack.
      apply ii1_injectivity in lstack.
      apply negpaths0sx in lstack.
      contradiction.
    - intros x xs IHxs lstack.
      exists x.
      unfold isaterm in lstack.
      rewrite oplistexec_cons in lstack.
      apply opexec_just_b in lstack.
      rewrite minuseq0' in lstack.
      induction (oplist2vecoplist xs lstack) as [vtail [vlen vflatten]].
      exists vtail.
      split.
      + exact (h1map (λ  _ p, natlehtolthsn _ _ p) vlen).
      + unfold oplist_build.
        rewrite <- vflatten.
        apply idpath.
  Defined.

  Definition princop (t: term σ): names σ
    := pr1 (term_decompose t).

  Definition subterms (t: term σ): vec (term σ) (arity (princop t))
    := pr12 (term_decompose t).

  Local Definition subterms_length (t: term σ)
    : hvec (vec_map (λ t', hProptoType (length (term2oplist t') < length t)) (subterms t))
    := pr122 (term_decompose t).

  Local Definition oplist_normalization (t: term σ)
     : term2oplist (build_term (princop t) (subterms t)) = t
     := pr22 (pr2 (term_decompose t)).

  (** *** Term normalization *)
  (**
    We prove that [princop (build_term nm v) = nm], [subterms (build_term nm v) = v] and
    [build_term (princop t) (subterms t))] is equal to [t] modulo [transport].
  *)

  Local Lemma term_normalization (t: term σ)
     : build_term (princop t) (subterms t) = t.
  Proof.
    unfold princop, subterms.
    induction (term_decompose t) as [nm [v [vlen normalization]]].
    change (build_term nm v = t).
    apply subtypePairEquality'.
    - apply normalization.
    - apply isapropisaterm.
  Defined.

  Local Lemma princop_build_term (nm: names σ) (v: vec (term σ) (arity nm))
    : princop (build_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Local Lemma subterms_build_term (nm: names σ) (v: vec (term σ) (arity nm))
    : subterms (build_term nm v) = v.
  Proof.
    set (tnorm := term_normalization (build_term nm v)).
    apply (maponpaths pr1) in tnorm.
    simpl in tnorm.
    apply cons_inj2 in tnorm.
    apply vecoplist2oplist_inj in tnorm.
    apply tnorm.
  Defined.

  (** *** Miscellanea properties for terms. *)

  Local Lemma length_term (t: term σ): length t > 0.
  Proof.
    induction t as [l stackl].
    induction (oplistexec_positive_b _ _ stackl) as [x [xs lstruct]].
    induction (! lstruct).
    apply idpath.
  Defined.

  Local Lemma term_notnil {X: UU} {t: term σ}: length t ≤ 0 → X.
  Proof.
    intro tlen.
    apply natlehneggth in tlen.
    contradicts tlen (length_term t).
  Defined.

End Term.

(** ** Term induction. *)

(**
If [P] is a map from terms to properties, then [term_ind_HP P] is the inductive hypothesis for terms:
given an operation symbol [nm], a sequence of terms of type specified by the arity of [nm], a proof of
the property [P] for eache of the terms in [v], we need a proof of [P] for the term built from [nm] and [v].
*)

Section TermInduction.

  Context {σ: signature}.

  Definition term_ind_HP (P: term σ → UU) :=
    ∏ (nm: names σ)
      (v: vec (term σ) (arity nm))
      (IH: hvec (vec_map P v))
    , P (build_term nm v).

  (**
  The proof of the induction principle [term_ind] for terms proceeds by induction on the lenght of
  the oplist forming the terms in [term_ind_onlength].
  *)

  Local Lemma term_ind_onlength (P: term σ → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (t: term σ), length t ≤ n →  P t.
  Proof.
    induction n.
    - intros t tlen.
      exact (term_notnil tlen).
    - intros t tlen.
      apply (transportf _ (term_normalization t)).
      apply (R (princop t) (subterms t)).
      refine (h1map _ (subterms_length t)).
      intros.
      apply IHn.
      apply natlthsntoleh.
      eapply natlthlehtrans.
      + exact X.
      + exact tlen.
  Defined.
(*
  Lemma term_ind_onlength_step (P: term σ s → UU) (R: term_ind_HP P) (nm: names σ) (v: vec (term σ) (arity nm))
    : ∏ (n: nat) (tlehn:  length (build_term nm v) ≤ n),
        term_ind_onlength P R n _ _ tlehn
        =  R nm v (transportf (λ x, hvec (hmap_vec P x))
                              (subterms_build_term nm v)
                              (hhmap (subterms_length (build_term nm v)) (λ s t p, term_ind_onlength P R n s t (istransnatleh (natlthtoleh _ _ p) tlehn)))).


: term_ind P R (build_term nm v) = R nm v (hmap (λ t, term_ind P R t) v).
*)

  Theorem term_ind (P: term σ → UU) (R: term_ind_HP P) (t: term σ): P t.
  Proof.
    exact (term_ind_onlength P R (length t) t (isreflnatleh _)).
  Defined.

  (** *** Term induction step *)

  (** In order to use term_induction, we need to prove an unfolding property. For example, for natural
  number induction the unfolding property is [nat_rect P a IH (S n) = IH n (nat_rect P a IH n)], in our
  case is given by [term_ind_step].
  *)

  Local Lemma term_ind_onlength_nirrelevant (P: term σ → UU) (R: term_ind_HP P)
    : ∏ (n m1 m2: nat)
        (m1lehn: m1 ≤ n) (m2lehn: m2 ≤ n)
        (t: term σ)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , term_ind_onlength P R m1 t lenm1 = term_ind_onlength P R m2  t lenm2.
  Proof.
    induction n.
    - intros.
      exact (term_notnil (istransnatleh lenm1 m1lehn)).
    - intros.
      induction m1.
      + exact (term_notnil lenm1).
      + induction m2.
        * exact (term_notnil lenm2).
        * simpl.
          do 2 apply maponpaths.
          apply (maponpaths (λ x, h1map x _)).
          do 2 (apply funextsec; intro).
          apply IHn.
          -- apply m1lehn.
          -- apply m2lehn.
  Defined.

  Local Lemma nat_rect_step {P: nat → UU} (a: P 0) (IH: ∏ n: nat, P n → P (S n)) (n: nat):
    nat_rect P a IH (S n) = IH n (nat_rect P a IH n).
  Proof. apply idpath. Defined.

  Local Lemma paths_rect_step (A : UU) (a : A) (P : ∏ a0 : A, a = a0 → UU) (x: P a (idpath a))
     : paths_rect A a P x a (idpath a) = x.
  Proof. apply idpath. Defined.

  Lemma term_ind_step (P: term σ  → UU) (R: term_ind_HP P) (nm: names σ) (v: vec (term σ) (arity nm))
    : term_ind P R (build_term nm v) = R nm v (h1map (λ t _, term_ind P R t) (h1lift v)).
  Proof.
    unfold term_ind.
    set (t := build_term nm v) in *.
    simpl (length t).
    unfold term_ind_onlength at 1.
    rewrite nat_rect_step.
    set (v0len := subterms_length t).
    set (v0norm := term_normalization t).
    clearbody v0len v0norm.  (* Needed to make induction work *)
    change (princop t) with nm in *.
    induction (! (subterms_build_term nm v: subterms t = v)).
    change (build_term nm v = t) in v0norm.
    assert (v0normisid: v0norm = idpath _).
    {
      apply proofirrelevance.
      apply isasetterm.
    }
    induction (! v0normisid).
    rewrite idpath_transportf.
    apply maponpaths.
    rewrite (h1map_h1lift v v0len).
    apply (maponpaths (λ x, h1map x _)).
    repeat (apply funextsec; intro).
    apply (term_ind_onlength_nirrelevant P R  (pr1 (vecoplist2oplist (vec_map term2oplist v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh.
      apply x0.
  Defined.

  (** *** Immediate applications of term induction *)

  (**
  [depth] returns the depth of a term, while [fromterm] is the evaluation map from terms
  to an algebra. Finally, [fromtermstep] is the unfolding property for [fromterm].
  *)

  Definition depth: term σ → nat
    := term_ind (λ _, nat)
                (λ (nm: names σ) (v: vec (term σ) (arity nm)) (depths: hvec (vec_map (λ _ , nat) v)),
                   1 + h1foldr (λ _, max) 0 depths).

  Local Definition fromterm {A: UU} (op : ∏ (nm : names σ), vec A (arity nm) → A)
    : term σ → A
    := term_ind (λ _, A) (λ nm v rec, op nm (h1lower rec)).

  Lemma fromtermstep {A: UU} (nm: names σ)
                     (op : ∏ (nm : names σ), vec A (arity nm) → A)
                     (v:  vec (term σ) (arity nm))
    : fromterm op (build_term nm v) = op nm (vec_map (@fromterm A op) v).
  Proof.
    unfold fromterm.
    rewrite term_ind_step.
    rewrite h1lower_h1map_h1lift.
    apply idpath.
  Defined.

  Lemma build_term_inj (nm1 nm2: names σ) (v1: vec (term σ) (arity nm1)) (v2: vec (term σ) (arity nm2))
    : build_term nm1 v1 = build_term nm2 v2 → ∑ eqnm: nm1 = nm2, (transportf (λ op, vec (term σ) (arity op)) eqnm v1) = v2.
  Proof.
    intro X.
    unfold build_term in X.
    unfold oplist_build in X.
    apply (maponpaths pr1) in X.
    simpl in X.
    pose (eqnm := X).
    apply cons_inj1 in eqnm.
    exists eqnm.
    induction eqnm.
    apply cons_inj2 in X.
    apply vecoplist2oplist_inj in X.
    exact X.
  Defined.

End TermInduction.

(** ** Notations for ground terms. *)
(**
Since [term], [termset], [fromterm] and [fromtermstep]  will be redefined in
[UniMath.Algebra.Universal.Multisorted.VTerms] in their more general form with variables, we introduce
here notations [gterm], [make_gterm] and similar to make the ground version publically
available with special names.
*)

Notation gterm := term.

Notation gtermset := termset.

Notation fromgterm := fromterm.

Notation fromgtermstep := fromtermstep.

Notation build_gterm := build_term.

(** *** Helpers for working with curried functions. *)

Definition build_gterm' {σ: signature} (nm: names σ)
  : Vectors.iterfun (arity nm) (term σ) (term σ)
  := Vectors.currify (build_term nm).
