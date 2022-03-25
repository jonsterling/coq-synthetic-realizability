From synrl Require Import Preamble.

Scheme eq_ind := Induction for eq Sort Type.

Definition is_contr (A : Type) := exists x : A, forall y : A, x = y.

Module Ext.
  Definition L (A : Type) := {ϕ : Prop & ϕ -> A}.
  Definition U := L Type.

  Definition prop : U → Prop.
  Proof. apply: projT1. Defined.

  Definition part : forall A : U, prop A -> Type.
  Proof. apply: projT2. Defined.

  Definition el (X : U) : Type :=
    forall z : prop X, part X z.

  Definition le : Type -> U.
  Proof.
    move=> A.
    exists True => _.
    apply: A.
  Defined.

  Definition elle_fwd {A} : el (le A) → A.
  Proof. by rewrite /el /le; apply. Defined.

  Definition elle_bwd {A} : A -> el (le A).
  Proof. by rewrite /el /le. Defined.

  Definition elle_fwd_bwd {A} : forall x : A, elle_fwd (elle_bwd x) = x.
  Proof. by []. Qed .

  Definition elle_bwd_fwd {A} : forall x : el (le A), elle_bwd (elle_fwd x) = x.
  Proof. by move=> ?; apply: funext; case. Qed.


  Definition extend (ϕ : Prop) (X : ϕ -> U) : U.
  Proof.
    unshelve esplit.
    + refine (ϕ /\ (forall z : ϕ, prop (X z))).
    + move=> z.
      apply: (part (X (fst z))).
      apply: (snd z).
  Defined.

  Lemma rew_partial {A} {ϕ : Prop} (f : ϕ → A) : forall (ψ : Prop) (H : ϕ = ψ) (x : _), (rew [fun z : Prop => z -> A] H in f) x = f (rew <- H in x).
  Proof. by apply: eq_ind. Qed.


  Lemma extend_restricts (ϕ : Prop) (X : ϕ → U) : forall z : ϕ, extend ϕ X = X z.
  Proof.
    move=> u.
    apply: eq_sigT=>//=.
    - apply: propext; split.
      + by case=>?; apply.
      + move=> h; split=>//.
        move=> v.
        rewrite (_ : v = u) //=.
    - move=> H.
      apply: depfunext=> v.
      rewrite rew_partial //=.
      move: (proj1 (rew <- [fun ψ : Prop => ψ] H in v))=> w.
      move: (proj2 (rew <- [fun ψ : Prop => ψ] H in v) w)=> x.
      move: v x.
      rewrite (_ : w = u) {w} //=.
      move=> ??.
      by congr (projT2 (X u)).
  Qed.


  Section iso.
    Context (ϕ : Prop) (X : ϕ → U).

    Definition fwd : (forall z, el (X z)) -> el (extend ϕ X).
    Proof.
      move=> x z.
      apply: x.
    Defined.

    Definition bwd (x : el (extend ϕ X)) : (∀ z, el (X z)).
    Proof.
      move=> u v.
      unfold extend, el in *; simpl in *.
      suff w: ϕ ∧ (∀ z : ϕ, prop (X z)).
      - rewrite (_ : v = snd w u) //= (_ : u = fst w) => //=.
      - abstract by split; first by []; move=> w; rewrite (_ : w = u).
    Defined.

    Lemma fwd_bwd : ∀ x, fwd (bwd x) = x.
    Proof.
      move=> x.
      apply: depfunext=> u.
      rewrite /fwd /bwd /ssr_suff /eq_rect_r //=; cbn.
      apply: JMeq_eq.
      simplify_eqs.
      move: (bwd_subproof _ _)=> v.
      by rewrite (_ : v = u).
    Qed.

    Lemma bwd_fwd : forall x, bwd (fwd x) = x.
    Proof.
      move=> x.
      apply: depfunext=> u.
      apply: depfunext=> v.
      rewrite /fwd /bwd /ssr_suff /eq_rect_r //=.
      apply: JMeq_eq.
      by simplify_eqs.
    Qed.
  End iso.
End Ext.
