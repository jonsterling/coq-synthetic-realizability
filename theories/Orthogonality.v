From synrl Require Import Preamble.

Definition trm (A : Type) : A → 𝟙 :=
  λ _, I.

Section Orthogonality.
  Context {I A A'} (θ : A → A') (X : I → Type).

  Definition restrict_fam : ∀ i, (A' → X i) → (A → X i) :=
    λ i f a, f (θ a).

  Definition orthogonal_to :=
    ∀ i, is_isomorphism (restrict_fam i).
End Orthogonality.

Class OrthogonalTo {I A A'} (θ : A → A') (X : I → Type) :=
  lift : orthogonal_to θ X.

Infix "⫫" := OrthogonalTo (at level 10).

Notation "[ A ] ⫫ X" := (trm A ⫫ X) (at level 10).

Definition has_surjection (E B : Type) : Prop := ∃ f : E → B, surjective f.

Class Covers (E B : Type) :=
  cov : has_surjection E B.

Infix "⇾" := Covers (right associativity, at level 60).

Lemma covers_𝟙_inh {A} `{A ⇾ 𝟙} : ∃ x : A, True.
Proof.
  case: cov=> p psurj.
  case: (psurj _)=> a _.
  by exists a.
Qed.

Section Covers.
  Context {I} {X : I → Type}.

  Lemma orth_cover {A B} `{A ⇾ B} `{[A] ⫫ X} : [B] ⫫ X.
  Proof.
    move=> i f.
    case: cov=> [p psurj].
    case: (lift i (λ a : A, f (p a)))=> xi [/equal_f h1xi h2xi].
    exists xi; split.
    - apply: funext.
      move=> b.
      case: (psurj b)=> a pab.
      rewrite /restrict_fam.
      have->:(trm B b = trm A a) by [].
      rewrite /restrict_fam in h1xi.
      by rewrite h1xi pab.
    - by move=> ? h; apply/h2xi/funext=>?; rewrite -h.
  Qed.

  Instance orth_subfamily {A} {P : ∀ i, X i → Prop} `{A ⇾ 𝟙} `{[A] ⫫ X} : [A] ⫫ λ i, {x : X i | P i x}.
  Proof.
    case: covers_𝟙_inh=> a0 _.
    move=> i f.
    case: (lift i (λ a, sval (f a)))=> xi [h1xi h2xi].
    unshelve esplit.
    - move=> u.
      unshelve esplit.
      + by apply: (xi).
      + rewrite /restrict_fam in h1xi.
        move: (equal_f h1xi a0)=> h.
        rewrite (_ : trm A a0 = u) in h; first by [].
        rewrite h.
        by apply: svalP.
    - split=>//=.
      + rewrite /restrict_fam.
        apply: funext=> a.
        apply: eq_sig=>//=.
        by apply: (equal_f h1xi).
      + move=> x'i h.
        apply: funext=> u.
        apply: eq_sig=>//=.
        rewrite (h2xi (λ u, sval (x'i u)))//=.
        by rewrite -h.
  Qed.
End Covers.

Lemma surjection_cancel {E B C} (p : E → B) {c1 c2 : B → C} :
  surjective p
  → (c1 ∘ p = c2 ∘ p)
  → c1 = c2.
Proof.
  move=> psurj hc.
  apply: funext=> b.
  case: (psurj b)=> e <-.
  by apply: (equal_f hc).
Qed.

Definition precomp {J A} B (a : J → A) : (A → B) → (J → B) :=
  λ f j, f (a j).

Notation "B ^[ f ]" := (precomp B f) (at level 10).

Lemma covers_compose {A B C} `{A ⇾ B} `{B ⇾ C} : A ⇾ C.
Proof.
  case: (@cov A B)=> f hf.
  case: (@cov B C)=> g hg.
  exists (g ∘ f).
  move=> c.
  case: (hg c)=> b hb.
  case: (hf b)=> a ha.
  by exists a; rewrite /= ha hb.
Qed.

Section Orthogonality.
  Context {I} {X : I → Type}.

  (** Proposition 2.5 of HRR87 *)
  Lemma orth_reduce_to_pair {A} `{A ⇾ 𝟙} :
    (∀ i, ∀ u : A → X i, ∀ a1 a2 : A, u a1 = u a2)
    → [A] ⫫ X.
  Proof.
    case: covers_𝟙_inh=> a0 _.
    move=> h i xi.
    exists (λ _, xi a0); split.
    - rewrite /restrict_fam.
      apply: funext=>?.
      by apply: h.
    - move=> xi0.
      rewrite /restrict_fam.
      move/equal_f/(_ a0)=> h'.
      apply: funext=> u.
      rewrite -h'.
      by congr xi0.
  Qed.

  Lemma orth_reduce_to_pair_converse {A} `{A ⇾ 𝟙} `{[A] ⫫ X}:
    ∀ i, ∀ u : A → X i, ∀ a1 a2 : A, u a1 = u a2.
  Proof.
    case: covers_𝟙_inh=> a0 _.
    move=> i u a1 a2.
    case: (lift i u)=> xi [/equal_f h1xi h2xi].
    rewrite /restrict_fam in h1xi, h2xi.
    by rewrite -(h1xi a1) -(h1xi a2).
  Qed.

  (** Proposition 2.7 of HRR87 *)
  Lemma orth_cover_converse {A B} `{B ⇾ A} `{A ⇾ 𝟙} `{[A] ⫫ X} (a : 𝟚 → A) :
    surjective (B ^[ a ])
    → [B] ⫫ X.
  Proof.
    case: covers_𝟙_inh=> a0 _.
    move=> asurjB.
    apply: orth_reduce_to_pair; first by apply: covers_compose.
    move=> i u b1 b2.
    pose b12 := (λ i, if i then b1 else b2).
    fold (b12 true) (b12 false); move: {b1 b2} b12.
    apply: equal_f.
    apply: surjection_cancel=>//=.
    apply: funext=> b //=.
    rewrite /precomp.
    case: (lift i (u ∘ b))=> xi [/equal_f h1xi h2xi].
    rewrite /restrict_fam /comp in h1xi, h2xi.
    by rewrite -(h1xi (a true)) (h1xi (a false)).
  Qed.
End Orthogonality.
