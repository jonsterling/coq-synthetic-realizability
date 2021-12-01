From synrl Require Import Preamble.

Definition trm (A : Type) : A → 𝟙 :=
  λ _, I.

Definition is_isomorphism {A B} (f : A → B) : Prop :=
  ∀ x : B, exists! y : A, f y = x.

Lemma balanced {A B} (f : A → B) : injective f → surjective f → is_isomorphism f.
Proof.
  move=> inj surj b.
  case: (surj b)=> a ha.
  exists a; split=>//=.
  move=> a' ha'.
  apply: inj.
  by congruence.
Qed.

Lemma balanced_converse {A B} (f : A → B) : is_isomorphism f → injective f ∧ surjective f.
Proof.
  move=> iso; split.
  - move=> a a' h.
    case: (iso (f a)) (iso (f a'))=> [za [hza1 /(_ a') hza2]] [za' [hza'1 hza'2]].
    by move: (hza'2 za) (hza'2 a); rewrite hza2//=; move=> <-//= <-//=; congruence.
  - move=> b.
    case: (iso b)=> a [ha1 _].
    by exists a.
Qed.

Definition restrict_fam {I A A'} (θ : A → A') (X : I → Type) :
  ∀ i, (A' → X i) → (A → X i).
Proof. by move=> i f a; apply/f/θ/a. Defined.

Definition orthogonal_to {I A A'} (θ : A → A') (X : I → Type) : Prop :=
  ∀ i, is_isomorphism (restrict_fam θ X i).

Infix "⫫" := orthogonal_to (at level 10).

Definition orthogonal_to_type {I} (A : Type) (X : I → Type) := trm A ⫫ X.

Notation "{ A } ⫫ X" := (orthogonal_to_type A X) (at level 10).

Definition has_surjection (E B : Type) : Prop := ∃ f : E → B, surjective f.
Infix "⇾" := has_surjection (right associativity, at level 60).

Lemma covers_𝟙_inh {A} : A ⇾ 𝟙 → ∃ x : A, True.
Proof.
  move=> [p psurj].
  case: (psurj _)=> a _.
  by exists a.
Qed.


Lemma orth_surj {I A B} {X : I → Type} : A ⇾ B → {A} ⫫ X → {B} ⫫ X.
Proof.
  move=> [p psurj] orthA i f.
  case: (orthA i (λ a : A, f (p a)))=> xi [/equal_f h1xi h2xi].
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

Lemma inh_orth_closed_under_subobjects {I A} {X : I → Type} {P : ∀ i, X i → Prop} :
  A ⇾ 𝟙
  → {A} ⫫ X
  → {A} ⫫ λ i, {x : X i | P i x}.
Proof.
  move=> /covers_𝟙_inh [a0 _] X_orth i f.
  case: (X_orth i (λ a, sval (f a)))=> xi [h1xi h2xi].
  unshelve esplit.
  - move=> u.
    unshelve esplit.
    + by apply: (xi).
    + rewrite /restrict_fam in h1xi.
      move: (equal_f h1xi a0)=> h.
      rewrite (_ : trm A a0 = u) in h; first by [].
      rewrite h.
      apply: svalP.
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

Definition to_slice {A B} I (f : A → B) : I * A → I * B :=
  λ u, (fst u, f (snd u)).

Lemma surjection_to_slice {X E B} (p : E → B) :
  surjective p
  → surjective (to_slice X p).
Proof.
  move=> psurj [x b].
  case: (psurj b)=> e he.
  exists (x, e).
  by rewrite /to_slice he.
Qed.

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

(** Proposition 2.5 of HRR87 *)
Lemma orth_reduce_to_pair {I A} {X : I → Type} :
  A ⇾ 𝟙
  → (∀ i, ∀ u : A → X i, ∀ a1 a2 : A, u a1 = u a2)
  → {A} ⫫ X.
Proof.
  move=> /covers_𝟙_inh [a0 _] h i xi.
  unshelve esplit.
  - move=> u.
    apply: xi.
    exact: a0.
  - split.
    + rewrite /restrict_fam.
      apply: funext=>?.
      by apply: h.
    + move=> xi0.
      rewrite /restrict_fam.
      move/equal_f/(_ a0)=> h'.
      apply: funext=> u.
      rewrite -h'.
      by congr xi0.
Qed.

Lemma orth_reduce_to_pair_converse {I A} {X : I → Type} :
  A ⇾ 𝟙
  → {A} ⫫ X
  → ∀ i, ∀ u : A → X i, ∀ a1 a2 : A, u a1 = u a2.
Proof.
  move=> /covers_𝟙_inh [a0 _] orthA i u a1 a2.
  case: (orthA i u)=> xi [/equal_f h1xi h2xi].
  rewrite /restrict_fam in h1xi, h2xi.
  by rewrite -(h1xi a1) -(h1xi a2).
Qed.

(** Proposition 2.7 of HRR87 *)
Lemma orth_surj_converse {I A B} {X : I → Type} (a : bool → A) :
  B ⇾ A
  → A ⇾ 𝟙
  → surjective (B ^[ a ])
  → {A} ⫫ X
  → {B} ⫫ X.
Proof.
  move=> [p psurj] /covers_𝟙_inh [a0 _] asurjB orthA.
  apply: orth_reduce_to_pair.
  - unshelve esplit; first by [].
    move=> u.
    case: (psurj a0)=> b _.
    by exists b.
  - move=> i u b1 b2.
    pose b12 := (λ i, if i then b1 else b2).
    rewrite (eq_refl : b1 = b12 true) (eq_refl : b2 = b12 false).
    move: {b1 b2} b12.
    apply: equal_f.
    apply: (surjection_cancel (B ^[a]) asurjB).
    apply: funext=> b //=.
    rewrite /precomp.
    case: (orthA i (u ∘ b))=> xi [/equal_f h1xi h2xi].
    rewrite /restrict_fam /comp in h1xi, h2xi.
    by rewrite -(h1xi (a true)) (h1xi (a false)).
Qed.
