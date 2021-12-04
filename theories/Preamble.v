Require Export ssreflect ssrfun Unicode.Utf8.
From HB Require Export structures.
Require Export Coq.Logic.Description Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality Program.Equality.

Set Primitive Projections.

(* NOTE: Universe Polymorphism must not be turned on, as this actually
causes axioms from Set to be lifted to Type!!! That's so messed
up!! *)
Unset Universe Polymorphism.

Export EqNotations.


Definition surjective {E B} (f : E → B) : Prop :=
  ∀ x : B, ∃ y : E, f y = x.


Arguments proj1_sig {A P}.
Notation sval := proj1_sig.

Definition iota {X : Type} (P : X → Prop) (h : exists! x, P x) : X :=
  proj1_sig (constructive_definite_description _ h).

Lemma iota_prop {X : Type} (P : X → Prop) (h : exists! x, P x) : P (iota P h).
Proof. rewrite /iota; apply proj2_sig. Qed.

Definition extract {X : Type} {P : X → Prop} : (∀ x y, P x → P y → x = y) → (∃ x, P x) → X.
Proof.
  move=> H J.
  apply: (@iota X P).
  case: J=> x xP.
  exists x; split=>//.
  by move=>?; apply: H.
Defined.

Definition extract_prop {X : Type} {P : X → Prop} : ∀ H J, P (@extract X P H J).
Proof.
  move=> ? ?.
  apply: iota_prop.
Qed.

Opaque extract.

Class Functional {A B} (R : A → B → Prop) :=
  func : ∀ a, exists! b, R a b.

Definition funcompr {A B} R `{Functional A B R} : A → B.
Proof.
  move=> x.
  apply: (iota (λ y : B, R x y)).
  case: (func x)=> y hy.
  by exists y.
Defined.

Definition funcompr_compute {A B} R `{Functional A B R} : ∀ x y, R x y → funcompr R x = y.
Proof.
  move=> x y rxy.
  case: (func x)=> y' [h1 h2].
  rewrite -(h2 (funcompr R x)); first by apply: iota_prop.
  by rewrite -(h2 y).
Qed.

Opaque funcompr.



Module Im.
  Section Im.
    Context {X Y : Type} (f : X → Y).

    Definition T : Type :=
      { y : Y | ∃ x, f x = y }.

    Definition surj : X → T.
    Proof. by move=> x; exists (f x); exists x. Defined.

    Definition inj : T → Y.
    Proof. by apply: proj1_sig. Defined.

    Lemma inj_injective : injective inj.
    Proof. by move=> x y h; apply/eq_sig/proof_irrelevance. Qed.

    Lemma surj_surjective : surjective surj.
    Proof. by move=> [y [x h]]; exists x; apply/eq_sig/proof_irrelevance. Qed.
  End Im.
End Im.

Notation Im := Im.T.

Notation propext := propositional_extensionality.
Notation funext := functional_extensionality.
Notation depfunext := functional_extensionality_dep.
Notation proofirr := proof_irrelevance.

#[global]
Hint Resolve proofirr : core.
Infix "∘" := comp (right associativity, at level 60).
Notation "𝟙" := True.
Notation "𝟚" := bool.


Definition projective (B : Type) : Prop :=
  ∀ E (r : E → B), surjective r → ∃ i : B → E, ∀ b : B, r (i b) = b.

Class Projective (B : Type) :=
  choice : projective B.

Instance : Projective bool.
Proof.
  move=> E p hp.
  case: (hp true)=> e0 he0.
  case: (hp false)=> e1 he1.
  unshelve esplit.
  - case; [exact: e0 | exact: e1].
  - by case.
Qed.


Definition strictly_bipointed (A : Type) : Prop :=
  ∃ a1 a2 : A, ¬ (a1 = a2).

Definition decidable (A : Type) : Prop :=
  ∀ a1 a2 : A, a1 = a2 ∨ ¬ (a1 = a2).

Class Decidable (A : Type) :=
  dcd : decidable A.

Class StrictlyBipointed (A : Type) : Prop :=
  sbptd : strictly_bipointed A.



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

Lemma iso_injective {A B} (f : A → B) : is_isomorphism f → injective f.
Proof.
  move=> iso a a' h.
  case: (iso (f a)) (iso (f a'))=> [za [hza1 /(_ a') hza2]] [za' [hza'1 hza'2]].
  by move: (hza'2 za) (hza'2 a); rewrite hza2//=; move=> <-//= <-//=; congruence.
Qed.

Lemma iso_surjective {A B} (f : A → B) : is_isomorphism f → surjective f.
Proof. by move=> iso b; case: (iso b) => a [? _]; exists a. Qed.




Class IsProp (A : Type) :=
  irr : ∀ {x y : A}, x = y.


Module PropTrunc.
  Definition T (A : Type) : Prop := ∃ x : A, True.

  Definition unit {A} : A → T A.
  Proof. by move=> x; exists x. Defined.

  Global Instance IsProp_Props (A : Prop) : IsProp A.
  Proof. by []. Qed.

  Definition alg {A} `{IsProp A} : T A → A.
  Proof.
    move=> u.
    apply: (iota (λ x : A, True)).
    case: u=> a _.
    exists a; split=>//.
  Qed.

  Lemma alg_beta {A} `{IsProp A} : ∀ x, alg (unit x) = x.
  Proof. by move=>?; apply: irr. Qed.

  Lemma alg_eta {A} `{IsProp A} : ∀ x, unit (alg x) = x.
  Proof. move=>?; apply: irr. Qed.

  Definition ind {A : Type} {B : T A → Type} `{∀ x : T A, IsProp (B x)} : (∀ x : A, B (unit x)) → ∀ x : T A, B x.
  Proof.
    move=> f x; apply: alg; case: x=> x [].
    apply/unit/f.
  Defined.

  Definition rec {A : Type} {B : Type} `{IsProp B} : (A → B) → T A → B.
  Proof. by apply: ind. Defined.

End PropTrunc.




Definition iso_inv {A B} (f : A → B) : is_isomorphism f → B → A.
Proof.
  move=> iso.
  apply: (funcompr (λ b a, f a = b)).
  apply: iso.
Defined.

Lemma iso_inv_beta {A B} (f : A → B) (h : is_isomorphism f) : ∀ x, f (iso_inv f h x) = x.
Proof.
  move=> b.
  rewrite /iso_inv.
  case: (h b)=> a [h1a h2a].
  by rewrite (funcompr_compute (λ b a, f a = b) b a).
Qed.

Lemma iso_inv_iso {A B} (f : A → B) (h : is_isomorphism f) : is_isomorphism (iso_inv f h).
Proof.
  move=> a.
  exists (f a).
  split.
  - rewrite /iso_inv.
    by apply: funcompr_compute.
  - move=> b h'.
    rewrite -h'.
    rewrite /iso_inv.
    by rewrite (funcompr_compute _ b a)  -h' iso_inv_beta.
Qed.

Definition const {B A} : B → A → B :=
  λ b _, b.
