From synrl Require Import Preamble Coequalizer.

Set Primitive Projections.

Class Modal (P : Type → Prop) (A : Type) : Prop :=
  mod : P A.

Definition connected (P : Type → Prop) (A : Type) : Prop :=
  ∀ B, Modal P B → @is_isomorphism B (A → B) const.


Class RepleteSubuniverse (P : Type → Prop) :=
  replete : ∀ A B (f : A → B), is_isomorphism f → P A → P B.

Arguments replete P {_} A [B] f iso : rename.

Class LexSubuniverse P : Prop :=
  {connected_eq : ∀ A, connected P A → ∀ x y : A, connected P (x = y)}.

Class DenseSubuniverse (P : Type → Prop) : Prop :=
  {modal_false : P False}.

Class RegularSubuniverse (P : Type → Prop) : Prop :=
  {modal_exists : ∀ A (B : A → Prop), P A → (∀ x : A, P (B x)) → P (∃ x : A, B x)}.

Module Mod.
  Class ModalOperator (P : Type → Prop) :=
    {T : Type → Type;
     modal : ∀ {A}, P (T A);
     unit : ∀ {A}, A → T A}.

  (** A dependent idempotent modality will support a dependent elimination rule, and will be closed under sigma types. *)
  Class DepModality (P : Type → Prop) :=
    {DepModality_Operator :> ModalOperator P;
     DepModality_RepleteSubuniverse :> RepleteSubuniverse P;
     depmod_ump : ∀ {A B} `{∀ x, Modal P (B x)}, @is_isomorphism (∀ x : T A, B x) (∀ x : A, B (unit x)) (λ f a, f (unit a))}.

  (** A simple idempotent modality will support a simple elimination rule, and will be closed under product types. *)
  Class SimpleModality (P : Type → Prop) :=
    {SimpleModality_Operator :> ModalOperator P;
     SimpleModality_RepleteSubuniverse :> RepleteSubuniverse P;
     simpmod_ump : ∀ {A B} `{Modal P B}, @is_isomorphism (T A → B) (A → B) (λ f, f ∘ unit)}.

  Arguments T P {_}.

  Section Dep.
    Context {P} `{DepModality P}.

    Definition ind {A} (B : T P A → Type) `{∀ x : T P A, Modal P (B x)} (f : ∀ x : A, B (unit x)) : ∀ x : T P A, B x.
    Proof. by apply: iso_inv _ depmod_ump _. Defined.

    Lemma ind_beta {A B} `{∀ x : T P A, Modal P (B x)} (f : ∀ x : A, B (unit x)) (a : A) : ind B f (unit a) = f a.
    Proof.
      case: (depmod_ump f)=> f' [h1 h2].
      rewrite -h1.
      move: (unit a).
      apply: equal_f_dep.
      by apply: funcompr_compute.
    Qed.

    Global Instance Dep_to_Simple : SimpleModality P.
    Proof.
      unshelve esplit.
      - apply: DepModality_RepleteSubuniverse.
      - move=> A B ?.
        abstract apply: depmod_ump.
    Defined.
  End Dep.


  Section Simple.
    Context {P} `{SimpleModality P}.

    Global Instance Modal_T {A} : Modal P (T P A).
    Proof. by apply: modal. Qed.

    Definition rec {A B} `{Modal P B} (f : A → B) : T P A → B.
    Proof. by apply: iso_inv _ simpmod_ump _. Defined.

    Lemma rec_beta {A B} `{Modal P B} (f : A → B) (a : A) : rec f (unit a) = f a.
    Proof.
      case: (simpmod_ump f)=> f' [h1 h2].
      rewrite -h1 /comp.
      move: (unit a).
      apply: equal_f.
      by apply: funcompr_compute.
    Qed.

    Opaque rec.

    Definition alg {A} `{Modal P A} : T P A → A.
    Proof. by apply: rec. Defined.

    Lemma alg_beta {A} `{Modal P A} : ∀ x : A, alg (unit x) = x.
    Proof. by move=>?; rewrite /alg rec_beta. Qed.

    Lemma alg_eta {A} `{Modal P A} : ∀ x : T P A, x = unit (alg x).
    Proof.
      apply: equal_f.
      apply: (iso_injective _ simpmod_ump).
      apply: funext=> x//=.
      by rewrite alg_beta.
    Qed.

    Opaque alg.

    Lemma alg_iso {A} `{Modal P A} : @is_isomorphism (T P A) A alg.
    Proof.
      move=> x.
      exists (unit x); split.
      - by rewrite alg_beta.
      - move=> x' <-.
        by rewrite -alg_eta.
    Qed.

    Lemma unit_iso_to_modal {A} : is_isomorphism (unit : A → T P A) → Modal P A.
    Proof.
      move=> iso.
      rewrite /Modal.
      apply: (replete P _ (iso_inv _ iso)).
      - apply: iso_inv_iso.
      - apply: modal.
    Qed.
  End Simple.
End Mod.


Section Instances.
  Context {P} `{LexSubuniverse P} `{DenseSubuniverse P} `{RegularSubuniverse P}.

  Global Instance Modal_false : Modal P False.
  Proof. by apply: modal_false. Qed.

  Global Instance Modal_exists {A} {B : A → Prop} `{Modal P A} `{∀ x : A, Modal P (B x)} : Modal P (∃ x : A, B x).
  Proof. by apply: modal_exists. Qed.
End Instances.



Section SimpleInstances.
  Context {P} `{Mod.SimpleModality P}.

  Global Instance Modal_true : Modal P True.
  Proof.
    apply: Mod.unit_iso_to_modal.
    move=> x.
    exists I; split.
    - move: x.
      apply: equal_f.
      apply: (iso_injective _ Mod.simpmod_ump).
      by apply: funext; case.
    - by case.
  Qed.



  Global Instance Modal_prod {A B} `{Modal P A} `{Modal P B} : Modal P (A * B).
  Proof.
    apply: Mod.unit_iso_to_modal=> p.
    unshelve esplit.
    - split.
      + apply: Mod.alg; move: p; apply: Mod.rec.
        move=> p; apply: Mod.unit; move: p.
        apply: fst.
      + apply: Mod.alg; move: p; apply: Mod.rec.
        move=> p; apply: Mod.unit; move: p.
        apply: snd.
    - split.
      + move: p.
        apply: equal_f.
        apply: (iso_injective _ Mod.simpmod_ump).
        apply: funext=> x//=.
        congr Mod.unit.
        rewrite ?Mod.rec_beta ?Mod.alg_beta.
        by case: x.
      + case=> x y <-.
        by rewrite ?Mod.rec_beta ?Mod.alg_beta.
  Qed.

  Global Instance Modal_and {A B : Prop} `{Modal P A} `{Modal P B} : Modal P (A ∧ B).
  Proof.
    rewrite /Modal.
    apply: (replete P (A * B)).
    - by move=> p; split; move: p; [apply: fst | apply: snd].
    - move=> ? p.
      unshelve esplit=>//.
      split; move: p; [apply: proj1 | apply: proj2].
    - change P with (Modal P).
      typeclasses eauto.
  Qed.

  Global Instance Modal_fun {A B} `{Modal P B} : Modal P (A → B).
  Proof.
    apply: Mod.unit_iso_to_modal=> f.
    unshelve esplit.
    - move=> a.
      move: f.
      apply: Mod.rec.
      by apply.
    - split.
      + move: f.
        apply: equal_f.
        apply: (iso_injective _ Mod.simpmod_ump).
        apply: funext=> f//=.
        congr Mod.unit.
        apply: funext=> x.
        by rewrite Mod.rec_beta.
      + move=> f' <-.
        apply: funext=>?.
        by rewrite Mod.rec_beta.
  Qed.

  Global Instance IsProp_T {A} `{IsProp A} : IsProp (Mod.T P A).
  Proof.
    move=> x.
    apply: equal_f.
    move: x.
    apply: equal_f.
    apply: (iso_injective _ Mod.simpmod_ump).
    apply: funext=> x//=.
    apply: (iso_injective _ Mod.simpmod_ump).
    apply: funext=> y //=.
    congr Mod.unit.
    apply: irr.
  Qed.

  Global Instance Modal_eq {A} {x y : A} `{Modal P A} : Modal P (x = y).
  Proof.
    apply: Mod.unit_iso_to_modal=> e.
    unshelve esplit.
    - move: e.
      apply: equal_f.
      apply: (iso_injective _ Mod.simpmod_ump).
      by apply: funext=>//=.
    - split=>//=.
      apply: irr.
  Qed.

  Global Instance Modal_not {A} `{DenseSubuniverse P} : Modal P (not A).
  Proof. by rewrite /not; typeclasses eauto. Qed.
End SimpleInstances.

Section DepInstances.
  Context {P} `{Mod.DepModality P}.

  Global Instance Modal_T {A} : Modal P (Mod.T P A).
  Proof. by apply: Mod.modal. Defined.

  Global Instance Modal_pi {A B} `{∀ x : A, Modal P (B x)} : Modal P (∀ x : A, B x).
  Proof.
    apply: Mod.unit_iso_to_modal=> f.
    unshelve esplit.
    - move=> a.
      move: f.
      apply: Mod.rec.
      by apply.
    - split.
      + move: f.
        apply: equal_f_dep.
        apply: (iso_injective _ Mod.simpmod_ump).
        rewrite /comp //=.
        apply: funext=> ?; f_equal.
        apply: depfunext=> x.
        by rewrite Mod.rec_beta.
      + move=> f' <-.
        apply: depfunext=> x.
        by rewrite Mod.rec_beta.
  Qed.

  Global Instance Modal_sg {A B} `{Modal P A} `{∀ x : A, Modal P (B x)} : Modal P {x : A & B x}.
  Proof.
    apply: Mod.unit_iso_to_modal=> p.
    unshelve esplit.
    - unshelve esplit.
      + apply: Mod.alg; move: p.
        apply: Mod.rec=> u.
        apply: Mod.unit.
        move: u.
        apply: projT1.
      + apply: Mod.alg; move: p.
        apply: Mod.ind; case=> a b.
        apply: Mod.unit.
        rewrite (_ : (Mod.alg _) = a) //=.
        abstract by rewrite Mod.rec_beta Mod.alg_beta.
      - split=>//=.
        + move: p.
          apply: equal_f_dep.
          apply: (iso_injective _ Mod.simpmod_ump).
          apply: funext; case=> a b //=.
          congr Mod.unit.
          apply: eq_sigT=>//=.
          * by rewrite Mod.rec_beta Mod.alg_beta.
          * move=> ?.
            rewrite Mod.ind_beta Mod.alg_beta rew_compose.
            by simplify_eqs.
        + case=> a b//= <-.
          apply: eq_sigT=>//=.
          * by rewrite Mod.rec_beta Mod.alg_beta.
          * move=> ?.
            rewrite Mod.ind_beta Mod.alg_beta rew_compose.
            by simplify_eqs.
  Qed.
End DepInstances.

Module ModP.
  Definition T P `{Mod.ModalOperator P} (A : Prop) := PropTrunc.T (Mod.T P A).

  Lemma unit {P} `{Mod.ModalOperator P} {A : Prop} : A → T P A.
  Proof. by move/Mod.unit/PropTrunc.unit. Defined.

  Section Dep.
    Context {P} `{Mod.DepModality P}.

    Definition ind {A} (B : T P A → Type) `{∀ x : T P A, Modal P (B x)} (f : ∀ x : A, B (unit x)) : ∀ x : T P A, B x.
    Proof.
      move=> a.
      rewrite -[a]PropTrunc.alg_eta.
      move: (PropTrunc.alg a).
      by apply/Mod.ind/f.
    Defined.

    Lemma ind_beta {A B} `{∀ x : T P A, Modal P (B x)} (f : ∀ x : A, B (unit x)) (a : A) : ind B f (unit a) = f a.
    Proof.
      apply: JMeq_eq.
      rewrite /ind /unit; simplify_eqs.
      by rewrite PropTrunc.alg_beta Mod.ind_beta.
    Qed.

    Opaque ind.
  End Dep.

  Section Simple.
    Context {P} `{Mod.SimpleModality P}.


    Global Instance Modal_T {A} : Modal P (T P A).
    Proof.
      apply: Mod.unit_iso_to_modal=> p.
      unshelve esplit.
      - apply: PropTrunc.unit.
        move: p.
        apply: Mod.rec.
        apply: (@PropTrunc.rec (Mod.T P A) (Mod.T P A) _ id).
      - split=>//=.
        apply: irr.
    Qed.

    Definition rec {A : Prop} {B} `{Modal P B} (f : A → B) : T P A → B.
    Proof.
      move/PropTrunc.alg.
      by apply/Mod.rec/f.
    Defined.

    Lemma rec_beta {A : Prop} {B} `{Modal P B} (f : A → B) (a : A) : rec f (unit a) = f a.
    Proof. by rewrite /rec /unit PropTrunc.alg_beta Mod.rec_beta. Qed.

    Opaque rec.
  End Simple.
End ModP.



Section SeparatedReflection.
  Context P `{Mod.DepModality P}.

  Definition separated (P : Type → Prop) : Type → Prop :=
    λ A, ∀ x y : A, P (x = y).

  Instance separated_replete : RepleteSubuniverse (separated P).
  Proof.
    move=> A B f iso sepA x y.
    pose g := iso_inv f iso.
    apply: (replete P (g x = g y)).
    - by apply/iso_injective/iso_inv_iso.
    - move=> ? h.
      unshelve esplit=>//.
      by rewrite h.
    - by apply: sepA.
  Qed.

  Definition modally_eq (A : Type) (x y : A) : Prop :=
    ModP.T P (x = y).

  Global Instance Reflexive_modally_eq {A} : RelationClasses.Reflexive (modally_eq A).
  Proof. by move=>?; apply: ModP.unit. Qed.

  Global Instance Symmetric_modally_eq {A} : RelationClasses.Symmetric (modally_eq A).
  Proof. by move=>??; apply: ModP.rec=>->; apply: ModP.unit. Qed.

  Global Instance Transitive_modally_eq {A} : RelationClasses.Transitive (modally_eq A).
  Proof. by move=> ???; apply: ModP.rec=>->. Qed.

  Global Instance Equivalence_modally_eq {A} : RelationClasses.Equivalence (modally_eq A).
  Proof. by split; typeclasses eauto. Qed.

  Definition Sep A := Quotient.T A (modally_eq A).

  Notation Separated := (Modal (separated P)).

  Global Instance Separated_Sep {A} : Separated (Sep A).
  Proof.
    apply: Quotient.indp=> x.
    apply: Quotient.indp=> y.
    apply: (replete P _ Quotient.glue).
    - by apply: Quotient.glue_is_iso.
    - by apply: ModP.Modal_T.
  Qed.

  Global Instance separated_ModalOperator : Mod.ModalOperator (separated P).
  Proof.
    unshelve esplit.
    - by apply: Sep.
    - by move=>?; apply: Separated_Sep.
    - by move=>?; apply: Quotient.intro.
  Defined.

  Global Instance Modal_EqOfSeparated {A} `{Separated A} {x y : A} : Modal P (x = y).
  Proof. by apply: (mod x y). Qed.

  Global Instance DepModality_separated : Mod.DepModality (separated P).
  Proof.
    unshelve esplit; first by typeclasses eauto.
    move=> A B HB f.
    unshelve esplit.
    - unshelve apply: Quotient.ind.
      + by apply: f.
      + by move=>??; apply: ModP.ind=>?; simplify_eqs.
    - split=>//=.
      move=> h <-.
      by apply: depfunext; apply: Quotient.indp.
  Defined.
End SeparatedReflection.

Notation Separated := (λ P, Modal (separated P)).
