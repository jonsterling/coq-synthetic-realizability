From synrl Require Import Preamble.

Class LexSubuniverse (P : Type → Prop) : Prop :=
  {modal_eq : ∀ A (x y : A), P A → P (x = y);
   modal_pi : ∀ A B, (∀ x, P (B x)) → P (∀ x : A, B x);
   modal_sigma : ∀ A B, P A → (∀ x, P (B x)) → P {x : A & B x};
   modal_subset : ∀ A (B : A → Prop), P A → (∀ x, P (B x)) → P {x : A | B x};
   modal_and : ∀ (A B : Prop), P A → P B → P (A ∧ B);
   modal_true : P True}.

Class DenseSubuniverse (P : Type → Prop) : Prop :=
  {modal_false : P False}.

Class RegularSubuniverse (P : Type → Prop) : Prop :=
  {modal_exists : ∀ A (B : A → Prop), P A → (∀ x : A, P (B x)) → P (∃ x : A, B x)}.

Class Modal (modal : Type → Prop) (A : Type) : Prop :=
  mod : modal A.

(* The reflection of types into the lex subuniverse. *)
Module Mod.
  Axiom T : ∀ P : (Type → Prop), ∀ `{LexSubuniverse P}, Type → Type.

  Section Operations.
    Context {P : Type → Prop} `{LexSubuniverse P}.

    Axiom ret : ∀ {A}, A → T P A.
    Axiom rec : ∀ {A B} `{Modal P B}, (A → B) → T P A → B.
    Axiom ind : ∀ {A} B `{∀ x, Modal P (B x)}, (∀ x : A, B (ret x)) → ∀ x : T P A, B x.
    Axiom rec_beta : ∀ {A B} `{Modal P B} (f : A → B) (a : A), rec f (ret a) = f a.
    Axiom ind_beta : ∀ {A B} `{∀ x, Modal P (B x)} (f : ∀ x, B (ret x)) (a : A), ind B f (ret a) = f a.
  End Operations.
End Mod.

(* The reflection of propositions into the lex subuniverse. *)
Module ModP.
  Axiom T : ∀ P : (Type → Prop), ∀ `{LexSubuniverse P}, Prop → Prop.

  Section Operations.
    Context {P : Type → Prop} `{LexSubuniverse P}.

    Axiom ret : ∀ {A : Prop}, A → T P A.
    Axiom rec : ∀ {A : Prop} {B} `{Modal P B}, (A → B) → T P A → B.
    Axiom ind : ∀ {A : Prop} B `{∀ x, Modal P (B x)}, (∀ x : A, B (ret x)) → ∀ x : T P A, B x.
    Axiom rec_beta : ∀ {A : Prop} {B} `{Modal P B} (f : A → B) (a : A), rec f (ret a) = f a.
    Axiom ind_beta : ∀ {A : Prop} {B} `{∀ x, Modal P (B x)} (f : ∀ x, B (ret x)) (a : A), ind B f (ret a) = f a.
  End Operations.
End ModP.

Section Instances.
  Context {P : Type → Prop} `{LexSubuniverse P} `{DenseSubuniverse P} `{RegularSubuniverse P}.

  Global Declare Instance Modal_Mod_T {A : Type} : Modal P (Mod.T P A).
  Global Declare Instance Modal_ModP_T {A : Prop} : Modal P (ModP.T P A).

  Global Instance Modal_true : Modal P True.
  Proof. by apply: modal_true. Qed.

  Global Instance Modal_false : Modal P False.
  Proof. by apply: modal_false. Qed.

  Global Instance Modal_pi {A B} `{∀ x : A, Modal P (B x)} : Modal P (∀ x : A, B x).
  Proof. by apply: modal_pi. Qed.

  Global Instance Modal_exists {A} {B : A → Prop} `{Modal P A} `{∀ x : A, Modal P (B x)} : Modal P (∃ x : A, B x).
  Proof. by apply: modal_exists. Qed.

  Global Instance Modal_eq {A} `{Modal P A} {x y : A} : Modal P (x = y).
  Proof. by apply: modal_eq. Qed.

  Global Instance Modal_and {A B : Prop} `{Modal P A} `{Modal P B} : Modal P (A ∧ B).
  Proof. by apply: modal_and. Qed.
End Instances.
