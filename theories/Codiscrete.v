From synrl Require Import Preamble Orthogonality.

Axiom codiscrete : Type → Prop.
Class Codiscrete (A : Type) : Prop :=
  {codisc : codiscrete A}.

Axiom Codisc : Type → Type.
Notation "∇ A" := (Codisc A) (at level 60).

Module Codisc.
  Axiom ret : ∀ {A}, A → ∇ A.
  Axiom rec : ∀ {A B} `{Codiscrete B}, (A → B) → ∇ A → B.
  Axiom ind : ∀ {A B} `{∀ a, Codiscrete (B a)}, (∀ x : A, B (ret x)) → ∀ x : ∇ A, B x.
  Axiom rec_beta : ∀ {A B} `{Codiscrete B} (f : A → B) (a : A), rec f (ret a) = f a.
End Codisc.

Axiom codiscrete_def : ∀ A, is_isomorphism (@Codisc.ret A) → codiscrete A.

Instance Codiscrete_Codisc {A} : Codiscrete (∇ A).
Admitted.

Instance : ∀ A, Codiscrete A → ∀ x y : A, Codiscrete (x = y).
Admitted.

Instance : ∀ A B, Codiscrete A → (∀ x, Codiscrete (B x)) → Codiscrete {x : A & B x}.
Admitted.


Section Interval.

  Definition 𝕀 := ∇ bool.

  (** Relative to HRR, we must add the decidability assumption. *)
  Context {S} `{Codiscrete S} `{Decidable S} `{StrictlyBipointed S}.

  Lemma codiscrete_set_covers_𝕀 : S ⇾ 𝕀.
  Proof.
    case: sbptd => [s1 [s2 sdisj]].
    unshelve esplit.
    - move=> s.
      apply: (iota (λ i, (s = s1 → i = Codisc.ret true) ∧ (¬ (s = s1) → i = Codisc.ret false))).
      case: (dcd s s1).
      + abstract by [move=> ->; exists (Codisc.ret true); split; [by split | move=> i [hi1 hi2]; by rewrite -hi1]].
      + abstract by [move=> sns1; exists (Codisc.ret false); split; [by split| move=> i [hi1 hi2]; by rewrite -hi2]].
    - move=> i; unshelve esplit; move: i.
      + exact: (Codisc.rec (λ i, if i then s1 else s2)).
      + apply: Codisc.ind.
        match goal with
          [|- ∀ x : bool, iota (@?P x) (@?prf x) = _] =>
          move=> x;
          case: (iota_prop (P x) (prf x));
          move: x
        end.
        case.
        * move=> h1 h2.
          by rewrite h1 ?Codisc.rec_beta //=.
        * move=> h1 h2.
          rewrite h2 ?Codisc.rec_beta //=.
          by move=> ?; apply: sdisj.
  Qed.

  Lemma prop_6_1_i_fwd {I} {X : I → Type} :
    {S} ⫫ X
    → {𝕀} ⫫ X.
  Proof.
    move=> orthS.
    apply: orth_surj=>//=.
    by apply: codiscrete_set_covers_𝕀.
  Qed.

  Lemma prop_6_1_i_bwd {I} {X : I → Type} :
    {𝕀} ⫫ X
    → {S} ⫫ X.
  Proof.
    move=> orthS.
    unshelve apply: orth_surj_converse=>//=.
    - exact: Codisc.ret.
    - by apply: codiscrete_set_covers_𝕀.
    - unshelve esplit; first by [].
      by move=> ?; exists (Codisc.ret true).
    - move=> s.
      exists (Codisc.rec s).
      rewrite /precomp.
      apply: funext=>?.
      by apply: Codisc.rec_beta.
  Qed.

End Interval.
