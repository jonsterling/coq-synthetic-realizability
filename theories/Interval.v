From synrl Require Import Preamble Orthogonality Codiscrete.

Section Interval.

  (** HRR prove that Orth(∇𝟚) = Orth(S) for any strictly bipointed codiscrete object S. We generalize this result to realizability over a topos other than Set; to do so, we must assume that S is decidable. *)

  Definition 𝕀 := ∇ bool.

  Context {S} `{Codiscrete S} `{Decidable S} `{StrictlyBipointed S}.

  Lemma bipointed_codiscrete_set_covers_𝕀 : S ⇾ 𝕀.
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

  Lemma to_orth_𝕀 {I} {X : I → Type} :
    {S} ⫫ X
    → {𝕀} ⫫ X.
  Proof.
    move=> orthS.
    apply: orth_surj=>//=.
    by apply: bipointed_codiscrete_set_covers_𝕀.
  Qed.

  Lemma from_orth_𝕀 {I} {X : I → Type} :
    {𝕀} ⫫ X
    → {S} ⫫ X.
  Proof.
    move=> orthS.
    unshelve apply: orth_surj_converse=>//=.
    - exact: Codisc.ret.
    - by apply: bipointed_codiscrete_set_covers_𝕀.
    - unshelve esplit; first by [].
      by move=> ?; exists (Codisc.ret true).
    - move=> s.
      exists (Codisc.rec s).
      rewrite /precomp.
      apply: funext=>?.
      by apply: Codisc.rec_beta.
  Qed.

End Interval.
