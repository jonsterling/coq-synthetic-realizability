From synrl Require Import Preamble Orthogonality Codiscrete.

Definition 𝕀 := ∇ 𝟚.

Instance : 𝕀 ⇾ 𝟙.
Proof. by exists (λ _, Logic.I)=> ?; exists (Codisc.ret true). Qed.

Section BipointedCodiscrete.

  (** HRR prove that Orth(𝕀) = Orth(S) for any strictly bipointed codiscrete object S. We generalize this result to realizability over a topos other than Set; to do so, we must assume that S is decidable. *)


  Context {S} `{Codiscrete S} `{Decidable S} `{StrictlyBipointed S}.

  Instance : S ⇾ 𝕀.
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
          [|- ∀ x : 𝟚, iota (@?P x) (@?prf x) = _] =>
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

  Instance to_orth_𝕀 {I} {X : I → Type} `{[S] ⫫ X} : [𝕀] ⫫ X.
  Proof. by apply: orth_cover. Qed.

  Instance from_orth_𝕀 {I} {X : I → Type} `{[𝕀] ⫫ X} : [S] ⫫ X.
  Proof.
    unshelve apply: orth_cover_converse =>//=.
    - exact: Codisc.ret.
    - move=> s.
      exists (Codisc.rec s).
      rewrite /precomp.
      apply: funext=>?.
      by apply: Codisc.rec_beta.
  Qed.

End BipointedCodiscrete.

(** The theorem of HRR that Orth(U) = Orth(∇2) for a uniform strictly bipointed object U does *not* hold in generality. It seems to require that all codiscrete objects are decidable. *)
