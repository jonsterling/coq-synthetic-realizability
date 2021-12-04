From synrl Require Import Preamble Orthogonality Modality Codiscrete.

Notation 𝕀 := (∇ 𝟚).

Instance : 𝕀 ⇾ 𝟙.
Proof. exists (λ _, Logic.I)=> ?; by exists (Mod.unit true). Qed.

Section BipointedCodiscrete.

  (** HRR prove that Orth(𝕀) = Orth(S) for any strictly bipointed
  codiscrete object S. We generalize this result to realizability over
  a topos other than Set; to do so, we must assume that S is
  codiscretely decidable. In fact, a slightly weaker but somewhat
  unnatural assumption would suffice: that S has a basepoint whose
  equivalence class is decidable. *)


  Context {S} `{Codiscrete S} `{StrictlyBipointed S} `{CodiscretelyDecidable S}.

  Local Definition covering_map_graph (s0 : S) : S → 𝕀 → Prop :=
    λ s i, (s0 = s → i = Mod.unit true) ∧ (¬(s0 = s) → i = Mod.unit false).

  Local Lemma covering_graph_functional (s0 : S) : Functional (covering_map_graph s0).
  Proof.
    move=> s.
    generalize (codisc_dcd s s0); apply: ModP.rec.
    case.
    - move=> ss0.
      exists (Mod.unit true); split.
      + split=>//= h.
        by case: h.
      + by move=> ? [h' _]; rewrite h'.
    - move=> h.
      exists (Mod.unit false); split.
      + split=>//= s0s.
        by case: h.
      + move=> i [h1 h2].
        rewrite h2//= => ?.
        by apply: h.
  Qed.

  #[global]
  Instance : S ⇾ 𝕀.
  Proof.
    case: sbptd => [s1 [s2 sdisj]].
    unshelve esplit.
    - apply: (funcompr (covering_map_graph s1)).
      by apply: covering_graph_functional.
    - move=> i; unshelve esplit; move: i.
      + by apply: Mod.rec; case; [exact: s1 | exact: s2].
      + apply: Mod.ind=> x.
        rewrite Mod.rec_beta.
        apply: funcompr_compute.
        case: x; split=>//= [].
  Qed.

  Instance to_orth_𝕀 {I} {X : I → Type} `{[S] ⫫ X} : [𝕀] ⫫ X.
  Proof. by apply: orth_cover. Qed.

  Instance from_orth_𝕀 {I} {X : I → Type} `{[𝕀] ⫫ X} : [S] ⫫ X.
  Proof.
    unshelve apply: orth_cover_converse =>//=.
    - exact: Mod.unit.
    - move=> s.
      exists (Mod.rec s).
      rewrite /precomp.
      apply: funext=>?.
      by apply: Mod.rec_beta.
  Qed.

End BipointedCodiscrete.

(** The theorem of HRR that Orth(U) = Orth(∇2) for a uniform strictly
bipointed object U does *not* hold in generality. It seems to require
that all codiscrete objects are decidable. But this is needed to check
that Orth(Ω) = Orth(∇2). Of course, it may be that this is just not
the right definition of discreteness; I suspect that for defining the
correct notion of modest set, we would still want Orth(∇2). *)
