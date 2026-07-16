import stacks_proof.stacks_project.Chap10.Lemma_10_159_1.PrefixStageChain

universe u v w

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Chap10 Lemma 10 159 1: a coherent open prefix-stage system below a limit ordinal.
This is the directed-system payload needed before taking the direct limit at the limit stage. -/
structure OpenPrefixStageSystem
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α) where
  stage :
    (β : Set.Iio α) →
      ResidueExtensionStage.{u, v, max u v} (R := R) K (openPrefixField (R := R) K hα β)
  hom :
    {β γ : Set.Iio α} →
      (hβγ : β ≤ γ) →
        ResidueExtensionStage.Hom.{u, v, max u v, max u v}
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
          (stage β) (stage γ)
  hom_id :
    ∀ β,
      (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (stage β).A
  hom_comp :
    ∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
      ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
          (hom (β := β) (γ := γ) hβγ).toAlgHom) =
        (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom
  base :
    Nonempty
      (ResidueExtensionStage.Hom
        (base_le_prefixField (R := R) (K := K)
          (hα := le_trans (le_of_lt hlimit.bot_lt) hα))
        (ResidueExtensionStage.base (R := R) K)
        (stage ⟨0, hlimit.bot_lt⟩))

end
