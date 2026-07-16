import stacks_proof.stacks_project.Chap10.Lemma_10_159_1.WellOrderedPrefix

universe u v w

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Lemma 10.159.1: the closed prefix field indexed by `β ≤ α`. This keeps the later
chain packaging from repeatedly re-elaborating the same proof-dependent field expression. -/
noncomputable def closedPrefixField
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (β : Set.Iic α) :
    IntermediateField (ResidueField R) K :=
  wellOrder_prefixField (R := R) (K := K) β.1 (le_trans β.2 hα)

/-- Helper for Lemma 10.159.1: the open prefix field indexed by `β < α`. This is the field
appearing in the limit-stage cover statement. -/
noncomputable def openPrefixField
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (β : Set.Iio α) :
    IntermediateField (ResidueField R) K :=
  wellOrder_prefixField (R := R) (K := K) β.1 (le_trans β.2.le hα)

/-- Helper for Lemma 10.159.1: a coherent prefix chain stores, for every ordinal stage up to `α`,
a realizing local flat stage together with compatible transition morphisms. This is the exact
payload needed to feed the source proof's direct-limit construction at limit ordinals. -/
structure PrefixStageChain
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) where
  stage :
    (β : Set.Iic α) →
      ResidueExtensionStage.{u, v, max u v} (R := R) K (closedPrefixField (R := R) K hα β)
  hom :
    {β γ : Set.Iic α} →
      (hβγ : β ≤ γ) →
        ResidueExtensionStage.Hom.{u, v, max u v, max u v}
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2 hα) (le_trans γ.2 hα) hβγ)
          (stage β) (stage γ)
  hom_id :
    ∀ β,
      (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (stage β).A
  hom_comp :
    ∀ {β γ δ : Set.Iic α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
      ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
          (hom (β := β) (γ := γ) hβγ).toAlgHom) =
        (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom

/-- Helper for Lemma 10.159.1: the stage indexed by the top ordinal in a coherent prefix chain is
the distinguished realizing object for the terminal prefix field of that chain. -/
noncomputable def PrefixStageChain.topStage
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα) :
    ResidueExtensionStage.{u, v, max u v} (R := R) K
      (closedPrefixField (R := R) K hα ⟨α, show α ≤ α from le_rfl⟩) :=
  C.stage ⟨α, show α ≤ α from le_rfl⟩

/-- Helper for Lemma 10.159.1: restricting a coherent prefix chain to a smaller terminal ordinal
simply reindexes the old stage family. This is the canonical owner used by the recursive limit
construction to compare a larger chain with its literal lower-stage truncations. -/
noncomputable def PrefixStageChain.restrictStage
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α)
    (γ : Set.Iic β) :
    ResidueExtensionStage.{u, v, max u v} (R := R) K
      (closedPrefixField (R := R) K (le_trans hβα hα) γ) :=
  by
  -- Proof comment: view `γ` as an index of the larger chain and use proof irrelevance on the
  -- closed-prefix field witness.
  simpa [closedPrefixField] using C.stage ⟨γ.1, le_trans γ.2 hβα⟩

/-- Helper for Lemma 10.159.1: the transition maps of a restricted chain are the ambient chain
maps on the reindexed lower stages. -/
noncomputable def PrefixStageChain.restrictHom
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α)
    {γ δ : Set.Iic β} (hγδ : γ ≤ δ) :
    ResidueExtensionStage.Hom.{u, v, max u v, max u v}
      (wellOrder_prefixField_mono (R := R) (K := K)
        (le_trans γ.2 (le_trans hβα hα))
        (le_trans δ.2 (le_trans hβα hα))
        hγδ)
      (PrefixStageChain.restrictStage C hβα γ)
      (PrefixStageChain.restrictStage C hβα δ) :=
  by
  -- Proof comment: after reindexing the endpoints into the ambient chain, the restricted
  -- transition map is exactly the original one.
  simpa [PrefixStageChain.restrictStage, closedPrefixField] using
    C.hom (β := ⟨γ.1, le_trans γ.2 hβα⟩) (γ := ⟨δ.1, le_trans δ.2 hβα⟩) hγδ

/-- Helper for Lemma 10.159.1: the identity coherence of a restricted chain is inherited from the
ambient chain after reindexing. -/
theorem PrefixStageChain.restrict_hom_id
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α)
    (γ : Set.Iic β) :
    (PrefixStageChain.restrictHom C hβα (γ := γ) (δ := γ) le_rfl).toAlgHom =
      AlgHom.id R (PrefixStageChain.restrictStage C hβα γ).A := by
  -- Proof comment: the restricted identity map is the ambient identity map at the same stage.
  simpa [PrefixStageChain.restrictHom, PrefixStageChain.restrictStage, closedPrefixField] using
    C.hom_id ⟨γ.1, le_trans γ.2 hβα⟩

/-- Helper for Lemma 10.159.1: the composition coherence of a restricted chain is inherited from
the ambient chain after reindexing all three indices. -/
theorem PrefixStageChain.restrict_hom_comp
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α)
    {γ δ ε : Set.Iic β} (hγδ : γ ≤ δ) (hδε : δ ≤ ε) :
    ((PrefixStageChain.restrictHom C hβα (γ := δ) (δ := ε) hδε).toAlgHom.comp
        (PrefixStageChain.restrictHom C hβα (γ := γ) (δ := δ) hγδ).toAlgHom) =
      (PrefixStageChain.restrictHom C hβα (γ := γ) (δ := ε) (le_trans hγδ hδε)).toAlgHom := by
  -- Proof comment: the restricted composition law is literally the ambient composition law on
  -- the reindexed stages.
  simpa [PrefixStageChain.restrictHom, PrefixStageChain.restrictStage, closedPrefixField] using
    C.hom_comp
      (β := ⟨γ.1, le_trans γ.2 hβα⟩)
      (γ := ⟨δ.1, le_trans δ.2 hβα⟩)
      (δ := ⟨ε.1, le_trans ε.2 hβα⟩)
      hγδ hδε

/-- Helper for Lemma 10.159.1: restricting a coherent prefix chain to a smaller ordinal produces a
coherent prefix chain on that smaller ordinal. -/
noncomputable def PrefixStageChain.restrict
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α) :
    PrefixStageChain (R := R) K β (le_trans hβα hα) :=
  { stage := PrefixStageChain.restrictStage C hβα
    hom := PrefixStageChain.restrictHom C hβα
    hom_id := PrefixStageChain.restrict_hom_id C hβα
    hom_comp := PrefixStageChain.restrict_hom_comp C hβα }

/-- Helper for Lemma 10.159.1: the stage family of a restricted chain is definitionally the
reindexed stage family packaged by `restrictStage`. -/
@[simp] theorem PrefixStageChain.restrict_stage
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α)
    (γ : Set.Iic β) :
    (C.restrict hβα).stage γ = PrefixStageChain.restrictStage C hβα γ := by
  rfl

/-- Helper for Lemma 10.159.1: the transition maps of a restricted chain are definitionally the
reindexed ambient transition maps packaged by `restrictHom`. -/
@[simp] theorem PrefixStageChain.restrict_hom
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α)
    {γ δ : Set.Iic β} (hγδ : γ ≤ δ) :
    (C.restrict hβα).hom hγδ = PrefixStageChain.restrictHom C hβα hγδ := by
  rfl

/-- Helper for Lemma 10.159.1: the top stage of a restricted chain is the ambient stage at the
same ordinal index. -/
@[simp] theorem PrefixStageChain.restrict_topStage
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα)
    {β : Ordinal} (hβα : β ≤ α) :
    (C.restrict hβα).topStage =
      PrefixStageChain.restrictStage C hβα ⟨β, show β ≤ β from le_rfl⟩ := by
  rfl

end
