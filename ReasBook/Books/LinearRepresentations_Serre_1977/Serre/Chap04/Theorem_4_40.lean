import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap04.ContinuousIrreducibleFamily
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.ExternalTensor

open scoped Representation.ExternalTensor

noncomputable section

/- Source/core/bridge triage:
* source-facing: Theorem 4-40 as the compact-group/continuous form of Serre's external-tensor
  decomposition theorem.
* core/canonical: `FDRep.externalTensor_simple`,
  `FDRep.exists_iso_externalTensor_of_simple`, and `Representation.char_tensor`.
* bridge/view: this file keeps the Chapter 4 continuity input on
  `Representation.IsContinuous` and `FDRep.HasContinuousRealization`, while using the notation
  `ρ₁ ⊠ ρ₂` from `Serre.RepresentationTheory.ExternalTensor`.
-/

namespace Representation

section ContinuousCompact

variable {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [CompactSpace G₁]
variable {G₂ : Type} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [CompactSpace G₂]
variable {V₁ : Type} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
  [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁] [T2Space V₁] [FiniteDimensional ℂ V₁]
variable {V₂ : Type} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
  [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂] [FiniteDimensional ℂ V₂]
variable {U : Type} [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℂ U] [T2Space U] [FiniteDimensional ℂ U]

/-- Theorem 4-40 (1): if `ρ₁` and `ρ₂` are irreducible finite-dimensional continuous complex
representations of the compact groups `G₁` and `G₂`, then their exterior tensor product
`ρ₁ ⊠ ρ₂` is irreducible as a representation of `G₁ × G₂`. -/
theorem isIrreducible_externalTensor_of_isContinuousCompact
    (ρ₁ : Representation ℂ G₁ V₁) [Representation.IsContinuous ρ₁]
    [Representation.IsIrreducible ρ₁] (ρ₂ : Representation ℂ G₂ V₂)
    [Representation.IsContinuous ρ₂] [Representation.IsIrreducible ρ₂] :
    Representation.IsIrreducible (ρ₁ ⊠ ρ₂) := sorry

/-- Theorem 4-40 (2): conversely, every irreducible finite-dimensional continuous complex
representation `π` of `G₁ × G₂` is isomorphic in `FDRep ℂ (G₁ × G₂)` to an exterior tensor
product `τ₁.ρ ⊠ τ₂.ρ`, where `τ₁ : FDRep ℂ G₁` and `τ₂ : FDRep ℂ G₂` are irreducible and admit
continuous realizations. This keeps the continuity data on the canonical Chapter 4 owner
`FDRep.HasContinuousRealization` instead of a raw existential tower of carriers and topologies. -/
theorem exists_equiv_externalTensor_of_isIrreducible_of_isContinuousCompact
    (π : Representation ℂ (G₁ × G₂) U) [Representation.IsContinuous π]
    [Representation.IsIrreducible π] :
    ∃ τ₁ : FDRep ℂ G₁,
      FDRep.HasContinuousRealization τ₁ ∧
        Representation.IsIrreducible τ₁.ρ ∧
        ∃ τ₂ : FDRep ℂ G₂,
          FDRep.HasContinuousRealization τ₂ ∧
            Representation.IsIrreducible τ₂.ρ ∧
            Nonempty (FDRep.of π ≅ FDRep.of (τ₁.ρ ⊠ τ₂.ρ)) := sorry

end ContinuousCompact

section

variable {G₁ : Type} [Group G₁]
variable {G₂ : Type} [Group G₂]
variable {V₁ : Type} [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
variable {V₂ : Type} [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]

/-- Theorem 4-40 (3): the character of the exterior tensor product satisfies
`(ρ₁ ⊠ ρ₂).character (s₁, s₂) = ρ₁.character s₁ * ρ₂.character s₂`. This is the external-tensor
specialization of `Representation.char_tensor`, so no irreducibility or continuity assumptions are
needed in the statement itself. -/
theorem char_externalTensor_of_isContinuousCompact
    (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂) :
    (ρ₁ ⊠ ρ₂).character = fun s : G₁ × G₂ ↦ ρ₁.character s.1 * ρ₂.character s.2 := by
  ext s
  simpa [Representation.character] using
    congrFun
      (Representation.char_tensor
        (ρ₁.comp (MonoidHom.fst G₁ G₂))
        (ρ₂.comp (MonoidHom.snd G₁ G₂)))
      s

end

end Representation
