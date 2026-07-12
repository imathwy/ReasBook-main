import LinearRepresentations_Serre_1977.Chap04.Definition_4_10
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.RepresentationTheory.Subrepresentation

noncomputable section

universe u v

namespace HilbertSpaceRepresentation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Semantic recall: `lean_leansearch` surfaced `IsHilbertSum` and
-- `IsHilbertSum.linearIsometryEquiv` as the canonical Hilbert direct-sum owners; for a
-- Hilbert-space representation, the summands are most naturally recorded as `Subrepresentation`s
-- of `ρ.toRepresentation`.
--
-- Source/core/bridge triage:
-- `source-facing`: the existence of a Hilbert direct-sum decomposition of `ρ` by finite-dimensional
-- unitary subrepresentations.
-- `core/canonical`: `IsHilbertSum` for the family of underlying submodules.
-- `bridge/view`: the canonical isometric isomorphism `hσ.linearIsometryEquiv : H ≃ₗᵢ[ℂ] lp ... 2`.
/-- Theorem 4-11: every Hilbert-space representation of a compact group is a Hilbert direct sum of
finite-dimensional unitary subrepresentations. In this file, the decomposition is recorded by a
family of finite-dimensional `Subrepresentation`s of `ρ.toRepresentation` whose inclusion maps
form an `IsHilbertSum`; the resulting isometric isomorphism with
`lp (fun i ↦ (σ i).toSubmodule) 2` is `hσ.linearIsometryEquiv`. -/
theorem exists_isHilbertSum_finiteDimensional_subrepresentations_of_compact
    (ρ : HilbertSpaceRepresentation G H) :
    ∃ (ι : Type (max u v)) (σ : ι → Subrepresentation ρ.toRepresentation),
      IsHilbertSum ℂ (fun i ↦ (σ i).toSubmodule) (fun i ↦ ((σ i).toSubmodule).subtypeₗᵢ) ∧
        ∀ i, FiniteDimensional ℂ ((σ i).toSubmodule) := sorry

end

end HilbertSpaceRepresentation
