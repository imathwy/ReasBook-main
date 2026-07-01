import Mathlib
import Serre.Chap12.Proposition_12_12_1_2
import Serre.Chap12.Theorem_12_12_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open scoped Representation

section

variable {K : Type} [Field K] [Algebra K ℂ]
variable {G : Type} [Group G] [Finite G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance fintypeG_corollary_12_12_3_2 : Fintype G := Fintype.ofFinite G

-- Proof sketch: the finite-dimensional complex character of `ρ` belongs to `R(G)`. Then apply
-- `characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity`
-- to identify `R(G)` with
-- the image of `R_K(G)`, and conclude with
-- `isRealizableOver_iff_character_mem_characterRingOverFieldInExtension`.
--
-- Source/core/bridge triage:
-- * source-facing: the realizability statement for a finite-dimensional complex representation.
-- * core/canonical owners: `IsRealizableOver K ρ`, `R[K](G)`, and `R(G)`.
-- * bridge/view used only internally: `Rep.of ρ`, needed to reuse the Chapter `11`
--   character-ring membership theorem.
/-- Helper for Corollary 12-12.3-2: the character of a finite-dimensional complex
`Representation` already lies in the ordinary character ring `R(G)`. -/
private theorem character_mem_characterRing_of_representation
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
    ρ.character ∈ R(G) := by
  -- Pass to the bundled `Rep` interface used by the Chapter 11 character-ring theorem.
  simpa using rep_character_mem_characterRing (Rep.of ρ)

/-- Corollary 12-12.3-2: every finite-dimensional complex representation of the finite group `G`
can be realized over `K` when `K` contains the roots of unity of orders dividing
`Monoid.exponent G`. -/
theorem isRealizableOver_of_hasEnoughRootsOfUnity
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
    IsRealizableOver K ρ := by
  -- Rewrite realizability as the corresponding character-ring membership statement.
  rw [isRealizableOver_iff_character_mem_characterRingOverFieldInExtension]
  -- Identify the extension character ring with `R(G)` using the enough-roots-of-unity bridge.
  rw [characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity (K := K) (G := G)]
  -- The helper isolates the only interface change from `Representation` to `Rep`.
  exact character_mem_characterRing_of_representation (G := G) ρ

end

end Representation
