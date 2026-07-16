import LinearRepresentations_Serre_1977.Serre.Chap04.ContinuousIrreducibleFamily
import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_12
import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_28

noncomputable section

open CategoryTheory
open MeasureTheory
open scoped ENNReal Representation

-- Semantic recall: `lean_leansearch` surfaced `HilbertBasis.mk` and `Orthonormal.isHilbertSum`,
-- while Definitions 4-12 and 4-28 already export the canonical Chapter 4 owners
-- `Representation.characterL2`, `FDRep.characterToLp`,
-- `IsCompleteContinuousIrreducibleFamily`, and
-- `squareIntegrableClassFunctionSubmodule`. The source claim is therefore recorded as the
-- orthonormality and dense-span pair in ambient `L²(G)`, together with thin companion theorems
-- on the chapter-level `characterL2` surface.

universe v

namespace Representation

section

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable {ι : Type v}

local notation "L²G" => (G →₂[(μG : Measure G)] ℂ)

/-- Theorem 4-29 (1): for a pairwise nonisomorphic family of finite-dimensional irreducible
complex representations of the compact group `G` whose characters are continuous, the
corresponding characters, viewed in `L²(G)` through the canonical `ContinuousMap.toLp` map, form
an orthonormal family. Combined with Theorem 4-29 (2), this yields the source statement that a
complete irreducible family gives an orthonormal basis of `L²_cl(G)`. -/
theorem orthonormal_irreducibleCharacters_of_pairwiseNonisomorphic
    (π : ι → FDRep ℂ G)
    (hπ_irred : ∀ i, Representation.IsIrreducible (π i).ρ)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_char_cont : ∀ i, Continuous fun g ↦ (π i).character g) :
    Orthonormal ℂ (fun i ↦ FDRep.characterToLp (π i) (hπ_char_cont i)) := sorry

/-- Companion to Theorem 4-29 (1): when the family members are continuous representations, the
same orthonormality statement is available on the canonical Chapter 4 surface
`Representation.characterL2`. -/
theorem orthonormal_characterL2_of_pairwiseNonisomorphic
    (π : ι → FDRep ℂ G)
    (hπ_irred : ∀ i, Representation.IsIrreducible (π i).ρ)
    (hπ_pairwise : PairwiseNonisomorphic π)
    [(i : ι) → TopologicalSpace (π i).V]
    [(i : ι) → IsTopologicalAddGroup (π i).V]
    [(i : ι) → ContinuousSMul ℂ (π i).V]
    [(i : ι) → T2Space (π i).V]
    [hπ_cont : ∀ i, Representation.IsContinuous (π i).ρ] :
    Orthonormal ℂ (fun i ↦ characterL2 (π i).ρ) := by
  let hπ_char_cont : ∀ i, Continuous fun g ↦ (π i).character g :=
    fun i ↦ continuous_character_of_isContinuousCompact (π i).ρ
  simpa using
    orthonormal_irreducibleCharacters_of_pairwiseNonisomorphic
      π hπ_irred hπ_pairwise hπ_char_cont

/-- Theorem 4-29 (2): for a complete family of finite-dimensional irreducible complex
representations of the compact group `G` whose characters are continuous and which is complete up
to isomorphism for continuous irreducible finite-dimensional complex representations, the closed
`ℂ`-span of their characters inside `L²(G)` is exactly
`squareIntegrableClassFunctionSubmodule`, the canonical submodule underlying `L²_cl(G)`. Together
with `orthonormal_characterL2_of_pairwiseNonisomorphic`, this is the Hilbert-basis form of the
source statement. Pairwise nonisomorphism is not needed for the dense-span claim because repeated
or isomorphic members do not change the character range or its closed span. -/
theorem denseSpan_irreducibleCharacters_eq_squareIntegrableClassSubmodule_of_completeFamily
    (π : ι → FDRep ℂ G)
    (hπ_complete : IsCompleteContinuousIrreducibleFamily π)
    (hπ_char_cont : ∀ i, Continuous fun g ↦ (π i).character g) :
    (Submodule.span ℂ
      (Set.range fun i ↦ FDRep.characterToLp (π i) (hπ_char_cont i))).topologicalClosure =
      squareIntegrableClassFunctionSubmodule := sorry

/-- Companion to Theorem 4-29 (2): when the family members are continuous representations, the
dense-span statement uses the canonical Chapter 4 family `fun i ↦ Representation.characterL2
(π i).ρ`. -/
theorem denseSpan_characterL2_eq_squareIntegrableClassSubmodule_of_completeFamily
    (π : ι → FDRep ℂ G)
    (hπ_complete : IsCompleteContinuousIrreducibleFamily π)
    [(i : ι) → TopologicalSpace (π i).V]
    [(i : ι) → IsTopologicalAddGroup (π i).V]
    [(i : ι) → ContinuousSMul ℂ (π i).V]
    [(i : ι) → T2Space (π i).V]
    [hπ_cont : ∀ i, Representation.IsContinuous (π i).ρ] :
    (Submodule.span ℂ
      (Set.range fun i ↦ characterL2 (π i).ρ)).topologicalClosure =
      squareIntegrableClassFunctionSubmodule := by
  let hπ_char_cont : ∀ i, Continuous fun g ↦ (π i).character g :=
    fun i ↦ continuous_character_of_isContinuousCompact (π i).ρ
  simpa using
    denseSpan_irreducibleCharacters_eq_squareIntegrableClassSubmodule_of_completeFamily
      π hπ_complete hπ_char_cont

end

end Representation
