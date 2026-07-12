import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5

open MeasureTheory
open scoped ENNReal

-- Semantic recall: `MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le` is the canonical
-- approximation theorem. Using an `ε`-approximation statement here avoids imposing the hidden
-- `SecondCountableTopologyEither G ℂ` assumption carried by `Lp.boundedContinuousFunction_dense`,
-- while remaining faithful to the source on a compact group, where continuous maps are bounded.

section

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- Lemma 4-47 — Density of `C(G)` in `L^2(G)`.

For a compact group `G` with normalized Haar measure `normalizedHaarMeasure`, every `L²(G)`
function can be approximated arbitrarily well in `eLpNorm` by a continuous complex-valued
function. -/
theorem continuousFunctions_denseInL2
    {f : G → ℂ} (hf : MemLp f (2 : ENNReal) μG) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : C(G, ℂ), eLpNorm (fun x : G ↦ f x - g x) (2 : ENNReal) μG ≤ ε := by
  rcases hf.exists_boundedContinuous_eLpNorm_sub_le (by simp) hε with ⟨g, hg, _⟩
  exact ⟨g.toContinuousMap, by simpa using hg⟩

/-- Companion form of `continuousFunctions_denseInL2` that also records that the approximating
continuous function belongs to `L²(G)`. -/
theorem continuousFunctions_denseInL2_memLp
    {f : G → ℂ} (hf : MemLp f (2 : ENNReal) μG) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : C(G, ℂ), eLpNorm (fun x : G ↦ f x - g x) (2 : ENNReal) μG ≤ ε ∧
      MemLp (fun x : G ↦ g x) (2 : ENNReal) μG := by
  rcases continuousFunctions_denseInL2 hf hε with ⟨g, hg⟩
  exact ⟨g, hg, by simpa using ContinuousMap.memLp (μG : Measure G) ℂ g⟩

end
