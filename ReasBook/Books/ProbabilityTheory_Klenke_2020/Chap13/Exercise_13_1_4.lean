import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped BigOperators

/-- Exercise 13.1.4: if a family of positive-length intervals in `ℝ` has union of finite Lebesgue
measure, then for every `ε > 0` there is a finite pairwise disjoint subfamily whose total
Lebesgue measure is strictly larger than `((1 - ε) / 3)` times the measure of the whole union. -/
-- Proof sketch: first choose a finite subfamily whose union captures all but an `ε`-fraction of
-- `⋃₀ 𝓤`. Then apply the Vitali covering theorem to this finite interval family. The resulting
-- disjoint subfamily has the property that every interval in the finite approximation is contained
-- in the triple expansion of one selected interval, so the union measure is controlled by `3`
-- times the total measure of the disjoint family.
theorem exists_pairwiseDisjoint_interval_subfamily_large_measure
    (𝓤 : Set (Set ℝ))
    (h𝓤 : ∀ U ∈ 𝓤, U.OrdConnected ∧ 0 < volume.real U)
    (hfinite : volume (⋃₀ 𝓤) < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (Set ℝ),
      (↑s : Set (Set ℝ)) ⊆ 𝓤 ∧
      (↑s : Set (Set ℝ)).PairwiseDisjoint id ∧
      ((1 - ε) / 3) * volume.real (⋃₀ 𝓤) < ∑ U ∈ s, volume.real U :=
  sorry
