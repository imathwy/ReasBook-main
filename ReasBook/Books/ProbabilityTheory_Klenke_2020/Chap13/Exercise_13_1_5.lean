import Mathlib

open scoped BigOperators Pointwise
open MeasureTheory Set

/-- Exercise 13.1.5 (1): from a family of positive homothetic copies of a fixed open bounded convex
set in `ℝ^d`, modeled as `(Fin d → ℝ)`, whose union has finite Lebesgue measure, one can extract
finitely many pairwise disjoint members whose total measure is larger than
`((1 - ε) / 3^d) * λ^d(⋃₀ 𝒰)`. -/
-- Proof sketch: apply a Vitali-type covering argument to the family of translated dilates
-- `{x} + r • C`,
-- extract a disjoint subfamily covering almost all of the union, and then truncate the countable
-- disjoint family to a finite subfamily while losing only an `ε`-fraction of the total measure.
theorem exists_pairwiseDisjoint_homothetic_subfamily_large_measure
    (d : ℕ) (C : Set (Fin d → ℝ)) (𝒰 : Set (Set (Fin d → ℝ)))
    (hC_open : IsOpen C) (hC_convex : Convex ℝ C) (hC_bounded : Bornology.IsBounded C)
    (h𝒰 :
      ∀ U ∈ 𝒰,
        ∃ x : Fin d → ℝ, ∃ r > 0, U = ({x} : Set (Fin d → ℝ)) + r • C)
    (h_union_finite : volume (⋃₀ 𝒰) < ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (Set (Fin d → ℝ)),
      (↑s : Set (Set (Fin d → ℝ))) ⊆ 𝒰 ∧
      (↑s : Set (Set (Fin d → ℝ))).PairwiseDisjoint id ∧
      ((1 - ε) / (3 : ℝ) ^ d) * volume.real (⋃₀ 𝒰) < ∑ U ∈ s, volume.real U := sorry

/-- Exercise 13.1.5 (2): there is a family of open bounded convex sets in `ℝ²` with finite union
measure, modeled as `(Fin 2 → ℝ)`, for which the same positive-measure finite disjoint selection
lower bound fails, showing that the common similarity hypothesis in part (1) is essential. -/
-- Proof sketch: take a classical counterexample built from nonsimilar thin convex sets with large
-- overlap so that the union has finite measure but every finite pairwise disjoint subfamily carries
-- too little total measure compared with the union.
theorem exists_open_bounded_convex_counterexample_without_similarity :
    ∃ 𝒰 : Set (Set (Fin 2 → ℝ)), ∃ ε : ℝ,
      0 < ε ∧
      (∀ U ∈ 𝒰, IsOpen U ∧ Bornology.IsBounded U ∧ Convex ℝ U) ∧
      0 < volume.real (⋃₀ 𝒰) ∧
      volume (⋃₀ 𝒰) < ⊤ ∧
      ¬ ∃ s : Finset (Set (Fin 2 → ℝ)),
          (↑s : Set (Set (Fin 2 → ℝ))) ⊆ 𝒰 ∧
          (↑s : Set (Set (Fin 2 → ℝ))).PairwiseDisjoint id ∧
          ((1 - ε) / (3 : ℝ) ^ 2) * volume.real (⋃₀ 𝒰) < ∑ U ∈ s, volume.real U := sorry
