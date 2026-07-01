import FirstOrderMethodsinOptimization.Chap01.Definition_1_27
import FirstOrderMethodsinOptimization.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)
open scoped BigOperators

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.17 is a `bridge/view` item in the chapter Euclidean subdifferential API. The
owner abstraction is `subdifferentialAt` from Theorem 3.4, and its canonical vector-side bridge is
`euclideanSubdifferentialAt`. The only source-facing content here is the coordinate sign-cube
description of that owner set for the `ℓ₁` norm, now written through mathlib's canonical
`WithLp 1` norm on finite products, so the theorem should use the bridge directly rather than
re-expand the `toDualMap` preimage by hand. -/

recall euclideanSubdifferentialAt
recall PiLp.norm_eq_of_L1

/-- The coordinatewise sign cube describing the vector-side subgradients of the `ℓ₁` norm at
`x`. -/
def l1CoordinateSubgradientVectors (x : E) : Set E :=
  (fun z : E ↦ fun i ↦ z i) ⁻¹'
    Set.pi Set.univ (fun i ↦ if x i = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign (x i)})

/-- Membership in `l1CoordinateSubgradientVectors x` means matching the coordinatewise sign on the
nonzero coordinates of `x` and staying in `[-1, 1]` on the zero coordinates. -/
@[simp] theorem mem_l1CoordinateSubgradientVectors_iff
    {x z : E} :
    z ∈ l1CoordinateSubgradientVectors x ↔
      (∀ i, x i ≠ 0 → z i = Real.sign (x i)) ∧
        ∀ i, x i = 0 → |z i| ≤ 1 := by
  constructor
  · intro hz
    have hz' : ∀ i, z i ∈ if x i = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign (x i)} := by
      simpa [l1CoordinateSubgradientVectors] using hz
    refine ⟨?_, ?_⟩
    · intro i hxi
      simpa [hxi] using hz' i
    · intro i hxi
      simpa [Set.mem_Icc, abs_le, hxi] using hz' i
  · rintro ⟨hsign, hzero⟩
    have hz' : ∀ i, z i ∈ if x i = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign (x i)} := by
      intro i
      by_cases hxi : x i = 0
      · simpa [Set.mem_Icc, abs_le, hxi] using hzero i hxi
      · simp [hxi, hsign i hxi]
    simp [l1CoordinateSubgradientVectors, hz']

/-- The canonical coordinatewise sign vector belongs to the coordinate description of the `ℓ₁`
subdifferential. -/
theorem sign_vector_mem_l1CoordinateSubgradientVectors (x : E) :
    toLp 2 (sgn x) ∈ l1CoordinateSubgradientVectors x := by
  rw [mem_l1CoordinateSubgradientVectors_iff]
  refine ⟨?_, ?_⟩
  · intro i hxi
    rcases lt_or_gt_of_ne hxi with h_neg | h_pos
    · simp [sgn_apply, not_le_of_gt h_neg, Real.sign_of_neg h_neg]
    · simp [sgn_apply, h_pos.le, Real.sign_of_pos h_pos]
  · intro i hxi
    simp [sgn_apply, hxi]

-- Proof sketch: write the `ℓ₁` norm on `ℝ^n` as the finite sum of the coordinate functions
-- `y ↦ |y i|`, apply the finite-dimensional sum rule for subdifferentials, and use the
-- one-dimensional computation `euclidean_subdifferentialAt_abs_eq_piecewise` for `t ↦ |t|` on
-- each
-- coordinate. The resulting statement is expressed directly through the chapter bridge
-- `euclideanSubdifferentialAt`, with the objective written via the canonical `WithLp 1` norm on
-- finite products.
/-- Proposition 3.17: for the `ℓ₁` norm
`f(x) = ‖toLp 1 (fun i ↦ x i)‖ = ∑ i, |x i|` on `ℝ^n = EuclideanSpace ℝ (Fin n)`, the
Euclidean/vector-side subdifferential consists exactly of the vectors in
`l1CoordinateSubgradientVectors x`, i.e. the vectors whose coordinates equal `Real.sign (x i)` on
the nonzero coordinates of `x` and lie in `[-1, 1]` on the zero coordinates. -/
theorem subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖toLp 1 fun i ↦ y i‖) x =
      l1CoordinateSubgradientVectors x := sorry

end
