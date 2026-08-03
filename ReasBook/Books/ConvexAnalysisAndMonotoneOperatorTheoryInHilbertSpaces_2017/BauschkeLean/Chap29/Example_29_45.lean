import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap29.Definition_29_40

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped BigOperators

universe u v

section

variable {ι : Type u} {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall: `lean_leansearch` only surfaced generic projection owners in mathlib, so this
-- item uses the project-local metric projection notation `P[C, hC]`.

/-- Each member of an intersecting closed convex family in a real Hilbert space is Chebyshev. -/
theorem family_isChebyshev_of_iInter_nonempty_closed_convex
    (C : ι → Set H) (hinter : (⋂ i, C i).Nonempty)
    (hclosed : ∀ i, IsClosed (C i)) (hconvex : ∀ i, Convex ℝ (C i))
    (i : ι) : IsChebyshev (C i) := by
  -- An intersection witness lies in every `C i`, so each family member is nonempty.
  rcases hinter with ⟨z, hz⟩
  have hz_i : z ∈ C i := Set.mem_iInter.mp hz i
  -- Closed convex nonempty subsets of a real Hilbert space are Chebyshev.
  exact isChebyshev_of_nonempty_isClosed_convex ⟨z, hz_i⟩ (hclosed i) (hconvex i)

variable [Fintype ι]

/-- The weighted average of the metric projectors onto a finite family of Chebyshev sets. -/
noncomputable def weighted_projection_average
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i)) : H → H :=
  fun x ↦ ∑ i, ω i • P[C i, hC i] x

/-- The weighted half squared-distance potential attached to a finite family of sets. -/
noncomputable def weighted_sq_infDist (C : ι → Set H) (ω : ι → ℝ) : H → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * ∑ i, ω i * Metric.infDist x (C i) ^ 2

/-- The weighted numerator in the Example 29.45 subgradient-projector formula. -/
noncomputable def weighted_projection_residual_sq_sum
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i)) : H → ℝ :=
  fun x ↦ ∑ i, ω i * ‖P[C i, hC i] x - x‖ ^ 2

/-- The field `x ↦ x - ∑ i, ω i • P_{C i} x` used in Example 29.45; under
`∑ i, ω i = 1`, this is the gradient of `weighted_sq_infDist C ω`. -/
noncomputable def weighted_sq_infDist_gradient
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i)) : H → H :=
  fun x ↦ x - weighted_projection_average C ω hC x

/-- The source-facing differentiable subgradient projector attached to the weighted half
squared-distance potential `f = (1 / 2) ∑ i, ω i * d(x, C i)^2` at threshold `0`. -/
noncomputable def weighted_sq_infDist_subgradientProjector
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i)) : H → H :=
  fun x ↦
    if 0 < weighted_sq_infDist C ω x then
      x +
        (((0 : ℝ) - weighted_sq_infDist C ω x) /
            ‖weighted_sq_infDist_gradient C ω hC x‖ ^ 2) •
          weighted_sq_infDist_gradient C ω hC x
    else
      x

/-- Zero lower-level-set identity for Example 29.45: for a finite intersecting family of
closed convex subsets of a real Hilbert space with normalized positive weights, the zero
lower level set of the weighted half squared-distance potential is the intersection of the
family. -/
theorem weighted_sq_infDist_zeroSublevelSet_eq_iInter
    (C : ι → Set H) (ω : ι → ℝ) (hinter : (⋂ i, C i).Nonempty)
    (hclosed : ∀ i, IsClosed (C i))
    (hconvex : ∀ i, Convex ℝ (C i))
    (hω_pos : ∀ i, 0 < ω i) (hω_sum : ∑ i, ω i = 1) :
    lowerLevelSet (weighted_sq_infDist C ω).toEReal.asEReal 0 = ⋂ i, C i := by
  let _ := hconvex
  let _ := hω_sum
  ext x
  have hCi_nonempty : ∀ i, (C i).Nonempty := by
    rcases hinter with ⟨z, hz⟩
    intro i
    exact ⟨z, Set.mem_iInter.mp hz i⟩
  constructor
  · intro hx
    rw [mem_lowerLevelSet_iff] at hx
    norm_num [Function.toEReal_apply] at hx
    have hsum_nonneg :
        0 ≤ ∑ i, ω i * Metric.infDist x (C i) ^ 2 := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg (le_of_lt (hω_pos i)) (sq_nonneg (Metric.infDist x (C i)))
    have hfx_nonneg : 0 ≤ weighted_sq_infDist C ω x := by
      rw [weighted_sq_infDist]
      exact mul_nonneg (by positivity) hsum_nonneg
    have hfx_zero : weighted_sq_infDist C ω x = 0 := le_antisymm hx hfx_nonneg
    have hsum_zero : ∑ i, ω i * Metric.infDist x (C i) ^ 2 = 0 := by
      rw [weighted_sq_infDist] at hfx_zero
      nlinarith
    have hterm_zero :
        ∀ i, ω i * Metric.infDist x (C i) ^ 2 = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj ↦ mul_nonneg (le_of_lt (hω_pos j))
          (sq_nonneg (Metric.infDist x (C j))))).1 hsum_zero i (Finset.mem_univ i)
    -- Each weighted squared distance vanishes, so each pointwise distance is zero.
    refine Set.mem_iInter.mpr ?_
    intro i
    have hsq_zero : Metric.infDist x (C i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp (hterm_zero i) with hω_zero | hsq_zero
      · exact False.elim ((ne_of_gt (hω_pos i)) hω_zero)
      · exact hsq_zero
    have hdist_zero : Metric.infDist x (C i) = 0 := sq_eq_zero_iff.mp hsq_zero
    exact ((hclosed i).mem_iff_infDist_zero (hCi_nonempty i)).2 hdist_zero
  · intro hx
    rw [mem_lowerLevelSet_iff]
    have hdist_zero : ∀ i, Metric.infDist x (C i) = 0 := by
      intro i
      exact Metric.infDist_zero_of_mem (Set.mem_iInter.mp hx i)
    -- Inside every `C i`, all distance terms vanish, so the weighted potential is zero.
    simpa [Function.asEReal_apply, Function.toEReal_apply, weighted_sq_infDist, hdist_zero]

/-- Lower-level-set branch for Example 29.45: on
the lower-level-set branch
`x ∈ lowerLevelSet (weighted_sq_infDist C ω).toEReal.asEReal 0`, the Example 29.45
subgradient projector fixes `x`. -/
theorem weighted_sq_infDist_subgradientProjector_apply_of_mem_lowerLevelSet
    (C : ι → Set H) (ω : ι → ℝ) (hinter : (⋂ i, C i).Nonempty)
    (hclosed : ∀ i, IsClosed (C i)) (hconvex : ∀ i, Convex ℝ (C i))
    {x : H} (hx : x ∈ lowerLevelSet (weighted_sq_infDist C ω).toEReal.asEReal 0) :
    weighted_sq_infDist_subgradientProjector C ω
      (family_isChebyshev_of_iInter_nonempty_closed_convex C hinter hclosed hconvex) x = x := by
  have hfx : weighted_sq_infDist C ω x ≤ 0 := by
    simpa [Function.toEReal_apply] using
      (mem_lowerLevelSet_iff (weighted_sq_infDist C ω).toEReal.asEReal 0 x).1 hx
  simp [weighted_sq_infDist_subgradientProjector, not_lt.mpr hfx]

/-- On the active branch `0 < weighted_sq_infDist C ω x`, the Example 29.45 subgradient
projector is given by its defining differentiable formula. -/
theorem weighted_sq_infDist_subgradientProjector_apply_of_pos
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i))
    {x : H} (hx : 0 < weighted_sq_infDist C ω x) :
    weighted_sq_infDist_subgradientProjector C ω hC x =
      x + (((0 - weighted_sq_infDist C ω x) /
          ‖weighted_sq_infDist_gradient C ω hC x‖ ^ 2) •
        weighted_sq_infDist_gradient C ω hC x) := by
  simp [weighted_sq_infDist_subgradientProjector, hx]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 29.45: the weighted squared-distance potential is one half of the weighted
projection-residual square sum. -/
lemma weighted_sq_infDist_eq_half_residual_sq_sum
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i)) (x : H) :
    weighted_sq_infDist C ω x =
      (1 / 2 : ℝ) * weighted_projection_residual_sq_sum C ω hC x := by
  have hterm :
      ∀ i, ω i * Metric.infDist x (C i) ^ 2 =
        ω i * ‖P[C i, hC i] x - x‖ ^ 2 := by
    intro i
    congr 1
    -- Each chosen projection point realizes the infimum distance to `C i`.
    have hdist :
        Metric.infDist x (C i) = ‖P[C i, hC i] x - x‖ := by
      simpa [dist_eq_norm, norm_sub_rev] using
        (projectionPoint_isBestApproximation (C i) (hC i) x).2.symm
    rw [hdist]
  -- Rewrite the finite sum termwise and keep the common factor `1 / 2`.
  simp [weighted_sq_infDist, weighted_projection_residual_sq_sum, hterm]

omit [CompleteSpace H] in
/-- Helper for Example 29.45: the chosen gradient field is the negative of the displayed weighted
projection residual vector. -/
lemma weighted_sq_infDist_gradient_eq_neg_projection_average_sub
    (C : ι → Set H) (ω : ι → ℝ) (hC : ∀ i, IsChebyshev (C i)) (x : H) :
    weighted_sq_infDist_gradient C ω hC x =
      -(weighted_projection_average C ω hC x - x) := by
  -- The gradient field is defined as `x - avg`, which is `-(avg - x)`.
  rw [weighted_sq_infDist_gradient]
  exact (neg_sub (weighted_projection_average C ω hC x) x).symm

/-- Example 29.45 (3): on the branch
`x ∉ lowerLevelSet (weighted_sq_infDist C ω).toEReal.asEReal 0`, the Example 29.45
subgradient projector is given by the weighted projector formula `(29.75)` for a finite
intersecting closed convex family with positive weights. -/
theorem weighted_sq_infDist_subgradientProjector_apply_of_not_mem_lowerLevelSet
    (C : ι → Set H) (ω : ι → ℝ) (hinter : (⋂ i, C i).Nonempty)
    (hclosed : ∀ i, IsClosed (C i)) (hconvex : ∀ i, Convex ℝ (C i))
    (hω_pos : ∀ i, 0 < ω i)
    {x : H} (hx : x ∉ lowerLevelSet (weighted_sq_infDist C ω).toEReal.asEReal 0) :
    weighted_sq_infDist_subgradientProjector C ω
      (family_isChebyshev_of_iInter_nonempty_closed_convex C hinter hclosed hconvex) x =
      x +
        (weighted_projection_residual_sq_sum C ω
            (family_isChebyshev_of_iInter_nonempty_closed_convex C hinter hclosed hconvex) x /
            (2 * ‖weighted_projection_average C ω
              (family_isChebyshev_of_iInter_nonempty_closed_convex C hinter hclosed hconvex) x -
                x‖ ^ 2)) •
          (weighted_projection_average C ω
            (family_isChebyshev_of_iInter_nonempty_closed_convex C hinter hclosed hconvex) x -
            x) := by
  let hC : ∀ i, IsChebyshev (C i) :=
    family_isChebyshev_of_iInter_nonempty_closed_convex C hinter hclosed hconvex
  have hsum_nonneg :
      0 ≤ ∑ i, ω i * Metric.infDist x (C i) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (le_of_lt (hω_pos i)) (sq_nonneg (Metric.infDist x (C i)))
  have hfx_nonneg : 0 ≤ weighted_sq_infDist C ω x := by
    rw [weighted_sq_infDist]
    exact mul_nonneg (by positivity) hsum_nonneg
  have hx_pos : 0 < weighted_sq_infDist C ω x := by
    -- Outside the lower level set, nonnegativity forces the active branch `0 < f x`.
    refine lt_of_not_ge ?_
    intro hfx_le
    exact hx <|
      by
        rw [mem_lowerLevelSet_iff]
        simpa [Function.asEReal_apply, Function.toEReal_apply] using hfx_le
  have hcoeff :
      (((1 / 2 : ℝ) * weighted_projection_residual_sq_sum C ω hC x) /
          ‖weighted_projection_average C ω hC x - x‖ ^ 2) =
        weighted_projection_residual_sq_sum C ω hC x /
          (2 * ‖weighted_projection_average C ω hC x - x‖ ^ 2) := by
    ring
  -- Rewrite the canonical active branch into the displayed weighted-projector formula `(29.75)`.
  calc
    weighted_sq_infDist_subgradientProjector C ω hC x
        =
      x + (((0 - weighted_sq_infDist C ω x) /
          ‖weighted_sq_infDist_gradient C ω hC x‖ ^ 2) •
        weighted_sq_infDist_gradient C ω hC x) := by
          exact weighted_sq_infDist_subgradientProjector_apply_of_pos C ω hC hx_pos
    _ =
      x + (((0 - ((1 / 2 : ℝ) * weighted_projection_residual_sq_sum C ω hC x)) /
          ‖weighted_sq_infDist_gradient C ω hC x‖ ^ 2) •
        weighted_sq_infDist_gradient C ω hC x) := by
          rw [weighted_sq_infDist_eq_half_residual_sq_sum]
    _ =
      x + (((0 - ((1 / 2 : ℝ) * weighted_projection_residual_sq_sum C ω hC x)) /
          ‖weighted_projection_average C ω hC x - x‖ ^ 2) •
        (-(weighted_projection_average C ω hC x - x))) := by
          rw [weighted_sq_infDist_gradient_eq_neg_projection_average_sub, norm_neg]
    _ =
      x +
        (weighted_projection_residual_sq_sum C ω hC x /
            (2 * ‖weighted_projection_average C ω hC x - x‖ ^ 2)) •
          (weighted_projection_average C ω hC x - x) := by
            rw [zero_sub, neg_div, neg_smul, smul_neg, neg_neg, hcoeff]

end
