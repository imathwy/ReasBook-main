import Mathlib
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `stdSimplex ℝ ι` is the canonical owner for simplex coefficients, while
-- `Set.Finite.isClosed_convexHull` and `Finset.mem_convexHull` are the main mathlib entry points
-- for finite convex hulls and their barycentric descriptions.

open scoped BigOperators InnerProductSpace

universe u v

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {ι : Type v} [Fintype ι]

/-- The quadratic objective from Proposition 29.26 on the simplex of coefficients of a finite
family `x`. -/
def convexHullProjectionObjective (x : ι → 𝓗) (z : 𝓗) (α : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, α i * α j * ⟪x i, x j⟫_ℝ - (2 : ℝ) * ∑ i, α i * ⟪x i, z⟫_ℝ

section

variable (hι : Nonempty ι) (x : ι → 𝓗)

local notation "C" => convexHull ℝ (Set.range x)
private theorem isChebyshev_convexHull_range {ι : Type v} [Finite ι] (x : ι → 𝓗)
    (hι : Nonempty ι) :
    IsChebyshev (convexHull ℝ (Set.range x)) := by
  refine
    isChebyshev_of_nonempty_isClosed_convex ?_ ?_ (convex_convexHull ℝ (Set.range x))
  · exact Set.Nonempty.convexHull <|
      Set.range_nonempty_iff_nonempty.mpr hι
  · simpa using (Set.finite_range x).isClosed_convexHull ℝ

local notation "P_C" => P[C, isChebyshev_convexHull_range x hι]

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 29.26: membership in `convexHull ℝ (Set.range x)` is equivalent to a
barycentric representation with coefficients in `stdSimplex ℝ ι`. -/
private lemma mem_convexHull_range_iff_exists_stdSimplex_sum {y : 𝓗} :
    y ∈ convexHull ℝ (Set.range x) ↔
      ∃ α : ι → ℝ, α ∈ stdSimplex ℝ ι ∧ y = ∑ i, α i • x i := by
  classical
  constructor
  · intro hy
    rw [convexHull_range_eq_exists_affineCombination] at hy
    rcases hy with ⟨s, w, hw₀, hw₁, rfl⟩
    let α : ι → ℝ := fun i ↦ if i ∈ s then w i else 0
    have hα_sum : ∑ i, α i = 1 := by
      simpa [α] using (Finset.sum_ite_mem_eq s w).trans hw₁
    have hy_sum :
        s.affineCombination ℝ x w = ∑ i, α i • x i := by
      -- Extend the finitely supported affine coefficients by zero to all of `ι`.
      calc
        s.affineCombination ℝ x w = Finset.sum s (fun i ↦ w i • x i) := by
          simpa using (Finset.affineCombination_eq_linear_combination s x w hw₁)
        _ = ∑ i, if i ∈ s then w i • x i else 0 := by
          symm
          exact Finset.sum_ite_mem_eq s (fun i ↦ w i • x i)
        _ = ∑ i, α i • x i := by
          simp [α]
    refine ⟨α, ?_, hy_sum⟩
    constructor
    · intro i
      by_cases hi : i ∈ s
      · simpa [α, hi] using hw₀ i hi
      · simp [α, hi]
    · exact hα_sum
  · intro hy
    rcases hy with ⟨α, hα, hy⟩
    rw [convexHull_range_eq_exists_affineCombination]
    refine ⟨Finset.univ, α, ?_, hα.2, ?_⟩
    · intro i hi
      exact hα.1 i
    · -- On the whole index set, affine and linear combinations coincide because the weights sum
      -- to `1`.
      rw [hy]
      simpa using (Finset.affineCombination_eq_linear_combination Finset.univ x α hα.2)

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 29.26: the quadratic program is the squared distance to the barycentric
sum, shifted by the constant `‖z‖ ^ 2`. -/
private lemma convexHullProjectionObjective_eq_sqDist_sub_normSq
    (z : 𝓗) (α : ι → ℝ) :
    convexHullProjectionObjective x z α = ‖(∑ i, α i • x i) - z‖ ^ 2 - ‖z‖ ^ 2 := by
  have hnorm :
      ‖∑ i, α i • x i‖ ^ 2 =
        ∑ i, ∑ j, α i * α j * ⟪x i, x j⟫_ℝ := by
    -- Expand the squared norm into the double inner-product sum from the statement.
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    ring
  have hinner :
      ⟪∑ i, α i • x i, z⟫_ℝ =
        ∑ i, α i * ⟪x i, z⟫_ℝ := by
    -- The linear term is the inner product of the barycentric sum with `z`.
    simp_rw [sum_inner, real_inner_smul_left]
  -- Rewrite the norm square and then identify the resulting polynomial expression.
  rw [norm_sub_sq_real]
  rw [convexHullProjectionObjective, hnorm, hinner]
  ring

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 29.26: the squared-distance objective attains a minimum on
`stdSimplex ℝ ι`. -/
private lemma exists_isMinOn_sqDist_on_stdSimplex (hι : Nonempty ι) (z : 𝓗) :
    ∃ αbar : ι → ℝ,
      αbar ∈ stdSimplex ℝ ι ∧
        IsMinOn (fun α ↦ ‖(∑ i, α i • x i) - z‖ ^ 2) (stdSimplex ℝ ι) αbar := by
  classical
  let f : (ι → ℝ) → ℝ := fun α ↦ ‖(∑ i, α i • x i) - z‖ ^ 2
  have hne : (stdSimplex ℝ ι).Nonempty := by
    rcases hι with ⟨i⟩
    exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
  have hcont : Continuous f := by
    -- The barycentric map is continuous, and taking a squared norm preserves continuity.
    dsimp [f]
    fun_prop
  obtain ⟨αbar, hαbar, hmin⟩ :=
    (isCompact_stdSimplex ℝ ι).exists_isMinOn hne hcont.continuousOn
  exact ⟨αbar, hαbar, hmin⟩

/-- Proposition 29.26: if `C = convexHull ℝ (Set.range x)`, then the metric projection of `z`
onto `C` is a barycentric sum `∑ i, αbar i • x i` for some simplex minimizer `αbar` of the
quadratic program
`min_{α ∈ stdSimplex ℝ ι} \sum_{i,j} α_i α_j ⟪x_i, x_j⟫ - 2 \sum_i α_i ⟪x_i, z⟫`.
This is the finite-index owner statement; the textbook `m`-tuple form is its specialization to
`ι = Fin m` with `m > 0`. -/
theorem exists_simplex_isMinOn_convexHullProjectionObjective_eq_projectionPoint
    (z : 𝓗) :
    ∃ αbar : ι → ℝ,
      αbar ∈ stdSimplex ℝ ι ∧
        IsMinOn (convexHullProjectionObjective x z) (stdSimplex ℝ ι) αbar ∧
        P_C z = ∑ i, αbar i • x i := by
  obtain ⟨αbar, hαbar, hminSq⟩ := exists_isMinOn_sqDist_on_stdSimplex (x := x) hι z
  let p : 𝓗 := ∑ i, αbar i • x i
  have hminSq' :
      ∀ α ∈ stdSimplex ℝ ι,
        ‖(∑ i, αbar i • x i) - z‖ ^ 2 ≤ ‖(∑ i, α i • x i) - z‖ ^ 2 := by
    simpa [IsMinOn, IsMinFilter, Filter.mem_principal, Set.mem_setOf_eq] using hminSq
  have hp_mem : p ∈ C := by
    -- The minimizing barycentric sum lies in the convex hull because its coefficients belong to
    -- the simplex.
    exact (mem_convexHull_range_iff_exists_stdSimplex_sum (x := x)).2 ⟨αbar, hαbar, rfl⟩
  have hminObjective : IsMinOn (convexHullProjectionObjective x z) (stdSimplex ℝ ι) αbar := by
    -- Reinterpret the squared-distance minimum as a minimum for the shifted quadratic objective.
    simpa [IsMinOn, IsMinFilter, Filter.mem_principal, Set.mem_setOf_eq] using
      (fun α hα ↦ by
        have hsq := hminSq' α hα
        rw [convexHullProjectionObjective_eq_sqDist_sub_normSq (x := x) (z := z) (α := αbar)]
        rw [convexHullProjectionObjective_eq_sqDist_sub_normSq (x := x) (z := z) (α := α)]
        linarith)
  have hproj_best : IsBestApproximation z C (P_C z) :=
    projectionPoint_isBestApproximation C (isChebyshev_convexHull_range x hι) z
  obtain ⟨β, hβ, hβ_sum⟩ :=
    (mem_convexHull_range_iff_exists_stdSimplex_sum (x := x)).1
      (projectionPoint_mem C (isChebyshev_convexHull_range x hι) z)
  have hdist_sq : dist z p ^ 2 ≤ dist z (P_C z) ^ 2 := by
    -- Compare the minimizing barycenter against the projection point written in simplex
    -- coordinates.
    simpa [p, hβ_sum.symm, dist_eq_norm, norm_sub_rev] using hminSq' β hβ
  have hdist_le : dist z p ≤ dist z (P_C z) := by
    have hp_nonneg : 0 ≤ dist z p := dist_nonneg
    have hproj_nonneg : 0 ≤ dist z (P_C z) := dist_nonneg
    nlinarith
  have hp_dist : dist z p = Metric.infDist z C := by
    apply le_antisymm
    · calc
        dist z p ≤ dist z (P_C z) := hdist_le
        _ = Metric.infDist z C := hproj_best.2
    · exact Metric.infDist_le_dist_of_mem hp_mem
  have hp_best : IsBestApproximation z C p := ⟨hp_mem, hp_dist⟩
  refine ⟨αbar, hαbar, hminObjective, ?_⟩
  -- Any best approximation in a Chebyshev set must be the chosen projection point.
  simpa [p] using (eq_projectionPoint_of_isBestApproximation C
    (isChebyshev_convexHull_range x hι) hp_best).symm

end
