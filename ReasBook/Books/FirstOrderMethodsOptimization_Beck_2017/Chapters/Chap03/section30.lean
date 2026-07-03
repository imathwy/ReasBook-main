

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_30 (from Chap03) -/
open Matrix
open scoped BigOperators

section

variable {m n : ℕ}

/- Proposition 3.30 is a `bridge/view` item in the chapter's max-affine subdifferential API. The
source-facing statement is the active-face weight criterion for optimality, while the matrix
version below is only a coordinate rewrite of the same condition using the owner matrix action
`Aᵀ *ᵥ weights`. -/

/- Proposition 3.30: for the max-affine function
`f(x) = max_i (a_i^T x + b_i)` on `ℝ^n`, the vector-side subdifferential at `x` is exactly the
set of convex combinations of the active slope vectors `a_i`, equivalently the image of the active
face of the standard simplex under the barycentric combination map. -/
recall isMinOn_univ_iff_zero_mem_subdifferentialAt
recall subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace

-- Proof sketch: a point `x` is a global minimizer exactly when the zero vector belongs to the
-- vector-side subdifferential of the max-affine objective at `x`. Then specialize the recalled
-- max-affine subdifferential formula at `g = 0`, which turns membership of the subdifferential
-- into the existence of simplex weights in the active coordinate face of the affine-value vector
-- whose weighted sum of active slopes is zero.
/-- A point `x` minimizes the max-affine objective globally if and only if there are simplex
weights in the active coordinate face of the affine-value vector
`i ↦ a i ⬝ᵥ x + b i` whose weighted sum of the slope vectors is zero. -/
theorem isMinOn_piecewiseLinearMax_iff_exists_activeWeights
    (hm : 0 < m) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    IsMinOn (fun y ↦ coordinatewiseMax (fun i ↦ a i ⬝ᵥ y + b i)) Set.univ x ↔
      ∃ weights : Fin m → ℝ,
        weights ∈ activeCoordinateFace (fun i ↦ a i ⬝ᵥ x + b i) ∧
          (∑ i, weights i • a i) = 0 := by
  rw [isMinOn_univ_iff_zero_mem_subdifferentialAt]
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace hm a b x]
  simp only [Set.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨weights, hweights, hzero⟩
    exact ⟨weights, hweights,
      ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap).map_eq_zero_iff.mp
        hzero⟩
  · rintro ⟨weights, hweights, hzero⟩
    exact ⟨weights, hweights,
      ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap).map_eq_zero_iff.mpr
        hzero⟩

-- Proof sketch: rewrite the weighted-sum condition `∑ i, λ i • A i = 0` as the matrix equation
-- `Aᵀ *ᵥ λ = 0`, and note that
-- `activeCoordinateFace (fun i ↦ A i ⬝ᵥ x + b i)` already packages the simplex
-- constraint together with support on the active affine pieces.
/- Matrix form of the max-affine optimality criterion: the minimizing weights lie in the active
coordinate face of the affine-value vector and annihilate the transpose of the slope matrix. -/
theorem isMinOn_piecewiseLinearMax_matrix_iff_exists_activeWeights
    (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    IsMinOn (fun y ↦ coordinatewiseMax (fun i ↦ A i ⬝ᵥ y + b i)) Set.univ x ↔
      ∃ weights : Fin m → ℝ,
        weights ∈ activeCoordinateFace (fun i ↦ A i ⬝ᵥ x + b i) ∧
          Aᵀ *ᵥ weights = 0 := by
  rw [isMinOn_piecewiseLinearMax_iff_exists_activeWeights hm (fun i ↦ A i) b x]
  constructor
  · rintro ⟨weights, hweights, hsum⟩
    refine ⟨weights, hweights, ?_⟩
    simpa [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum] using hsum
  · rintro ⟨weights, hweights, hmul⟩
    refine ⟨weights, hweights, ?_⟩
    simpa [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum] using hmul

end

/-! ### Theorem_3_30 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Theorem 3.30 is a `source-facing` Fermat criterion for the chapter owner notion
`subdifferential`. Its primitive data are already owned upstream:
`effective_domain` comes from Chapter 2, while
`subdifferential` is the derived set of `is_subgradient_at` from Definitions 3.1 and 3.2.
This file therefore reuses that owner API directly instead of introducing a parallel local copy.
-/

-- Proof sketch: if `x` minimizes `f` on all of `E`, a point of `effective_domain f` supplies
-- some `y` with `f y < ⊤`, hence also `f x < ⊤`; then the subgradient inequality for the zero
-- functional is
-- exactly the global minimality inequality. Conversely, if `0 ∈ ∂ f(x)`, unfold
-- `subdifferential`; the zero functional kills `y - x`, leaving `f x ≤ f y` for every `y`.
/-- Theorem 3.30: Fermat's optimality condition for the chapter's extended-real subdifferential.
If the effective domain of an extended-real-valued function is nonempty, then a point is a global
minimizer exactly when the zero dual vector belongs to its subdifferential. -/
theorem isMinOn_univ_iff_zero_mem_subdifferential
    {f : E → EReal} (hdom : (effective_domain f).Nonempty) {x : E} :
    IsMinOn f Set.univ x ↔ 0 ∈ subdifferential f x := by
  rw [isMinOn_univ_iff, mem_subdifferential, is_subgradient_at]
  constructor
  · intro hx
    rcases hdom with ⟨y, hy⟩
    refine ⟨lt_of_le_of_lt (hx y) hy, ?_⟩
    intro z
    simpa using hx z
  · rintro ⟨_, hx⟩ y
    simpa using hx y

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The real-valued strong-dual formulation is a `bridge/view` corollary of the source-facing
owner theorem above. The primitive data still belongs to `subdifferential`; `subdifferentialAt`
is only the canonical real-valued view used later in the chapter. -/

/-- Theorem 3.30 in the real-valued strong-dual view: a point globally minimizes `f`
exactly when the zero continuous linear functional belongs to `subdifferentialAt f x`. -/
theorem isMinOn_univ_iff_zero_mem_subdifferentialAt
    {f : E → ℝ} {x : E} :
    IsMinOn f Set.univ x ↔ (0 : StrongDual ℝ E) ∈ subdifferentialAt f x := by
  have hdom : (effective_domain fun y ↦ (f y : EReal)).Nonempty := ⟨x, by simp [effective_domain]⟩
  have hferm :
      IsMinOn (fun y ↦ (f y : EReal)) Set.univ x ↔
        (0 : Module.Dual ℝ E) ∈ subdifferential (fun y ↦ (f y : EReal)) x :=
    isMinOn_univ_iff_zero_mem_subdifferential hdom
  simp [isMinOn_univ_iff, subdifferentialAt, mem_subdifferential,
    is_subgradient_at_coe_iff] at hferm ⊢

end
