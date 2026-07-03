import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Matrix
open PointedCone

noncomputable section

section

variable {m n : ℕ}

/-- The cone cut out by the coordinatewise inequalities `A *ᵥ x ≤ 0`, realized as the preimage of
the positive cone under the matrix linear map. -/
def matrix_nonpositive_cone (A : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ (Fin n → ℝ) :=
  (positive ℝ (Fin m → ℝ)).comap (-A).mulVecLin

/-- The transpose image of the nonnegative orthant in `ℝⁿ`, realized as the image of the positive
cone under the transpose matrix linear map. -/
def transpose_nonnegative_cone (A : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ (Fin n → ℝ) :=
  (positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin

/-- The Euclidean-dual realization of `transpose_nonnegative_cone A`, transported along
`dotProductEquiv ℝ (Fin n)`. -/
def transpose_nonnegative_dual_cone (A : Matrix (Fin m) (Fin n) ℝ) :
    PointedCone ℝ (Module.Dual ℝ (Fin n → ℝ)) :=
  (transpose_nonnegative_cone A).map (dotProductEquiv ℝ (Fin n))

@[simp]
theorem mem_matrix_nonpositive_cone (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ matrix_nonpositive_cone A ↔ A *ᵥ x ≤ (0 : Fin m → ℝ) := by
  simp [matrix_nonpositive_cone]

@[simp]
theorem mem_transpose_nonnegative_cone (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    y ∈ transpose_nonnegative_cone A ↔
      ∃ z ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ z = y := by
  rw [transpose_nonnegative_cone, mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, ?_, ?_⟩
    · simpa using hz
    have hzy' : z ᵥ* A = y := by
      simpa [Matrix.mulVecLin_apply] using hzy
    exact (Matrix.mulVec_transpose A z).trans hzy'
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, ?_, ?_⟩
    · simpa using hz
    have hzy' : z ᵥ* A = y := (Matrix.mulVec_transpose A z).symm.trans hzy
    simpa [Matrix.mulVecLin_apply] using hzy'

@[simp]
theorem mem_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Module.Dual ℝ (Fin n → ℝ)) :
    y ∈ transpose_nonnegative_dual_cone A ↔
      ∃ z ∈ Set.Ici (0 : Fin m → ℝ), dotProductEquiv ℝ (Fin n) (Aᵀ *ᵥ z) = y := by
  rw [transpose_nonnegative_dual_cone, mem_map]
  constructor
  · rintro ⟨v, hv, hy⟩
    rcases (mem_transpose_nonnegative_cone A v).mp hv with ⟨z, hz, rfl⟩
    exact ⟨z, hz, hy⟩
  · rintro ⟨z, hz, hy⟩
    exact ⟨Aᵀ *ᵥ z, (mem_transpose_nonnegative_cone A _).2 ⟨z, hz, rfl⟩, hy⟩

-- Proof sketch: rewrite membership in
-- `polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ))` as the implication
-- `A *ᵥ x ≤ 0 → dotProduct y x ≤ 0` for every `x`; then use the bridge
-- `farkas_lemma_second_formulation_iff_mem_positive_map` to identify the representing vector with
-- the owner-side image of the positive cone under `Aᵀ.mulVecLin`, and finally transport along
-- `dotProductEquiv ℝ (Fin n)`.
/-- The polar cone of the matrix inequality set consists exactly of Euclidean-dual vectors of the
form `Aᵀ *ᵥ λ` with `λ ≥ 0`. -/
theorem polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ)) =
      (transpose_nonnegative_dual_cone A : Set (Module.Dual ℝ (Fin n → ℝ))) := sorry

-- Proof sketch: combine the cone-case identity `σ_K = δ_{Kᵒ}` with the explicit description of
-- `polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ))` from
-- `polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone`.
/-- Example 2.7: for `S = {x : ℝ^n | A *ᵥ x ≤ 0}`, the support function `σ_S` is the indicator
function of the Euclidean-dual image `{(Aᵀ *ᵥ λ) | λ ∈ ℝ^m_+}`. -/
theorem support_function_matrix_nonpositive_cone_eq_extendedIndicator_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    support_function (matrix_nonpositive_cone A : Set (Fin n → ℝ)) =
      extendedIndicator (transpose_nonnegative_dual_cone A : Set (Module.Dual ℝ (Fin n → ℝ))) :=
    sorry

end
