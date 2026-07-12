import SmoothManifolds_Lee_2012.Chap07.Sec07_51.Exercise_7_31

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling pass:
-- * primary domain: matrix Lie groups and semidirect-product decompositions;
-- * sampled owners: `LieGroupIsomorphicToSemidirectProduct`, `semidirectProductGroup`,
--   `semidirectProductLieGroup`, and the matrix-group owners
--   `Matrix.orthogonalGroup` / `Matrix.specialOrthogonalGroup` /
--   `Matrix.unitaryGroup` / `Matrix.specialUnitaryGroup`;
-- * owner abstraction used below: the source-facing predicate
--   `LieGroupIsomorphicToSemidirectProduct`;
-- * primitive data: only the ambient Lie-group structures on the matrix groups;
-- * derived API: the semidirect-product realization data are supplied existentially by the owner.

open scoped Manifold ContDiff MatrixGroups

section RealMatrixGroupStatements

variable (n : ℕ) [Fact (0 < n)]

local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ
local notation "SO(" n ")" => Matrix.specialOrthogonalGroup (Fin n) ℝ
local notation "Mₙℝ" => Matrix (Fin n) (Fin n) ℝ
local notation "Iₙℝ" => 𝓘(ℝ, Mₙℝ)
local notation "I₁ℝ" => 𝓘(ℝ, Matrix (Fin 1) (Fin 1) ℝ)

variable [ChartedSpace Mₙℝ (SO(n))] [LieGroup Iₙℝ ∞ (SO(n))]
variable [ChartedSpace (Matrix (Fin 1) (Fin 1) ℝ) (O(1))] [LieGroup I₁ℝ ∞ (O(1))]
variable [ChartedSpace Mₙℝ (O(n))] [LieGroup Iₙℝ ∞ (O(n))]

/-- Problem 7-20 (1): for positive `n`, `O(n)` is Lie-group-isomorphic to a semidirect product
`SO(n) ⋊ O(1)`. -/
theorem orthogonal_group_semidirect_specialOrthogonal_orthogonal_one :
    LieGroupIsomorphicToSemidirectProduct Iₙℝ I₁ℝ Iₙℝ (SO(n)) (O(1)) (O(n)) :=
  sorry

variable [ChartedSpace Mₙℝ (SL(n, ℝ))] [LieGroup Iₙℝ ∞ (SL(n, ℝ))]
variable [ChartedSpace Mₙℝ (GL(n, ℝ))] [LieGroup Iₙℝ ∞ (GL(n, ℝ))]
variable [ChartedSpace ℝ ℝˣ] [LieGroup (𝓘(ℝ, ℝ)) ∞ ℝˣ]

/-- Problem 7-20 (3): for positive `n`, `GL(n, ℝ)` is Lie-group-isomorphic to a semidirect
product `SL(n, ℝ) ⋊ ℝˣ`. -/
theorem generalLinearGroup_real_semidirect_specialLinear_units :
    LieGroupIsomorphicToSemidirectProduct
      Iₙℝ (𝓘(ℝ, ℝ)) Iₙℝ (SL(n, ℝ)) ℝˣ (GL(n, ℝ)) :=
  sorry

end RealMatrixGroupStatements

section ComplexMatrixGroupStatements

variable (n : ℕ) [Fact (0 < n)]
local notation "U(" n ")" => Matrix.unitaryGroup (Fin n) ℂ
local notation "SU(" n ")" => Matrix.specialUnitaryGroup (Fin n) ℂ
local notation "Mₙℂ" => Matrix (Fin n) (Fin n) ℂ
local notation "Iₙℂ" => 𝓘(ℝ, Mₙℂ)
local notation "I₁ℂ" => 𝓘(ℝ, Matrix (Fin 1) (Fin 1) ℂ)

variable [ChartedSpace Mₙℂ (SU(n))] [LieGroup Iₙℂ ∞ (SU(n))]
variable [ChartedSpace (Matrix (Fin 1) (Fin 1) ℂ) (U(1))] [LieGroup I₁ℂ ∞ (U(1))]
variable [ChartedSpace Mₙℂ (U(n))] [LieGroup Iₙℂ ∞ (U(n))]

/-- Problem 7-20 (2): for positive `n`, `U(n)` is Lie-group-isomorphic to a semidirect product
`SU(n) ⋊ U(1)`. -/
theorem unitary_group_semidirect_specialUnitary_unitary_one :
    LieGroupIsomorphicToSemidirectProduct Iₙℂ I₁ℂ Iₙℂ (SU(n)) (U(1)) (U(n)) :=
  sorry

variable [ChartedSpace Mₙℂ (SL(n, ℂ))] [LieGroup Iₙℂ ∞ (SL(n, ℂ))]
variable [ChartedSpace Mₙℂ (GL(n, ℂ))] [LieGroup Iₙℂ ∞ (GL(n, ℂ))]
variable [ChartedSpace ℂ ℂˣ] [LieGroup (𝓘(ℝ, ℂ)) ∞ ℂˣ]

/-- Problem 7-20 (4): for positive `n`, `GL(n, ℂ)` is Lie-group-isomorphic to a semidirect
product `SL(n, ℂ) ⋊ ℂˣ`. -/
theorem generalLinearGroup_complex_semidirect_specialLinear_units :
    LieGroupIsomorphicToSemidirectProduct
      Iₙℂ (𝓘(ℝ, ℂ)) Iₙℂ (SL(n, ℂ)) ℂˣ (GL(n, ℂ)) :=
  sorry

end ComplexMatrixGroupStatements
