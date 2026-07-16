import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_04.Example_1_36

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic search note: no `lean_leansearch` tool was available in this environment.
-- The statement below reuses the `grassmannian.chart_fun` owner from Example 1.36 together with
-- mathlib's product-coordinate linear algebra API.

/-- The first coordinate plane in the standard splitting `ℝ^k × ℝ^(n-k)`. -/
abbrev left_coordinate_plane (k n : ℕ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin (n - k) → ℝ)) :=
  LinearMap.range
    (LinearMap.inl ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))

/-- The second coordinate plane in the standard splitting `ℝ^k × ℝ^(n-k)`. -/
abbrev right_coordinate_plane (k n : ℕ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin (n - k) → ℝ)) :=
  LinearMap.range
    (LinearMap.inr ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))

/-- Helper for Problem 1-10: the standard coordinate planes are complementary. -/
theorem coordinate_planes_isCompl (k n : ℕ) :
    IsCompl (left_coordinate_plane k n) (right_coordinate_plane k n) := sorry

/-- Helper for Problem 1-10: the first coordinate plane has dimension `k`. -/
theorem left_coordinate_plane_finrank (k n : ℕ) :
    Module.finrank ℝ (left_coordinate_plane k n) = k := sorry

/-- Helper for Problem 1-10: the `j`th column of the block matrix `\(\begin{pmatrix} I_k \\ B
\end{pmatrix}\)` in the standard splitting `ℝ^k × ℝ^(n-k)`. -/
def block_column_vector (k n : ℕ) (B : Matrix (Fin (n - k)) (Fin k) ℝ) (j : Fin k) :
    (Fin k → ℝ) × (Fin (n - k) → ℝ) :=
  (Pi.single j (1 : ℝ), fun i ↦ B i j)

/-- Helper for Problem 1-10: the subspace spanned by the columns of the block matrix
`\(\begin{pmatrix} I_k \\ B \end{pmatrix}\)`. -/
def block_column_subspace (k n : ℕ) (B : Matrix (Fin (n - k)) (Fin k) ℝ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin (n - k) → ℝ)) :=
  Submodule.span ℝ (Set.range (block_column_vector k n B))

/-- Helper for Problem 1-10: the span of the columns of `\(\begin{pmatrix} I_k \\ B
\end{pmatrix}\)` is the graph of the linear map represented by `B`. -/
theorem block_column_subspace_eq_graph (k n : ℕ) (B : Matrix (Fin (n - k)) (Fin k) ℝ) :
    block_column_subspace k n B = LinearMap.graph (Matrix.toLin' B) := sorry

/-- Helper for Problem 1-10: the first coordinate plane is canonically identified with `ℝ^k`. -/
noncomputable def left_coordinate_plane_equiv (k n : ℕ) :
    (Fin k → ℝ) ≃ₗ[ℝ] left_coordinate_plane k n :=
  LinearEquiv.ofInjective
    (LinearMap.inl ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))
    LinearMap.inl_injective

/-- Helper for Problem 1-10: the second coordinate plane is canonically identified with
`ℝ^(n-k)`. -/
noncomputable def right_coordinate_plane_equiv (k n : ℕ) :
    (Fin (n - k) → ℝ) ≃ₗ[ℝ] right_coordinate_plane k n :=
  LinearEquiv.ofInjective
    (LinearMap.inr ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))
    LinearMap.inr_injective

/-- Helper for Problem 1-10: the matrix form of Lee's chart coordinate `φ(S)` from Example 1.36
for the standard decomposition `ℝ^n = P ⊕ Q` with `P = ℝ^k × {0}` and `Q = {0} × ℝ^(n-k)`. -/
noncomputable def problem_1_10_chart_matrix (k n : ℕ)
    (S : grassmannian ((Fin k → ℝ) × (Fin (n - k) → ℝ)) k)
    (hS : S ∈ grassmannian.chart_domain (right_coordinate_plane k n)) :
    Matrix (Fin (n - k)) (Fin k) ℝ :=
  LinearMap.toMatrix' <|
    ((((right_coordinate_plane_equiv k n).symm : right_coordinate_plane k n ≃ₗ[ℝ]
        (Fin (n - k) → ℝ)).toLinearMap).comp
      (grassmannian.chart_fun (coordinate_planes_isCompl k n) (left_coordinate_plane_finrank k n)
        S hS)).comp
      (left_coordinate_plane_equiv k n).toLinearMap

/-- Problem 1-10: for the standard splitting `ℝ^n = P ⊕ Q` with
`P = \operatorname{span}(e_1,\ldots,e_k)` and `Q = \operatorname{span}(e_{k+1},\ldots,e_n)`,
the coordinate representation `φ(S)` from Example 1.36 is exactly the unique matrix
`B : Matrix (Fin (n - k)) (Fin k) ℝ` whose block columns span `S`. -/
theorem standard_chart_matrix_unique {k n : ℕ}
    (S : grassmannian ((Fin k → ℝ) × (Fin (n - k) → ℝ)) k)
    (hS : S ∈ grassmannian.chart_domain (right_coordinate_plane k n)) :
    S.1 = block_column_subspace k n (problem_1_10_chart_matrix k n S hS) ∧
      ∀ B : Matrix (Fin (n - k)) (Fin k) ℝ,
        S.1 = block_column_subspace k n B →
          B = problem_1_10_chart_matrix k n S hS := sorry
