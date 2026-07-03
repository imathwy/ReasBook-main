import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_11 (from Chap05) -/
open Matrix
open WithLp (ofLp)

noncomputable section

section

variable {n : ℕ}

local notation "X" => Fin n → ℝ
local notation "X₂" => WithLp (2 : ENNReal) X

/- Proposition 5.11 is `source-facing`: it specializes the Chapter 4 quadratic owner
`quadratic_affine_function A b c` to the canonical `ℓ₂` model of `ℝ^n` and studies strong
convexity for a symmetric quadratic form. The canonical matrix-side owner abstractions are
`Matrix.PosSemidef`, `Matrix.PosDef`, and the ordered Hermitian spectrum. -/

/-- The quadratic-affine function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n`. -/
def quadratic_affine_function (A : Matrix (Fin n) (Fin n) ℝ) (b : X) (c : ℝ) : X → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * dotProduct x (A *ᵥ x) + dotProduct b x + c

/-- The quadratic-affine function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c`, viewed on the canonical
`ℓ₂` model of `ℝ^n`. -/
def quadratic_affine_function_on_l2 (A : Matrix (Fin n) (Fin n) ℝ) (b : X) (c : ℝ) : X₂ → ℝ :=
  quadratic_affine_function A b c ∘ ofLp

-- Proof sketch: `quadratic_affine_function_on_l2` is the coordinate quadratic-affine map
-- precomposed with `WithLp.ofLp`.
/-- Evaluating `quadratic_affine_function_on_l2 A b c` at `x` applies the coordinate
quadratic-affine map to the underlying vector `ofLp x`. -/
@[simp] theorem quadratic_affine_function_on_l2_apply
    (A : Matrix (Fin n) (Fin n) ℝ) (b : X) (c : ℝ) (x : X₂) :
    quadratic_affine_function_on_l2 A b c x = quadratic_affine_function A b c (ofLp x) := sorry

-- Proof sketch: for real matrices, Hermitian means equality with the conjugate transpose, and the
-- conjugate transpose is just the ordinary transpose.
/-- A real symmetric matrix is Hermitian. -/
theorem Matrix.IsSymm.isHermitian_real {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.IsHermitian := sorry

/-- The smallest eigenvalue of a real symmetric `n × n` matrix, using the canonical increasing
order endpoint of the Hermitian spectrum when `n > 0`. -/
noncomputable def symmetric_matrix_min_eigenvalue (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hn : 0 < n) : ℝ :=
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  (hA.isHermitian_real).eigenvalues ⊤

-- Proof sketch: apply the inner-product-space characterization
-- `strongConvexOn_iff_convex` to `quadratic_affine_function_on_l2 A b c`, expand the quadratic
-- correction, and identify convexity of the remaining quadratic form with positive semidefiniteness
-- of `A - σ • 1`.
/-- Proposition 5.11: for the quadratic function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n`
equipped with the `ℓ₂` norm, strong convexity with positive parameter `σ` is equivalent to the
shifted symmetric matrix `A - σ I` being positive semidefinite. -/
theorem quadratic_affine_function_on_l2_strongConvexOn_iff_posSemidef_shift
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (b : X) (c σ : ℝ) (hσ : 0 < σ) :
    StrongConvexOn Set.univ σ (quadratic_affine_function_on_l2 A b c) ↔
      (A - σ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := sorry

-- Proof sketch: combine the shifted-matrix criterion above with the Hermitian spectral theorem:
-- for a real symmetric matrix, `A - σ • 1` is positive semidefinite iff all its eigenvalues are
-- nonnegative, equivalently iff the smallest eigenvalue of `A` is at least `σ`.
/-- For a real symmetric quadratic form, the strong-convexity modulus `σ` is admissible exactly
when it does not exceed the smallest eigenvalue of the Hessian matrix `A`. -/
theorem quadratic_affine_function_on_l2_strongConvexOn_iff_le_min_eigenvalue
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hn : 0 < n) (b : X) (c σ : ℝ) (hσ : 0 < σ) :
    StrongConvexOn Set.univ σ (quadratic_affine_function_on_l2 A b c) ↔
      σ ≤ symmetric_matrix_min_eigenvalue A hA hn := sorry

-- Proof sketch: translate existence of a positive strong-convexity modulus into existence of
-- `σ > 0` with `(A - σ • 1).PosSemidef`, then use the Hermitian eigenvalue criterion to identify
-- this with positivity of every eigenvalue of `A`, i.e. positive definiteness.
/-- The quadratic function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n` is strongly convex for some
positive modulus if and only if its symmetric Hessian matrix `A` is positive definite. -/
theorem quadratic_affine_function_on_l2_exists_pos_strongConvexOn_iff_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (b : X) (c : ℝ) :
    (∃ σ : ℝ, 0 < σ ∧ StrongConvexOn Set.univ σ (quadratic_affine_function_on_l2 A b c)) ↔
      A.PosDef := sorry

-- Proof sketch: use the previous eigenvalue characterization to show that the admissible positive
-- moduli are exactly the interval `(0, λ_min(A)]`; positive definiteness ensures this interval is
-- nonempty and that its greatest element is `λ_min(A)`.
/-- If the quadratic Hessian matrix `A` is positive definite, then its smallest eigenvalue is the
largest positive strong-convexity parameter of the associated quadratic function on `ℝ^n` with the
`ℓ₂` norm. -/
theorem symmetric_matrix_min_eigenvalue_isGreatest_strongConvexity_parameter
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hn : 0 < n) (hApos : A.PosDef)
    (b : X) (c : ℝ) :
    IsGreatest
      {σ : ℝ | 0 < σ ∧ StrongConvexOn Set.univ σ (quadratic_affine_function_on_l2 A b c)}
      (symmetric_matrix_min_eigenvalue A hA hn) := sorry

end
