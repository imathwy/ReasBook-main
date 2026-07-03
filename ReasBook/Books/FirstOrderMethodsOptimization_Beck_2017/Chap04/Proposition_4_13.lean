import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Matrix

section

variable {n : ℕ}

/- Proposition 4.13 is `source-facing`: the genuine new content here is the affine-range
description of the conjugate of a positive-semidefinite quadratic and its source-facing
range-inverse witness. The `core/canonical` owners for the quadratic itself and for Fenchel
conjugation are already `quadratic_affine_function` and `conjugate_function` from Definition 4.4
and Definition 4.1, so this file reuses those owners instead of keeping parallel local copies. -/

/-- The affine set `b + Range(A)` appearing in the conjugate formula for a convex quadratic. -/
def quadratic_affine_range
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun z : Fin n → ℝ ↦ b + z) '' (LinearMap.range A.mulVecLin : Set (Fin n → ℝ))

-- Proof sketch: unwind membership in the image defining `quadratic_affine_range`; this is exactly
-- the existence of a vector `z ∈ Range(A)` with `y = b + z`, equivalently `y - b ∈ Range(A)`.
/-- Membership in `quadratic_affine_range A b` is equivalent to the translated vector `y - b`
lying in `Range(A)`. -/
theorem mem_quadratic_affine_range_iff
    (A : Matrix (Fin n) (Fin n) ℝ) (b y : Fin n → ℝ) :
    y ∈ quadratic_affine_range A b ↔ y - b ∈ LinearMap.range A.mulVecLin := sorry

/-- For a positive semidefinite real matrix, every `y ∈ Range(A)` has a unique preimage that also
lies in `Range(A)`. This is the source-facing range version of the Moore--Penrose inverse. -/
theorem quadratic_positive_semidefinite_range_preimage_existsUnique
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (y : Fin n → ℝ) :
    y ∈ LinearMap.range A.mulVecLin →
      ∃! x : Fin n → ℝ, x ∈ LinearMap.range A.mulVecLin ∧ A *ᵥ x = y := sorry

/-- The canonical inverse of a positive semidefinite matrix on `Range(A)`: for `y ∈ Range(A)` it is
the unique vector `x ∈ Range(A)` with `A x = y`, and it is `0` off the range. -/
noncomputable def quadratic_positive_semidefinite_pseudoinverse_on_range
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun y ↦
    open scoped Classical in
    if hy : y ∈ LinearMap.range A.mulVecLin then
      Classical.choose
        (ExistsUnique.exists (quadratic_positive_semidefinite_range_preimage_existsUnique A hA y hy))
    else
      0

-- Proof sketch: unfold `quadratic_positive_semidefinite_pseudoinverse_on_range`; on the branch
-- `hy : y ∈ Range(A)`, the result is the chosen witness from the unique-existence statement
-- `quadratic_positive_semidefinite_range_preimage_existsUnique A hA y hy`.
/-- On `Range(A)`, the canonical range pseudoinverse vector lies in `Range(A)` and is sent to `y`
by `A`. -/
theorem quadratic_positive_semidefinite_pseudoinverse_on_range_spec
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (y : Fin n → ℝ)
    (hy : y ∈ LinearMap.range A.mulVecLin) :
    quadratic_positive_semidefinite_pseudoinverse_on_range A hA y ∈ LinearMap.range A.mulVecLin ∧
      A *ᵥ quadratic_positive_semidefinite_pseudoinverse_on_range A hA y = y := sorry

-- Proof sketch: rewrite the conjugate as the supremum of the concave quadratic
-- `x ↦ -1/2 xᵀ A x + (y - b)ᵀ x - c`. If `y ∈ b + Range(A)`, solve the stationarity equation
-- `A x = y - b` using the Moore--Penrose pseudoinverse and evaluate the objective at that maximizer.
-- If `y ∉ b + Range(A)`, choose a null vector with positive pairing against `y - b` and send its
-- scalar multiples to `∞`.
/-- Proposition 4.13: for the convex quadratic `f(x) = 1/2 xᵀ A x + bᵀ x + c` with `A`
positive semidefinite, the Fenchel conjugate equals `1/2 (y - b)ᵀ A† (y - b) - c` on
`b + Range(A)` and equals `∞` outside that affine range. On the branch `y - b ∈ Range(A)`, the
term `A† (y - b)` is represented by the canonical range inverse
`quadratic_positive_semidefinite_pseudoinverse_on_range A hA (y - b)`. -/
theorem convex_quadratic_function_conjugate_eq
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (b y : Fin n → ℝ) (c : ℝ) :
    open scoped Classical in
      conjugate_function (fun x : Fin n → ℝ ↦ (quadratic_affine_function A b c x : EReal))
        (dotProductEquiv ℝ (Fin n) y) =
        if y ∈ quadratic_affine_range A b then
          (((1 / 2 : ℝ) * dotProduct (y - b)
              (quadratic_positive_semidefinite_pseudoinverse_on_range A hA (y - b)) - c : ℝ) :
            EReal)
        else
          ⊤ := sorry

end
