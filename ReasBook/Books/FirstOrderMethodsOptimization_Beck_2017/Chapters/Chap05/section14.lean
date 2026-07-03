import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_14 (from Chap05) -/
open scoped BigOperators
open WithLp (ofLp)

noncomputable section

section

variable {n : ℕ}

local notation "E₁" => WithLp 1 (Fin n → ℝ)
local notation "E₂" => EuclideanSpace ℝ (Fin n)
local notation "Δ₁" => Set.preimage (ofLp : E₁ → Fin n → ℝ) (stdSimplex ℝ (Fin n))
local notation "Δ₂" =>
  Set.preimage (fun x : E₂ ↦ fun i : Fin n ↦ x i) (stdSimplex ℝ (Fin n))

/- Proposition 5.14 is `source-facing`: the primitive data are the negative-entropy integrand
`x ↦ ∑ i, x_i log x_i` and the standard simplex. Domain sampling points to mathlib's
`StrongConvexOn` as the natural `core/canonical` owner abstraction, so in item-per-file mode the
statement is repaired directly to strong convexity of the real-valued entropy on the simplex in the
two ambient normed models, without relying on unavailable project-local wrapper imports. -/

/-- The coordinatewise negative entropy `x ↦ ∑ i, x_i log x_i` on `ℝ^n`. -/
def coordinatewise_negative_entropy (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * Real.log (x i)

-- Proof sketch: restrict the source extension-by-`∞` to the simplex, where it is exactly the
-- finite-valued entropy `coordinatewise_negative_entropy`. Compute the Hessian on the relative
-- interior as the diagonal form with entries `(x i)⁻¹`, then use the weighted Cauchy-Schwarz
-- inequality on tangent directions to obtain the quadratic lower bound by the `ℓ₁` norm.
/-- Proposition 5.14 (1): the negative entropy on the unit simplex is `1`-strongly convex with
respect to the `l_1` norm, stated in the canonical real-valued form on the simplex itself. -/
theorem negative_entropy_on_stdSimplex_is_one_strongly_convex_l1 (n : ℕ) :
    StrongConvexOn
      Δ₁
      1
      (fun x : E₁ ↦ coordinatewise_negative_entropy (ofLp x)) := sorry

-- Proof sketch: use the same Hessian formula as in the `ℓ₁` statement and combine the tangent
-- lower bound by `‖h‖₁²` with the norm comparison `‖h‖₂ ≤ ‖h‖₁`. This yields the same modulus `1`
-- for the Euclidean norm on the simplex.
/-- Proposition 5.14 (2): the negative entropy on the unit simplex is `1`-strongly convex with
respect to the `l_2` norm, stated in the canonical real-valued form on the simplex itself. -/
theorem negative_entropy_on_stdSimplex_is_one_strongly_convex_l2 (n : ℕ) :
    StrongConvexOn
      Δ₂
      1
      (fun x : E₂ ↦ coordinatewise_negative_entropy (fun i ↦ x i)) := sorry

end
