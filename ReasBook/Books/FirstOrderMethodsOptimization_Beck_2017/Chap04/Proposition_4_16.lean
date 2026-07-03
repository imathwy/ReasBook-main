import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_35

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

/- Proposition 4.16 is `source-facing`: its primitive data are the simplex-constrained negative
entropy and the associated finite Fenchel objective, while the canonical softmax owner declaration
is already `softmax_point` from Proposition 3.35. The Chapter 4 `core/canonical` owner
abstraction for Fenchel conjugates is `conjugate_function` from Definition 4.1, so this file
reuses both upstream owners directly instead of keeping parallel local copies. -/

section

variable {n : ℕ}

/-- Classical decidability for membership in the standard simplex, used to define the extended
negative entropy by cases. -/
local instance stdSimplex_mem_decidable :
    DecidablePred (fun x : Fin n → ℝ ↦ x ∈ stdSimplex ℝ (Fin n)) :=
  Classical.decPred _

/-- The negative entropy on the standard simplex, extended by `∞` outside `stdSimplex ℝ (Fin n)`.
This is the function `x ↦ ∑ i, x i * log (x i)` from the source proposition. -/
def negative_entropy_on_stdSimplex (n : ℕ) : (Fin n → ℝ) → EReal :=
  fun x ↦
    if x ∈ stdSimplex ℝ (Fin n) then
      ((∑ i, x i * Real.log (x i) : ℝ) : EReal)
    else
      ⊤

/-- The finite-dimensional Fenchel objective associated with the negative entropy on the simplex.
It is the negative of `entropy_linear_objective` from Proposition 3.35. -/
def negative_entropy_fenchel_objective
    (y x : Fin n → ℝ) : ℝ :=
  -entropy_linear_objective y x

-- Proof sketch: unfold the canonical Chapter 4 `conjugate_function` and
-- `negative_entropy_on_stdSimplex`. For `x` outside the simplex, the term
-- `(dotProductEquiv ℝ (Fin n) y x : EReal) - ⊤` is `⊥`, so those points do not affect the
-- supremum. On the simplex, the affine-minus-entropy term is exactly the coercion of
-- `negative_entropy_fenchel_objective y x`, leaving the supremum over the simplex image.
/-- Evaluating the conjugate of the simplex negative entropy at `y` is the supremum of the finite
Fenchel objective over the standard simplex. -/
theorem negative_entropy_on_stdSimplex_conjugate_eq_sSup
    (y : Fin n → ℝ) :
    conjugate_function (negative_entropy_on_stdSimplex n)
        (dotProductEquiv ℝ (Fin n) y) =
      sSup
        ((fun x : Fin n → ℝ ↦
            ((negative_entropy_fenchel_objective y x : ℝ) : EReal)) ''
          stdSimplex ℝ (Fin n)) := sorry

section

variable [NeZero n]

-- Proof sketch: optimize `negative_entropy_fenchel_objective y` on the simplex using a Lagrange
-- multiplier for the constraint `∑ i, x i = 1`. The stationarity equations
-- `log (x i) = y i + λ - 1` yield `x i = c * exp (y i)`, and the simplex constraint forces
-- `c = (∑ j, exp (y j))⁻¹`, so the optimizer is exactly `softmax_point y`.
/-- The softmax point is a maximizer of the Fenchel objective of the negative entropy over the
standard simplex. -/
theorem softmax_point_isMaxOn_negative_entropy_fenchel_objective
    (y : Fin n → ℝ) :
    IsMaxOn (negative_entropy_fenchel_objective y) (stdSimplex ℝ (Fin n)) (softmax_point y) := sorry

end

-- Proof sketch: expand `negative_entropy_fenchel_objective` at `softmax_point y`, use
-- `log (softmax_point y i) = y i - log (∑ j, exp (y j))`, and then sum over the simplex identity
-- `∑ i, softmax_point y i = 1` to collapse the entropy terms. No nonemptiness assumption is
-- needed here: when `n = 0`, both sides reduce to `Real.log 0 = 0` by the empty-sum convention.
/-- The Fenchel objective at the softmax point equals the log-sum-exp of `y`. -/
theorem negative_entropy_fenchel_objective_softmax_eq_log_sum_exp
    (y : Fin n → ℝ) :
    negative_entropy_fenchel_objective y (softmax_point y) =
      Real.log (∑ j, Real.exp (y j)) := sorry

section

variable [NeZero n]

-- Proof sketch: rewrite the conjugate with `negative_entropy_on_stdSimplex_conjugate_eq_sSup`,
-- use `softmax_point_isMaxOn_negative_entropy_fenchel_objective` to identify that supremum with
-- the value at `softmax_point y`, and then apply
-- `negative_entropy_fenchel_objective_softmax_eq_log_sum_exp`.
/-- Proposition 4.16: the Fenchel conjugate of the negative entropy on the unit simplex is the
log-sum-exp function. -/
theorem negative_entropy_on_stdSimplex_conjugate_eq_log_sum_exp
    (y : Fin n → ℝ) :
    conjugate_function (negative_entropy_on_stdSimplex n)
        (dotProductEquiv ℝ (Fin n) y) =
      ((Real.log (∑ j, Real.exp (y j)) : ℝ) : EReal) := sorry

end

end
