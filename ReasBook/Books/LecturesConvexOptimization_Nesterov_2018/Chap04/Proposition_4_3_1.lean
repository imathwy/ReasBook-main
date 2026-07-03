import Nesterov.Chap01.Definition_1_3_3
import Nesterov.Chap04.Definition_4_2_11
import Nesterov.Chap04.Definition_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConstrainedArgmin

variable {n k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.3.1 lies in the Chapter 4 cubic hard-instance / degree-3 uniform-convexity
domain on Euclidean spaces.

Sampled owner-style declarations:
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the chapter owner
  for feasible minimizer sets;
* `uniformConvexPowerModulus` in `Definition_4_2_8`, the chapter owner for the degree-`p` power
  modulus used on theorem surfaces;
* `HasUniformConvexityParameterOfDegree` in `Definition_4_2_11`, whose primitive witness data is
  a positive constant `σ` with `UniformConvexOn Set.univ (uniformConvexPowerModulus σ p) f`;
* `lower_bound_at_minimizer_of_uniformConvexOn` in `Theorem_4_2_1`, the chapter owner theorem
  built from `argmin[Q]` and `UniformConvexOn`;
* mathlib `UniformConvexOn.strictConvexOn`, the canonical bridge from a positive modulus witness
  to strict convexity.

Best owner abstraction:
* source-facing: the cubic hard-instance objective `fk hkn`, its explicit minimizer `x_*`, its
  optimal value, and the radius estimate;
* core/canonical: a positive degree-`3` witness
  `∃ σ > 0, UniformConvexOn Set.univ (uniformConvexPowerModulus σ (3 : ℝ)) (fk hkn)` together
  with the minimizer owner `argmin[Set.univ] (fk hkn)`;
* bridge/view: the singleton-argmin consequence for the explicit minimizer, plus the coordinate
  and norm-expansion lemmas below.

Primitive data:
* the hard-instance objective `fk hkn`;
* the explicit vector `cubicLowerBoundMinimizer n k`.

Derived API:
* the coordinate formula for the explicit minimizer;
* degree-`3` whole-space uniform convexity of `fk hkn`;
* uniqueness of the explicit global minimizer through the canonical owner
  `argmin[Set.univ] (fk hkn)`;
* the value and distance formulas at that minimizer.

The file therefore keeps the explicit minimizer as the source-facing owner for the hard instance,
but uses the chapter's canonical degree-`3` `UniformConvexOn` and `argmin[Set.univ]` surfaces
instead of a raw existential modulus function `∃ φ : ℝ → ℝ, ...` or a bespoke uniqueness package.
-/

/-- The explicit vector `x_*` with coordinates `x_*^(i) = (k - i + 1)_+`. -/
def cubicLowerBoundMinimizer (n k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i : Fin n ↦ ((k - (i : ℕ) : ℕ) : ℝ)

-- Proof sketch: unfold `cubicLowerBoundMinimizer`; on the `i`-th zero-based coordinate the value
-- is the truncated natural difference `k - i`, which is exactly `(k - i + 1)_+` in textbook
-- one-based indexing.
/-- The coordinates of the explicit minimizer are `x_*^(i) = (k - i + 1)_+`. -/
theorem cubicLowerBoundMinimizer_apply (i : Fin n) :
    cubicLowerBoundMinimizer n k i = ((k - (i : ℕ) : ℕ) : ℝ) := by
  simp [cubicLowerBoundMinimizer]

-- Proof sketch: the cubic sum of adjacent differences and tail coordinates in `fk hkn`
-- yields a modulus witnessing uniform convexity.
/-- Proposition 4.3.1 (1): the hard-instance objective `fk hkn` from
Definition 4.3.2 is uniformly convex. -/
theorem cubicLowerBoundObjective_uniformlyConvex
    (hkn : k ≤ n) :
    ∃ σ > 0,
      UniformConvexOn Set.univ
        (uniformConvexPowerModulus σ (3 : ℝ))
        (fk hkn) := sorry

-- Proof sketch: strict convexity follows from the positive modulus in
-- `cubicLowerBoundObjective_uniformlyConvex`, and a strictly convex function has at most one
-- global minimizer. The explicit vector `cubicLowerBoundMinimizer n k` is then identified as the
-- unique point of the canonical owner `argmin[Set.univ] (fk hkn)` by checking the optimality
-- conditions.
/-- Proposition 4.3.1 (2): the canonical minimizer set of the cubic hard-instance objective is the
singleton containing the explicit vector `x_*^(i) = (k - i + 1)_+`. -/
theorem cubicLowerBoundObjective_argmin_eq_singleton
    (hkn : k ≤ n) :
    argmin[Set.univ] (fk hkn) = {cubicLowerBoundMinimizer n k} := sorry

-- Proof sketch: substitute the explicit coordinates of `cubicLowerBoundMinimizer` into the
-- defining formula of `fk hkn`; each adjacent difference contributes `1`,
-- the tail contributes the final `1`, and the linear term contributes `-k`.
/-- Evaluating the cubic hard instance at the explicit minimizer gives the optimal value
`f_k(x_*) = -(2 / 3) k`. -/
theorem cubicLowerBoundObjective_value_at_minimizer (hkn : k ≤ n) :
    fk hkn (cubicLowerBoundMinimizer n k) =
      -((2 : ℝ) / 3) * k := sorry

-- Proof sketch: the zero initialization leaves only the coordinates of `x_*`; summing their
-- squares gives `∑_{i=1}^k i^2` after reindexing from textbook one-based coordinates to `Fin n`,
-- using `k ≤ n` so the nonzero coordinates of `x_*` all lie in the ambient space.
/-- The squared Euclidean distance from the zero vector to the explicit minimizer is
`∑_{i=1}^k i^2` under the hard-instance range hypothesis `k ≤ n`. -/
theorem cubicLowerBoundMinimizer_sqDist_eq_sumSquares
    (hkn : k ≤ n) :
    ‖(0 : E) - cubicLowerBoundMinimizer n k‖ ^ (2 : ℕ) =
      ∑ i ∈ Finset.Icc 1 k, (i : ℝ) ^ (2 : ℕ) := sorry

-- Proof sketch: compare the sum of squares with the integral of `x^2` on `[0, k + 1]`, or use
-- the closed formula `k (k + 1) (2 k + 1) / 6`.
/-- The squared Euclidean distance from the zero vector to the explicit minimizer is strictly less
than `(k + 1)^3 / 3` under the hard-instance range hypothesis `k ≤ n`. -/
theorem cubicLowerBoundMinimizer_sqDist_lt
    (hkn : k ≤ n) :
    ‖(0 : E) - cubicLowerBoundMinimizer n k‖ ^ (2 : ℕ) <
      (((k + 1 : ℕ) : ℝ) ^ (3 : ℕ)) / 3 := sorry
