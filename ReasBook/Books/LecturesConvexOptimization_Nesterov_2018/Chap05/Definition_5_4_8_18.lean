import Mathlib
import Nesterov.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanOrthant

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-
Definition 5.4.8.18 lies in the Chapter 5 geometric-programming / positive-orthant
logarithmic-coordinate domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the project owner for the
  strict positive orthant `ℝⁿ₊₊`;
* `EuclideanSpace.mem_positiveOrthant_iff` from `Chap01/Definition_1_10_2`, the coordinatewise
  membership bridge for that owner;
* `relativeDirection` and `relativeDirection_apply` from `Definition_5_4_7_14`, the nearby
  Chapter 5 precedent for using `positiveOrthant n` as the owner carrier and `WithLp.toLp` as the
  canonical ambient vector constructor;
* `standardLogarithmicBarrier_apply` from `Definition_5_4_3_2`, the canonical coordinatewise
  logarithmic formula already attached upstream to the same strict-orthant owner.

Best owner abstraction:
* source-facing: `logarithmicSubstitution`, the coordinatewise logarithm on `ℝⁿ₊₊`;
* core/canonical: the Chapter 1 strict-orthant owner `positiveOrthant n` together with
  `WithLp.toLp` for ambient `EuclideanSpace` vectors;
* bridge/view: the coordinate evaluation lemma and its exponential restatement.

Primitive data:
* a point `x : ℝ₊₊^n`.

Derived API:
* the owner map `logarithmicSubstitution`;
* the coordinate formula `logarithmicSubstitution_apply`;
* the exponential inverse relation `logarithmicSubstitution_spec`.

The previous version duplicated the strict-orthant owner with a local subtype alias. This
refinement reuses the Chapter 1 owner directly, uses the existing orthant notation on the theorem
surface, and keeps only the actual source-facing map together with its derived coordinate lemmas.
-/

/-- Definition 5.4.8.18: the logarithmic substitution sends a strictly positive vector
`x ∈ \mathbb{R}^n_{++}` to the vector `y ∈ \mathbb{R}^n` with coordinates
`y^(k) = log x^(k)`. -/
def logarithmicSubstitution (x : ℝ₊₊^n) : Eₙ :=
  WithLp.toLp 2 fun k ↦ Real.log ((x : Eₙ) k)

/-- The logarithmic substitution is the coordinatewise real logarithm. -/
@[simp] theorem logarithmicSubstitution_apply (x : ℝ₊₊^n) (k : Fin n) :
    logarithmicSubstitution x k = Real.log ((x : Eₙ) k) :=
  rfl

/-- Exponentiating the logarithmic substitution recovers the original strictly positive
coordinate. -/
-- Proof sketch: use `logarithmicSubstitution_apply` and then apply `Real.exp_log` to the
-- positive coordinate `x k`, whose positivity is part of the subtype data.
theorem logarithmicSubstitution_spec (x : ℝ₊₊^n) (k : Fin n) :
    (x : Eₙ) k = Real.exp (logarithmicSubstitution x k) := by
  rw [logarithmicSubstitution_apply, Real.exp_log]
  simpa using x.2 k

end
