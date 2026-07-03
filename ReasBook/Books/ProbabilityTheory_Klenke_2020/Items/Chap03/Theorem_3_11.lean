import Mathlib
import AchimKlenkeLean.Items.Chap03.Theorem_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology

/-- The `n`th Galton--Watson extinction approximation, obtained by iterating the offspring
probability generating function from `0`. -/
noncomputable abbrev galtonWatsonExtinctionApproximation (p : PMF ℕ) (n : ℕ) : ℝ :=
  Nat.iterate (probabilityGeneratingFunctionReal p) n 0

-- Proof sketch: unfold the zeroth iterate of a function.
/-- The zeroth extinction approximation is `0`. -/
theorem galtonWatsonExtinctionApproximation_zero (p : PMF ℕ) :
    galtonWatsonExtinctionApproximation p 0 = 0 := sorry

-- Proof sketch: use the defining recursion of `Nat.iterate` to rewrite the `(n + 1)`st iterate as
-- one further application of the probability generating function to the `n`th iterate.
/-- The extinction approximations satisfy the Galton--Watson recursion `q_(n+1) = ψ(q_n)`. -/
theorem galtonWatsonExtinctionApproximation_succ (p : PMF ℕ) (n : ℕ) :
    galtonWatsonExtinctionApproximation p (n + 1) =
      probabilityGeneratingFunctionReal p (galtonWatsonExtinctionApproximation p n) := sorry

/-- The Galton--Watson extinction probability, defined as the supremum of the extinction
approximations. -/
noncomputable abbrev galtonWatsonExtinctionProbability (p : PMF ℕ) : ℝ :=
  sSup (Set.range (galtonWatsonExtinctionApproximation p))

-- Proof sketch: this is immediate from the definition of
-- `galtonWatsonExtinctionProbability`.
/-- The extinction probability is the supremum of the iterated extinction approximations. -/
theorem galtonWatsonExtinctionProbability_def (p : PMF ℕ) :
    galtonWatsonExtinctionProbability p =
      sSup (Set.range (galtonWatsonExtinctionApproximation p)) := sorry

/-- The fixed points of the offspring probability generating function inside the unit interval. -/
noncomputable abbrev galtonWatsonFixedPoints (p : PMF ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩ Function.fixedPoints (probabilityGeneratingFunctionReal p)

-- Proof sketch: unfold `galtonWatsonFixedPoints` and `Function.fixedPoints`; membership is exactly
-- the conjunction of belonging to `[0,1]` and satisfying `ψ(r) = r`.
/-- A point belongs to `galtonWatsonFixedPoints p` exactly when it lies in `[0,1]` and is a fixed
point of the offspring probability generating function. -/
theorem mem_galtonWatsonFixedPoints_iff (p : PMF ℕ) (r : ℝ) :
    r ∈ galtonWatsonFixedPoints p ↔
      r ∈ Set.Icc (0 : ℝ) 1 ∧ probabilityGeneratingFunctionReal p r = r := sorry

/-- The expected offspring number of the Galton--Watson law `p`, written as the extended real
series `∑ k p_k`. -/
noncomputable abbrev galtonWatsonOffspringMean (p : PMF ℕ) : ENNReal :=
  ∑' k : ℕ, (k : ENNReal) * p k

-- Proof sketch: unfold `galtonWatsonOffspringMean`.
/-- The offspring mean is the `ENNReal` series `∑' k, k * p k`. -/
theorem galtonWatsonOffspringMean_eq_tsum (p : PMF ℕ) :
    galtonWatsonOffspringMean p = ∑' k : ℕ, (k : ENNReal) * p k := sorry

/-- The left derivative limit of the offspring probability generating function exists and is
strictly larger than `1`. -/
def probabilityGeneratingFunctionDerivativeLeftLimitGtOne (p : PMF ℕ) : Prop :=
  ∃ l : ENNReal,
    Filter.Tendsto
      (fun z : ℝ ↦ ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z))
      (𝓝[<] (1 : ℝ)) (𝓝 l) ∧ 1 < l

-- Proof sketch: unfold
-- `probabilityGeneratingFunctionDerivativeLeftLimitGtOne`.
/-- The derivative-left-limit condition is the existence of a left limit for `ψ'` at `1` that is
strictly greater than `1`. -/
theorem probabilityGeneratingFunctionDerivativeLeftLimitGtOne_iff (p : PMF ℕ) :
    probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
      ∃ l : ENNReal,
        Filter.Tendsto
          (fun z : ℝ ↦ ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z))
          (𝓝[<] (1 : ℝ)) (𝓝 l) ∧ 1 < l := sorry

-- Proof sketch: use strict convexity of the offspring generating function under `p 1 ≠ 1`,
-- identify `q` as the minimal fixed point obtained from the Galton--Watson extinction
-- approximations, and then show that the only fixed points in `[0,1]` are `q` and `1`.
/-- The fixed points of the Galton--Watson offspring generating function in `[0,1]` are exactly the
extinction probability and `1`. -/
theorem galtonWatson_fixedPoints_eq_extinctionProbability_or_one (p : PMF ℕ) (hp1 : p 1 ≠ 1) :
    galtonWatsonFixedPoints p = ({galtonWatsonExtinctionProbability p, (1 : ℝ)} : Set ℝ) := sorry

-- Proof sketch: combine the strict-convexity fixed-point picture near `1` with the existence and
-- identification of the left limit of `ψ'` at `1`, then rewrite that limit as the offspring mean
-- using the first-derivative case of the pgf derivative formula.
/-- The extinction probability is strictly less than `1` exactly when the left limit of `ψ'` at
`1` is greater than `1`, equivalently when the offspring mean exceeds `1`. -/
theorem galtonWatson_extinctionProbability_lt_one_iff_derivativeLeftLimit_gt_one_iff_offspringMean_gt_one
    (p : PMF ℕ) (hp1 : p 1 ≠ 1) :
    (galtonWatsonExtinctionProbability p < 1 ↔
      (probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
        1 < galtonWatsonOffspringMean p)) := sorry

-- Proof sketch: combine the atomic fixed-point statement with the two supercriticality
-- equivalences.
/-- Theorem 3.11: If `p 1 ≠ 1`, then the fixed points of the offspring generating function on
`[0,1]` are exactly the extinction probability `q` and `1`, and the conditions `q < 1`,
`lim_{z \uparrow 1} ψ'(z) > 1`, and `∑ k, k p_k > 1` are equivalent. -/
theorem galtonWatson_extinctionProbability_fixedPoints_and_supercriticality
    (p : PMF ℕ) (hp1 : p 1 ≠ 1) :
    galtonWatsonFixedPoints p = ({galtonWatsonExtinctionProbability p, (1 : ℝ)} : Set ℝ) ∧
      (galtonWatsonExtinctionProbability p < 1 ↔
        probabilityGeneratingFunctionDerivativeLeftLimitGtOne p) ∧
      (probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
        1 < galtonWatsonOffspringMean p) := sorry
