import Mathlib
import Nesterov.Chap05.Definition_5_4_9_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Theorem 5.4.9.1 lies in the chapter's ellipsoid-method arithmetic-complexity domain.

Sampled owner declarations before refining:
* `HasEllipsoidMethodComplexityBounds` in `Definition_5_4_9_2`, the source-facing Chapter 5
  owner on the primitive iteration-count and per-iteration cost data;
* `HasLpBarrierShortStepTotalArithmeticComplexityBound` in `Theorem_5_4_9_3`, the nearby Chapter
  5 owner for a direct total arithmetic-complexity bound on primitive arithmetic-work data;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the project
  pattern where the public complexity notion is a `Prop` on primitive data, with explicit bridge
  lemmas unpacking it.

Best owner abstraction:
* source-facing: the total arithmetic complexity of the ellipsoid method induced by the primitive
  iteration-count model and the two per-iteration cost functions;
* core/canonical: a direct `Prop`-valued owner expressing the final `O(n^3 (m + n) log (1 / ε))`
  bound on those primitive data;
* bridge/view: the theorem below deriving that total-complexity owner from the primitive bounds in
  `HasEllipsoidMethodComplexityBounds`.

Primitive data:
* the accuracy-indexed iteration count `N_it`;
* the oracle arithmetic cost per iteration;
* the additional per-iteration arithmetic overhead.

Derived API:
* the source-facing total arithmetic-complexity owner below;
* its explicit existential-constant unpacking lemma;
* the theorem deriving that owner from Definition 5.4.9.2.

Source/core/bridge triage:
* source-facing: `HasEllipsoidMethodTotalArithmeticComplexityBound`;
* core/canonical: the primitive complexity-model owner `HasEllipsoidMethodComplexityBounds`;
* bridge/view: `ellipsoidMethodTotalArithmeticComplexity_bound`.

The earlier version stated the final total-complexity estimate directly as a one-off existential
theorem. The surrounding chapter instead organizes complexity statements around `Prop`-valued
owners on primitive data. This refinement therefore keeps Definition 5.4.9.2 as the primitive
owner, introduces the direct source-facing total-complexity owner in this theorem file, and
rewrites the theorem as the canonical bridge from the primitive model to that owner. -/

/-- Theorem 5.4.9.1's source-facing total arithmetic-complexity owner for the ellipsoid method.
It records the textbook bound saying that the total arithmetic work induced by the primitive
iteration-count, oracle-cost, and extra-cost data is `O(n^3 (m + n) log (1 / ε))` with a
constant independent of the target accuracy `ε ∈ (0, 1)`. -/
def HasEllipsoidMethodTotalArithmeticComplexityBound
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ) : Prop :=
  ∃ C : ℝ,
    0 < C ∧
      ∀ {ε : ℝ} {m n : ℕ},
        ε ∈ Set.Ioo (0 : ℝ) 1 →
        0 < m →
        0 < n →
        (iterationCount ε n * (oracleCostPerIteration m n + extraCostPerIteration n) : ℝ) ≤
          C * (n : ℝ) ^ 3 * ((m : ℝ) + (n : ℝ)) * Real.log (1 / ε)

-- Proof sketch: unfold `HasEllipsoidMethodTotalArithmeticComplexityBound`; this is exactly the
-- explicit constant-factor form of the textbook total arithmetic estimate on the primitive
-- iteration-count and per-iteration arithmetic-work data.
/-- Unfolding `HasEllipsoidMethodTotalArithmeticComplexityBound` recovers the explicit
constant-factor form of the textbook ellipsoid-method total arithmetic bound. -/
theorem hasEllipsoidMethodTotalArithmeticComplexityBound_iff
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ) :
    HasEllipsoidMethodTotalArithmeticComplexityBound
        iterationCount oracleCostPerIteration extraCostPerIteration ↔
      ∃ C : ℝ,
        0 < C ∧
          ∀ {ε : ℝ} {m n : ℕ},
            ε ∈ Set.Ioo (0 : ℝ) 1 →
            0 < m →
            0 < n →
            (iterationCount ε n * (oracleCostPerIteration m n + extraCostPerIteration n) : ℝ) ≤
              C * (n : ℝ) ^ 3 * ((m : ℝ) + (n : ℝ)) * Real.log (1 / ε) := by
  rfl

-- Proof sketch: unpack the constants from `HasEllipsoidMethodComplexityBounds`, combine the
-- bounds `N_it = O(n^2 log (1 / ε))`, `C_oracle = O(m n)`, and `C_iter = O(n^2)` to obtain the
-- per-iteration estimate `O(m n + n^2) = O(n (m + n))`, and then multiply by the iteration-count
-- bound. The resulting total-complexity constant is still uniform in `ε ∈ (0, 1)`.
/-- Theorem 5.4.9.1: under the textbook iteration-count, oracle-cost, and per-iteration overhead
bounds from Definition 5.4.9.2, the total arithmetic complexity of the ellipsoid method satisfies
the source-facing owner `HasEllipsoidMethodTotalArithmeticComplexityBound`. -/
theorem ellipsoidMethodTotalArithmeticComplexity_bound
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ)
    (hmodel :
      HasEllipsoidMethodComplexityBounds
        iterationCount oracleCostPerIteration extraCostPerIteration) :
    HasEllipsoidMethodTotalArithmeticComplexityBound
      iterationCount oracleCostPerIteration extraCostPerIteration := sorry
