import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open Asymptotics Filter

variable {r : ℕ → ℝ}

/- Definition 1.2.6 lies in the chapter's scalar geometric-convergence domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner file, plus direct recall of its canonical
  constructor and companion bridge theorems

Primary domain:
* geometric decay bounds for real-valued error sequences

Relevant owner-style declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Nesterov/Chap01/Definition_1_2_6.lean`, the chapter owner
  for the fixed-parameter geometric estimate `r k ≤ c * (1 - q)^k`;
* `HasGeometricRateOfConvergence.of_step_bound` in the same file, the canonical constructor from
  a one-step contraction estimate;
* `HasGeometricRateOfConvergence.isBigO`, the canonical asymptotic bridge to
  `r =O[atTop] (fun k ↦ (1 - q)^k)`;
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le`, the exact logarithmic
  threshold consequence attached to the owner estimate.

Source/core/bridge triage:
* source-facing: the existential textbook statement
  `∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c`;
* core/canonical: the chapter owner `HasGeometricRateOfConvergence`;
* bridge/view: the one-step constructor, the asymptotic `=O[atTop]` consequence, the convergence
  consequence, and the exact iteration-threshold consequence.

Primitive data:
* the sequence `r`;
* witnesses `q` and `c`;
* the owner bound `HasGeometricRateOfConvergence r q c`.

Derived API:
* the source-facing existential recall;
* the one-step contraction constructor;
* the asymptotic and convergence-to-zero bridges;
* the exact logarithmic iteration-threshold consequence.

This item file intentionally introduces no parallel local owner or alias. The numbered definition
is recalled directly, and the reusable API is taken from the chapter owner file. -/

/- Definition 1.2.6: a geometric rate of convergence is the direct existential textbook bound. -/
#check (∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c)

namespace HasGeometricRateOfConvergence

/- A one-step contraction estimate is recalled from the chapter owner file as the canonical
constructor for `HasGeometricRateOfConvergence`. -/
recall of_step_bound
    {r : ℕ → ℝ} {q c : ℝ}
    (hq₁ : q ≤ 1)
    (h0 : r 0 ≤ c)
    (hstep : ∀ k : ℕ, r (k + 1) ≤ (1 - q) * r k) :
    HasGeometricRateOfConvergence r q c

/- A nonnegative geometric-rate bound recalls the canonical asymptotic bridge to `=O[atTop]`. -/
recall isBigO
    {r : ℕ → ℝ} {q c : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hc : 0 ≤ c) :
    r =O[atTop] (fun k : ℕ ↦ (1 - q) ^ k)

/- Under the standard positivity range `0 < q < 1`, the owner estimate recalls the canonical
convergence-to-zero consequence. -/
recall tendsto_zero
    {r : ℕ → ℝ} {q c : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 ≤ c)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto r atTop (nhds 0)

/- The exact logarithmic stopping threshold is recalled directly from the chapter owner file. -/
recall le_target_of_iterationThreshold_le
    {r : ℕ → ℝ} {q c ε : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hq_contract : 1 < (1 - q)⁻¹) (hε : 0 < ε)
    {k : ℕ} (hk : iterationThreshold q c ε ≤ (k : ℝ)) :
    r k ≤ ε

end HasGeometricRateOfConvergence
