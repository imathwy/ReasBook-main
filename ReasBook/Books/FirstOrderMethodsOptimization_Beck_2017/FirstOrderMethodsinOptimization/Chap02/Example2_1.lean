import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u}

/- Example 2.1 uses the chapter's source-facing indicator-function owner
`extendedIndicator`. -/
recall extendedIndicator

/- The finite-value locus in this example is the canonical owner `effective_domain` from
Definition 2.1, reused by Definition 2.5. -/
recall effective_domain

/- The real-epigraph owner for extended-real-valued functions is the chapter declaration
`realEpigraph`. -/
recall realEpigraph

-- Proof sketch: use extensionality on sets, unfold `effective_domain` and `extendedIndicator`,
-- and split on whether the point lies in `C`.
/-- Example2.1: The effective domain of the indicator function `δ_C` is exactly the set `C`. -/
theorem effective_domain_indicatorFunction (C : Set E) :
    effective_domain (extendedIndicator C) = C := sorry

-- Proof sketch: unfold the displayed real-epigraph set and `effective_domain`; if `f x ≤ y` with
-- `y : ℝ`, then
-- `(y : EReal) < ⊤`, so transitivity gives `f x < ⊤`.
/-- A point in the real epigraph projects to a point in the effective domain. -/
theorem mem_effective_domain_of_mem_real_epigraph {f : E → EReal} {x : E} {y : ℝ}
    (h : (x, y) ∈ realEpigraph f) : x ∈ effective_domain f := sorry

/- Proper extended-real-valued functions are already owned upstream in Definition 2.5. -/
recall IsProperExtendedRealFunction
