import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 5.1.3 lives in the scalar self-concordance domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith`, the chapter owner for self-concordance with constant `Mf`;
* `IsStandardSelfConcordantOn`, the canonical chapter owner for the case `Mf = 1`;
* `IsSelfConcordantBarrierOnWith`, the later barrier refinement extending the standard owner;
* `Real.deriv_log`, the mathlib scalar logarithm derivative owner used in proofs.

Best owner abstraction:
* source-facing: the logarithmic barrier on `(0, ∞)`;
* core/canonical: `IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ))`;
* bridge/view: `IsSelfConcordantBarrierOnWith`, which adds the barrier parameter inequality.

The scalar derivative identities for `x ↦ -log x` are proof-level derived API here, not the
mathematical owner of the example, so the file keeps only the canonical self-concordance
statement. -/

-- Proof sketch: verify the standard self-concordance conditions for `x ↦ -Real.log x` on
-- `(0, ∞)` using the canonical scalar logarithm derivative identities.
/-- Example 5.1.3: the univariate logarithmic barrier `x ↦ -log x` on `(0, ∞)` is standard
self-concordant. -/
instance negLog_isStandardSelfConcordantOn :
    IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := sorry
