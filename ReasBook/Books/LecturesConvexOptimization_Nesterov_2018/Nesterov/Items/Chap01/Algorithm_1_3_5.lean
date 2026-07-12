import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Algorithm_1_3_5

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Algorithm 1.3.5 lies in the box-constrained deterministic value-oracle midpoint-grid domain.

Relevant owner-style declarations sampled before refining:
* `uniformGridMethod` in `Nesterov/Chap01/Algorithm_1_3_5.lean`, the chapter owner of the
  textbook midpoint-grid method;
* `uniformGridMethod_output_isMinOn` in the same file, the owner theorem giving the sampled
  minimizer property after exactly `p^n` calls;
* `DeterministicValueOracleMethod.oracleTranscript` in `Theorem_1_3_9.lean`, the canonical
  ordered sampled-value history used by the owner method;
* `uniformGrid` in `Theorem_1_3_6.lean`, the source-facing midpoint grid on which the minimizer
  statement lives.

Best owner abstraction:
* source-facing: `uniformGridMethod n p`;
* core/canonical: `DeterministicValueOracleMethod (zeroOneBox n)`;
* bridge/view: the owner theorem evaluated on the transcript after `p^n` oracle calls.

Primitive data:
* the mesh parameter `p : ℕ+`;
* the chapter owner `uniformGridMethod n p`.

Derived API:
* the transcript-based output after `p^n` calls;
* the minimizing property of that output on `uniformGrid n p`.

Source/core/bridge triage:
* source-facing: the textbook midpoint-grid search method `𝒢(p)`;
* core/canonical: `uniformGridMethod n p : DeterministicValueOracleMethod (zeroOneBox n)`;
* bridge/view: `uniformGridMethod_output_isMinOn`.

This item is therefore recall-only: the chapter already owns both the algorithm and its canonical
minimizer theorem, so the duplicate `uniformGridPointInBox` / `uniformGridSearchOutput` layer is
removed instead of being kept as a parallel public API. -/

/- Algorithm 1.3.5: the textbook midpoint-grid method `𝒢(p)` is the chapter owner
`uniformGridMethod n p`. -/
recall uniformGridMethod (n : ℕ) (p : ℕ+) :
    DeterministicValueOracleMethod (zeroOneBox n)

/- After exactly `p^n` value-oracle calls, the owner method returns a minimizer of the objective
on the midpoint grid `uniformGrid n p`. -/
recall uniformGridMethod_output_isMinOn (p : ℕ+) (f : E → ℝ) :
    IsMinOn f (uniformGrid n p)
      ((uniformGridMethod n p).output
        ((uniformGridMethod n p).oracleTranscript
          (f ∘ ((↑) : zeroOneBox n → E)) ((p : ℕ) ^ n)))

end
