import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_2_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/- Definition 1.2.4 lies in the Chapter 1 black-box optimization problem-class domain.

Relevant owner-style declarations sampled before refining:
* `#check (Type u)` in `Definition_1_2_1.lean`, the canonical owner of the model `Σ`;
* `#check (Query → Answer)` in `Definition_1_2_2.lean`, the canonical owner of a fixed-problem
  oracle;
* `#check (Set State)` in `Definition_1_2_3.lean`, the canonical owner of the stopping criterion
  `𝒯_ε`;
* `BlackBoxOptimizationProblemClass` in `Nesterov/Chap01/Definition_1_2_4.lean`, which already
  packages exactly the source-facing triple from those primitive owners.

Best owner abstraction:
* `BlackBoxOptimizationProblemClass Query Answer State`

Primitive data:
* `model`
* `oracle`
* `stoppingCriterion`

Derived API:
* fixed-problem oracle evaluation `problemClass.oracle σ : Query → Answer`
* no separate function-view wrapper: downstream usage stays on the owner field `problemClass.oracle`

Source/core/bridge triage:
* source-facing: the textbook triple `𝒫 ≡ (Σ, 𝒪, 𝒯_ε)`;
* core/canonical: the chapter owner `BlackBoxOptimizationProblemClass Query Answer State`;
* bridge/view: the primitive projections `model`, `oracle`, and `stoppingCriterion`.

The exact source-facing owner already exists in the chapter file, so this item is refined to a
recall-only surface instead of reintroducing a parallel local structure and duplicate coercion
API. -/

/- Definition 1.2.4: a black-box optimization problem class is the chapter owner
`BlackBoxOptimizationProblemClass Query Answer State`. -/
recall BlackBoxOptimizationProblemClass
    (Query : Type v) (Answer : Type w) (State : Type x) :
    Type (max (max (max (u + 1) v) w) x)

section

variable {Query : Type v} {Answer : Type w} {State : Type x}

/- The problem model `Σ` is the owner field `problemClass.model`. -/
recall BlackBoxOptimizationProblemClass.model
    (problemClass : BlackBoxOptimizationProblemClass Query Answer State) : Type u

/- The class oracle `𝒪` is the owner field `problemClass.oracle`. -/
recall BlackBoxOptimizationProblemClass.oracle
    (problemClass : BlackBoxOptimizationProblemClass Query Answer State) :
    problemClass.model → Query → Answer

/- The stopping criterion `𝒯_ε` is the owner field `problemClass.stoppingCriterion`. -/
recall BlackBoxOptimizationProblemClass.stoppingCriterion
    (problemClass : BlackBoxOptimizationProblemClass Query Answer State) : Set State

end
