import Mathlib.Tactic.Recall
import Nesterov.Chap01.Algorithm_1_2_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Algorithm 1.2.10 lies in the Chapter 1 black-box optimization / information-set iteration
domain.

Layer targeted by this refinement:
* source-facing recall of the chapter owner `GeneralIterativeScheme`

Relevant owner-style declarations sampled before refining:
* `#check (Query → Answer)` in `Definition_1_2_2.lean`, the canonical owner for a fixed-problem
  oracle;
* `#check (Set State)` in `Definition_1_2_3.lean`, instantiated here by the informational-state
  stopping criterion `Set (Set (Query × Answer))`;
* `BlackBoxOptimizationProblemClass` in `Definition_1_2_4.lean`, the chapter owner packaging a
  problem model, oracle, and stopping criterion at the class level;
* `Nesterov.Chap01.Algorithm_1_2_10.GeneralIterativeScheme`, the existing chapter owner for the
  single-problem iterative method together with its recursive information-state API.

Owner abstraction:
* `GeneralIterativeScheme Query Answer`

Primitive data:
* `oracle : Query → Answer`
* `query : Set (Query × Answer) → Query`
* `shouldStop : Set (Set (Query × Answer))`
* `output : Set (Query × Answer) → Query`

Derived API:
* `informationState` and the coercion `scheme : ℕ → Set (Query × Answer)`
* `currentPoint`, `currentAnswer`, `currentSample`
* `informationState_zero`, `informationState_succ`
* `HaltsAt`, `outputAt`

Source/core/bridge triage:
* source-facing: the textbook general iterative scheme and its recursively generated
  informational sets;
* core/canonical: the chapter owner `GeneralIterativeScheme Query Answer`;
* bridge/view: the current-point, current-sample, halting, and output declarations derived from
  that owner.

The exact owner and its recursive derived API already exist in the chapter file, so this item
reuses them directly instead of keeping a parallel local structure and duplicate recursion/theorem
copy. -/

/- Algorithm 1.2.10: a general iterative scheme is the chapter owner
`GeneralIterativeScheme Query Answer`. -/
#check GeneralIterativeScheme Query Answer

section

variable (scheme : GeneralIterativeScheme Query Answer)

/- The fixed-problem oracle `𝒪` is the owner field `scheme.oracle`. -/
recall GeneralIterativeScheme.oracle
    (scheme : GeneralIterativeScheme Query Answer) : Query → Answer

/- The method rule choosing the next query point from the accumulated informational set is the
owner field `scheme.query`. -/
recall GeneralIterativeScheme.query
    (scheme : GeneralIterativeScheme Query Answer) :
    Set (Query × Answer) → Query

/- The stopping criterion `𝒯_ε` is the owner field `scheme.shouldStop`. -/
recall GeneralIterativeScheme.shouldStop
    (scheme : GeneralIterativeScheme Query Answer) :
    Set (Set (Query × Answer))

/- The output rule is the owner field `scheme.output`. -/
recall GeneralIterativeScheme.output
    (scheme : GeneralIterativeScheme Query Answer) :
    Set (Query × Answer) → Query

end

namespace GeneralIterativeScheme

/- The recursively generated informational sets are the owner-side definition
`scheme.informationState`. -/
recall GeneralIterativeScheme.informationState
    (scheme : GeneralIterativeScheme Query Answer) :
    ℕ → Set (Query × Answer)

/- A general iterative scheme is canonically usable as its trajectory of informational sets. -/
#check (inferInstance :
  CoeFun (GeneralIterativeScheme Query Answer) (fun _ ↦ ℕ → Set (Query × Answer)))

/- The current query point is the owner-side derived definition `scheme.currentPoint`. -/
recall GeneralIterativeScheme.currentPoint
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Query

/- The current oracle answer is the owner-side derived definition `scheme.currentAnswer`. -/
recall GeneralIterativeScheme.currentAnswer
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Answer

/- The current oracle sample is the owner-side derived definition `scheme.currentSample`. -/
recall GeneralIterativeScheme.currentSample
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Query × Answer

/- The initial informational set is the empty set. -/
recall GeneralIterativeScheme.informationState_zero
    (scheme : GeneralIterativeScheme Query Answer) :
    scheme 0 = ∅

/- The next informational set is obtained by adjoining the current oracle sample. -/
recall GeneralIterativeScheme.informationState_succ
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) :
    scheme (k + 1) = insert (scheme.currentSample k) (scheme k)

/- Halting at iteration `k` is the owner-side predicate `scheme.HaltsAt k`. -/
recall GeneralIterativeScheme.HaltsAt
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Prop

/- The output produced at iteration `k` is the owner-side definition `scheme.outputAt k`. -/
recall GeneralIterativeScheme.outputAt
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Query

end GeneralIterativeScheme
