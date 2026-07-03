import Nesterov.Chap03.Algorithm_3_9
import Nesterov.Chap03.Definition_3_66

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin (n - 1))
local notation "Z" => ℝ × X

open scoped ConstrainedArgmin

/- Theorem 3.56 lies in the chapter's Kelley cutting-plane lower-bound domain.

Relevant owner-style declarations sampled before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the owner of a feasible set
  together with a real-valued objective;
- `kelleyCompleteObjective` and `kelleyCompleteFeasibleSet` in `Proposition_3_48`, the
  source-facing objective and feasible set of the complete-data hard instance;
- `kelleyCompleteProblem` and `kelleyCompleteProblem_argmin_eq_singleton_origin` in
  `Definition_3_66`, the chapter owner and its canonical argmin description for the complete-data
  hard instance;
- `KelleyMethod` and `KelleyMethod.iterates_mem` in `Algorithm_3_9`, the chapter owner for a
  Kelley execution on a constrained problem;
- `nonsmoothModel` in `Lemma_3_3_2`, the canonical Kelley-model owner reused by `KelleyMethod`.

Best owner abstraction:
- source-facing: a complete-data iterate sequence `z : ℕ → ℝ × ℝ^(n - 1)` together with the
  objective-gap and oracle-call lower bounds on the explicit feasible set `Q`;
- core/canonical: `kelleyCompleteObjective`, `kelleyCompleteFeasibleSet`,
  `kelleyCompleteProblem (n - 1)`, and the constrained argmin owner
  `argmin[problem.feasibleSet] problem`;
- bridge/view: a Kelley-method witness on `kelleyCompleteProblemL2 (n - 1)` transported back to
  the source-facing product by `WithLp.equiv 2 Z`.

Primitive data:
- the explicit complete-data objective and feasible set;
- the packaged complete-data constrained problem from `Definition_3_66`;
- an auxiliary Kelley method on the transported `WithLp` problem.

Derived API:
- feasible optimality of the origin;
- the geometric objective-gap lower bound along a Kelley execution;
- the induced oracle-call lower bound.

The Kelley-method owner API lives on the `WithLp` transport from `Definition_3_66`, but the
source-facing theorem statement is about iterates `(y, x) ∈ Q` in the explicit complete-data model
`ℝ × ℝ^(n - 1)`. Accordingly, the theorem below exposes the iterate sequence directly on that
product and keeps the `WithLp` Kelley method only as an auxiliary existence witness.
-/

/-- Theorem 3.56 (1): in the complete-data Kelley example on `ℝ × ℝ^(n - 1)`, the origin belongs
to the canonical argmin set of the packaged constrained problem. -/
-- Proof sketch: `Definition_3_66` already packages the complete-data instance as
-- `kelleyCompleteProblem`, and its canonical argmin set is the singleton `{0}`.
theorem origin_mem_kelleyCompleteProblem_argmin :
    (0 : Z) ∈
      (argmin[(kelleyCompleteProblem (n - 1)).feasibleSet] (kelleyCompleteProblem (n - 1)) :
        Set Z) := by
  rw [kelleyCompleteProblem_argmin_eq_singleton_origin (n - 1)]
  simp

/-- Theorem 3.56 (2): for the complete-data Kelley example in `ℝ × ℝ^(n - 1)` with `n ≥ 1`,
there exists a source-facing complete-data iterate sequence in the feasible set `Q` whose
objective gaps and oracle-call complexity satisfy the displayed lower bounds; this sequence is
realized by transporting a Kelley method on the canonical `WithLp` bridge problem back to
`ℝ × ℝ^(n - 1)`. -/
-- Proof sketch: Proposition 3.48 gives optimality of the origin for the explicit objective on
-- the unit ball. The lower-bound execution comes from the hard Kelley-cutting-plane construction
-- for this instance, which yields the geometric estimate on `f(z_k)`. Combining that estimate
-- with an `ε`-accuracy hypothesis, taking logarithms, and using the textbook comparison
-- `log t ≤ t - 1` produces the oracle-call lower bound.
theorem exists_kelleyCompleteFirstOrderExecution_with_gap_and_call_lower_bounds
    (hn : 1 ≤ n) :
    ∃ z : ℕ → Z,
      (∀ k : ℕ,
        z k ∈ kelleyCompleteFeasibleSet ∧
        kelleyCompleteObjective (z k) ≥
          ((1 / 4 : ℝ) ^ k) * ((Real.sqrt 3 / 2) ^ (n - 1))) ∧
      (∀ (ε : Set.Ioo (0 : ℝ) 1) (k : ℕ),
        kelleyCompleteObjective (z k) ≤ ε →
          (1 / (2 * Real.log 2)) * ((2 / Real.sqrt 3) ^ (n - 1)) * Real.log (1 / (ε : ℝ)) ≤
            (k : ℝ)) ∧
      ∃ method : KelleyMethod (kelleyCompleteProblemL2 (n - 1)),
        ∀ k : ℕ, z k = (WithLp.equiv 2 Z) (method k) := by
  sorry
