import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

open scoped Rockafellar

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.3 is Rockafellar's Kuhn--Tucker existence theorem for an ordinary
  convex program under the qualification that the nonaffine inequality constraints are satisfied
  strictly at some feasible point.
- `core/canonical`: the Chapter 6 owners already present are `P.feasibleSet`,
  `P.optimalValue`, and `P.IsKuhnTuckerVector`.
- `bridge/view`: the source set `I` of indices of nonaffine inequality constraints is expressed
  intrinsically by `¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet)`, while the source
  phrase “there is a feasible solution strict in `i ∈ I`” is packaged as a single qualification
  predicate on `P`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `affOn[𝕜](·, ·)` (on `extendZero` realizations) from
  `Definition_6_28_1`;
- `P.feasibleSet`, `P.optimalValue`, and `P.IsKuhnTuckerVector` from `Definition_6_28_3`;
- intrinsic constrained-data evaluation `P.inequality i x` for `x : P.constraintSet`.

Primitive data vs derived API:
- primitive source data: the existing program owner `P`;
- source-facing qualification: existence of a feasible point where every nonaffine inequality
  constraint is strict;
- derived theorem: existence of multiplier blocks `(lam, μ)` forming a Kuhn--Tucker vector.

Layer target: `source-facing`. The theorem is stated directly on the existing program and
Kuhn--Tucker owners, with the source qualification isolated as one reusable predicate rather than
as an existential package or surrogate program wrapper.
-/

variable {r s : ℕ}
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- A feasible point of `P` is strictly feasible on the nonaffine inequalities if every
inequality constraint that is not affine on `P.constraintSet` is satisfied strictly there. The
owner is stated on the canonical feasible-set layer of `P`. -/
def HasStrictlyFeasiblePointOnNonaffineInequalities : Prop :=
  ∃ x : P.feasibleSet,
    ∀ i, ¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet) →
      extendZero (P.inequality i) x.1 < 0

-- Proof sketch: this is the definitional expansion of
-- `HasStrictlyFeasiblePointOnNonaffineInequalities` at the canonical feasible-set owner layer.
/-- The nonaffine strict-feasibility qualification is exactly the existence of a feasible point
whose nonaffine inequalities are strict. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_iff_exists_feasiblePoint :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities ↔
      ∃ x : P.feasibleSet,
        ∀ i, ¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet) →
          extendZero (P.inequality i) x.1 < 0 :=
  Iff.rfl

-- Proof sketch: expand feasibility through the intrinsic split owner
-- `P.mem_feasibleSet`, then use `extendZero_apply` only as a bridge for the strict-inequality
-- clause stated in ambient form.
/-- Bridge form of nonaffine strict feasibility: this recovers the fully expanded constrained-data
surface with weak feasibility plus strictness on nonaffine inequalities. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_iff :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities ↔
      ∃ x : P.constraintSet,
        (∀ i, P.inequality i x ≤ 0) ∧
          (∀ j, P.equality j x = 0) ∧
          (∀ i, ¬ affOn[𝕜](extendZero (P.inequality i), P.constraintSet) →
            P.inequality i x < 0) := by
  constructor
  · rintro ⟨x, hxStrict⟩
    rcases (P.mem_feasibleSet x.1).1 x.2 with ⟨hxC, hxI, hxE⟩
    refine ⟨⟨x.1, hxC⟩, hxI, hxE, ?_⟩
    · intro i hnonaffine
      have hxI : extendZero (P.inequality i) x.1 < 0 := hxStrict i hnonaffine
      have hxIeq :
          extendZero (P.inequality i) x.1 =
            P.inequality i ⟨x.1, hxC⟩ := by
        simpa using (extendZero_apply (P.inequality i) ⟨x.1, hxC⟩)
      exact hxIeq ▸ hxI
  · rintro ⟨x, hxIneq, hxEq, hxStrict⟩
    have hxFeasible : x.1 ∈ P.feasibleSet := by
      exact (P.mem_feasibleSet x.1).2 ⟨x.2, hxIneq, hxEq⟩
    refine ⟨⟨x.1, hxFeasible⟩, ?_⟩
    intro i hnonaffine
    simpa [extendZero_apply] using hxStrict i hnonaffine

-- Proof sketch: in the pure-inequality case, apply the mixed strict/weak separation theorem from
-- Chapter 21 to the optimal-value-shifted system consisting of the strict nonaffine block and the
-- weak affine block, then normalize the objective coefficient to `1` and read off a
-- Kuhn--Tucker vector. When equality constraints are present, replace each affine equality by the
-- pair of weak inequalities `h ≤ 0` and `-h ≤ 0`, apply the already proved inequality case, and
-- combine the two resulting coefficient blocks into the unrestricted equality multipliers.
/-- Theorem 6.28.3: if the optimal value of an ordinary convex program is not `-∞` and the
program has a feasible point at which every nonaffine inequality constraint is strict, then a
Kuhn--Tucker vector exists for the program. -/
theorem exists_kuhnTuckerVector_of_nonaffine_strict_feasibility
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities) :
    ∃ lam : ι → 𝕜, ∃ μ : κ → 𝕜, P.IsKuhnTuckerVector lam μ := sorry

end OrdinaryConvexProgram

end
