import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable [InfSet (WithBotTop β)]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.5 introduces the perturbation-value function of an ordinary
  convex program by taking, for each perturbation vector, the infimum of the corresponding
  perturbed problem.
- `core/canonical`: the existing Chapter 6 owner for such value functions is
  `Bifunction.perturbationFunction`.
- `bridge/view`: for an ordinary convex program `P`, the bifunction to which that owner is applied
  is the canonical extension by `+∞` of the objective to the perturbed feasible set, where the
  textbook vector `u = (v₁, …, v_m)` is represented on the canonical owner
  `P.ConstraintIndex`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `extendZero` from `Definition_6_28_1`;
- `Function.toWithBotTopOn` from `Remark_4_4_5`;
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`.

Primitive data vs derived API:
- primitive data: the ordinary convex program `P`;
- core/canonical owner: `Bifunction.perturbationFunction` applied directly to the perturbed-problem
  family attached to `P`;
- derived API: the pointwise value formula for that specialization, already owned upstream by
  `Bifunction.perturbationFunction_apply`.

Layer target: `source-facing` on top of the canonical owner. This item introduces the source
vocabulary `P.perturbationValue` as a thin owner-level specialization of
`Bifunction.perturbationFunction` to `P.perturbedProblem`, then reuses the canonical upstream
evaluation theorem.
-/

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E β r s)

/-- Definition 6.28.5: the perturbation-value function of an ordinary convex program `P`,
obtained by specializing the chapter's canonical perturbation-function owner to
`P.perturbedProblem`. -/
abbrev perturbationValue : (P.ConstraintIndex → β) → WithBotTop β :=
  Bifunction.perturbationFunction P.perturbedProblem

/-- Evaluating the source-facing perturbation-value owner is the canonical row-infimum formula. -/
@[simp] theorem perturbationValue_apply
    (u : P.ConstraintIndex → β) :
    P.perturbationValue u = ⨅ x, P.perturbedProblem u x := by
  exact Bifunction.perturbationFunction_apply P.perturbedProblem u

end OrdinaryConvexProgram

end
