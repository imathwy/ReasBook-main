import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [InfSet α] [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.15 names the optimal value of the generalized convex program
  attached to a bifunction `F` as the infimum of the objective `F₀`.
- `core/canonical`: the existing owner abstractions are the zero-slice objective `objective F`
  from Definition 6.29.12 and the perturbation-value function `perturbationFunction F` from
  Definition 6.29.1.
- `bridge/view`: the source infimum of `F₀` over the primal variable is exactly both
  `perturbationFunction F 0` and `⨅ x, (F)₀ x`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.objective_apply`;
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`.

Primitive data vs derived API:
- primitive source data: the bifunction `F : U → X → α` at the codomain layer where infima are
  available (specialized in Chapter 6 to `WithBotTop` codomains);
- primitive source-facing owner in this file: `optimalValue F`;
- primitive defining formula: `optimalValue F = ⨅ x, (F)₀ x`;
- derived API: the bridge identification `optimalValue F = perturbationFunction F 0`.

Layer target: `source-facing`. This item introduces a genuine piece of chapter vocabulary, so it
gets a direct owner on the existing bifunction data rather than a wrapper package.
-/

/-- Definition 6.29.15: the optimal value of the generalized convex program attached to `F` is
the infimum of the zero-slice objective `F₀`. -/
def optimalValue (F : U → X → α) : α :=
  ⨅ x : X, (F)₀ x

/-- The optimal value is the perturbation value at the zero perturbation. -/
@[simp]
theorem optimalValue_eq_perturbationFunction_zero
    (F : U → X → α) :
    optimalValue F = perturbationFunction F 0 :=
  by
    simpa [optimalValue] using (perturbationFunction_zero_eq_iInf (F := F)).symm

/-- The optimal value is the infimum of the objective `F₀` over the primal variable. -/
@[simp]
theorem optimalValue_eq_iInf
    (F : U → X → α) :
    optimalValue F = ⨅ x : X, (F)₀ x :=
  rfl

end

end Bifunction
