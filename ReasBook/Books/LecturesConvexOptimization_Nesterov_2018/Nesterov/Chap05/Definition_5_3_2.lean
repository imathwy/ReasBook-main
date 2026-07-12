import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Theorem_5_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.3.2 lies in the Chapter 5 self-concordant-barrier domain.

Sampled owner-style declarations in this domain:
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for standard
  self-concordance on an open convex domain;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the canonical closed-domain barrier
  owner expressed through a bundled map on `interior (closure dom)`;
* `IsSelfConcordantOnWith.toBarrierMap` and `IsSelfConcordantOnWith.isBarrierFunctionOn` from
  `Theorem_5_1_3`, the canonical bridge turning self-concordance on `dom` into the Chapter 1
  barrier owner on `closure dom`.

Best owner abstraction:
* source-facing: `IsSelfConcordantBarrierOnWith dom ν F`;
* core/canonical ambient owners: `IsStandardSelfConcordantOn dom F` and
  `IsBarrierFunctionOn (closure dom) ...`;
* bridge/view: the finite-dimensional theorem
  `IsSelfConcordantBarrierOnWith.isBarrierFunctionOn`.

Primitive data:
* the standard self-concordance owner on `dom`;
* the pointwise barrier-parameter inequality.

Derived API:
* standard self-concordance as an inferable parent instance;
* the barrier-parameter inequality as a theorem-level owner consequence;
* the finite-dimensional bridge to `IsBarrierFunctionOn (closure dom)`.

Source/core/bridge triage:
* source-facing: `IsSelfConcordantBarrierOnWith dom ν F`;
* core/canonical: `IsStandardSelfConcordantOn dom F` and `IsBarrierFunctionOn`;
* bridge/view: `isBarrierFunctionOn`.

This file therefore keeps the source-facing barrier owner, but removes unused `Fact` wrappers
around derived consequences. The owner-level consequences are exposed directly as theorems instead
of parallel typeclass packaging. -/

/-- Definition 5.3.2: a standard self-concordant function `F` is a `ν`-self-concordant barrier
for `dom` when, for every `x ∈ dom`, every direction `u` satisfies the barrier inequality
`2 ⟪∇F(x), u⟫ - ⟪u, ∇²F(x)u⟫ ≤ ν`. The constant `ν` is the barrier parameter. The Chapter 1
barrier owner on `closure dom` is a separate finite-dimensional bridge that additionally needs
domain nonemptiness. -/
class IsSelfConcordantBarrierOnWith (dom : Set E) (ν : NNReal) (F : E → ℝ) : Prop where
  /-- A self-concordant barrier is standard self-concordant on its open convex domain. -/
  toIsStandardSelfConcordantOn : IsStandardSelfConcordantOn dom F
  /-- The barrier parameter bounds the gradient term by the Hessian quadratic form at each point
  of the domain. -/
  barrier_parameter_bound {x : E} (hx : x ∈ dom) (u : E) :
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)

attribute [instance] IsSelfConcordantBarrierOnWith.toIsStandardSelfConcordantOn

namespace IsSelfConcordantBarrierOnWith

/-- A self-concordant barrier instance canonically supplies the defining barrier-parameter
inequality at each point of its domain. -/
theorem barrier_parameter_bound_of_mem
    {dom : Set E} (ν : NNReal) {F : E → ℝ}
    [h : IsSelfConcordantBarrierOnWith dom ν F] {x : E} (hx : x ∈ dom) (u : E) :
    2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ) :=
  h.barrier_parameter_bound hx u

variable [FiniteDimensional ℝ E]

/-- A self-concordant barrier canonically supplies the Chapter 1 barrier owner on `closure dom`
through the restricted map `interior (closure dom) = dom → ℝ`. -/
theorem isBarrierFunctionOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ} (h : IsSelfConcordantBarrierOnWith dom ν F)
    (hdom : dom.Nonempty) :
    IsBarrierFunctionOn (closure dom) h.toIsStandardSelfConcordantOn.toBarrierMap :=
  h.toIsStandardSelfConcordantOn.isBarrierFunctionOn hdom

end IsSelfConcordantBarrierOnWith

end
