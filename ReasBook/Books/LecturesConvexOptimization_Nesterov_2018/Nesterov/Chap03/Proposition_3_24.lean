import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.24 lies in the chapter's extended-valued subdifferential / closed-convex domain.

Mandatory domain-style sampling before refinement:
- `dom` and `constrainedEpigraph` in `Definition_3_3`, the chapter owners for the effective domain
  and constrained epigraph;
- `subdifferential` together with the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner
  for extended-valued subgradients;
- `ClosedConvexOn` and `ClosedConvexFunction` in `Definition_3_1_1_5`, the chapter owner
  abstraction for closed convex extended-valued functions;
- `ClosedConvexOn.isClosed_constrainedEpigraph` and
  `ClosedConvexOn.convex_constrainedEpigraph` in `Definition_3_1_1_5`, the derived epigraph API
  from that owner.

Best owner abstraction:
- source-facing main conclusion: `ClosedConvexFunction f`;
- core/canonical owners: `dom f`, `∂ f(x)`, `constrainedEpigraph (dom f) f`, and
  `ClosedConvexFunction f`;
- bridge/view: the convex-hull presentation of `∂ f(x)` as a route to owner-level
  subdifferential nonemptiness.

Primitive data:
- the extended-real-valued function `f`;
- the owner-level subdifferential nonemptiness hypothesis `∀ x ∈ dom f, (∂ f(x)).Nonempty`.

Derived API:
- the owner-level closed-convex conclusion `ClosedConvexFunction f`;
- the source-facing bridge from a convex-hull presentation `∂ f(x) = convexHull ℝ (Y x)` with
  `Y x` nonempty on `dom f`.

Source/core/bridge triage:
- source-facing: the convex-hull presentation of `∂ f(x)` from the textbook proposition;
- core/canonical: `ClosedConvexFunction f`;
- bridge/view: the derivation of owner-level subdifferential nonemptiness from the convex-hull
  presentation.

The previous refinement still kept the source-facing witness family `Y` as primitive data in the
main proposition theorem. This file now organizes Proposition 3.24 around the owner-level
subdifferential nonemptiness hypothesis, while the convex-hull presentation becomes a thin bridge
lemma instead of a second owner-level wrapper.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition 3.24, owner-level form: if every subdifferential `∂ f(x)` on the effective domain
is nonempty, then `f` is a closed convex function. -/
-- Proof sketch: the mathematically relevant hypothesis is the owner-level pointwise nonemptiness
-- of the subdifferential on `dom f`, while the conclusion is the chapter owner
-- `ClosedConvexFunction f`.
theorem closedConvexFunction_of_subdifferential_nonempty
    {f : E → WithTop ℝ}
    (hsub_nonempty : ∀ x ∈ dom f, (∂ f(x)).Nonempty) :
    ClosedConvexFunction f := sorry

/-- Proposition 3.24, source-facing bridge: a convex-hull presentation of every nonempty
subdifferential on `dom f` implies the owner-level closed-convex conclusion. -/
theorem closedConvexFunction_of_subdifferential_eq_convexHull
    {f : E → WithTop ℝ}
    (Y : E → Set E)
    (hY_nonempty : ∀ x ∈ dom f, (Y x).Nonempty)
    (hsubdiff : ∀ x ∈ dom f, ∂ f(x) = convexHull ℝ (Y x)) :
    ClosedConvexFunction f := by
  refine closedConvexFunction_of_subdifferential_nonempty ?_
  intro x hx
  rw [hsubdiff x hx]
  exact (hY_nonempty x hx).convexHull

end
