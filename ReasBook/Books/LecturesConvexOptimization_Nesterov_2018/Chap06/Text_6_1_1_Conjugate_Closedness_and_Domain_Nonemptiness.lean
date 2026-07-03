import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_1_3
import LecturesConvexOptimization_Nesterov_2018.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Text 6.1.1 lies in the chapter's Fenchel-conjugacy / effective-epigraph domain.

Primary domain:
- the source-facing Fenchel dual `f⋆`, its effective domain `dom (f⋆)`, and its effective
  epigraph `effectiveEpigraph (f⋆)` on a real inner-product space.

Mandatory domain-style sampling before refinement:
- `fenchelDual` and the notation `f⋆` in `Chap03/Definition_3_1_2_1`, the source-facing Fenchel
  dual owner on real inner-product spaces;
- `subdifferential` and the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `effectiveEpigraph` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter
  owners for the `EReal` effective epigraph and finite real part;
- `subdifferential_subset_dom_fenchelDual` in `Chap03/Theorem_3_1_5_2`, the canonical
  subdifferential-to-dual-domain bridge already used downstream in later Fenchel files.

Best owner abstraction:
- core/canonical: the chapter owner stack `f⋆`, `dom (f⋆)`, and `effectiveEpigraph (f⋆)`;
- bridge/view: `IsClosed (effectiveEpigraph (f⋆))`, `Convex ℝ (effectiveEpigraph (f⋆))`, and the
  domain corollary derived from `subdifferential_subset_dom_fenchelDual`.

Primitive data:
- `f : E → WithTop ℝ`;
- the point `x : E` for the subdifferential-domain inclusion.

Derived API in this file:
- the source-facing theorem that `effectiveEpigraph (f⋆)` is closed and convex;
- the domain nonemptiness corollary from a nonempty subdifferential.

Source/core/bridge triage:
- source-facing: the textbook claims about the effective epigraph of the Fenchel dual and the
  finiteness of the dual at subgradients;
- core/canonical: `f⋆`, `dom (f⋆)`, and the chapter owner stack around `effectiveEpigraph`;
- bridge/view: `effectiveEpigraph (f⋆)` and the subdifferential-domain inclusion.

The previous version kept an extra local companion for the owner-level convexity surface of `f⋆`.
That surface already belongs upstream in the Chapter 3 Fenchel stack, so this file now keeps only
the source-facing closed-convex epigraph statement together with the domain consequence needed in
later Chapter 5/6 Fenchel files.
-/

-- Proof sketch: a Fenchel conjugate is convex on its effective domain, and Theorem 3.1.1.2
-- converts that owner-level convexity into convexity of the effective epigraph; closedness is the
-- standard epigraph closedness property of conjugates.
/-- Text 6.1.1-Conjugate Closedness and Domain Nonemptiness: the Fenchel dual has a closed and
convex effective epigraph. The domain nonemptiness consequence is recorded separately below. -/
theorem fenchelDual_effectiveEpigraph_closed_convex
    (f : E → WithTop ℝ) :
    IsClosed (effectiveEpigraph (f⋆)) ∧
      Convex ℝ (effectiveEpigraph (f⋆)) := sorry

-- The owner-level `ConvexOn` surface for `f⋆` is already the canonical Chapter 3 API, so this
-- file does not keep a second local theorem for it.

-- Proof sketch: choose `g ∈ ∂ f(x)` from the nonempty subdifferential and apply the inclusion
-- theorem above.
/-- If some subdifferential of `f` is nonempty, then the effective domain of the Fenchel dual is
nonempty. -/
theorem dom_fenchelDual_nonempty_of_subdifferential_nonempty
    {f : E → WithTop ℝ} {x : E} (hsub : (∂ f(x)).Nonempty) :
    (dom (f⋆)).Nonempty := sorry

end
