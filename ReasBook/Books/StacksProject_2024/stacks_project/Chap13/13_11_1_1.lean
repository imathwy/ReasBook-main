import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

local notation "H" => DerivedCategory.homologyFunctor C

/- 
Domain-style sampling:
- primary domain: exact five-term cohomology segments of distinguished triangles in the derived
  category.
- sampled owner declarations:
  `Functor.homologySequenceComposableArrows₅_exact`,
  `ComposableArrows.Exact.δlast`,
  `DerivedCategory.homologyFunctor`.
- best owner abstraction: the mathlib owner theorem
  `Functor.homologySequenceComposableArrows₅_exact`; the derived-category five-term statement in
  this file is its canonical `δlast` specialization for `H 0 : DerivedCategory C ⥤ C`.
- source/core/bridge triage:
  `source-facing`: the derived-category five-term cohomology segment;
  `core/canonical`: `Functor.homologySequenceComposableArrows₅_exact`;
  `bridge/view`: the canonical `δlast` truncation from the six-term exact sequence to the
    five-term source segment.
- primitive data vs derived API: the primitive data already live in the canonical homological
  owner theorem, so this file should only keep the thin `δlast` bridge matching the source
  wording.
-/

/- Companion recall: the degreewise cohomology functors on `D(C)` are the canonical owner
`DerivedCategory.homologyFunctor C`. -/
recall DerivedCategory.homologyFunctor

/- Companion recall: the exact five-term window for a distinguished triangle comes from the
canonical owner theorem `Functor.homologySequenceComposableArrows₅_exact`. -/
recall Functor.homologySequenceComposableArrows₅_exact

/- 
13.11.1.1: for a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]` in the derived category, the
cohomology maps and connecting morphism assemble into the exact five-term segment
`H^i(X) ⟶ H^i(Y) ⟶ H^i(Z) ⟶ H^(i + 1)(X) ⟶ H^(i + 1)(Y)`. This is the `δlast` truncation of the
canonical six-term exact sequence for `H 0 : DerivedCategory C ⥤ C`.
-/
theorem derivedCategory_five_term_exact
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ) :
    ((H 0).homologySequenceComposableArrows₅ T i (i + 1) rfl).δlast.Exact :=
  ((H 0).homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl).δlast
