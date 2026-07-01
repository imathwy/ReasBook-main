import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.Recall
import stacks_project.Chap12.Definition_12_3_8

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Source/core/bridge triage for Definition 12.5.1:
- source-facing: the source notion of an abelian category
- core/canonical owner: `Abelian`
- bridge/view: `Abelian.ofCoimageImageComparisonIsIso`, whose additive input reuses the earlier
  chapter owner `HasFiniteProducts` from Definition 12.3.8 together with `Preadditive` -/
/- Definition 12.5.1: the source notion of an abelian category is represented canonically by the
mathlib owner class `Abelian`. -/
recall Abelian

/- Source-facing bridge: the textbook criterion "additive, kernels, cokernels, and
`Coim(f) ⟶ Im(f)` an isomorphism for every morphism `f`" is implemented by the constructor
`Abelian.ofCoimageImageComparisonIsIso`, with the additive hypothesis represented in mathlib by
`Preadditive` together with finite products. -/
recall Abelian.ofCoimageImageComparisonIsIso

end CategoryTheory
