import StacksProject_2024.Chap04.Definition_4_19_1
import StacksProject_2024.Chap04.Lemma_4_19_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open ConnectedComponents

universe vI uI

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]

/-
Source/core/bridge triage for Lemma 4.19.8:
- `source-facing`: the span-cocone hypothesis `HasSpanCocones I` together with the explicit
  postcomposition-equalizer condition on parallel pairs in `I`.
- `core/canonical`: the canonical connected-component decomposition `decomposedEquiv` and the
  owner predicate `IsFiltered`.
- `bridge/view`: the source-facing conclusion is expressed by proving that every connected
  component in the canonical decomposition is filtered.
-/

/- Companion recall: `CategoryTheory.decomposedEquiv` is the canonical equivalence expressing any
category as the disjoint union of its connected components. -/
recall CategoryTheory.decomposedEquiv

-- Proof sketch: use `decomposedEquiv` to write `I` as the disjoint union of its connected
-- components; Lemma 4.19.6 supplies common successors inside each component from
-- `HasSpanCocones I`, and the postcomposition-equalizer hypothesis descends to the componentwise
-- full subcategories, giving the remaining filteredness axiom.
/-- Lemma 4.19.8: if every span in `I` admits a commuting cocone and every parallel pair in `I`
is equalized after postcomposition, then each connected component in the canonical decomposition
of `I` is a filtered index category. Together with `CategoryTheory.decomposedEquiv`, this is the
library-facing form of the statement that `I` is a possibly empty disjoint union of filtered
index categories. -/
theorem connected_components_are_filtered
    [HasSpanCocones I]
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : ConnectedComponents I) :
    IsFiltered j.Component := sorry

end CategoryTheory
