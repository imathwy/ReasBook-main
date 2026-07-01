import Mathlib
import stacks_project.Chap04.Definition_4_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe uI vI uA vA

namespace CategoryTheory

section Filtered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

/- Domain-style sampling for Lemma 12.30.1 in the filtered/cofiltered additive-diagram domain:
- sampled owner-level declarations:
  * `IsEssentiallyConstantFilteredDiagram`
  * `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone`
  * `essentiallyConstantFilteredDiagram_iff_comp_final`
  * `essentiallyConstantCofilteredDiagram_iff_comp_initial`
- best owner abstraction: the chapter owner
  `IsEssentiallyConstantFilteredDiagram M` from `Definition_4_22_2`.

Primitive-vs-derived split:
- primitive source-facing data: for a fixed colimit cocone `c`, each stage `M.obj i` splits into a
  stable summand that maps isomorphically to the colimit value and a complementary summand that
  eventually dies under some transition map.
- derived source-facing bridge criterion: a cofinal filtered full subcategory on which this
  pointwise stable-splitting condition holds.
- derived API: the dual cofiltered criterion `HasEventuallySplitLimit`, obtained by applying the
  filtered statement to the opposite diagram.

Source/core/bridge triage:
- `source-facing`: `HasEventuallySplitColimit` and its dual `HasEventuallySplitLimit`.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram`,
  `IsEssentiallyConstantCofilteredDiagram`, and the actual colimit owner `ColimitCocone`.
- `bridge/view`: restriction to a cofinal filtered full subcategory, and passage to the opposite
  diagram for the cofiltered dual.

The colimit witness should therefore use the canonical owner `ColimitCocone M`, not a duplicated
pair `(c : Cocone M)` together with a separate `IsColimit c`. -/

private def stableSplitStage {M : I ⥤ A} (c : ColimitCocone M) (i : I) : Prop :=
  ∃ (X Z : A) (f : X ⟶ M.obj i) (g : M.obj i ⟶ Z) (zero : f ≫ g = 0)
    (s : (ShortComplex.mk f g zero).Splitting),
      IsIso (f ≫ c.cocone.ι.app i) ∧
        ∃ (j : I) (h : i ⟶ j), s.s ≫ M.map h = 0

-- Internal stable-splitting criterion used to define the source-facing bridge
-- `HasEventuallySplitColimit`.
private def hasStableSplitColimit (M : I ⥤ A) : Prop :=
  ∃ c : ColimitCocone M,
    ∀ i : I, stableSplitStage c i

/-- A diagram has an eventual split colimit if, after restricting along the inclusion of some
cofinal filtered full subcategory, the restricted diagram has a stable split colimit. In Lemma
12.30.1 this is the source-facing bridge criterion for filtered diagrams. -/
def HasEventuallySplitColimit (M : I ⥤ A) : Prop :=
  ∃ P : ObjectProperty I,
    ∃ _ : IsFiltered P.FullSubcategory,
      ∃ _ : Functor.Final P.ι,
        hasStableSplitColimit (P.ι ⋙ M)

-- Proof sketch: from an essentially constant filtered cocone, take its colimit value, pass to the
-- cofinal full subcategory of stages receiving a map from the chosen index, and split the induced
-- idempotent at each such stage using idempotent completeness.
/-- Lemma 12.30.1 (1): for a filtered diagram in a preadditive Karoubian category, being
essentially constant is equivalent to admitting a cofinal filtered full subcategory whose stages
split into a stable summand mapping isomorphically to a colimit value and a complementary summand
that eventually becomes zero. -/
theorem essentiallyConstantFilteredDiagram_iff_hasEventuallySplitColimit
    [IsFiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantFilteredDiagram M ↔
      HasEventuallySplitColimit M := sorry

end Filtered

section Cofiltered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

/-- A diagram has an eventual split limit if, after passing to the opposite diagram, it has an
eventual split colimit. In Lemma 12.30.1 this is the cofiltered dual of
`HasEventuallySplitColimit`, applied to cofiltered diagrams. -/
abbrev HasEventuallySplitLimit (M : I ⥤ A) : Prop :=
  HasEventuallySplitColimit M.op

-- Proof sketch: apply the filtered statement to the opposite diagram `M.op`, translate the split
-- decomposition data across `op`/`unop`, and rewrite essential constancy using the dual
-- characterization of essentially constant cofiltered cones.
/-- Lemma 12.30.1 (2): for a cofiltered diagram in a preadditive Karoubian category, being
essentially constant is equivalent to admitting an initial cofiltered full subcategory whose stages
split into a stable summand receiving the limit isomorphically and a complementary summand killed
by some earlier transition map. -/
theorem essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit
    [IsCofiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      HasEventuallySplitLimit M := by
  rw [isEssentiallyConstantCofilteredDiagram_iff_op]
  simpa [HasEventuallySplitLimit] using
    essentiallyConstantFilteredDiagram_iff_hasEventuallySplitColimit M.op

end Cofiltered

end CategoryTheory
