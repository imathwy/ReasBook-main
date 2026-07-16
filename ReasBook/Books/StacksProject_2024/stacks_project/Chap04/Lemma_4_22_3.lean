import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

/- Domain-style sampling for Lemma 4.22.3:
- primary domain: essentially constant filtered/cofiltered diagrams and the resulting actual
  colimit/limit data.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredCocone.isColimit`,
  `IsEssentiallyConstantCofilteredCone.isLimit`,
  `IsEssentiallyConstantFilteredCocone`,
  `IsEssentiallyConstantFilteredDiagram`,
  `CategoryTheory.Limits.ColimitCocone`,
  `CategoryTheory.Limits.LimitCone`.
- best owner abstraction for the hypothesis: the chapter source-facing owners
  `IsEssentiallyConstantFilteredDiagram M` and `IsEssentiallyConstantCofilteredDiagram M`.
- best owner abstraction for the conclusion: `ColimitCocone M` / `LimitCone M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone/cone as in Definition 4.22.1.
- derived owner API: `IsEssentiallyConstantFilteredCocone.isColimit` and
  `IsEssentiallyConstantCofilteredCone.isLimit`.
- derived actual-colimit data: a colimit cocone or limit cone for `M`.
- derived duality bridge: `IsColimit.unop`, transporting the filtered cocone owner theorem to the
  cofiltered cone owner theorem.
- later bridge/view formulations via representability/corepresentability of the associated
  ind/pro-object belong to Lemmas 4.22.9 and 4.22.10, not to the main statements here.

Source/core/bridge triage:
- source-facing: the two theorems below, whose hypotheses are exactly the diagram-level notions
  from Definition 4.22.2.
- core/canonical: `ColimitCocone M` and `LimitCone M`.
- bridge/view: representability of `colimit (M ⋙ uliftYoneda)` and corepresentability of
  `limit (M.op ⋙ uliftCoyoneda)`. -/

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

-- Proof sketch: choose an essentially constant cocone from Definition 4.22.2; its distinguished
-- split leg and eventual factorization data already make it colimiting.
/-- Lemma 4.22.3 (1): a diagram satisfying
`IsEssentiallyConstantFilteredDiagram` admits an essentially constant colimit cocone. -/
theorem essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone
    (M : I ⥤ C) (hM : IsEssentiallyConstantFilteredDiagram M) :
    ∃ c : ColimitCocone M, IsEssentiallyConstantFilteredCocone c.cocone := by
  rcases hM with ⟨c, hc⟩
  exact ⟨⟨c, hc.isColimit⟩, hc⟩

-- Proof sketch: Definition 4.22.2 already identifies cofiltered essential constancy with the
-- existence of an essentially constant cone by direct unfolding; the canonical duality bridge
-- `IsColimit.unop` then transports the filtered cocone owner theorem to a genuine limit cone.
/-- Lemma 4.22.3 (2): a diagram satisfying
`IsEssentiallyConstantCofilteredDiagram` admits an essentially constant limit cone. -/
theorem essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone
    (M : I ⥤ C) (hM : IsEssentiallyConstantCofilteredDiagram M) :
    ∃ c : LimitCone M, IsEssentiallyConstantCofilteredCone c.cone := by
  rcases (isEssentiallyConstantCofilteredDiagram_iff_exists_essentiallyConstantCone M).1 hM with
    ⟨c, hc⟩
  exact ⟨⟨c, hc.isLimit⟩, hc⟩

end
