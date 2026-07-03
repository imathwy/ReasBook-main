import Mathlib
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap04.Lemma_4_22_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CostructuredArrow
open CategoryTheory.Pretriangulated
open Opposite

universe uI vI uC vC uD vD

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.42.2:
- primary domain: essentially constant cofiltered diagrams and fixed pro-object values in a
  pretriangulated/triangulated setting.
- inspected owner-level declarations:
  `SequentialInverseSystem` in `Chap12/Definition_12_31_2`,
  `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`,
  `HasProObjectValue` in `Chap04/Remark_4_22_7`,
  `hasProObjectValue_iff_exists_stageMap_homColimitComparison` in
    `Chap04/Lemma_4_22_10`,
  `Triangle.π₁`, `Triangle.π₂`, `Triangle.π₃` in mathlib.
- best owner abstraction: the sequential diagram owner `SequentialInverseSystem`, the
  essential-constancy owner `IsEssentiallyConstantCofilteredDiagram`, the fixed pro-object-value
  owner `HasProObjectValue M X`, and the stage-map comparison owner `HasHomColimitComparison`.
- primitive-vs-derived split: the primitive data are the inverse system `T`, the positive stage
  `n + 1`, the fixed distinguished triangle `T'`, and the morphism from that stage to `T'`;
  the owner-level conclusions `HasProObjectValue` and
  `IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₂)` are derived from the corresponding
  Hom-colimit comparison data via Lemma `4.22.10`.

Source/core/bridge triage:
- `source-facing`: after some positive stage, the system admits a fixed distinguished triangle
  together with a morphism of distinguished triangles from that stage whose three components
  satisfy the Hom-colimit comparison criterion.
- `core/canonical`: `HasProObjectValue`, `IsEssentiallyConstantCofilteredDiagram`, `Triangle D`,
  and `HasHomColimitComparison`.
- `bridge/view`: the companion owner-level consequences below, obtained from the source-facing
  stage-map theorem via
  `hasProObjectValue_iff_exists_stageMap_homColimitComparison`. -/

section

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

-- Proof sketch: first rewrite the outer systems using Lemma 13.42.1 so that, on a tail, their
-- terms split as fixed summands plus essentially zero complements. The connecting morphisms on the
-- fixed summands define a single map `C ⟶ A⟦1⟧`; choose a distinguished triangle on that map, then
-- use `TR3` to compare one stage with it. Applying the homological functors `Hom(-, D)` shows that
-- the three components of that stage map corepresent the original inverse systems, so in
-- particular the three projected systems have fixed pro-object values given by the components of
-- `T'`, so the middle term system is essentially constant as well.
/-- Lemma 13.42.2, source-facing form: for a sequential inverse system of distinguished triangles
in a triangulated category, and in fact already in a pretriangulated category, if the first and
third term systems are essentially constant, then after some positive stage the system admits a
fixed distinguished triangle together with a morphism of distinguished triangles from that stage,
whose three components satisfy the stage-map comparison criterion of Lemma `4.22.10`.

The owner-level pro-object-value and essential-constancy consequences are recorded below as thin
companions. -/
theorem essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    ∃ (T' : Triangle D) (n : ℕ),
      T' ∈ distTriang D ∧
        ∃ φ : T.obj (op (n + 1)) ⟶ T',
          HasHomColimitComparison
            (T ⋙ Triangle.π₁)
            (CostructuredArrow.mk φ.hom₁) ∧
          HasHomColimitComparison
            (T ⋙ Triangle.π₂)
            (CostructuredArrow.mk φ.hom₂) ∧
          HasHomColimitComparison
            (T ⋙ Triangle.π₃)
            (CostructuredArrow.mk φ.hom₃) := sorry

/-- Owner-level companion to Lemma 13.42.2: the fixed distinguished triangle produced there has
vertices corepresenting the three projected inverse systems. -/
theorem exists_proObjectValue_triangle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    ∃ T' : Triangle D,
      T' ∈ distTriang D ∧
        HasProObjectValue (T ⋙ Triangle.π₁) T'.obj₁ ∧
        HasProObjectValue (T ⋙ Triangle.π₂) T'.obj₂ ∧
        HasProObjectValue (T ⋙ Triangle.π₃) T'.obj₃ := sorry

/-- Owner-level consequence of Lemma 13.42.2: if the outer terms of a sequential inverse system
of distinguished triangles are essentially constant, then so is the middle term system. -/
theorem essentiallyConstant_middle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₂) := sorry

end

end CategoryTheory
