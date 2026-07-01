import Mathlib
import stacks_project.Chap18.Lemma_18_33_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

/-- The additive sheaf underlying the actual inverse image of `Ω(φ)`. -/
abbrev inverseImageNaiveCotangentSheaf
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    Sheaf JD AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf
      ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))).obj
    (inverseImageRelativeDifferentialsSource F O₁ O₂ φ)

/-- The additive sheaf underlying the pulled-back relative differentials. -/
abbrev pulledBackNaiveCotangentSheaf
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    Sheaf JD AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf
      ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))).obj
    (pulledBackRelativeDifferentials F O₁ O₂ φ)

-- Proof sketch: Lemma `18.33.5` produces the canonical comparison morphism from the actual
-- inverse image of `Ω_{O₂/O₁}` to the pulled-back owner
-- `pulledBackRelativeDifferentials F O₁ O₂ φ`, and that morphism is an isomorphism. The naive
-- cotangent complex in this site-level formulation is the single-term cochain complex
-- concentrated in degree `0` on the underlying additive sheaf, so applying `CochainComplex.single₀`
-- to the comparison gives the desired identification.
/-- Lemma 18.35.3: for a morphism of topoi presented by a continuous functor
`F : \mathcal D \to \mathcal C` and a morphism `\mathcal O_1 \to \mathcal O_2` of sheaves of
commutative rings on `\mathcal C`, the inverse image of the naive cotangent complex
`NL_{\mathcal O_2/\mathcal O_1}` is canonically isomorphic to the naive cotangent complex of the
pulled-back morphism. In this formalization, both naive cotangent complexes are the degree-`0`
single-term complexes on the corresponding sheaves of relative differentials. -/
theorem inverseImage_naive_cotangent_complex_iso
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    IsIsomorphic
      ((CochainComplex.single₀ (Sheaf JD AddCommGrpCat.{max u v})).obj
        (inverseImageNaiveCotangentSheaf F O₁ O₂ φ))
      ((CochainComplex.single₀ (Sheaf JD AddCommGrpCat.{max u v})).obj
        (pulledBackNaiveCotangentSheaf F O₁ O₂ φ)) := sorry
