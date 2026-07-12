import Mathlib
import StacksProject_2024.Chap18.Definition_18_35_1
import StacksProject_2024.Chap18.Lemma_18_33_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.35.3:
- primary domain: inverse-image compatibility for the naive cotangent complex on a ringed site;
- sampled owner declarations:
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `SheafOfModules.RingedSite.inverseImage_relativeDifferentialsIso`;
- best owner abstraction: the site-level owner `naiveCotangent` itself, not the degree-`0`
  `single₀` shadow of its relative-differentials term;
- primitive data: the continuous functor `F`, the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image
  functor on `O₂`-modules, and the pulled-back morphism `(F.sheafPullback CommRingCat JC JD).map φ`;
- derived API: the theorem-level `IsIsomorphic` comparison between the actual inverse image of
  `naiveCotangent O₁ (Under.mk φ)` and the pulled-back owner transported across
  `pullbackRingSheafIso F O₂`.

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1} NL_{\mathcal O_2/\mathcal O_1} = NL_{f^{-1}\mathcal O_2/f^{-1}\mathcal O_1}`;
- `core/canonical`: `naiveCotangent`, `pullbackRingSheafIso`, and
  `Functor.mapHomologicalComplex`;
- `bridge/view`: this file records the comparison after transporting the pulled-back complex to the
  raw pulled-back `RingCat`-valued structure sheaf. -/

section

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable [HasWeakSheafify JC (Type u)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [HasWeakSheafify JD RingCat.{u}]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{u}, F.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ RingCat.{u}, F.op.HasLeftKanExtension P]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD (Type u)]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf JC CommRingCat.{u})]
variable [HasBinaryCoproducts (Sheaf JD CommRingCat.{u})]
variable (O₂ : Sheaf JC CommRingCat.{u})
variable [(SheafOfModules.pushforward
    ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
      (ringSheaf JC O₂))).IsRightAdjoint]

private instance pullback_preservesZeroMorphisms :
    (SheafOfModules.pullback
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
        (ringSheaf JC O₂))).PreservesZeroMorphisms := by
  infer_instance

end

/-- Lemma 18.35.3: the actual inverse image of the naive cotangent complex is canonically
identified with the naive cotangent complex of the pulled-back morphism, viewed over the raw
pulled-back `RingCat`-valued structure sheaf. -/
@[stacks 08TZ]
theorem inverseImage_naiveCotangent_isIsomorphic
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JC (Type u)]
    [HasWeakSheafify JC CommRingCat.{u}]
    [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify JD CommRingCat.{u}]
    [HasWeakSheafify JD RingCat.{u}]
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{u}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{u}, F.op.HasLeftKanExtension P]
    [HasWeakSheafify JC AddCommGrpCat.{u}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify JD (Type u)]
    [HasWeakSheafify JD AddCommGrpCat.{u}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryCoproducts (Sheaf JC CommRingCat.{u})]
    [HasBinaryCoproducts (Sheaf JD CommRingCat.{u})]
    (O₁ O₂ : Sheaf JC CommRingCat.{u}) (φ : O₁ ⟶ O₂)
    [(SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
          (ringSheaf JC O₂))).IsRightAdjoint] :
    IsIsomorphic
      ((((SheafOfModules.pullback
            ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
              (ringSheaf JC O₂))).mapHomologicalComplex
          (up ℤ)).obj
        (naiveCotangent O₁ (Under.mk φ))))
      ((((SheafOfModules.restrictScalars
            (pullbackRingSheafIso F O₂).inv).mapHomologicalComplex
          (up ℤ)).obj
        (naiveCotangent ((F.sheafPullback CommRingCat JC JD).obj O₁)
          (Under.mk ((F.sheafPullback CommRingCat JC JD).map φ))))) := by
  -- Proof comment: after normalizing the two-term presentation and mapped differentials, the
  -- source and target complexes coincide definitionally.
  let K :=
    ((((SheafOfModules.pullback
            ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
              (ringSheaf JC O₂))).mapHomologicalComplex
          (up ℤ)).obj
        (naiveCotangent O₁ (Under.mk φ))))
  simpa [K, naiveCotangent, presentationNaiveCotangent, conormalSource, conormalTensorTerm,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d] using
    (show IsIsomorphic K K from ⟨Iso.refl K⟩)

end SheafOfModules.RingedSite
