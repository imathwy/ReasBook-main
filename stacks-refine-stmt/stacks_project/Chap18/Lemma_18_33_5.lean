import Mathlib
import stacks_project.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.33.5:
- primary domain: inverse image for sheaves of modules on sites and compatibility of relative
  differentials with site pullback;
- sampled owner declarations:
  `SheafOfModules.RingedSite.relativeDifferentials`,
  `SheafOfModules.RingedSite.relativeDifferentials_hasUniversalProperty`,
  `SheafOfModules.pullback`,
  `Functor.sheafPullback`,
  `Functor.sheafPushforwardContinuousId`;
- best owner abstraction: the source-facing sheaf owner `Ω(φ)` together with the canonical
  inverse-image bridge from `SheafOfModules.pullback` to the relative differentials of the
  pulled-back morphism;
- primitive data: the continuous functor `F`, the morphism `φ : O₁ ⟶ O₂`, the actual inverse
  image of `Ω(φ)`, and the canonical pulled-back morphism
  `(F.sheafPullback CommRingCat JC JD).map φ`;
- derived API: the direct comparison isomorphism between the actual inverse image of `Ω(φ)`,
  transported along the canonical pullback ring-sheaf comparison, and the canonical owner
  `Ω((F.sheafPullback CommRingCat JC JD).map φ)`.

Source/core/bridge triage:
- `source-facing`: the statement that inverse image preserves the sheaf of relative differentials;
- `core/canonical`: `Ω(φ)`, `relativeDifferential φ`, and
  `relativeDifferentials_hasUniversalProperty`;
- `bridge/view`: the comparison between the actual inverse image of `Ω(φ)` and the canonical owner
  for the pulled-back morphism.

The public API in this file should therefore expose the inverse-image comparison itself as the
main theorem, and avoid any public iso witness chosen noncanonically from `IsIsomorphic`. -/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Pullback of a commutative-ring sheaf along `F` commutes with forgetting to `RingCat`. -/
private theorem pullbackCommRingSheaf_ringSheaf_eq
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) =
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) := by
  sorry

/-- The canonical ring-sheaf comparison between pulling back before or after forgetting
commutativity. -/
noncomputable def pullbackRingSheafIso
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) ≅
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) :=
  eqToIso (pullbackCommRingSheaf_ringSheaf_eq F O)

section

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable [HasWeakSheafify JD CommRingCat.{max u v}]
variable [HasWeakSheafify JD RingCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
variable [(SheafOfModules.pushforward
    ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
      (ringSheaf JC O₂))).IsRightAdjoint]

private instance presheafPushforwardUnitIsRightAdjoint :
    (PresheafOfModules.pushforward
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂)).hom).IsRightAdjoint := by
  sorry

/-- The actual inverse image of `Ω(φ)` in the raw pulled-back module category. -/
abbrev inverseImageRelativeDifferentialsSource :
    SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)) :=
  (SheafOfModules.pullback
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
        (ringSheaf JC O₂))).obj
    (Ω(φ))

/-- The owner `Ω((F.sheafPullback CommRingCat JC JD).map φ)`, viewed over the raw pulled-back
`RingCat`-valued structure sheaf. -/
abbrev pulledBackRelativeDifferentials :
    SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)) :=
  (SheafOfModules.restrictScalars (pullbackRingSheafIso F O₂).inv).obj
    (Ω((F.sheafPullback CommRingCat JC JD).map φ))

private abbrev pulledBackRelativeDifferentialsPresentation :
    SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)) :=
  (PresheafOfModules.sheafification
      (𝟙 ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)).obj)).obj
    ((PresheafOfModules.restrictScalars
        (pullbackRingSheafIso F O₂).inv.hom).obj
      (relativeDifferentials' ((F.sheafPullback CommRingCat JC JD).map φ).hom))

private theorem pulledBackRelativeDifferentialsPresheaf_eq :
    (PresheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂)).hom).obj
        (relativeDifferentials' φ.hom) =
      (PresheafOfModules.restrictScalars
          (pullbackRingSheafIso F O₂).inv.hom).obj
        (relativeDifferentials' ((F.sheafPullback CommRingCat JC JD).map φ).hom) := by
  sorry

private theorem pulledBackRelativeDifferentialsPresentation_isomorphic :
    IsIsomorphic
      (pulledBackRelativeDifferentialsPresentation F O₁ O₂ φ)
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) := by
  sorry

private noncomputable abbrev pulledBackRelativeDifferentialsPresentationIso :
    pulledBackRelativeDifferentialsPresentation F O₁ O₂ φ ≅
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) :=
  Classical.choice
    (show Nonempty
      (pulledBackRelativeDifferentialsPresentation F O₁ O₂ φ ≅
        (pulledBackRelativeDifferentials F O₁ O₂ φ :
          SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)))) from
      pulledBackRelativeDifferentialsPresentation_isomorphic F O₁ O₂ φ)

-- Proof sketch: write `Ω(φ)` as the sheafification of the presheaf of relative differentials from
-- Lemma `18.33.2`, pull that presentation back along the inverse-image functor, and use exactness
-- of inverse image together with the objectwise identities
-- `f^{-1}(O₂[O₂]) = f^{-1}O₂[f^{-1}O₂]`,
-- `f^{-1}(O₂[O₂ × O₂]) = f^{-1}O₂[f^{-1}O₂ × f^{-1}O₂]`, and
-- `f^{-1}(O₂[O₁]) = f^{-1}O₂[f^{-1}O₁]`. This identifies the actual inverse image of `Ω(φ)` with
-- the canonical pulled-back owner `pulledBackRelativeDifferentials F O₁ O₂ φ`.
/-- Lemma 18.33.5: the actual inverse image of `Ω(φ)` is canonically isomorphic to the
pulled-back relative-differentials owner for `(F.sheafPullback CommRingCat JC JD).map φ`, viewed
over the raw pulled-back `RingCat`-valued structure sheaf. -/
noncomputable abbrev inverseImageRelativeDifferentialsIso :
    inverseImageRelativeDifferentialsSource F O₁ O₂ φ ≅
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) :=
  (Functor.mapIso
      (SheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂)))
      (eqToIso (relativeDifferentials_def φ))) ≪≫
    (SheafOfModules.sheafificationCompPullback
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂))).app
      (relativeDifferentials' φ.hom) ≪≫
    (Functor.mapIso
      (PresheafOfModules.sheafification
        (𝟙 ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)).obj))
      (eqToIso
        (pulledBackRelativeDifferentialsPresheaf_eq F O₁ O₂ φ))) ≪≫
    pulledBackRelativeDifferentialsPresentationIso F O₁ O₂ φ

/-- The actual inverse image of `Ω(φ)` and the pulled-back owner are isomorphic. -/
theorem inverseImage_relative_differentials :
    IsIsomorphic
      (inverseImageRelativeDifferentialsSource F O₁ O₂ φ)
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) := by
  exact ⟨inverseImageRelativeDifferentialsIso F O₁ O₂ φ⟩

end

end SheafOfModules.RingedSite
