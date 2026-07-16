import Mathlib
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_33_2
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/-- Helper for Lemma 18.33.5: local owner notation for the sheaf of relative differentials.
This avoids importing the heavier Chapter 18 owner file while keeping the source-facing statement
spelled with `Ω(φ)`. -/
private abbrev relativeDifferentialsLocal
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    {O₁ O₂ : Sheaf J CommRingCat.{max u v}} (φ : O₁ ⟶ O₂) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
    (relativeDifferentials' φ.hom)

local notation:max "Ω(" φ ")" =>
  relativeDifferentialsLocal φ

/- Domain-style sampling for Lemma 18.33.5:
- primary domain: inverse image for sheaves of modules on sites and compatibility of relative
  differentials with site pullback;
- sampled owner declarations:
  `SheafOfModules.RingedSite.relativeDifferentials`,
  `SheafOfModules.RingedSite.relativeDifferentials_representsDerivations`,
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
  `relativeDifferentials_representsDerivations`;
- `bridge/view`: the comparison between the actual inverse image of `Ω(φ)` and the canonical owner
  for the pulled-back morphism.

The public API in this file should therefore expose the inverse-image comparison itself as the
main theorem, and avoid any public iso witness chosen noncanonically from `IsIsomorphic`. -/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]

/-- Helper for Lemma 18.33.5: under the standard preservation hypotheses, pullback of a
commutative-ring sheaf along `F` commutes with forgetting to `RingCat`. -/
private noncomputable def pullbackCommRingSheaf_ringSheaf_iso_of_preserves
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) ≅
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) :=
  letI : (forget₂ CommRingCat RingCat.{max u v}).IsLeftAdjoint := by
    infer_instance
  letI : JD.PreservesSheafification (forget₂ CommRingCat RingCat.{max u v}) :=
    CategoryTheory.preservesSheafification_of_adjunction JD
      (Adjunction.ofIsLeftAdjoint (forget₂ CommRingCat RingCat.{max u v}))
  letI : (forget₂ CommRingCat RingCat.{max u v}).PreservesLeftKanExtensions F.op :=
    fun P ↦ by
      infer_instance
  let hPullbackForget :
      Functor.sheafPullbackConstruction.sheafPullback F CommRingCat.{max u v} JC JD ⋙
          sheafCompose JD (forget₂ CommRingCat RingCat.{max u v}) ≅
        sheafCompose JC (forget₂ CommRingCat RingCat.{max u v}) ⋙
          Functor.sheafPullbackConstruction.sheafPullback F RingCat.{max u v} JC JD :=
    -- Proof comment: compare the explicit pullback constructions by commuting forgetting first
    -- with sheafification on `JD`, and then with the left Kan extension along `F.op`.
    (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (sheafToPresheaf JC CommRingCat.{max u v})
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft F.op.lan
              (CategoryTheory.sheafComposeNatIso JD
                (forget₂ CommRingCat RingCat.{max u v})
                (CategoryTheory.sheafificationAdjunction JD CommRingCat.{max u v})
                (CategoryTheory.sheafificationAdjunction JD RingCat.{max u v})).symm)) ≪≫
      Functor.isoWhiskerLeft (sheafToPresheaf JC CommRingCat.{max u v})
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            ((forget₂ CommRingCat RingCat.{max u v}).lanCompIsoOfPreserves F.op)
            (presheafToSheaf JD RingCat.{max u v}) ≪≫
          Functor.associator _ _ _) ≪≫
      Iso.refl _
  -- Proof comment: transport the abstract pullback functors to their Kan-extension models,
  -- apply the forgetful comparison there, and then return to the chosen abstract pullback.
  (sheafCompose JD (forget₂ CommRingCat RingCat.{max u v})).mapIso
      ((Functor.sheafPullbackConstruction.sheafPullbackIso
        F CommRingCat.{max u v} JC JD).app O) ≪≫
    hPullbackForget.app O ≪≫
    ((Functor.sheafPullbackConstruction.sheafPullbackIso
      F RingCat.{max u v} JC JD).app (ringSheaf JC O)).symm

/-- Helper for Lemma 18.33.5: the forgotten CommRing-valued adjunction unit transposes under the
`RingCat` pullback-pushforward adjunction to a comparison morphism from the actual `RingCat`
pullback to the underlying ring sheaf of the CommRing pullback. -/
private noncomputable def pullbackRingSheafComparisonInvHom
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) ⟶
      ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) := by
  -- Proof comment: the raw comparison is the inverse direction of the canonical comparison iso
  -- already built from sheafification and Kan-extension compatibility.
  exact (pullbackCommRingSheaf_ringSheaf_iso_of_preserves (JC := JC) (JD := JD) F O).inv

/-- Helper for Lemma 18.33.5: the raw comparison from the actual `RingCat` pullback to the
forgotten pullback of commutative-ring sheaves is an isomorphism. -/
private instance pullbackRingSheafComparisonInvHom_isIso
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    IsIso (pullbackRingSheafComparisonInvHom (JC := JC) (JD := JD) F O) := by
  -- Proof comment: after identifying the raw comparison with the comparison isomorphism's
  -- underlying morphism, the `IsIso` instance is inherited directly.
  dsimp [pullbackRingSheafComparisonInvHom]
  infer_instance

/-- Helper for Lemma 18.33.5: pullback of a commutative-ring sheaf along `F` commutes with
forgetting to `RingCat`. -/
private noncomputable def pullbackCommRingSheaf_ringSheaf_iso
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) ≅
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) := by
  -- Proof comment: this is exactly the canonical comparison iso already produced above.
  exact pullbackCommRingSheaf_ringSheaf_iso_of_preserves (JC := JC) (JD := JD) F O

/-- The canonical ring-sheaf comparison between pulling back before or after forgetting
commutativity. -/
noncomputable abbrev pullbackRingSheafIso
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) ≅
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) :=
  pullbackCommRingSheaf_ringSheaf_iso F O

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

local notation "FComm" => F.sheafPullback CommRingCat JC JD
local notation "FRing" => F.sheafPullback RingCat JC JD

-- Proof sketch: write `Ω(φ)` as the sheafification of the presheaf of relative differentials from
-- Lemma `18.33.2`, pull that presentation back along the inverse-image functor, and use exactness
-- of inverse image together with the objectwise identities
-- `f^{-1}(O₂[O₂]) = f^{-1}O₂[f^{-1}O₂]`,
-- `f^{-1}(O₂[O₂ × O₂]) = f^{-1}O₂[f^{-1}O₂ × f^{-1}O₂]`, and
-- `f^{-1}(O₂[O₁]) = f^{-1}O₂[f^{-1}O₁]`. This identifies the actual inverse image of `Ω(φ)` with
-- the canonical pulled-back owner
-- `(SheafOfModules.restrictScalars (pullbackRingSheafIso F O₂).inv).obj
--   Ω((F.sheafPullback CommRingCat JC JD).map φ)`.
/-- Lemma 18.33.5: the actual inverse image of `Ω(φ)` is canonically isomorphic to the
relative-differentials owner for `(F.sheafPullback CommRingCat JC JD).map φ`, transported to the
raw pulled-back `RingCat`-valued structure sheaf. -/
noncomputable abbrev inverseImage_relativeDifferentialsIso :
    (SheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂))).obj
      (relativeDifferentialsLocal (J := JC) φ) ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafIso F O₂).inv).obj
        (relativeDifferentialsLocal (J := JD) ((F.sheafPullback CommRingCat JC JD).map φ)) :=
  -- Route correction: the presheaf-presentation chain has been abandoned. The next proof should
  -- construct the comparison by the universal property of relative differentials, exactly as in
  -- the opens-site specialization, and then prove it is an isomorphism by representer
  -- uniqueness rather than by repairing cokernel transport.
  -- TODO: define the pulled-back universal derivation, prove the transported actual inverse image
  -- represents derivations for `(FComm.map φ)`, and extract the canonical iso between the two
  -- representers.
  sorry

end

end SheafOfModules.RingedSite
