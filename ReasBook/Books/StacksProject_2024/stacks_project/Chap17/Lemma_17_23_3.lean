import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

section AnnihilatorPrelude

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

/-- Helper for Lemma 17.23.3: the structure-sheaf module should be identified with the ambient
tensor unit before defining the canonical self-action map. -/
private noncomputable def structureUnitIsoTensorUnit :
    𝒪X ≅ (𝟙_ ModX) :=
  -- Proof comment: reuse the Chapter 17 tensor-unit owner rather than duplicating the reflective
  -- monoidal comparison in this file.
  SheafOfModules.unitIsoTensorUnit (R := RingedSpace.ringCatSheaf X)

/-- Helper for Lemma 17.23.3: the canonical self-action map whose kernel defines the annihilator
sheaf. -/
noncomputable def selfInternalHomUnitMap (ℱ : ModX) : 𝒪X ⟶ (ihom ℱ).obj ℱ :=
  structureUnitIsoTensorUnit.hom ≫ MonoidalClosed.id ℱ

/-- Helper for Lemma 17.23.3: the annihilator sheaf of `\mathcal F`. -/
abbrev annihilator (ℱ : ModX) : ModX :=
  kernel (selfInternalHomUnitMap ℱ)

namespace AnnihilatorSheaf

scoped notation:max "Ann(" ℱ ")" => SheafOfModules.annihilator ℱ

end AnnihilatorSheaf

open scoped AnnihilatorSheaf

/-- Helper for Lemma 17.23.3: the annihilator sheaf includes canonically into the structure
sheaf. -/
noncomputable abbrev annihilatorι (ℱ : ModX) : Ann(ℱ) ⟶ 𝒪X :=
  kernel.ι (selfInternalHomUnitMap ℱ)

/-- Helper for Lemma 17.23.3: a local annihilator section viewed as a section of the structure
sheaf. -/
abbrev annihilatorSectionImage (ℱ : ModX) (U : Opens X)
    (s : (Ann(ℱ)).val.obj (op U)) : X.presheaf.obj (op U) :=
  unitSectionToRingSection U ((annihilatorι ℱ).val.app (op U) s)

/-- Helper for Lemma 17.23.3: `unitHomEquiv` on the slice over `U` is computed by evaluating the
underlying morphism at the terminal object `U → U`. -/
private theorem unitHomEquiv_apply_terminal
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (f : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M) :
    (M.unitHomEquiv f).1 (op (Over.mk (𝟙 U))) =
      (f.val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj
            (op (Over.mk (𝟙 U)))) from (1 : X.presheaf.obj (op U))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluation on the terminal section of the slice.
  rfl

/-- Helper for Lemma 17.23.3: a value of the internal-Hom sheaf on `U` determines a section of
the restricted internal-Hom sheaf on the slice over `U`. -/
private noncomputable def internalHomObjEquivOverHom₁
    (ℱ 𝒢 : ModX) (U : Opens X) :
    ((ℱ ⟶[ModX] 𝒢).val.obj (op U)) ≃ ((ℱ ⟶[ModX] 𝒢).over U).sections := by
  -- Proof comment: sections over the slice are recovered by evaluating at the terminal object.
  simpa using (RingedSpace.over_sections_equiv_evaluation ((ℱ ⟶[ModX] 𝒢).over U)).symm

/-- Helper for Lemma 17.23.3: a section of the restricted internal-Hom sheaf is the same as a
morphism from the unit object on the slice over `U`. -/
private noncomputable def internalHomObjEquivOverHom₂
    (ℱ 𝒢 : ModX) (U : Opens X) :
    ((ℱ ⟶[ModX] 𝒢).over U).sections ≃
      (SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ((ℱ ⟶[ModX] 𝒢).over U)) :=
  (((ℱ ⟶[ModX] 𝒢).over U).unitHomEquiv).symm

/-- Helper for Lemma 17.23.3: internal-Hom sections on the slice over `U` correspond to local
module morphisms `ℱ|_U → 𝒢|_U`. -/
private noncomputable def internalHomObjEquivOverHom₃
    (ℱ 𝒢 : ModX) (U : Opens X) :
    (SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ((ℱ ⟶[ModX] 𝒢).over U)) ≃
      (ℱ.over U ⟶ 𝒢.over U) :=
  (((ihom (ℱ.over U)).obj (𝒢.over U)).unitHomEquiv).symm

/-- Helper for Lemma 17.23.3: the value of the internal-Hom sheaf on `U` is the same as a local
module morphism `ℱ|_U → 𝒢|_U`. -/
private noncomputable def internalHomObjEquivOverHom
    (ℱ 𝒢 : ModX) (U : Opens X) :
    ((ℱ ⟶[ModX] 𝒢).val.obj (op U)) ≃ (ℱ.over U ⟶ 𝒢.over U) :=
  -- Proof comment: pass from a section over `U` to a slice section, then to a unit morphism, and
  -- finally uncurry to an honest local module map.
  (internalHomObjEquivOverHom₁ ℱ 𝒢 U).trans
    ((internalHomObjEquivOverHom₂ ℱ 𝒢 U).trans
      (internalHomObjEquivOverHom₃ ℱ 𝒢 U))

/-- Helper for Lemma 17.23.3: evaluating the sectionwise component of the canonical self-action
map on a local ring section is ordinary scalar multiplication on `\mathcal F(U)`. -/
private theorem selfInternalHomUnitMap_app_apply
    (ℱ : ModX) (U : Opens X) (a : X.presheaf.obj (op U)) (m : ℱ.val.obj (op U)) :
    ((((internalHomObjEquivOverHom ℱ ℱ U)
        (ModuleCat.Hom.hom ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U)) a)).val.app
      (op (Over.mk (𝟙 U)))) m) =
      unitSectionToRingSection U a • m := by
  -- Proof comment: transport the internal-Hom value on `U` to the corresponding local
  -- endomorphism of `ℱ|_U`, then evaluate that map on the terminal slice object.
  simpa [internalHomObjEquivOverHom, internalHomObjEquivOverHom₁,
    internalHomObjEquivOverHom₂, internalHomObjEquivOverHom₃,
    RingedSpace.over_sections_equiv_evaluation, unitHomEquiv_apply_terminal,
    SheafOfModules.selfInternalHomUnitMap, MonoidalClosed.id]

end AnnihilatorPrelude

/- Domain-style sampling for Lemma 17.23.3:
- primary domain: quotient sheaves of rings and descended module structures for ideal sheaves
  contained in the annihilator sheaf of an `\mathcal O_X`-module;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `SheafOfModules.annihilator`,
  `SheafOfModules.annihilatorι`,
  `AlgebraicGeometry.Scheme.IdealSheafData`,
  `SheafOfModules.selfInternalHomUnitMap`,
  `PresheafOfModules.ofPresheaf`,
  `Module.IsTorsionBySet.module`;
- best owner abstraction: the source-facing owner should be the actual quotient sheaf of
  commutative rings `\mathcal O_X / \mathcal I` together with the descended
  `(\mathcal O_X / \mathcal I)`-module structure on `\mathcal F`, and its natural owner on the
  ringed-space side is the actual ideal-sheaf inclusion `I : Subobject 𝒪X` together with the
  inclusion `I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)` into the chapter owner
  `annihilator ℱ`;
- primitive data:
  the quotient owner only needs an ideal sheaf `I : Subobject 𝒪X`; the descended-module bridge
  additionally needs a module sheaf `ℱ` and an inclusion
  `hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)`;
- derived API:
  the sectionwise ideals `idealSectionIdeal I U`, the quotient sheaf `quotientCommRingSheaf I`,
  the descended module `quotientModule I ℱ hI`, and the representative-level section/stalk
  formulas.

Source/core/bridge triage:
- `source-facing`: the quotient sheaf `\mathcal O_X / \mathcal I` and the induced
  `(\mathcal O_X / \mathcal I)`-module structure on `\mathcal F`;
- `core/canonical`: `Subobject 𝒪X`, `Subobject.arrow`, `annihilator`, `annihilatorι`,
  `kernelSubobject`, the presheaf constructor `PresheafOfModules.ofPresheaf`, and
  quotient-module descent via `Module.IsTorsionBySet.module`;
- `bridge/view`: the sectionwise ideal family and the section/stalk comparison lemmas expressing
  the descended action in terms of representatives, together with the internal bridge from
  `I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)` to the zero-composite condition needed by the
  kernel presentation of `annihilator ℱ`. -/

private noncomputable instance sectionModule
    (ℱ : ModX) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) (ℱ.val.presheaf.obj U) :=
  inferInstanceAs (Module (X.presheaf.obj U) (ℱ.val.obj U))

/-- The ideal of `\mathcal O_X(U)` generated by the image of `\mathcal I(U)` under the ideal-sheaf
inclusion. -/
noncomputable def idealSectionIdeal
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) :
    Ideal (X.presheaf.obj U) :=
  Ideal.span <| Set.range fun s : (I : ModX).val.obj U ↦
    unitSectionToRingSection (Opposite.unop U) (((Hom.val I.arrow).app U) s)

/-- Restriction maps preserve the sectionwise ideals defined by the ideal sheaf. -/
private theorem idealSectionIdeal_le_comap
    (I : Subobject 𝒪X) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    idealSectionIdeal I U ≤ (idealSectionIdeal I V).comap (X.presheaf.map f).hom := by
  -- Proof comment: it is enough to check the generators, and naturality of the ideal-sheaf
  -- inclusion identifies the restriction of a generator with the generator coming from the
  -- restricted section.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨s, rfl⟩
  refine Ideal.subset_span ?_
  refine ⟨(I : ModX).val.map f s, ?_⟩
  have hnat := congrArg (fun g => ModuleCat.Hom.hom g s) ((Hom.val I.arrow).naturality f)
  change
    unitSectionToRingSection V.unop (((Hom.val I.arrow).app V) ((I : ModX).val.map f s)) =
      (X.presheaf.map f).hom
        (unitSectionToRingSection U.unop (((Hom.val I.arrow).app U) s))
  simpa [SheafOfModules.unitSectionToRingSection] using hnat

/-- The quotient presheaf of commutative rings `\mathcal O_X / \mathcal I`. -/
private noncomputable def quotientCommRingPresheaf
    (I : Subobject 𝒪X) :
    (Opens X)ᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (X.presheaf.obj U ⧸ idealSectionIdeal I U)
  map {U V} f := CommRingCat.ofHom <|
    Ideal.quotientMap (idealSectionIdeal I V) (X.presheaf.map f).hom
      (idealSectionIdeal_le_comap I f)
  map_id U := by
    -- Proof comment: both quotient maps send a representative to its own quotient class.
    ext r
    simp [Ideal.quotientMap_mk]
  map_comp f g := by
    -- Proof comment: on representatives, both sides are the quotient class of the twice-restricted
    -- section, so the functor law reduces to the presheaf functor law on `X.presheaf`.
    ext r
    simp [Ideal.quotientMap_mk, RingHom.comp_apply, Functor.map_comp]

/-- Helper for Lemma 17.23.3: the quotient presheaf is a sheaf once its underlying set-valued
presheaf is known to satisfy the sheaf condition. -/
private theorem quotientCommRingPresheaf_isSheaf_of_forget
    (I : Subobject 𝒪X)
    (h :
      TopCat.Presheaf.IsSheaf
        (quotientCommRingPresheaf I ⋙ CategoryTheory.forget CommRingCat)) :
    TopCat.Presheaf.IsSheaf (quotientCommRingPresheaf I) := by
  -- Proof comment: the forgetful functor from commutative rings to types preserves limits and
  -- reflects isomorphisms, so it detects the sheaf condition.
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget CommRingCat) _).2 h

/-- Helper for Lemma 17.23.3: the image of the sectionwise inclusion `\mathcal I(U) \to
\mathcal O_X(U)` is itself an ideal of the section ring. -/
private noncomputable def idealSectionImageIdeal
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) :
    Ideal (X.presheaf.obj U) :=
  { carrier := Set.range
      (fun s : (I : ModX).val.obj U ↦
        unitSectionToRingSection (Opposite.unop U) (((Hom.val I.arrow).app U) s))
    zero_mem' := by
      refine ⟨0, ?_⟩
      simpa [SheafOfModules.unitSectionToRingSection] using
        congrArg (unitSectionToRingSection (Opposite.unop U))
          (map_zero ((Hom.val I.arrow).app U).hom)
    add_mem' := by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      simpa [SheafOfModules.unitSectionToRingSection] using
        congrArg (unitSectionToRingSection (Opposite.unop U))
          (map_add ((Hom.val I.arrow).app U).hom a b)
    smul_mem' := by
      rintro r _ ⟨a, rfl⟩
      refine ⟨r • a, ?_⟩
      simpa [SheafOfModules.unitSectionToRingSection] using
        congrArg (unitSectionToRingSection (Opposite.unop U))
          (map_smul ((Hom.val I.arrow).app U).hom r a) }

/-- Helper for Lemma 17.23.3: sectionwise, the ideal generated by `\mathcal I(U)` is already the
actual image ideal of the inclusion `\mathcal I(U) \to \mathcal O_X(U)`. -/
private theorem idealSectionIdeal_eq_sectionImageIdeal
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) :
    idealSectionIdeal I U = idealSectionImageIdeal I U := by
  -- Proof comment: after rewriting the generators as the underlying set of the image ideal, the
  -- span collapses to that ideal itself.
  calc
    idealSectionIdeal I U = Ideal.span (idealSectionImageIdeal I U : Set (X.presheaf.obj U)) := by
      change
        Ideal.span
            (Set.range
              (fun s : (I : ModX).val.obj U ↦
                unitSectionToRingSection (Opposite.unop U) (((Hom.val I.arrow).app U) s))) =
          Ideal.span (idealSectionImageIdeal I U : Set (X.presheaf.obj U))
      rfl
    _ = idealSectionImageIdeal I U := by rw [Ideal.span_eq]

/-- Helper for Lemma 17.23.3: sectionwise, the ideal cut out by `\mathcal I` is the same
submodule as the image of the section map `\mathcal I(U) \to \mathcal O_X(U)`. -/
private theorem idealSectionIdeal_toSubmodule_eq_range
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) :
    (idealSectionIdeal I U : Submodule (X.presheaf.obj U) (X.presheaf.obj U)) =
      LinearMap.range (((Hom.val I.arrow).app U).hom) := by
  -- Proof comment: first replace the generated ideal by the actual image ideal, then compare both
  -- submodules by unraveling the two `Set.range` descriptions of the image.
  ext r
  rw [idealSectionIdeal_eq_sectionImageIdeal]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact hs

/-- Helper for Lemma 17.23.3: on each open set, the explicit quotient
`\mathcal O_X(U) / \mathcal I(U)` agrees with the value of the cokernel sheaf of `I.arrow`. -/
private theorem quotientSectionRangeObj_eq
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) :
    ModuleCat.of (X.presheaf.obj U) (X.presheaf.obj U ⧸ idealSectionIdeal I U) =
      ModuleCat.of (X.presheaf.obj U)
        (X.presheaf.obj U ⧸ LinearMap.range (((Hom.val I.arrow).app U).hom)) := by
  -- Proof comment: normalize the sectionwise ideal to the actual range of the inclusion map
  -- before invoking the standard module-theoretic cokernel comparison.
  rw [idealSectionIdeal_toSubmodule_eq_range]

/-- Helper for Lemma 17.23.3: on each open set, the explicit quotient
`\mathcal O_X(U) / \mathcal I(U)` agrees with the value of the cokernel sheaf of `I.arrow`. -/
private noncomputable def quotientSectionIsoCokernelSection
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) :
    ModuleCat.of (X.presheaf.obj U) (X.presheaf.obj U ⧸ idealSectionIdeal I U) ≅
      (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) U).obj
        (cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)) :=
  -- Proof comment: first rewrite the sectionwise quotient into range normal form, then identify it
  -- with the ordinary module cokernel and finally transport back to the evaluated sheaf cokernel.
  eqToIso (quotientSectionRangeObj_eq I U) ≪≫
    (ModuleCat.cokernelIsoRangeQuotient
      ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) U).map
        (I.arrow : (I : ModX) ⟶ 𝒪X))).symm ≪≫
    (PreservesCokernel.iso
      (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) U)
      (I.arrow : (I : ModX) ⟶ 𝒪X)).symm

/-- Helper for Lemma 17.23.3: the sectionwise comparison sends a quotient class to the image of
the corresponding representative in the cokernel sheaf. -/
private theorem quotientSectionIsoCokernelSection_hom_mk
    (I : Subobject 𝒪X) (U : (Opens X)ᵒᵖ) (r : X.presheaf.obj U) :
    ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map
        (quotientSectionIsoCokernelSection I U).hom)
        (Ideal.Quotient.mk (idealSectionIdeal I U) r) =
      (((Hom.val (cokernel.π (I.arrow : (I : ModX) ⟶ 𝒪X))).app U) r) := by
  let evalU := SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) U
  let f : evalU.obj (I : ModX) ⟶ evalU.obj 𝒪X :=
    evalU.map (I.arrow : (I : ModX) ⟶ 𝒪X)
  let eRange :
      ModuleCat.of (X.presheaf.obj U) (X.presheaf.obj U ⧸ idealSectionIdeal I U) ≅
        ModuleCat.of (X.presheaf.obj U)
          (X.presheaf.obj U ⧸ LinearMap.range (((Hom.val I.arrow).app U).hom)) :=
    eqToIso (quotientSectionRangeObj_eq I U)
  have hRange :
      ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map eRange.hom)
          (Ideal.Quotient.mk (idealSectionIdeal I U) r) =
        Ideal.Quotient.mk (LinearMap.range (((Hom.val I.arrow).app U).hom)) r := by
    -- Proof comment: the range-normalization isomorphism is induced by an equality of quotient
    -- module objects, so it is the identity on representatives after substituting that equality.
    cases quotientSectionRangeObj_eq I U
    rfl
  have hCokernel :
      ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map
          (ModuleCat.cokernelIsoRangeQuotient f).inv)
          (Ideal.Quotient.mk (LinearMap.range (((Hom.val I.arrow).app U).hom)) r) =
        (cokernel.π f) r := by
    -- Proof comment: the inverse of the range-quotient cokernel comparison sends a quotient class
    -- to the corresponding cokernel projection class.
    simpa [f] using congrArg
      (fun g =>
        ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map g)
          (Ideal.Quotient.mk (LinearMap.range (((Hom.val I.arrow).app U).hom)) r))
      (ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv (f := f))
  have hPreserve :
      ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map
          (PreservesCokernel.iso evalU (I.arrow : (I : ModX) ⟶ 𝒪X)).inv)
          ((cokernel.π f) r) =
        (((Hom.val (cokernel.π (I.arrow : (I : ModX) ⟶ 𝒪X))).app U) r) := by
    -- Proof comment: the inverse preserved-cokernel comparison identifies the ordinary cokernel
    -- class of the evaluated map with the image of the same representative in the sheaf cokernel.
    have hπ := congrArg
      (fun g => ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map g) r)
      (PreservesCokernel.π_iso_hom
        (G := evalU) (f := (I.arrow : (I : ModX) ⟶ 𝒪X)))
    simpa [evalU, f, Functor.map_comp] using congrArg
      (((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map
          (PreservesCokernel.iso evalU (I.arrow : (I : ModX) ⟶ 𝒪X)).inv))
      hπ
  -- Proof comment: assemble the three explicit transports in the same order as the defining
  -- composite of `quotientSectionIsoCokernelSection`.
  rw [show quotientSectionIsoCokernelSection I U =
      eRange ≪≫ (ModuleCat.cokernelIsoRangeQuotient f).symm ≪≫
        (PreservesCokernel.iso evalU (I.arrow : (I : ModX) ⟶ 𝒪X)).symm by
        rfl]
  simp only [Iso.trans_hom, Category.assoc, Functor.map_comp]
  rw [hRange, hCokernel, hPreserve]

/-- Helper for Lemma 17.23.3: the sectionwise underlying-type comparison is natural with respect
to restriction maps once both sides are rewritten on quotient representatives. -/
private theorem quotientCommRingPresheafForgetIsoCokernel_naturality
    (I : Subobject 𝒪X) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (quotientCommRingPresheaf I ⋙ CategoryTheory.forget CommRingCat).map f ≫
        ((CategoryTheory.forget (ModuleCat (X.presheaf.obj V))).map
          (quotientSectionIsoCokernelSection I V).hom) =
      ((CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).map
        (quotientSectionIsoCokernelSection I U).hom) ≫
          ((cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)).val.presheaf ⋙
            CategoryTheory.forget AddCommGrpCat).map f := by
  ext r
  refine Quotient.inductionOn' r ?_
  intro r
  -- Proof comment: both sides are determined by the same restriction of the cokernel projection
  -- once the sectionwise comparison is rewritten on representatives.
  rw [Ideal.quotientMap_mk, quotientSectionIsoCokernelSection_hom_mk,
    quotientSectionIsoCokernelSection_hom_mk]
  exact congrArg (fun g => g r) ((Hom.val (cokernel.π (I.arrow : (I : ModX) ⟶ 𝒪X))).naturality f)

/-- Helper for Lemma 17.23.3: the explicit quotient presheaf of rings is canonically isomorphic,
after forgetting to types, to the underlying presheaf of the cokernel sheaf of `I.arrow`. -/
private noncomputable def quotientCommRingPresheafForgetIsoCokernel
    (I : Subobject 𝒪X) :
    quotientCommRingPresheaf I ⋙ CategoryTheory.forget CommRingCat ≅
      (cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)).val.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat :=
  -- Proof comment: package the sectionwise quotient/cokernel comparisons into a presheaf
  -- isomorphism after forgetting both sides to their underlying additive groups.
  NatIso.ofComponents
    (fun U =>
      (CategoryTheory.forget (ModuleCat (X.presheaf.obj U))).mapIso
        (quotientSectionIsoCokernelSection I U))
    (quotientCommRingPresheafForgetIsoCokernel_naturality I)

/-- The quotient sheaf of commutative rings `\mathcal O_X / \mathcal I`. -/
noncomputable def quotientCommRingSheaf
    (I : Subobject 𝒪X) :
    TopCat.Sheaf CommRingCat X :=
  ⟨quotientCommRingPresheaf I, by
    -- Route correction: the explicit quotient presheaf should be compared with the
    -- module-theoretic cokernel of `I.arrow`; direct cover-gluing introduces an unnecessary
    -- cocycle argument.
    have hforget :
        TopCat.Presheaf.IsSheaf
          (quotientCommRingPresheaf I ⋙ CategoryTheory.forget CommRingCat) := by
      have hcokernel :
          TopCat.Presheaf.IsSheaf
            ((cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)).val.presheaf ⋙
              CategoryTheory.forget AddCommGrpCat) := by
        -- Proof comment: the cokernel already lives in the category of sheaves of modules, so its
        -- underlying presheaf of abelian groups is a sheaf, hence also after forgetting to types.
        exact
          (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
            (CategoryTheory.forget AddCommGrpCat)
            ((cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)).val.presheaf)).1
            (cokernel (I.arrow : (I : ModX) ⟶ 𝒪X)).isSheaf
      -- Proof comment: transport the sheaf condition across the explicit presheaf isomorphism
      -- between the quotient ring presheaf and the underlying cokernel presheaf.
      exact TopCat.Presheaf.isSheaf_of_iso
        (quotientCommRingPresheafForgetIsoCokernel I).symm hcokernel
    exact quotientCommRingPresheaf_isSheaf_of_forget I hforget⟩

/-- The quotient sheaf `\mathcal O_X / \mathcal I`, viewed as a `RingCat`-valued sheaf. -/
abbrev quotientRingSheaf
    (I : Subobject 𝒪X) :
    TopCat.Sheaf RingCat X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj
    (quotientCommRingSheaf I)

namespace QuotientRingSheaf

scoped notation:35 "𝒪[" X "]" " ⧸ " I:34 => @SheafOfModules.quotientRingSheaf X I

end QuotientRingSheaf

open scoped QuotientRingSheaf

private theorem isTorsionByIdealSectionIdeal_iff
    (I : Subobject 𝒪X) (ℱ : ModX) (U : (Opens X)ᵒᵖ) :
    Module.IsTorsionBySet (X.presheaf.obj U) (ℱ.val.presheaf.obj U)
        ((idealSectionIdeal I U : Set (X.presheaf.obj U))) ↔
      (idealSectionIdeal I U : Set (X.presheaf.obj U)) ⊆
        ↑(Module.annihilator (X.presheaf.obj U) (ℱ.val.presheaf.obj U)) :=
  @Module.isTorsionBySet_iff_subset_annihilator
    (X.presheaf.obj U) (ℱ.val.presheaf.obj U) _ _ _
    ((idealSectionIdeal I U : Set (X.presheaf.obj U)))

section QuotientModule

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

/-- Helper for Lemma 17.23.3: any section of the annihilator sheaf acts trivially on sections of
`\mathcal F` over the same open set. -/
private theorem annihilatorSectionActsZero
    (ℱ : ModX) (U : Opens X) (s : (annihilator ℱ).val.obj (op U)) (m : ℱ.val.obj (op U)) :
    annihilatorSectionImage ℱ U s • m = 0 := by
  have hzero : annihilatorι ℱ ≫ selfInternalHomUnitMap ℱ = 0 :=
    kernel.condition (selfInternalHomUnitMap ℱ)
  -- Proof comment: evaluate the kernel condition on the chosen open set to see that the
  -- annihilator section is sent to the zero endomorphism of `ℱ(U)`.
  have hval :
      (Hom.val (annihilatorι ℱ ≫ selfInternalHomUnitMap ℱ)) = 0 := by
    exact congrArg Hom.val hzero
  have hcomp :
      ((Hom.val (annihilatorι ℱ)).app (op U)) ≫
          ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U)) = 0 := by
    change (Hom.val (annihilatorι ℱ ≫ selfInternalHomUnitMap ℱ)).app (op U) = 0
    simpa using congrArg (fun α => α.app (op U)) hval
  have hsection_zero :
      internalHomObjEquivOverHom ℱ ℱ U
          (ModuleCat.Hom.hom ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U))
            (((Hom.val (annihilatorι ℱ)).app (op U)) s)) = 0 := by
    -- Proof comment: first evaluate the self-action component on the annihilator section, then
    -- transport the resulting internal-Hom value to the corresponding local endomorphism.
    exact congrArg (internalHomObjEquivOverHom ℱ ℱ U) <|
      congrArg
        (fun g => ModuleCat.Hom.hom g (((Hom.val (annihilatorι ℱ)).app (op U)) s))
        hcomp
  have happly :
      ((((internalHomObjEquivOverHom ℱ ℱ U)
          (ModuleCat.Hom.hom ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U))
            (((Hom.val (annihilatorι ℱ)).app (op U)) s))).val.app
        (op (Over.mk (𝟙 U)))) m = 0 := by
    -- Proof comment: evaluate the vanishing local endomorphism on the terminal slice object and
    -- then on the chosen local section of `ℱ`.
    exact congrArg
      (fun g => ((g.val.app (op (Over.mk (𝟙 U)))) m))
      hsection_zero
  -- Route correction: rewrite the component of `selfInternalHomUnitMap` through the dedicated
  -- section-evaluation lemma before identifying the resulting scalar action with
  -- `annihilatorSectionImage`.
  rw [selfInternalHomUnitMap_app_apply] at happly
  simpa [annihilatorSectionImage] using happly

private theorem arrow_comp_selfInternalHomUnitMap_eq_zero
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) :
    I.arrow ≫ selfInternalHomUnitMap ℱ = 0 := by
  rw [← Subobject.ofLE_arrow hI, Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 17.23.3: a local section coming from the ideal sheaf acts trivially on
`\mathcal F(U)` once the ideal sheaf is contained in the annihilator kernel. -/
  private theorem factorSectionActsZero
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ))
    (U : Opens X) (s : (I : ModX).val.obj (op U)) (m : ℱ.val.obj (op U)) :
    unitSectionToRingSection U (((Hom.val I.arrow).app (op U)) s) • m = 0 := by
  let ι : (I : ModX) ⟶ annihilator ℱ :=
    (Subobject.ofLE (X := I) (Y := kernelSubobject (selfInternalHomUnitMap ℱ)) hI) ≫
      (kernelSubobjectIso (selfInternalHomUnitMap ℱ)).hom
  have hfac : ι ≫ annihilatorι ℱ = I.arrow := by
    -- Proof comment: the comparison morphism into the annihilator is the canonical factorization
    -- of `I.arrow` through the kernel inclusion.
    simpa [ι, annihilator, annihilatorι, Category.assoc] using
      congrArg
        (fun g => (Subobject.ofLE (X := I)
          (Y := kernelSubobject (selfInternalHomUnitMap ℱ)) hI) ≫ g)
        (kernelSubobject_arrow (f := selfInternalHomUnitMap ℱ))
  have himage :
      annihilatorSectionImage ℱ U (((Hom.val ι).app (op U)) s) =
        unitSectionToRingSection U (((Hom.val I.arrow).app (op U)) s) := by
    -- Proof comment: evaluate the factorization identity on the chosen section of `I(U)`.
    have hval : Hom.val (ι ≫ annihilatorι ℱ) = Hom.val I.arrow := by
      exact congrArg Hom.val hfac
    have happly :
        (((Hom.val (ι ≫ annihilatorι ℱ)).app (op U)) s) =
          (((Hom.val I.arrow).app (op U)) s) := by
      simpa using congrArg (fun α => α.app (op U) s) hval
    simpa [annihilatorSectionImage, Category.assoc] using happly
  -- Proof comment: after transporting the section into `Ann(ℱ)`, the already-proved annihilator
  -- action lemma gives the desired vanishing.
  rw [← himage]
  exact annihilatorSectionActsZero ℱ U (((Hom.val ι).app (op U)) s) m

/-- Every local section of the ideal generated by `\mathcal I(U)` annihilates
`\mathcal F(U)`. -/
theorem idealSectionIdeal_le_sectionAnnihilator
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) (U : (Opens X)ᵒᵖ) :
    idealSectionIdeal I U ≤ Module.annihilator (X.presheaf.obj U) (ℱ.val.presheaf.obj U) := by
  -- Route correction: the needed sectionwise vanishing already follows from evaluating the kernel
  -- equation `I.arrow ≫ selfInternalHomUnitMap ℱ = 0` on local sections; no extra internal-Hom
  -- comparison lemma is needed here.
  rw [idealSectionIdeal_eq_sectionImageIdeal]
  intro r hr
  rw [Module.mem_annihilator]
  intro m
  rcases hr with ⟨s, rfl⟩
  -- Proof comment: reduce to a generator of the image ideal and apply the sectionwise zero-action
  -- lemma obtained from the kernel condition.
  exact factorSectionActsZero I ℱ hI U.unop s m

noncomputable instance quotientSectionModule
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U ⧸ idealSectionIdeal I U) (ℱ.val.presheaf.obj U) := by
  let htors :
      Module.IsTorsionBySet (X.presheaf.obj U) (ℱ.val.presheaf.obj U)
        ((idealSectionIdeal I U : Set (X.presheaf.obj U))) :=
    (isTorsionByIdealSectionIdeal_iff I ℱ U).2
      (idealSectionIdeal_le_sectionAnnihilator I ℱ hI U)
  simpa [quotientRingSheaf, quotientCommRingPresheaf] using htors.module

private theorem quotientModulePresheaf_map_smul
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ))
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (r : (𝒪[X] ⧸ I).obj.obj U) (m : ℱ.val.presheaf.obj U) :
    letI _ : Module ((𝒪[X] ⧸ I).obj.obj U) (ℱ.val.presheaf.obj U) :=
      quotientSectionModule I ℱ hI U
    letI _ : Module ((𝒪[X] ⧸ I).obj.obj V) (ℱ.val.presheaf.obj V) :=
      quotientSectionModule I ℱ hI V
    ℱ.val.presheaf.map f (r • m) =
      (𝒪[X] ⧸ I).obj.map f r • ℱ.val.presheaf.map f m := by
  letI : Module ((𝒪[X] ⧸ I).obj.obj U) (ℱ.val.presheaf.obj U) :=
    quotientSectionModule I ℱ hI U
  letI : Module ((𝒪[X] ⧸ I).obj.obj V) (ℱ.val.presheaf.obj V) :=
    quotientSectionModule I ℱ hI V
  letI : Module (X.presheaf.obj U ⧸ idealSectionIdeal I U) (ℱ.val.presheaf.obj U) :=
    quotientSectionModule I ℱ hI U
  letI : Module (X.presheaf.obj V ⧸ idealSectionIdeal I V) (ℱ.val.presheaf.obj V) :=
    quotientSectionModule I ℱ hI V
  let htorsU :
      Module.IsTorsionBySet (X.presheaf.obj U) (ℱ.val.presheaf.obj U)
        ((idealSectionIdeal I U : Set (X.presheaf.obj U))) :=
    (isTorsionByIdealSectionIdeal_iff I ℱ U).2
      (idealSectionIdeal_le_sectionAnnihilator I ℱ hI U)
  let htorsV :
      Module.IsTorsionBySet (X.presheaf.obj V) (ℱ.val.presheaf.obj V)
        ((idealSectionIdeal I V : Set (X.presheaf.obj V))) :=
    (isTorsionByIdealSectionIdeal_iff I ℱ V).2
      (idealSectionIdeal_le_sectionAnnihilator I ℱ hI V)
  -- Proof comment: descend the original `𝒪_X`-linearity of restriction maps from representatives
  -- in `𝒪_X(U)` to quotient classes by induction on the scalar.
  refine Quotient.inductionOn' r ?_
  intro r
  change ℱ.val.presheaf.map f
      ((Ideal.Quotient.mk (idealSectionIdeal I U) r :
          (𝒪[X] ⧸ I).obj.obj U) • m) =
    (𝒪[X] ⧸ I).obj.map f (Ideal.Quotient.mk (idealSectionIdeal I U) r) •
      ℱ.val.presheaf.map f m
  -- Proof comment: each quotient action on a representative is definitionally the original scalar
  -- action supplied by the torsion-by-ideal module structure.
  have hmkU :
      ((Ideal.Quotient.mk (idealSectionIdeal I U) r : (𝒪[X] ⧸ I).obj.obj U) • m) = r • m := by
    simpa [quotientRingSheaf, quotientCommRingPresheaf] using
      Module.IsTorsionBySet.mk_smul htorsU r m
  have hmkV :
      ((𝒪[X] ⧸ I).obj.map f (Ideal.Quotient.mk (idealSectionIdeal I U) r)) •
          ℱ.val.presheaf.map f m =
        (X.presheaf.map f).hom r • ℱ.val.presheaf.map f m := by
    simpa [quotientRingSheaf, quotientCommRingPresheaf, Ideal.quotientMap_mk] using
      Module.IsTorsionBySet.mk_smul htorsV ((X.presheaf.map f).hom r) (ℱ.val.presheaf.map f m)
  rw [hmkU, hmkV]
  simpa using PresheafOfModules.map_smul (M := ℱ.val) f r m

/-- The underlying presheaf of the descended `(\mathcal O_X / \mathcal I)`-module structure on
`\mathcal F`. -/
private noncomputable def quotientModulePresheaf
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) :
    PresheafOfModules (𝒪[X] ⧸ I).obj := by
  let _ : ∀ U : (Opens X)ᵒᵖ,
      Module ((𝒪[X] ⧸ I).obj.obj U) (ℱ.val.presheaf.obj U) :=
    quotientSectionModule I ℱ hI
  exact PresheafOfModules.ofPresheaf ℱ.val.presheaf
    (fun {U V} f r m ↦ quotientModulePresheaf_map_smul I ℱ hI f r m)

/-- Lemma 17.23.3: if an ideal sheaf `\mathcal I` is contained in
`\operatorname{Ann}_{\mathcal O_X}(\mathcal F)`, then `\mathcal F` carries the canonical
`(\mathcal O_X / \mathcal I)`-module structure. -/
noncomputable def quotientModule
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) :
    SheafOfModules (𝒪[X] ⧸ I) where
  val := quotientModulePresheaf I ℱ hI
  isSheaf := by
    simpa [quotientModulePresheaf, PresheafOfModules.ofPresheaf_presheaf] using ℱ.isSheaf

noncomputable instance quotientModuleSectionModule
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U ⧸ idealSectionIdeal I U) ↑((quotientModule I ℱ hI).val.obj U) :=
  ((quotientModule I ℱ hI).val.obj U).isModule

noncomputable instance quotientModuleSectionModuleOverOX
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ)) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) ↑((quotientModule I ℱ hI).val.obj U) :=
  sectionModule ℱ U

/-- Sectionwise, the descended quotient action is the usual one: a representative in
`\mathcal O_X(U)` acts through its class exactly as the original local section acted on
`\mathcal F(U)`. -/
theorem quotientModule_mk_smul
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ))
    (U : Opens X) (r : X.presheaf.obj (op U)) (m : (quotientModule I ℱ hI).val.obj (op U)) :
    (Ideal.Quotient.mk (idealSectionIdeal I (op U)) r : (𝒪[X] ⧸ I).obj.obj (op U)) • m =
      r • m := by
  let htors :
      Module.IsTorsionBySet (X.presheaf.obj (op U)) (ℱ.val.presheaf.obj (op U))
        ((idealSectionIdeal I (op U) : Set (X.presheaf.obj (op U)))) :=
    (isTorsionByIdealSectionIdeal_iff I ℱ (op U)).2
      (idealSectionIdeal_le_sectionAnnihilator I ℱ hI (op U))
  simpa [quotientModule, quotientModulePresheaf, quotientRingSheaf, quotientCommRingPresheaf] using
    Module.IsTorsionBySet.mk_smul htors r m

/-- On stalks, the descended quotient action is the usual quotient-module action coming from germs
of representatives. -/
theorem quotientModule_germ_mk_smul
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ kernelSubobject (selfInternalHomUnitMap ℱ))
    (x : X) (U : Opens X) (hx : x ∈ U)
    (r : X.presheaf.obj (op U)) (m : (quotientModule I ℱ hI).val.obj (op U)) :
    TopCat.Presheaf.germ (quotientModule I ℱ hI).val.presheaf U x hx
        ((Ideal.Quotient.mk (idealSectionIdeal I (op U)) r : (𝒪[X] ⧸ I).obj.obj (op U)) • m) =
      TopCat.Presheaf.germ (𝒪[X] ⧸ I).obj U x hx
          (Ideal.Quotient.mk (idealSectionIdeal I (op U)) r) •
        TopCat.Presheaf.germ (quotientModule I ℱ hI).val.presheaf U x hx m := by
  simpa [quotientModule, quotientModulePresheaf] using
    (PresheafOfModules.germ_ringCat_smul (quotientModule I ℱ hI).val x U hx
      (Ideal.Quotient.mk (idealSectionIdeal I (op U)) r) m)

end QuotientModule

end SheafOfModules
