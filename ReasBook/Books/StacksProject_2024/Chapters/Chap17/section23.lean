import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_23_1 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]
variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

/- Domain-style sampling for Definition 17.23.1:
- primary domain: annihilator sheaves of modules on a ringed space, expressed through the
  monoidal closed structure on `SheafOfModules (RingedSpace.ringCatSheaf X)`;
- sampled owner declarations:
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `(RingedSpace.ringCatSheaf AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.unit`,
  `PresheafOfModules.sheafificationAdjunction`,
  `MonoidalClosed.id`,
  `kernel`;
- best owner abstraction:
  the ambient owner is the existing chapter ringed-space coefficient sheaf `(RingedSpace.ringCatSheaf X)`, and
  the source-facing annihilator object should be the categorical kernel in
  `ModX` of the canonical map from the structure sheaf `𝒪X` to `(ihom ℱ).obj ℱ`;
- primitive data: a module sheaf `ℱ`;
- derived API: the canonical inclusion `annihilatorι ℱ : annihilator ℱ ⟶ 𝒪X`, and the
  sectionwise bridge `annihilatorSectionImage`.

Source/core/bridge triage:
- `source-facing`: the annihilator sheaf `annihilator ℱ`;
- `core/canonical`: the ambient module category `ModX`, `𝒪X`, `ihom`, and categorical kernels;
- `bridge/view`: the canonical comparison isomorphism `unitIsoTensorUnit : 𝒪X ≅ 𝟙_ ModX`,
  obtained from the sheafification counit for the presheaf-side unit model of the tensor unit;
  this yields the comparison morphism `unitToTensorUnit`, the resulting inclusion
  `annihilatorι ℱ`, and the sectionwise inclusion `annihilatorSectionImage`.

This file therefore keeps `annihilator` as the source-facing owner and reuses the chapter owner
`(RingedSpace.ringCatSheaf X)` from Definition `17.4.1`, together with the canonical internal-hom
identity map `MonoidalClosed.id ℱ`. The bridge to the ambient tensor unit is the canonical
sheafification-counit comparison, not an equality identification with `𝒪X`. -/

private abbrev tensorUnitModel : ModX :=
  ((SheafOfModules.forget (RingedSpace.ringCatSheaf X) ⋙
      PresheafOfModules.restrictScalars (𝟙 (RingedSpace.ringCatSheaf X).obj)) ⋙
    PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj 𝒪X

-- Proof sketch: the chosen tensor unit in the ambient monoidal structure on `ModX` is the
-- sheafification of the presheaf-side free rank-one module. This is the same owner as the object
-- underlying the counit comparison below.
private theorem tensorUnitModel_eq_tensorUnit :
    tensorUnitModel = (𝟙_ ModX : ModX) := by
  sorry

/-- The canonical comparison isomorphism from the structure sheaf owner `\mathcal O_X` to the
ambient tensor unit in `SheafOfModules (RingedSpace.ringCatSheaf X)`. -/
noncomputable def unitIsoTensorUnit : 𝒪X ≅ 𝟙_ ModX :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (RingedSpace.ringCatSheaf X).obj)).counit.app 𝒪X)).symm ≪≫
    eqToIso tensorUnitModel_eq_tensorUnit

/-- The canonical comparison morphism from the structure sheaf owner `\mathcal O_X` to the
ambient tensor unit in `SheafOfModules (RingedSpace.ringCatSheaf X)`. -/
noncomputable abbrev unitToTensorUnit : 𝒪X ⟶ 𝟙_ ModX :=
  unitIsoTensorUnit.hom

/-- The canonical map `\mathcal O_X \to
\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal F)` whose kernel is the annihilator
sheaf. -/
noncomputable def selfInternalHomUnitMap (ℱ : ModX) : 𝒪X ⟶ (ihom ℱ).obj ℱ :=
  unitToTensorUnit ≫ MonoidalClosed.id ℱ

/-- Definition 17.23.1: the annihilator of an `\mathcal O_X`-module `\mathcal F` is the kernel
of the canonical map `\mathcal O_X \to \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F,
\mathcal F)`. -/
abbrev annihilator (ℱ : ModX) : ModX :=
  kernel (selfInternalHomUnitMap ℱ)

/-- The annihilator sheaf is definitionally the kernel of the canonical action map
`\mathcal O_X \to \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal F)`. -/
theorem annihilator_eq_kernel (ℱ : ModX) :
    annihilator ℱ = kernel (selfInternalHomUnitMap ℱ) :=
  rfl

/-- The annihilator sheaf carries its canonical inclusion into the structure sheaf. -/
noncomputable abbrev annihilatorι (ℱ : ModX) : annihilator ℱ ⟶ 𝒪X :=
  kernel.ι (selfInternalHomUnitMap ℱ)

/-- The annihilator sheaf, viewed canonically as a subobject of the structure sheaf. -/
noncomputable abbrev annihilatorSubobject (ℱ : ModX) : Subobject 𝒪X :=
  Subobject.mk (annihilatorι ℱ)

/-- A local section of the annihilator sheaf, regarded as a section of the structure sheaf via the
kernel inclusion. -/
abbrev annihilatorSectionImage (ℱ : ModX) (U : Opens X)
    (s : (annihilator ℱ).val.obj (op U)) : X.presheaf.obj (op U) :=
  unitSectionToRingSection U ((annihilatorι ℱ).val.app (op U) s)

end SheafOfModules

/-! ### Lemma_17_23_2 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]
variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)

/- Domain-style sampling for Lemma 17.23.2:
- primary domain: annihilator sheaves and their stalkwise comparison with annihilator ideals of
  stalk modules on a ringed space;
- sampled owner declarations:
  `SheafOfModules.annihilator`,
  `SheafOfModules.annihilatorι`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `AlgebraicGeometry.RingedSpace.moduleStalkHom`,
  `AlgebraicGeometry.RingedSpace.unitStalkLinearMap`,
  `AlgebraicGeometry.RingedSpace.internalHomStalkComparison_injective_of_isFiniteType`;
- best owner abstraction:
  the source-facing statement is the equality of ideals in the stalk ring `\mathcal O_{X,x}`;
  the annihilator-sheaf side should therefore be expressed via the chapter owner
  `annihilatorStalkIdeal ℱ x`, built from the canonical inclusion `annihilatorι ℱ`, rather than
  through an ad hoc existential presentation of stalk elements by local sections or a duplicated
  local identification of the unit-module stalk with the stalk ring;
- primitive data:
  a module sheaf `ℱ`, a point `x`, and the finite-type hypothesis on `ℱ`;
- derived API:
  the canonical stalk ideal `annihilatorStalkIdeal ℱ x`, obtained from the inclusion
  `annihilatorι ℱ` after transporting the unit-module stalk to the stalk ring.

Source/core/bridge triage:
- `source-facing`: the stalkwise equality
  `(Ann_{\mathcal O_X}(\mathcal F))_x = Ann_{\mathcal O_{X,x}}(\mathcal F_x)`;
- `core/canonical`: `annihilator`, `annihilatorι`,
  `RingedSpace.stalkModuleCat`, and
  `RingedSpace.moduleStalkHom`;
- `bridge/view`: `RingedSpace.unitStalkLinearMap`, the canonical linear identification of the
  unit-module stalk with `\mathcal O_{X,x}`.

The previous existential statement only unpacked the stalk-image side of this equality. The main
public entry is refined here to the actual ideal equality; the stalk-ideal owner itself now lives
in `17.23.1.1`, and any sectionwise/existential phrasing is derived bridge API rather than the
owner statement. -/

-- Proof sketch: Lemma `17.23.1.1` gives the inclusion from the stalk image of
-- `Ann_{\mathcal O_X}(\mathcal F)` into `Ann_{\mathcal O_{X,x}}(\mathcal F_x)` through the owner
-- theorem `annihilatorStalkIdeal_le_module_annihilator`. For the reverse
-- inclusion, use Lemma `17.22.4` to identify the stalk of the internal action map with the stalk
-- action on `\mathcal F_x`; if `\mathcal F` is finite type, injectivity of that comparison shows
-- that any stalk scalar acting by zero on `\mathcal F_x` already comes from the kernel sheaf.
/-- Lemma 17.23.2: for a finite type `\mathcal O_X`-module sheaf `\mathcal F`, the ideal of the
stalk ring `\mathcal O_{X, x}` cut out by the stalk of the annihilator sheaf agrees with the
annihilator ideal of the stalk module `\mathcal F_x`. This is the stalkwise equality
`(\operatorname{Ann}_{\mathcal O_X}(\mathcal F))_x =
\operatorname{Ann}_{\mathcal O_{X, x}}(\mathcal F_x)`. -/
theorem stalk_annihilator_eq_module_annihilator
    (ℱ : ModX) (x : X) [ℱ.IsFiniteType] :
    annihilatorStalkIdeal ℱ x =
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  apply le_antisymm
  · exact annihilatorStalkIdeal_le_module_annihilator ℱ x
  · intro r hr
    change r ∈ LinearMap.range
      ((RingedSpace.moduleStalkHom x (annihilatorι ℱ) ≫
        RingedSpace.unitStalkLinearMap x).hom)
    let S : ShortComplex ModX :=
      ShortComplex.mk (annihilatorι ℱ) (selfInternalHomUnitMap ℱ) (kernel.condition _)
    have hS : S.Exact := ShortComplex.exact_kernel (selfInternalHomUnitMap ℱ)
    have hSx : (RingedSpace.stalkShortComplex S x).Exact :=
      (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
    have hrange :
        LinearMap.range (RingedSpace.moduleStalkHom x (annihilatorι ℱ)).hom =
          LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom := by
      simpa [S, RingedSpace.stalkShortComplex] using hSx.moduleCat_range_eq_ker
    have hcompare :
        (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ) ≫
            RingedSpace.internalHomStalkComparison ℱ ℱ x).hom₂ =
          (LinearMap.lsmul (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)).comp
            (RingedSpace.unitStalkLinearMap x).hom := by
      sorry
    have hzero_lsmul :
        LinearMap.lsmul (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) r = 0 := by
      ext m
      exact Module.mem_annihilator.mp hr m
    have hker :
        (RingedSpace.unitStalkLinearEquiv x).symm r ∈
          LinearMap.ker (RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom := by
      apply LinearMap.mem_ker.mpr
      apply RingedSpace.internalHomStalkComparison_injective_of_isFiniteType ℱ ℱ x
      have hzero :
          (RingedSpace.internalHomStalkComparison ℱ ℱ x).hom
            ((RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ)).hom
              ((RingedSpace.unitStalkLinearEquiv x).symm r)) = 0 := by
        apply ModuleCat.hom_injective
        ext m
        change
          ((RingedSpace.moduleStalkHom x (selfInternalHomUnitMap ℱ) ≫
              RingedSpace.internalHomStalkComparison ℱ ℱ x).hom₂
            ((RingedSpace.unitStalkLinearEquiv x).symm r))
            m = 0
        have hm :=
          congrArg
            (fun F ↦ F ((RingedSpace.unitStalkLinearEquiv x).symm r) m) hcompare
        have hzero_rhs :
            ((LinearMap.lsmul (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) ∘ₗ
                ModuleCat.Hom.hom (RingedSpace.unitStalkLinearMap x))
              ((RingedSpace.unitStalkLinearEquiv x).symm r))
              m = 0 := by
          rw [LinearMap.comp_apply]
          rw [show ModuleCat.Hom.hom (RingedSpace.unitStalkLinearMap x)
              ((RingedSpace.unitStalkLinearEquiv x).symm r) = r by
                simpa [RingedSpace.unitStalkLinearMap] using
                  (RingedSpace.unitStalkLinearEquiv x).apply_symm_apply r]
          simpa [LinearMap.ext_iff] using congrArg (fun f ↦ f m) hzero_lsmul
        exact hm.trans hzero_rhs
      exact hzero.trans (by
        simpa using ((RingedSpace.internalHomStalkComparison ℱ ℱ x).hom.map_zero).symm)
    rw [← hrange] at hker
    rcases hker with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change RingedSpace.unitStalkLinearMap x (RingedSpace.moduleStalkHom x (annihilatorι ℱ) t) = r
    rw [ht]
    simpa [RingedSpace.unitStalkLinearMap] using
      (RingedSpace.unitStalkLinearEquiv x).apply_symm_apply r

end SheafOfModules

/-! ### Lemma_17_23_3 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

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
  inclusion `I ≤ annihilatorSubobject ℱ` into the chapter owner `annihilator ℱ`;
- primitive data:
  the quotient owner only needs an ideal sheaf `I : Subobject 𝒪X`; the descended-module bridge
  additionally needs a module sheaf `ℱ` and an inclusion `hI : I ≤ annihilatorSubobject ℱ`;
- derived API:
  the sectionwise ideals `idealSectionIdeal I U`, the quotient sheaf `quotientCommRingSheaf I`,
  the descended module `quotientModule I ℱ hI`, and the representative-level section/stalk
  formulas.

Source/core/bridge triage:
- `source-facing`: the quotient sheaf `\mathcal O_X / \mathcal I` and the induced
  `(\mathcal O_X / \mathcal I)`-module structure on `\mathcal F`;
- `core/canonical`: `Subobject 𝒪X`, `Subobject.arrow`, `annihilator`, `annihilatorι`,
  `Subobject.ofLEMk`, the presheaf constructor `PresheafOfModules.ofPresheaf`, and
  quotient-module descent via `Module.IsTorsionBySet.module`;
- `bridge/view`: the sectionwise ideal family and the section/stalk comparison lemmas expressing
  the descended action in terms of representatives, together with the internal bridge from
  `I ≤ annihilatorSubobject ℱ` to the zero-composite condition needed by the kernel presentation
  of `annihilator ℱ`. -/

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
  sorry

/-- The quotient presheaf of commutative rings `\mathcal O_X / \mathcal I`. -/
private noncomputable def quotientCommRingPresheaf
    (I : Subobject 𝒪X) :
    (Opens X)ᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (X.presheaf.obj U ⧸ idealSectionIdeal I U)
  map {U V} f := CommRingCat.ofHom <|
    Ideal.quotientMap (idealSectionIdeal I V) (X.presheaf.map f).hom
      (idealSectionIdeal_le_comap I f)
  map_id U := by
    sorry
  map_comp f g := by
    sorry

/-- The quotient sheaf of commutative rings `\mathcal O_X / \mathcal I`. -/
noncomputable def quotientCommRingSheaf
    (I : Subobject 𝒪X) :
    TopCat.Sheaf CommRingCat X :=
  ⟨quotientCommRingPresheaf I, by sorry⟩

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

private theorem arrow_comp_selfInternalHomUnitMap_eq_zero
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ) :
    I.arrow ≫ selfInternalHomUnitMap ℱ = 0 := by
  have hcomp : Subobject.ofLEMk I (annihilatorι ℱ) hI ≫ annihilatorι ℱ = I.arrow :=
    Subobject.ofLEMk_comp hI
  rw [← hcomp, Category.assoc]
  simp

/-- Every local section of the ideal generated by `\mathcal I(U)` annihilates
`\mathcal F(U)`. -/
theorem idealSectionIdeal_le_sectionAnnihilator
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ) (U : (Opens X)ᵒᵖ) :
    idealSectionIdeal I U ≤ Module.annihilator (X.presheaf.obj U) (ℱ.val.presheaf.obj U) := by
  have hzero : I.arrow ≫ selfInternalHomUnitMap ℱ = 0 :=
    arrow_comp_selfInternalHomUnitMap_eq_zero I ℱ hI
  sorry

noncomputable instance quotientSectionModule
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U ⧸ idealSectionIdeal I U) (ℱ.val.presheaf.obj U) := by
  let htors :
      Module.IsTorsionBySet (X.presheaf.obj U) (ℱ.val.presheaf.obj U)
        ((idealSectionIdeal I U : Set (X.presheaf.obj U))) :=
    (isTorsionByIdealSectionIdeal_iff I ℱ U).2
      (idealSectionIdeal_le_sectionAnnihilator I ℱ hI U)
  simpa [quotientRingSheaf, quotientCommRingPresheaf] using htors.module

private theorem quotientModulePresheaf_map_smul
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (r : (𝒪[X] ⧸ I).obj.obj U) (m : ℱ.val.presheaf.obj U) :
    let _ : Module ((𝒪[X] ⧸ I).obj.obj U) (ℱ.val.presheaf.obj U) :=
      quotientSectionModule I ℱ hI U
    let _ : Module ((𝒪[X] ⧸ I).obj.obj V) (ℱ.val.presheaf.obj V) :=
      quotientSectionModule I ℱ hI V
    ℱ.val.presheaf.map f (r • m) =
      (𝒪[X] ⧸ I).obj.map f r • ℱ.val.presheaf.map f m := by
  sorry

/-- The underlying presheaf of the descended `(\mathcal O_X / \mathcal I)`-module structure on
`\mathcal F`. -/
private noncomputable def quotientModulePresheaf
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ) :
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
    (hI : I ≤ annihilatorSubobject ℱ) :
    SheafOfModules (𝒪[X] ⧸ I) where
  val := quotientModulePresheaf I ℱ hI
  isSheaf := by
    simpa [quotientModulePresheaf, PresheafOfModules.ofPresheaf_presheaf] using ℱ.isSheaf

noncomputable instance quotientModuleSectionModule
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U ⧸ idealSectionIdeal I U) ↑((quotientModule I ℱ hI).val.obj U) :=
  ((quotientModule I ℱ hI).val.obj U).isModule

noncomputable instance quotientModuleSectionModuleOverOX
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) ↑((quotientModule I ℱ hI).val.obj U) :=
  sectionModule ℱ U

/-- Sectionwise, the descended quotient action is the usual one: a representative in
`\mathcal O_X(U)` acts through its class exactly as the original local section acted on
`\mathcal F(U)`. -/
theorem quotientModule_mk_smul
    (I : Subobject 𝒪X) (ℱ : ModX)
    (hI : I ≤ annihilatorSubobject ℱ)
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
    (hI : I ≤ annihilatorSubobject ℱ)
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

/-! ### Lemma_17_23_4 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.23.4:
- primary domain: coherence of annihilator sheaves for modules on a ringed space;
- sampled owner declarations:
  `SheafOfModules.annihilator`,
  `AlgebraicGeometry.RingedSpace.moduleInternalHom_isCoherent_of_isFinitePresentation`,
  `AlgebraicGeometry.RingedSpace.isCoherent_kernel`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, and this lemma should stay a bridge/view statement:
  the source-facing annihilator sheaf is already owned by `SheafOfModules.annihilator`, while its
  coherence is derived from the canonical internal-Hom coherence theorem and the canonical closure
  of coherent sheaves under kernels;
- primitive data:
  a module sheaf `ℱ : RingedSpace.Modules X`, coherence of the structure sheaf as a module, and
  coherence of `ℱ`;
- derived API:
  the coherence statement for `annihilator ℱ`.

Source/core/bridge triage:
- `source-facing`: the annihilator sheaf `annihilator ℱ`;
- `core/canonical`: `RingedSpace.Modules X`, `selfInternalHomUnitMap ℱ`, internal Hom, and
  kernels;
- `bridge/view`: the present theorem, which identifies the source-facing annihilator with a kernel
  of coherent sheaves and deduces coherence from the upstream owner API. -/

-- Proof sketch: `annihilator ℱ` is the kernel of the canonical map
-- `\mathcal O_X → \mathcal H\!om_{\mathcal O_X}(ℱ, ℱ)`. If `ℱ` is coherent, then it is finitely
-- presented, so Lemma `17.22.6` makes the internal endomorphism sheaf coherent; with the
-- structure sheaf coherent as well, Lemma `17.12.4` identifies the kernel as coherent.
/-- Lemma 17.23.4: if the structure sheaf `\mathcal O_X`, viewed as an `\mathcal O_X`-module, and
`\mathcal F` are coherent, then the annihilator sheaf
`\operatorname{Ann}_{\mathcal O_X}(\mathcal F)` is coherent. -/
theorem annihilator_isCoherent (ℱ : ModX)
    [(SheafOfModules.unit (RingedSpace.ringCatSheaf X)).IsCoherent] [ℱ.IsCoherent] :
    (annihilator ℱ).IsCoherent := by
  letI : ((ihom ℱ).obj ℱ).IsCoherent :=
    RingedSpace.moduleInternalHom_isCoherent_of_isFinitePresentation ℱ ℱ
  change (kernel (selfInternalHomUnitMap ℱ)).IsCoherent
  exact RingedSpace.isCoherent_kernel (selfInternalHomUnitMap ℱ)

end SheafOfModules
