import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.stacks_project.Chap18.«18_19_2_1»
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap18.Remark_18_19_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]

/-- Helper for Lemma 18.28.7: in an abelian setting, preserving monomorphisms together with
finite colimits upgrades a functor to an exact functor. -/
private theorem exactOfPreservesMonomorphismsAndFiniteColimits
    {A : Type*} {B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B)
    [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    (hMono : F.PreservesMonomorphisms) :
    exactFunctor A B F := by
  let _ : F.PreservesMonomorphisms := hMono
  let _ : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  -- Proof comment: in an abelian category, homology preservation recovers finite-limit
  -- preservation, so exactness reduces to the formal finite-colimit half.
  exact
    (CategoryTheory.exactFunctor_iff F).2
      ⟨F.preservesFiniteLimits_of_preservesHomology, inferInstance⟩

/-- The localized structure module `\mathcal O_U` on the slice category `C/U`, regarded as a
module over the localized ring presheaf. -/
abbrev localizedStructureModule
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules ((Over.forget U).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.unit ((Over.forget U).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat))

/-- The presheaf `j_{U!}\mathcal O_U` obtained by extending the localized structure module by zero
from `C/U` back to `C`. -/
abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pullback
      (𝟙 ((Over.forget U).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat)))).obj
    (localizedStructureModule 𝒪 U)

/-- Helper for Lemma 18.28.7: evaluating the presheaf lower shriek at `V` identifies it with the
coproduct of copies of `\mathcal O(V)` indexed by arrows `V ⟶ U`. -/
private noncomputable abbrev localizedStructureModuleExtensionByZeroObjIsoCoproduct
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U V : C) :
    ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V)) ≅
      (∐ fun _φ : V ⟶ U ↦ ModuleCat.of (𝒪.obj (op V)) (𝒪.obj (op V))) := by
  -- Proof comment: specialize Remark 18.19.7 to the unit module on `C/U`; each fiber is then the
  -- unit module over `𝒪(V)`, i.e. a copy of `𝒪(V)` itself.
  simpa [localizedStructureModuleExtensionByZero, localizedStructureModule] using
    (presheafLocalizedExtensionByZero_objIsoSigma
      (𝒪 := 𝒪 ⋙ forget₂ CommRingCat RingCat)
      (U := U) (𝒢 := localizedStructureModule 𝒪 U) V)

/-- Helper for Lemma 18.28.7: each section module of `j_{U!}\mathcal O_U` is flat over the
corresponding ring of sections. -/
private theorem localizedStructureModuleExtensionByZero_objFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U V : C) :
    Module.Flat (𝒪.obj (op V)) ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V)) := by
  classical
  let R := 𝒪.obj (op V)
  let Z : (V ⟶ U) → ModuleCat R := fun _ ↦ ModuleCat.of R R
  let eCoproduct :
      ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V)) ≅ ∐ Z :=
    localizedStructureModuleExtensionByZeroObjIsoCoproduct 𝒪 U V
  let eDirectSum : (∐ Z) ≅ ModuleCat.of R (DirectSum (V ⟶ U) fun _ ↦ R) :=
    ModuleCat.coprodIsoDirectSum (R := R) Z
  letI : ∀ φ : V ⟶ U, Module.Flat R (R : Type u) := fun _ ↦ Module.Flat.self
  letI : Module.Flat R (DirectSum (V ⟶ U) fun _ ↦ R) := Module.Flat.directSum
  -- Proof comment: rewrite the coproduct formula to the canonical direct sum, where flatness is
  -- immediate because every summand is the free rank-one module over `R`.
  exact Module.Flat.of_linearEquiv ((eCoproduct ≪≫ eDirectSum).toLinearEquiv)

/-- Helper for Lemma 18.28.7: the presheaf lower shriek has flat sections at every object. -/
private theorem localizedStructureModuleExtensionByZero_flatSections
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    ∀ V : C, Module.Flat (𝒪.obj (op V)) ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V))
    := by
  -- Proof comment: this is just the objectwise flatness computation packaged in the shape
  -- consumed by the sectionwise flatness criterion from Lemma `18.28.2`.
  intro V
  exact localizedStructureModuleExtensionByZero_objFlat 𝒪 U V

/-- Helper for Lemma 18.28.7: tensoring on the right by the presheaf lower shriek preserves
monomorphisms because its sections are flat modules. -/
private theorem localizedStructureModuleExtensionByZero_tensorPreservesMonomorphisms
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    (CategoryTheory.MonoidalCategory.tensorRight
      (localizedStructureModuleExtensionByZero 𝒪 U)).PreservesMonomorphisms := by
  refine ⟨fun {M N} α _ ↦ ?_⟩
  -- Proof comment: monomorphisms of presheaves of modules are checked sectionwise, and tensoring
  -- a sectionwise monomorphism with a flat section module stays injective.
  refine PresheafOfModules.mono_of_injective ?_
  intro X
  have hαinj :
      Function.Injective (ModuleCat.Hom.hom (α.app X)) :=
    PresheafOfModules.injective_of_mono α X
  letI :
      Module.Flat (𝒪.obj X)
        ((localizedStructureModuleExtensionByZero 𝒪 U).obj X) := by
    simpa using localizedStructureModuleExtensionByZero_flatSections 𝒪 U (unop X)
  simpa using
    Module.Flat.rTensor_preserves_injective_linearMap
      (R := 𝒪.obj X)
      (M := (localizedStructureModuleExtensionByZero 𝒪 U).obj X)
      (f := ModuleCat.Hom.hom (α.app X))
      hαinj

-- Proof sketch: evaluate `j_{U!}\mathcal O_U` at an object `V`. By Remark `18.19.7` this section
-- module is the coproduct over all arrows `V ⟶ U` of copies of `\mathcal O(V)`, hence is a free,
-- in particular flat, `\mathcal O(V)`-module. Then apply Lemma `18.28.2`.
/-- Lemma 18.28.7 (1): for a presheaf of commutative rings `\mathcal O` on a category
`\mathcal C` and an object `U : \mathcal C`, the lower-shriek module `j_{U!}\mathcal O_U` is flat
as a presheaf of `\mathcal O`-modules. -/
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    IsFlat (localizedStructureModuleExtensionByZero 𝒪 U) := by
  let F := CategoryTheory.MonoidalCategory.tensorRight
    (localizedStructureModuleExtensionByZero 𝒪 U)
  have hMono : F.PreservesMonomorphisms :=
    localizedStructureModuleExtensionByZero_tensorPreservesMonomorphisms 𝒪 U
  let _ : F.Additive :=
    functor_additive_of_leftExact_or_rightExact (F := F)
      (.inr ((CategoryTheory.rightExactFunctor_iff F).2 inferInstance))
  -- Proof comment: tensoring on the right is formally right exact, and the flat section modules
  -- show it also preserves monomorphisms; the abelian exactness criterion then gives flatness.
  exact ⟨exactOfPreservesMonomorphismsAndFiniteColimits F hMono⟩

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "PMod(" 𝒪 ")" => PresheafOfModules 𝒪
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪
local notation "PModS(" 𝒪 ")" => PresheafOfModules (𝒪.1 ⋙ forget₂ CommRingCat RingCat)

/-- Helper for Lemma 18.28.7: exactness is stable under composition of functors. -/
private theorem exactFunctorComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness means finite-limit and finite-colimit preservation, and each half
  -- composes formally.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  let _ : CategoryTheory.Limits.PreservesFiniteLimits G := hG.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.7: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B}
    (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the functor
  -- isomorphism and then repackage the result as exactness.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso e⟩

/-- Helper for Lemma 18.28.7: finite colimits descend along a reflective localization. -/
private theorem preservesFiniteColimitsOfReflectiveComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    [CategoryTheory.Limits.HasFiniteColimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G)] :
    CategoryTheory.Limits.PreservesFiniteColimits G := by
  -- Proof comment: pull a finite diagram in `B` back along the right adjoint, compute its
  -- colimit upstairs, and compare it with the original diagram via the counit isomorphism.
  refine ⟨?_⟩
  intro K _ _
  refine ⟨?_⟩
  intro L
  let P := L ⋙ R
  let e : L ≅ P ⋙ F :=
    Functor.isoWhiskerLeft L (asIso adj.counit).symm
  have hPF : CategoryTheory.Limits.PreservesColimit (P ⋙ F) G := by
    refine CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
      (CategoryTheory.Limits.isColimitOfPreserves F (CategoryTheory.Limits.colimit.isColimit P))
      ?_
    change CategoryTheory.Limits.IsColimit
      (CategoryTheory.Functor.mapCocone (F ⋙ G) (CategoryTheory.Limits.colimit.cocone P))
    exact CategoryTheory.Limits.isColimitOfPreserves
      (F ⋙ G) (CategoryTheory.Limits.colimit.isColimit P)
  exact CategoryTheory.Limits.preservesColimit_of_iso_diagram G e.symm

/-- Helper for Lemma 18.28.7: finite limits descend along a reflective localization. -/
private theorem preservesFiniteLimitsOfReflectiveComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    [CategoryTheory.Limits.HasFiniteLimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G)] :
    CategoryTheory.Limits.PreservesFiniteLimits G := by
  -- Proof comment: the same reflective-localization argument works for finite limits.
  refine ⟨?_⟩
  intro K _ _
  refine ⟨?_⟩
  intro L
  let P := L ⋙ R
  let e : L ≅ P ⋙ F :=
    Functor.isoWhiskerLeft L (asIso adj.counit).symm
  have hPF : CategoryTheory.Limits.PreservesLimit (P ⋙ F) G := by
    refine CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (CategoryTheory.Limits.isLimitOfPreserves F (CategoryTheory.Limits.limit.isLimit P)) ?_
    change CategoryTheory.Limits.IsLimit
      (CategoryTheory.Functor.mapCone (F ⋙ G) (CategoryTheory.Limits.limit.cone P))
    exact CategoryTheory.Limits.isLimitOfPreserves
      (F ⋙ G) (CategoryTheory.Limits.limit.isLimit P)
  exact CategoryTheory.Limits.preservesLimit_of_iso_diagram G e.symm

/-- Helper for Lemma 18.28.7: exactness descends from the sheafification image to all sheaf
modules. -/
private theorem exactFunctorOfReflectiveComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    [CategoryTheory.Limits.HasFiniteLimits A]
    [CategoryTheory.Limits.HasFiniteColimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    (h : exactFunctor A D (F ⋙ G)) :
    exactFunctor B D G := by
  -- Proof comment: exactness is the conjunction of finite-limit and finite-colimit
  -- preservation, and each half descends through the reflective localization.
  rw [CategoryTheory.exactFunctor_iff] at h ⊢
  constructor
  · let _ : CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G) := h.1
    exact preservesFiniteLimitsOfReflectiveComp F R adj G
  · let _ : CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G) := h.2
    exact preservesFiniteColimitsOfReflectiveComp F R adj G

/-- Helper for Lemma 18.28.7: the fixed-owner sheafification functor viewed with the presheaf owner
spelling used throughout this file. -/
private noncomputable abbrev fixedOwnerModuleSheafification
    (𝒪 : Sheaf J CommRingCat.{u}) :
    PModS(𝒪) ⥤ Mod(𝒪) :=
  show PModS(𝒪) ⥤ Mod(𝒪) from moduleSheafification 𝒪

/-- Helper for Lemma 18.28.7: fixed-owner module sheafification commutes with right tensoring via
the canonical monoidal comparison. -/
private noncomputable def moduleSheafificationTensorRightIso
    (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : PModS(𝒪)) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification 𝒪 ≅
      moduleSheafification 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ) :=
  by
  -- Route correction: keep the comparison in the target owner spelling and use the canonical
  -- oplax tensor map directly, instead of asking separately for a monoidal instance on a
  -- differently normalized functor expression.
  -- Proof comment: the comparison between sheafification-after-tensor and tensor-after-
  -- sheafification is the oplax monoidal structure map of `moduleSheafification 𝒪`.
  refine NatIso.ofComponents
    (fun X ↦ asIso (Functor.OplaxMonoidal.δ (moduleSheafification 𝒪) X ℱ)) ?_
  intro X Y f
  -- Proof comment: naturality is the standard right-naturality of the oplax tensor comparison.
  exact Functor.OplaxMonoidal.δ_natural_right (moduleSheafification 𝒪) X f

/-- Helper for Lemma 18.28.7: exactness of tensoring by a sheafified module descends from the
essential image of fixed-owner sheafification. -/
private theorem tensorRightExactOfSheafificationImage
    (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : PModS(𝒪))
    (hComposite :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (moduleSheafification 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ))) :
    exactFunctor
      (Mod(𝒪))
      (Mod(𝒪))
      (CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ)) := by
  let R := SheafOfModules.forget (ringSheaf J 𝒪)
  let S := moduleSheafification 𝒪
  let T := CategoryTheory.MonoidalCategory.tensorRight (S.obj ℱ)
  let adj : S ⊣ R :=
    PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J 𝒪).obj)
  let _ : IsIso adj.counit := by
    infer_instance
  let hSExact := (CategoryTheory.exactFunctor_iff S).1 ((ExactFunctor.of S).property)
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ S) := by
    exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso (asIso adj.counit).symm
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ S) := by
    exact CategoryTheory.Limits.preservesFiniteColimits_of_natIso (asIso adj.counit).symm
  let _ : CategoryTheory.Limits.PreservesFiniteLimits S := hSExact.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits S := hSExact.2
  -- Proof comment: the counit identifies every sheaf module with a sheafification image, so
  -- exactness of the composite through sheafification descends to exactness of `tensorRight`.
  exact exactFunctorOfReflectiveComp S R adj T hComposite

/-- Helper for Lemma 18.28.7: flat presheaves remain flat after fixed-owner sheafification. -/
private theorem sheafificationIsFlatOfFlatPresheaf
    (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : PModS(𝒪))
    (hℱ : PresheafOfModules.IsFlat ℱ) :
    IsFlat 𝒪 ((moduleSheafification 𝒪).obj ℱ) := by
  refine ⟨?_⟩
  let hTensor :
      exactFunctor
        (PModS(𝒪))
        (PModS(𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ) :=
    PresheafOfModules.IsFlat.exact_tensor (ℱ := ℱ)
  let hSheafification :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (moduleSheafification 𝒪) :=
    (ExactFunctor.of (moduleSheafification 𝒪)).property
  let hCompositePresheaf :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification 𝒪) :=
    exactFunctorComp hTensor hSheafification
  let hCompositeSheaf :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (moduleSheafification 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ)) :=
    exactFunctorOfNatIso
      (moduleSheafificationTensorRightIso 𝒪 ℱ)
      hCompositePresheaf
  -- Proof comment: after rewriting the composite by the monoidal comparison, reflective
  -- descent along the sheafification counit gives the sheaf-level exactness criterion.
  exact tensorRightExactOfSheafificationImage 𝒪 ℱ hCompositeSheaf

/-- Helper for Lemma 18.28.7: the sheaf lower shriek is the sheafification of the presheaf lower
shriek over the fixed ring sheaf. -/
private noncomputable abbrev localizedStructureModuleExtensionByZeroSheafificationIso
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    j![𝒪, U] ≅
      (moduleSheafification 𝒪).obj
        (PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪.1 U) := by
  -- Proof comment: `SheafOfModules.pullbackIso` compares the sheaf pullback defining `j!` with the
  -- sheafification of the corresponding presheaf pullback, and both specializations are the
  -- localized structure module extension-by-zero constructions.
  simpa [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero,
    PresheafOfModules.localizedStructureModuleExtensionByZero,
    PresheafOfModules.localizedStructureModule, moduleSheafification] using
    (SheafOfModules.pullbackIso
      (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))).app
      (SheafOfModules.unit
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))

-- Proof sketch: the source proof identifies the sheaf lower shriek with the sheafification of the
-- presheaf lower shriek from part (1), then applies the sheafification-flatness bridge.
/-- Lemma 18.28.7 (2): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of
commutative rings on it, then the lower-shriek module `j_{U!}\mathcal O_U` is a flat sheaf of
`\mathcal O`-modules. -/
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Sheaf J CommRingCat.{u}) [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] (U : C) :
    IsFlat 𝒪 (j![𝒪, U]) := by
  let ℱ := PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪.1 U
  have hPresheafFlat : PresheafOfModules.IsFlat ℱ :=
    PresheafOfModules.localizedStructureModuleExtensionByZero_isFlat 𝒪.1 U
  have hSheafifiedFlat :
      IsFlat 𝒪 ((moduleSheafification 𝒪).obj ℱ) :=
    sheafificationIsFlatOfFlatPresheaf 𝒪 ℱ hPresheafFlat
  let e :
      CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ) ≅
        CategoryTheory.MonoidalCategory.tensorRight (j![𝒪, U]) :=
    (CategoryTheory.MonoidalCategory.tensoringRight (Mod(𝒪))).mapIso
      (localizedStructureModuleExtensionByZeroSheafificationIso 𝒪 U).symm
  refine ⟨?_⟩
  -- Proof comment: part (1) gives flatness before sheafification; the fixed-owner sheafification
  -- bridge upgrades that to flatness of the sheafified lower shriek, and the final tensor-right
  -- transport along `localizedStructureModuleExtensionByZeroSheafificationIso` identifies that
  -- sheafified object with the source-facing lower-shriek sheaf `j![𝒪,U]`.
  exact exactFunctorOfNatIso e hSheafifiedFlat.exact_tensor

end SheafOfModules.RingedSite
