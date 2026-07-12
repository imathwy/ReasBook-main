import Mathlib
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable [MonoidalCategory (ringedSiteModuleCategory J (commRingSheafification J 𝒪))]
variable (ℱ : PresheafOfModules (ringPresheaf 𝒪))
variable [PresheafOfModules.IsFlat ℱ]

local notation "IsFlat" => SheafOfModules.RingedSite.IsFlat

/-- Helper for Lemma 18.28.3: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Exactness is finite-limit and finite-colimit preservation, and both properties compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  let _ : CategoryTheory.Limits.PreservesFiniteLimits G := hG.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.3: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctor_of_natIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B} (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Transport finite-limit and finite-colimit preservation across the functor isomorphism.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Lemma 18.28.3: finite colimits descend along a reflective presentation. -/
private theorem preservesFiniteColimits_of_reflective_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G)] :
    CategoryTheory.Limits.PreservesFiniteColimits G := by
  refine ⟨?_⟩
  intro K _ _
  refine ⟨?_⟩
  intro L
  let P := L ⋙ R
  let e : L ≅ P ⋙ F :=
    Functor.isoWhiskerLeft L (asIso adj.counit).symm
  have hPF : CategoryTheory.Limits.PreservesColimit (P ⋙ F) G := by
    refine CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
      (CategoryTheory.Limits.isColimitOfPreserves F (CategoryTheory.Limits.colimit.isColimit P)) ?_
    change CategoryTheory.Limits.IsColimit
      (CategoryTheory.Functor.mapCocone (F ⋙ G) (CategoryTheory.Limits.colimit.cocone P))
    exact CategoryTheory.Limits.isColimitOfPreserves
      (F ⋙ G) (CategoryTheory.Limits.colimit.isColimit P)
  exact CategoryTheory.Limits.preservesColimit_of_iso_diagram G e.symm

/-- Helper for Lemma 18.28.3: finite limits descend along a reflective presentation. -/
private theorem preservesFiniteLimits_of_reflective_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G)] :
    CategoryTheory.Limits.PreservesFiniteLimits G := by
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

/-- Helper for Lemma 18.28.3: exactness descends along a reflective presentation. -/
private theorem exactFunctor_of_reflective_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    (h : exactFunctor A D (F ⋙ G)) :
    exactFunctor B D G := by
  rw [CategoryTheory.exactFunctor_iff] at h ⊢
  constructor
  · let _ : CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G) := h.1
    exact preservesFiniteLimits_of_reflective_comp F R adj G
  · let _ : CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G) := h.2
    exact preservesFiniteColimits_of_reflective_comp F R adj G

/-- Helper for Lemma 18.28.3: sheafifying after tensoring by a presheaf module agrees
functorially with tensoring after sheafification. -/
private noncomputable def moduleSheafification_tensorRight_iso
    (ℱ' : PresheafOfModules (ringPresheaf 𝒪))
    : CategoryTheory.MonoidalCategory.tensorRight ℱ' ⋙ moduleSheafification J 𝒪 ≅
      moduleSheafification J 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ') :=
  -- Proof comment: this is the canonical monoidal comparison of module sheafification,
  -- specialized to tensoring on the right by the fixed module `ℱ'`.
  let _ : Functor.Monoidal (moduleSheafification J 𝒪) := inferInstance
  NatIso.ofComponents
    (fun X ↦ (Functor.Monoidal.μIso (moduleSheafification J 𝒪) X ℱ').symm)
    (fun {_ _} f ↦ by
      -- Proof comment: naturality follows from the generic naturality of `μIso`.
      ext
      rw [μ_natural_right_assoc]
      simp)

/-- Helper for Lemma 18.28.3: the right adjoint of module sheafification along
`\mathcal O \to \mathcal O^\#`. -/
private noncomputable abbrev sheafificationRightAdjoint :
    ringedSiteModuleCategory J (commRingSheafification J 𝒪) ⥤
      PresheafOfModules (ringPresheaf 𝒪) :=
  SheafOfModules.forget (ringSheaf J (commRingSheafification J 𝒪)) ⋙
    PresheafOfModules.restrictScalars (sheafificationRingMap J 𝒪)

/-- Helper for Lemma 18.28.3: exactness of tensoring by `\mathcal F^\#` descends from the
essential image of module sheafification to all sheaf modules. -/
omit [PresheafOfModules.IsFlat ℱ]
private theorem tensorRight_exact_of_sheafification_image
    (hComposite :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (ringedSiteModuleCategory J (commRingSheafification J 𝒪))
        (moduleSheafification J 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ))) :
    exactFunctor
      (ringedSiteModuleCategory J (commRingSheafification J 𝒪))
      (ringedSiteModuleCategory J (commRingSheafification J 𝒪))
      (CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ)) := by
  -- Proof comment: module sheafification is a reflective localization, so exactness on its
  -- essential image descends through the adjunction counit to all sheaf-module diagrams.
  let R := sheafificationRightAdjoint J 𝒪
  let S := moduleSheafification J 𝒪
  let T := CategoryTheory.MonoidalCategory.tensorRight (S.obj ℱ)
  let adj : S ⊣ R :=
    PresheafOfModules.sheafificationAdjunction (sheafificationRingMap J 𝒪)
  let _ : IsIso adj.counit := by
    infer_instance
  let hSExact := (CategoryTheory.exactFunctor_iff S).1 ((ExactFunctor.of S).property)
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ S) := by
    exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso (asIso adj.counit).symm
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ S) := by
    exact CategoryTheory.Limits.preservesFiniteColimits_of_natIso (asIso adj.counit).symm
  let _ : CategoryTheory.Limits.PreservesFiniteLimits S := hSExact.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits S := hSExact.2
  exact exactFunctor_of_reflective_comp S R adj T hComposite
include [PresheafOfModules.IsFlat ℱ]

/- Domain-style sampling for Lemma 18.28.3:
- primary domain: flatness of module objects under sheafification on a ringed site;
- sampled owner declarations:
  `PresheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `PresheafOfModules.moduleSheafification`,
  `moduleSheafificationTensorIso`;
- best owner abstraction: the sheaf-level conclusion should live directly in the chapter owner
  `SheafOfModules.RingedSite.IsFlat` for the sheafified module
  `((moduleSheafification J 𝒪).obj ℱ)` over `commRingSheafification J 𝒪`;
- primitive data: a presheaf of commutative rings `𝒪`, a presheaf module
  `ℱ : PresheafOfModules (ringPresheaf 𝒪)`, and the flatness owner `[PresheafOfModules.IsFlat ℱ]`;
- derived API: the canonical flatness instance on the sheafification.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that a flat presheaf remains flat after sheafification;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: `moduleSheafification`, transporting the presheaf module to the sheaf-level owner.
-/

-- Proof sketch: flatness of `ℱ` means that tensoring with `ℱ` is an exact endofunctor on
-- presheaves of modules. The exactness owner recalled in `Lemma_18_11_2` applies to module
-- sheafification, and the tensor-sheafification comparison from `Lemma_18_26_1` identifies
-- tensoring with `ℱ^#` over `𝒪^#` with sheafifying tensoring with `ℱ`; therefore the
-- sheafification `ℱ^#` is flat over the sheafified structure sheaf `𝒪^#`.
/-- Lemma 18.28.3: if a presheaf of `\mathcal O`-modules `\mathcal F` on a site is flat, then its
sheafification `\mathcal F^\#` is a flat `\mathcal O^\#`-module in the chapter's canonical
sheaf-level flatness owner. -/
@[stacks 03ET]
theorem sheafification_isFlat :
    IsFlat (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) := by
  -- Route correction: first rewrite the sheafified tensor functor by the monoidal comparison,
  -- then invoke the remaining exactness-descent helper instead of mixing the transport steps.
  refine ⟨?_⟩
  let hTensor :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ) :=
    PresheafOfModules.IsFlat.exact_tensor (ℱ := ℱ)
  let hSheafification :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (ringedSiteModuleCategory J (commRingSheafification J 𝒪))
        (moduleSheafification J 𝒪) :=
    (ExactFunctor.of (moduleSheafification J 𝒪)).property
  let hCompositePresheaf :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (ringedSiteModuleCategory J (commRingSheafification J 𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification J 𝒪) :=
    exactFunctor_comp hTensor hSheafification
  let hCompositeSheaf :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (ringedSiteModuleCategory J (commRingSheafification J 𝒪))
        (moduleSheafification J 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ)) :=
    exactFunctor_of_natIso
      (moduleSheafification_tensorRight_iso (J := J) (𝒪 := 𝒪) (ℱ' := ℱ))
      hCompositePresheaf
  -- Proof comment: the remaining descent lemma upgrades exactness from the sheafification image
  -- to all sheaf modules, which is precisely the flatness criterion on the ringed site.
  exact tensorRight_exact_of_sheafification_image (J := J) (𝒪 := 𝒪) (ℱ := ℱ) hCompositeSheaf

/-- The sheafification of a flat presheaf carries its canonical flatness instance. -/
instance :
    IsFlat (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) :=
  sheafification_isFlat J 𝒪 ℱ

end PresheafOfModules
