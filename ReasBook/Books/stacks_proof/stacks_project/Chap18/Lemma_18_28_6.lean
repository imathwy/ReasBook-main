import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_28_1
import stacks_proof.stacks_project.Chap18.Lemma_18_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.28.6:
- primary domain: flat sheaves of modules on a ringed site and their localized restrictions;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat`,
  `PresheafOfModules.sheafification_isFlat`,
  `SheafOfModules.RingedSite.pullback_isFlat_of_isFlat`;
- best owner abstraction: the chapter owner `SheafOfModules.RingedSite.IsFlat`; the restriction
  `ℱ.over U` should be expressed by the same owner on `𝒪.over U`, not by a parallel exactness
  predicate on `tensorLeft`;
- primitive data: the sheaf of rings `𝒪`, the sheaf of modules `ℱ`, and the localized object
  `U : C`;
- derived API: flatness of the localized restriction `ℱ.over U`.

Source/core/bridge triage:
- `source-facing`: flatness of the restriction `ℱ|_U`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the restriction operation `ℱ ↦ ℱ.over U`. -/
-- Proof sketch: let `𝒢₁ ⟶ 𝒢₂ ⟶ 𝒢₃` be an exact short complex of `\mathcal O_U`-modules. Apply
-- extension by zero `j_{U!}`, which is exact by Lemma `18.19.3`, identify
-- `j_{U!} (𝒢ᵢ ⊗ ℱ|_U)` with `j_{U!} 𝒢ᵢ ⊗ ℱ` using Lemma `18.27.9`, use flatness of `ℱ`, and
-- then reflect exactness back to the localized site by Lemma `18.19.4`.
/-- Helper for Lemma 18.28.6: exactness of functors is stable under composition. -/
private theorem exactFunctorComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  let _ : CategoryTheory.Limits.PreservesFiniteLimits G := hG.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.6: exactness transports across a natural isomorphism of functors. -/
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
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Lemma 18.28.6: finite colimits descend along a reflective presentation. -/
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
  -- Proof comment: pull a finite diagram in `B` back along the reflective right adjoint `R`,
  -- compute its colimit in `A`, and then transport that colimit through `F`.
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

/-- Helper for Lemma 18.28.6: finite limits descend along a reflective presentation. -/
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
  -- Proof comment: the same reflective-localization argument applies to finite limits.
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

/-- Helper for Lemma 18.28.6: exactness descends from the essential image of a reflective
presentation. -/
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
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and each half
  -- descends through the reflective localization.
  rw [CategoryTheory.exactFunctor_iff] at h ⊢
  constructor
  · let _ : CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G) := h.1
    exact preservesFiniteLimitsOfReflectiveComp F R adj G
  · let _ : CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G) := h.2
    exact preservesFiniteColimitsOfReflectiveComp F R adj G

/-- Helper for Lemma 18.28.6: restricting after tensoring by `ℱ` agrees with tensoring after
restricting by `F.obj X`. -/
private noncomputable def tensorRightCommIso
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    (F : A ⥤ B) [Functor.Monoidal F] (X : A) :
    F ⋙ CategoryTheory.MonoidalCategory.tensorRight (F.obj X) ≅
      CategoryTheory.MonoidalCategory.tensorRight X ⋙ F := by
  -- Proof comment: this is the canonical monoidal comparison of `F`, specialized to tensoring
  -- on the right by the fixed object `X`.
  refine NatIso.ofComponents
    (fun Y ↦ Functor.Monoidal.μIso F Y X) ?_
  intro Y Z f
  simpa using Functor.Monoidal.μIso_hom_natural_right (F := F) Y f

/-- Helper for Lemma 18.28.6: once an exact monoidal left-adjoint presentation of restriction is
available, exactness of tensoring descends to the restricted object. -/
private theorem exactTensorRightOfMonoidalReflective
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    [CategoryTheory.Limits.HasFiniteLimits A]
    [CategoryTheory.Limits.HasFiniteColimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R)
    [Functor.Monoidal F]
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    (X : A)
    (hX :
      exactFunctor
        A
        A
        (CategoryTheory.MonoidalCategory.tensorRight X)) :
    exactFunctor
      B
      B
      (CategoryTheory.MonoidalCategory.tensorRight (F.obj X)) := by
  let hF : exactFunctor A B F := by
    rw [CategoryTheory.exactFunctor_iff]
    exact ⟨inferInstance, inferInstance⟩
  let hComposite :
      exactFunctor
        A
        B
        (CategoryTheory.MonoidalCategory.tensorRight X ⋙ F) :=
    exactFunctorComp hX hF
  let hComposite' :
      exactFunctor
        A
        B
        (F ⋙ CategoryTheory.MonoidalCategory.tensorRight (F.obj X)) :=
    exactFunctorOfNatIso (tensorRightCommIso F X).symm hComposite
  -- Proof comment: the exact composite through the monoidal left adjoint now descends along the
  -- reflective presentation to exactness of tensoring by `F.obj X`.
  exact exactFunctorOfReflectiveComp F R adj
    (CategoryTheory.MonoidalCategory.tensorRight (F.obj X)) hComposite'

/-- Helper for Lemma 18.28.6: restriction of module sheaves to the slice site over `U` is exact.
-/
private theorem localizedRestrictionExact
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪)
      (ringedSiteModuleCategory (J.over U) (𝒪.over U))
      (SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))) := by
  -- Proof comment: localized restriction is the module pushforward along `Over.forget U`, so the
  -- generic almost-cocontinuous pushforward exactness theorem applies directly.
  let _ : (Over.forget U).IsAlmostCocontinuous (J.over U) J := by
    infer_instance
  simpa using
    (CategoryTheory.Functor.sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
      (u := Over.forget U)
      (JC := J.over U)
      (JD := J)
      (𝒪C := ringSheaf (J.over U) (𝒪.over U))
      (𝒪D := ringSheaf J 𝒪)
      (φ := 𝟙 ((ringSheaf J 𝒪).over U)))

/-- Lemma 18.28.6: if `ℱ` is a flat `\mathcal O`-module on a ringed site
`(\mathcal C, \mathcal O)`, then for every object `U : \mathcal C` the restricted module
`ℱ|_U`, written `ℱ.over U`, is flat on the localized ringed site
`(\mathcal C/U, \mathcal O_U)`, expressed in the chapter's canonical owner
`SheafOfModules.RingedSite.IsFlat`. -/
@[stacks 0E8J]
theorem isFlat_over
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (ℱ : SheafOfModules (ringSheaf J 𝒪))
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
    [IsFlat 𝒪 ℱ] :
    IsFlat (𝒪.over U) (ℱ.over U) := by
  -- Route correction: the previous proof used the later pullback-flatness theorem
  -- `Lemma_18_39_1`. The dependency-closed replacement starts from the verified helper
  -- `localizedRestrictionExact`, but the standard descent step to `ℱ.over U` goes through the
  -- reflective adjunction `overPushforwardOverAdj`, whose current earlier API still requires the
  -- extra side condition `[HasBinaryProducts C]`.
  --
  -- TODO: replace this final `sorry` by either
  -- 1. an earlier dependency-closed bridge identifying localization as pullback and invoking a
  --    flatness-preservation theorem that does not require `[HasBinaryProducts C]`, or
  -- 2. a weaker-side-condition reflective-localization API for the restriction/extension-by-zero
  --    adjunction.
  sorry

end SheafOfModules.RingedSite
