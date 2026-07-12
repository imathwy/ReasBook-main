import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits
open SheafOfModules.RingedSite
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

local notation "PMod(" 𝒪 ")" => PresheafOfModules 𝒪
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪
local notation "FAdd(" 𝒪 ")" => PresheafOfModules.toPresheaf 𝒪
local notation "IsFlat" => SheafOfModules.RingedSite.IsFlat

open CategoryTheory.ShortComplex

/- Domain-style sampling for Lemma 18.28.4:
- primary domain: sheafification of locally flat presheaves of modules, with the core
  sheafification machinery owned by the Chapter 18 flatness API for sheaves of modules;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `PresheafOfModules.moduleSheafification`,
  `PresheafOfModules.sheafificationRingMap`,
  `tensorRight`,
  `exactFunctor`;
- best owner abstraction: the source-facing result should be stated directly in the chapter owner
  `SheafOfModules.RingedSite.IsFlat` for the sheafified module
  `((moduleSheafification J 𝒪).obj ℱ)` over `commRingSheafification J 𝒪`; exactness of tensoring
  is then derived API via the field `IsFlat.exact_tensor`;
- primitive data: a presheaf of commutative rings `𝒪`, a presheaf module
  `ℱ : PresheafOfModules (ringPresheaf 𝒪)`, and the local sectionwise flatness hypothesis;
- derived API: exactness of the sheaf tensor-right functor on
  `SheafOfModules (ringSheaf J (commRingSheafification J 𝒪))`.

Layer triage:
- `source-facing`: the local-flatness criterion for the sheafified module;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the exactness consequence expressed by `IsFlat.exact_tensor`.
-/

/- The reflective-localization part of the proof is the same as Lemma 18.28.3. The only new
ingredient here is the source-faithful bridge from coverwise sectionwise flatness to monicity after
sheafification. -/
/-- Helper for Lemma 18.28.4: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and those
  -- preservation properties compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  let _ : CategoryTheory.Limits.PreservesFiniteLimits G := hG.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.4: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctor_of_natIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B} (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the functor
  -- isomorphism.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso e⟩

/-- Helper for Lemma 18.28.4: finite colimits descend along a reflective presentation. -/
private theorem preservesFiniteColimits_of_reflective_comp
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
  -- compute its colimit in `A`, and then push it forward along `F`.
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

/-- Helper for Lemma 18.28.4: finite limits descend along a reflective presentation. -/
private theorem preservesFiniteLimits_of_reflective_comp
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
  -- Proof comment: the same reflective argument works for finite limits by replacing colimits
  -- with limits throughout.
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

/-- Helper for Lemma 18.28.4: exactness descends along a reflective presentation. -/
private theorem exactFunctor_of_reflective_comp
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
  -- preservation, and each half descends along the reflective presentation.
  rw [CategoryTheory.exactFunctor_iff] at h ⊢
  constructor
  · let _ : CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G) := h.1
    exact preservesFiniteLimits_of_reflective_comp F R adj G
  · let _ : CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G) := h.2
    exact preservesFiniteColimits_of_reflective_comp F R adj G

/-- Helper for Lemma 18.28.4: sheafifying after tensoring by a presheaf module agrees
functorially with tensoring after sheafification. -/
private noncomputable def moduleSheafificationTensorComparison
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    [MonoidalCategory (Mod(commRingSheafification J 𝒪))]
    (M N : PMod(ringPresheaf 𝒪)) :
    (moduleSheafification J 𝒪).obj (PresheafOfModules.Monoidal.tensorObj M N) ⟶
      (CategoryTheory.MonoidalCategory.tensorObj
        ((moduleSheafification J 𝒪).obj M)
        ((moduleSheafification J 𝒪).obj N) : Mod(commRingSheafification J 𝒪)) :=
  let S : PMod(ringPresheaf 𝒪) ⥤ Mod(commRingSheafification J 𝒪) :=
    PresheafOfModules.sheafification (sheafificationRingMap J 𝒪)
  (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J 𝒪)).symm
    (show PresheafOfModules.Monoidal.tensorObj M N ⟶
        (PresheafOfModules.restrictScalars (sheafificationRingMap J 𝒪)).obj
          ((SheafOfModules.forget (ringSheaf J (commRingSheafification J 𝒪))).obj
            (MonoidalCategoryStruct.tensorObj (S.obj M) (S.obj N)) from
      (PresheafOfModules.Monoidal.tensorHom
          ((PresheafOfModules.sheafificationAdjunction (sheafificationRingMap J 𝒪)).unit.app M)
          ((PresheafOfModules.sheafificationAdjunction (sheafificationRingMap J 𝒪)).unit.app N)) ≫
        Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars (sheafificationRingMap J 𝒪))
          ((SheafOfModules.forget (ringSheaf J (commRingSheafification J 𝒪))).obj (S.obj M))
          ((SheafOfModules.forget (ringSheaf J (commRingSheafification J 𝒪))).obj (S.obj N)))

/-- Helper for Lemma 18.28.4: the sheafification/tensor comparison morphism is an isomorphism. -/
private instance moduleSheafificationTensorComparison_isIso
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    [MonoidalCategory (Mod(commRingSheafification J 𝒪))]
    (M N : PMod(ringPresheaf 𝒪)) :
    IsIso (moduleSheafificationTensorComparison (J := J) (𝒪 := 𝒪) M N) := by
  rw [← isIso_iff_of_reflects_iso
    (moduleSheafificationTensorComparison (J := J) (𝒪 := 𝒪) M N)
    (SheafOfModules.toSheaf (ringSheaf J (commRingSheafification J 𝒪)))]
  simp [moduleSheafificationTensorComparison,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]

/-- Helper for Lemma 18.28.4: sheafifying after tensoring by a presheaf module agrees
functorially with tensoring after sheafification. -/
private noncomputable def moduleSheafification_tensorRight_iso
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    [MonoidalCategory (Mod(commRingSheafification J 𝒪))]
    (ℱ' : PMod(ringPresheaf 𝒪)) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ' ⋙ moduleSheafification J 𝒪 ≅
      moduleSheafification J 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorRight
          ((moduleSheafification J 𝒪).obj ℱ') := by
  -- Proof comment: package the objectwise sheafification/tensor comparison into a natural
  -- isomorphism of endofunctors.
  refine NatIso.ofComponents
    (fun X ↦ asIso (moduleSheafificationTensorComparison (J := J) (𝒪 := 𝒪) X ℱ')) ?_
  intro X Y f
  -- Proof comment: this is the naturality square of the tensor map determined by the two unit
  -- morphisms into the sheafifications.
  apply (SheafOfModules.toSheaf (ringSheaf J (commRingSheafification J 𝒪))).map_injective
  simp [moduleSheafificationTensorComparison]

/-- Helper for Lemma 18.28.4: in an abelian target, preserving monomorphisms together with
finite colimits upgrades a functor to an exact functor. -/
private theorem exact_of_preserves_monomorphisms_and_finite_colimits
    {A : Type*} {B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B)
    [F.Additive]
    [PreservesFiniteColimits F]
    (hMono : F.PreservesMonomorphisms) :
    exactFunctor A B F := by
  let _ : F.PreservesMonomorphisms := hMono
  let _ : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  -- Proof comment: homology preservation recovers finite-limit preservation, so the exactness
  -- criterion becomes available.
  exact
    (exactFunctor_iff F).2
      ⟨F.preservesFiniteLimits_of_preservesHomology, inferInstance⟩

/-- Helper for Lemma 18.28.4: the right adjoint of module sheafification along
`\mathcal O \to \mathcal O^\#`. -/
private noncomputable abbrev sheafificationRightAdjoint
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Mod(commRingSheafification J 𝒪) ⥤ PMod(ringPresheaf 𝒪) :=
  SheafOfModules.forget (ringSheaf J (commRingSheafification J 𝒪)) ⋙
    PresheafOfModules.restrictScalars (sheafificationRingMap J 𝒪)

/-
The helper below does not use the additive-sheaf composition instance directly; omit it to keep
the theorem-local section-variable set minimal.
-/
omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Helper for Lemma 18.28.4: exactness of tensoring by `\mathcal F^\#` descends from the
essential image of module sheafification to all sheaf modules. -/
private theorem tensorRight_exact_of_sheafification_image
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    [MonoidalCategory (Mod(commRingSheafification J 𝒪))]
    (ℱ : PMod(ringPresheaf 𝒪))
    (hComposite :
      exactFunctor
        (PMod(ringPresheaf 𝒪))
        (Mod(commRingSheafification J 𝒪))
        (moduleSheafification J 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ))) :
    exactFunctor
      (Mod(commRingSheafification J 𝒪))
      (Mod(commRingSheafification J 𝒪))
      (CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ)) := by
  -- Proof comment: module sheafification is a reflective localization, so exactness on its
  -- essential image descends through the counit isomorphism to all sheaf-module diagrams.
  let R := sheafificationRightAdjoint (J := J) 𝒪
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

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Helper for Lemma 18.28.4: a Type-valued presheaf morphism is locally injective once every
object has a covering on which all component maps are injective. -/
private theorem isLocallyInjective_of_cover_by_componentwise_injective
    {F G : Cᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hcover :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Function.Injective (η.app (op V))) :
    Presheaf.IsLocallyInjective J η := by
  -- Proof comment: on the chosen covering family, equality after applying `η` can be cancelled
  -- componentwise; closure under precomposition extends this to the generated sieve.
  refine ⟨fun {X} x y hxy ↦ ?_⟩
  obtain ⟨R, hR, hRinj⟩ := hcover X.unop
  refine J.superset_covering ?_ hR
  intro Y g hg
  rw [Sieve.generate_apply] at hg
  rcases hg with ⟨V, k, f, hf, hk⟩
  have hfg : F.map f.op x = F.map f.op y := by
    exact (hRinj f hf) <|
      (FunctorToTypes.naturality _ _ η f.op x).trans <|
        (congrArg (G.map f.op) hxy).trans
          (FunctorToTypes.naturality _ _ η f.op y).symm
  change F.map g.op x = F.map g.op y
  calc
    F.map g.op x = F.map k.op (F.map f.op x) := by
      rw [← hk]
      simp [op_comp]
    _ = F.map k.op (F.map f.op y) := by simpa using congrArg (F.map k.op) hfg
    _ = F.map g.op y := by
      rw [← hk]
      simp [op_comp]

/-- Helper for Lemma 18.28.4: after tensoring a monomorphism of presheaf modules with the locally
flat presheaf `\mathcal F`, module sheafification upgrades the resulting coverwise-injective map
to a monomorphism of sheaves. -/
private theorem mono_moduleSheafification_tensor_map_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (ℱ : PMod(ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V)))
    {M N : PMod(ringPresheaf 𝒪)} (α : M ⟶ N) [Mono α] :
    Mono ((moduleSheafification J 𝒪).map
      ((CategoryTheory.MonoidalCategory.tensorRight ℱ).map α)) := by
  let β := (CategoryTheory.MonoidalCategory.tensorRight ℱ).map α
  let η := (FAdd(ringPresheaf 𝒪)).map β
  have hLocInjForget :
      Presheaf.IsLocallyInjective J
        (Functor.whiskerRight η (forget AddCommGrpCat.{u})) := by
    refine isLocallyInjective_of_cover_by_componentwise_injective (J := J)
      (η := Functor.whiskerRight η (forget AddCommGrpCat.{u})) ?_
    intro U
    obtain ⟨R, hR, hflat⟩ := hlocal U
    refine ⟨R, hR, ?_⟩
    intro V f hf
    let _ : Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V)) := hflat f hf
    have hαinj :
        Function.Injective (ModuleCat.Hom.hom (α.app (op V))) :=
      PresheafOfModules.injective_of_mono α (op V)
    simpa [β, η] using
      (Module.Flat.rTensor_preserves_injective_linearMap (R := 𝒪.obj (op V))
        (M := ℱ.obj (op V)) (f := ModuleCat.Hom.hom (α.app (op V))) hαinj)
  have hLocInj :
      Presheaf.IsLocallyInjective J η :=
    (Presheaf.isLocallyInjective_forget_iff (J := J) (φ := η)).1 hLocInjForget
  let τ :
      (presheafToSheaf J AddCommGrpCat.{u}).obj
          ((FAdd(ringPresheaf 𝒪)).obj ((CategoryTheory.MonoidalCategory.tensorRight ℱ).obj M)) ⟶
        (presheafToSheaf J AddCommGrpCat.{u}).obj
          ((FAdd(ringPresheaf 𝒪)).obj ((CategoryTheory.MonoidalCategory.tensorRight ℱ).obj N)) :=
    (presheafToSheaf J AddCommGrpCat.{u}).map η
  have hLocInjSheaf : Sheaf.IsLocallyInjective τ := by
    exact (Presheaf.isLocallyInjective_presheafToSheaf_map_iff (J := J) η).2 hLocInj
  let T := SheafOfModules.toSheaf (ringSheaf J (commRingSheafification J 𝒪))
  have hMonoMap : Mono ((moduleSheafification J 𝒪).map β) := by
    rw [PresheafOfModules.sheafification_map (sheafificationRingMap J 𝒪) β]
    let _ : Sheaf.IsLocallyInjective τ := hLocInjSheaf
    simpa [τ, PresheafOfModules.sheafifyMap] using
      (Sheaf.mono_of_isLocallyInjective τ)
  exact hMonoMap

/-- Helper for Lemma 18.28.4: tensoring with the locally flat presheaf `\mathcal F` and then
sheafifying is an exact functor on presheaf modules. -/
private theorem tensorRight_moduleSheafification_exact_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (ℱ : PMod(ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    exactFunctor
      (PMod(ringPresheaf 𝒪))
      (Mod(commRingSheafification J 𝒪))
      (CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification J 𝒪) := by
  let F := CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification J 𝒪
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F)
      (.inr ((CategoryTheory.rightExactFunctor_iff F).2 inferInstance))
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := by infer_instance
  let hMono : F.PreservesMonomorphisms := by
    refine ⟨fun {M N} α _ ↦ ?_⟩
    simpa [F] using
      mono_moduleSheafification_tensor_map_of_locally_flat (J := J) (𝒪 := 𝒪) (ℱ := ℱ) hlocal α
  -- Proof comment: finite-colimit preservation is formal, and the local flatness hypothesis
  -- supplies preservation of monomorphisms through the coverwise injectivity argument above.
  exact exact_of_preserves_monomorphisms_and_finite_colimits F hMono

-- Proof sketch: use the local-flatness hypothesis to reduce injectivity of tensoring with
-- `\mathcal F^\#` to injectivity after passing to a covering on which the section modules of
-- `\mathcal F` are flat; then apply exactness of module sheafification and the local criterion
-- that a morphism of presheaves which is injective on a cover sheafifies to a monomorphism.
/-- Lemma 18.28.4: if every object of the site has a covering on which the section modules of a
presheaf `\mathcal F` are flat over the corresponding sections of `\mathcal O`, then the
associated sheaf `\mathcal F^\#` is flat over the sheafified structure sheaf `\mathcal O^\#`,
expressed in the chapter's canonical owner `SheafOfModules.RingedSite.IsFlat`. -/
@[stacks 0GN1]
theorem sheafification_isFlat_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    [MonoidalCategory (Mod(commRingSheafification J 𝒪))]
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    IsFlat (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) := by
  -- Proof comment: exactness of tensoring with `ℱ` survives sheafification through the monoidal
  -- comparison, and reflective descent promotes that exactness from the sheafification image to
  -- all sheaf modules.
  refine ⟨?_⟩
  let hCompositePresheaf :
      exactFunctor
        (PMod(ringPresheaf 𝒪))
        (Mod(commRingSheafification J 𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification J 𝒪) :=
    tensorRight_moduleSheafification_exact_of_locally_flat (J := J) (𝒪 := 𝒪) (ℱ := ℱ) hlocal
  let hCompositeSheaf :
      exactFunctor
        (PMod(ringPresheaf 𝒪))
        (Mod(commRingSheafification J 𝒪))
        (moduleSheafification J 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ)) :=
    exactFunctor_of_natIso
      (moduleSheafification_tensorRight_iso (J := J) (𝒪 := 𝒪) (ℱ' := ℱ))
      hCompositePresheaf
  exact tensorRight_exact_of_sheafification_image (J := J) (𝒪 := 𝒪) (ℱ := ℱ) hCompositeSheaf

/-- Exactness companion to Lemma 18.28.4: the canonical flatness statement implies that
tensoring on the right by `\mathcal F^\#` is exact on sheaves of `\mathcal O^\#`-modules. -/
theorem sheafification_exact_tensor_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    [MonoidalCategory (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))]
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    exactFunctor
      (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))
      (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))
      (CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ)) :=
  (sheafification_isFlat_of_locally_flat J 𝒪 ℱ hlocal).exact_tensor

end PresheafOfModules
