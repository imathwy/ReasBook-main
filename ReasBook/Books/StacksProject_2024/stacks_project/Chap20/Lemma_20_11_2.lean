import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_1
import StacksProject_2024.stacks_project.Chap20.Bounded_below_derived_sections_at_open
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3
import StacksProject_2024.stacks_project.Chap20.Lemma_20_10_2
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_11_1
import StacksProject_2024.stacks_project.Chap20.Sections_on_open
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomologicalComplex
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.11.2:
- primary domain: the Čech-to-cohomology comparison for `𝒪_X`-modules on a fixed open
  subset of a ringed space;
- sampled owner declarations:
  `ringedSiteModuleCechCohomology`,
  `ringedSiteModuleCechCohomology_zero_isomorphic_evaluation`,
  `ringedSpaceCechCohomologyDeltaFunctor`,
  `boundedBelowRightDerivedDeltaFunctor`,
  `SheafOfModules.evaluation`,
  `Functor.totalRightDerived`;
- best owner abstraction:
  `source-facing`: the degree-`p` comparison natural transformation
    `Čech H^p(𝒰, -) ⟶ H^p(U, -)` and its component map on one module;
  `core/canonical`: the ringed-site module Čech owner
    `ringedSiteModuleCechCohomology`, the degree-zero ringed-site evaluation comparison
    `ringedSiteModuleCechCohomology_zero_isomorphic_evaluation`, the Chapter 20 Čech
    `δ`-functor owner `ringedSpaceCechCohomologyDeltaFunctor`, the Chapter 13 owner
    `boundedBelowRightDerivedDeltaFunctor`, and the canonical bounded-below derived sections
    functor obtained from `Functor.totalRightDerived`;
  `bridge/view`: the passage from an indexed open family `𝒰 : ι → Opens X.carrier` with
    `iSup 𝒰 = U` to the slice-site covering family `openCoverOver U 𝒰 h𝒰`, and then the
    degreewise comparison from the Čech owner to the bounded-below derived sections owner.
- primitive data: the ringed space `X`, the open subset `U`, the indexed open family `𝒰`, and
  the cover equality `h𝒰 : iSup 𝒰 = U`;
- derived API: the module-valued Čech cohomology and cohomology owners on `U`, the canonical
  degree-`p` comparison natural transformation, its component map, and the underlying
  additive-group-valued comparison.

Source/core/bridge triage:
- `source-facing`: the comparison maps of Lemma `20.11.2`;
- `core/canonical`: `ringedSiteModuleCechCohomology`,
  `ringedSiteModuleCechCohomology_zero_isomorphic_evaluation`,
  `ringedSpaceCechCohomologyDeltaFunctor`, `boundedBelowRightDerivedDeltaFunctor`,
  `SheafOfModules.evaluation`, and `Functor.totalRightDerived`;
- `bridge/view`: the passage from the open family `𝒰` to `openCoverOver U 𝒰 h𝒰`, and from the
  bounded-below derived comparison to the ordinary module cohomology functors on `U`.
-/

section Comparison

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable (U : Opens X.carrier)

local notation "ModX" => RingedSpace.Modules X
local notation "ΓModU" => ModuleCat (sectionsRingOnOpen X U)

local instance : IsGrothendieckAbelian.{u} ModX := sheafModules_isGrothendieckAbelian X

private abbrev sectionsFunctor : ModX ⥤ ΓModU :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

private instance sectionsFunctor_additive :
    (sectionsFunctor U).Additive :=
  moduleSectionsEvaluation_additive X U

/-- The indexed open family `𝒰` over `U`, viewed as a family in `Over U`. -/
def openCoverOver
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) :
    ι → Over U :=
  fun i ↦ Over.mk (homOfLE (openFamily_le_of_iSup_eq U 𝒰 h𝒰.symm i))

/-- The family `openCoverOver U 𝒰 h𝒰` is a covering family of `U` in the slice site. -/
theorem openCoverOver_coversTop
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) :
    ((Opens.grothendieckTopology X.carrier).over U).CoversTop (openCoverOver U 𝒰 h𝒰) := by
  sorry

/-- The degree-`p` Čech cohomology of `ℱ` for the cover `𝒰` of `U`, viewed as a
`Γ(U, 𝒪_X)`-module. -/
abbrev moduleCechCohomologyAtOpen
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ) :
    ΓModU :=
  ringedSpaceModuleCechCohomology U (openCoverOver U 𝒰 h𝒰)
    ((SheafOfModules.forget X.ringCatSheaf).obj ℱ) p

/-- The degree-`p` Čech cohomology of a presheaf of `𝒪_X`-modules for the cover `𝒰` of `U`,
viewed as a `Γ(U, 𝒪_X)`-module. -/
abbrev presheafModuleCechCohomologyAtOpen
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : RingedSpace.PresheafModules X)
    (p : ℕ) : ΓModU :=
  ringedSpaceModuleCechCohomology U (openCoverOver U 𝒰 h𝒰) ℱ p

/-- The degree-`p` Čech cohomology functor for the cover `𝒰` of `U`, valued in
`Γ(U, 𝒪_X)`-modules. -/
noncomputable abbrev moduleCechCohomologyDegreeAtOpen
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ) :
    ModX ⥤+ ΓModU :=
  let T := (ringedSpaceCechCohomologyDegree U (openCoverOver U 𝒰 h𝒰) p).obj
  AdditiveFunctor.of (SheafOfModules.forget X.ringCatSheaf ⋙ T)

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
  [HasInjectiveResolutions ModX] in
@[simp] theorem moduleCechCohomologyDegreeAtOpen_obj
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ) (ℱ : ModX) :
    ((moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj.obj ℱ) =
      moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p := by
  change
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      (ringedSpaceCechCohomologyDegree U (openCoverOver U 𝒰 h𝒰) p).obj).obj ℱ) =
      moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p
  rfl

/-- The degree-`p` cohomology functor on the open subset `U`, valued in
`Γ(U, 𝒪_X)`-modules. -/
noncomputable abbrev moduleCohomologyDegreeAtOpen (p : ℕ) : ModX ⥤ ΓModU :=
  let F : ModX ⥤ ΓModU := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : F.Additive := moduleSectionsEvaluation_additive X U
  F.rightDerived p

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] in
@[simp] theorem moduleCohomologyDegreeAtOpen_obj (p : ℕ) (ℱ : ModX) :
    (moduleCohomologyDegreeAtOpen U p).obj ℱ = moduleCohomologyAtOpen U ℱ p := by
  simpa [moduleCohomologyDegreeAtOpen, moduleCohomologyAtOpen]
    using (rfl : ((moduleCohomologyDegreeAtOpen U p).obj ℱ) =
      ((moduleCohomologyDegreeAtOpen U p).obj ℱ))

private theorem moduleForget_map_shortExact
    {S : ShortComplex ModX} (hS : S.ShortExact) :
    (S.map (SheafOfModules.forget X.ringCatSheaf)).ShortExact := by
  sorry

private theorem moduleCechComplex_map_shortExact
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    {S : ShortComplex ModX} (hS : S.ShortExact) :
    ((S.map (SheafOfModules.forget X.ringCatSheaf)).map
      (ringedSpaceModuleCechComplexFunctor U (openCoverOver U 𝒰 h𝒰))).ShortExact := by
  let hExact := ringedSpaceModuleCechComplexFunctor_exact U (openCoverOver U 𝒰 h𝒰)
  let hPres := (exactFunctor_iff (ringedSpaceModuleCechComplexFunctor U (openCoverOver U 𝒰 h𝒰))).1
    hExact
  letI : PreservesFiniteLimits (ringedSpaceModuleCechComplexFunctor U (openCoverOver U 𝒰 h𝒰)) :=
    hPres.1
  letI :
      PreservesFiniteColimits (ringedSpaceModuleCechComplexFunctor U (openCoverOver U 𝒰 h𝒰)) :=
    hPres.2
  exact (moduleForget_map_shortExact hS).map_of_exact
    (ringedSpaceModuleCechComplexFunctor U (openCoverOver U 𝒰 h𝒰))

private noncomputable def moduleCechCohomologyConnectingMorphism
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    {S : ShortComplex ModX} (hS : S.ShortExact) (p : ℕ) :
    ((moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj).obj S.X₃ ⟶
      ((moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 (p + 1)).obj).obj S.X₁ :=
  eqToHom (moduleCechCohomologyDegreeAtOpen_obj U 𝒰 h𝒰 p S.X₃) ≫
    (moduleCechComplex_map_shortExact U 𝒰 h𝒰 hS).δ p (p + 1)
      (ComplexShape.up_mk p (p + 1) rfl) ≫
    eqToHom (moduleCechCohomologyDegreeAtOpen_obj U 𝒰 h𝒰 (p + 1) S.X₁).symm

private noncomputable def moduleCechCohomologyDeltaFunctor
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) :
    CohomologicalDeltaFunctor ModX ΓModU where
  F := moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰
  δ := fun {_} hS p ↦ moduleCechCohomologyConnectingMorphism U 𝒰 h𝒰 hS p
  mono_map_f_zero := fun {_} hS ↦ by
    sorry
  exact₅ := fun {_} hS p ↦ by
    sorry
  δ_naturality := fun {_ _} hS hT φ p ↦ by
    sorry

@[simp] private theorem moduleCechCohomologyDeltaFunctor_obj
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ) :
    ((moduleCechCohomologyDeltaFunctor U 𝒰 h𝒰 p).obj) =
      (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj :=
  rfl

private theorem moduleCechCohomologyDeltaFunctor_isUniversal
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) :
    (moduleCechCohomologyDeltaFunctor U 𝒰 h𝒰).IsUniversal := by
  sorry

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] in
/-- A cohomological `δ`-functor on `X.Modules` computes the open cohomology of `U` if it is
universal and its degree-`p` branch is `moduleCohomologyDegreeAtOpen U p`. -/
def IsModuleCohomologyDeltaFunctorAtOpen
    (T : CohomologicalDeltaFunctor ModX ΓModU) : Prop :=
  CohomologicalDeltaFunctor.IsUniversal T ∧
    ∀ p : ℕ, (T p).obj = moduleCohomologyDegreeAtOpen U p

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] in
/-- A degree-`p` natural transformation is a Čech-to-cohomology comparison if it is induced by a
morphism to a universal cohomological `δ`-functor computing cohomology on `U`, whose degree-zero
branch is identified with the canonical Čech `H⁰` comparison via a pointwise isomorphism to
sections. -/
def IsModuleCechToModuleCohomologyNatTrans
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ)
    (τ : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj ⟶
      moduleCohomologyDegreeAtOpen U p) : Prop :=
  ∃ T : CohomologicalDeltaFunctor ModX ΓModU,
    ∃ hT : IsModuleCohomologyDeltaFunctorAtOpen U T,
      ∃ δτ : moduleCechCohomologyDeltaFunctor U 𝒰 h𝒰 ⟶ T,
        (∃ τ₀ : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 0).obj ⟶ sectionsFunctor U,
          (∀ ℱ : ModX, IsIso (τ₀.app ℱ)) ∧
            ∃ σ₀ : sectionsFunctor U ⟶ (T 0).obj,
              (∀ ℱ : ModX, IsIso (σ₀.app ℱ)) ∧
                δτ.app 0 =
                  eqToHom (moduleCechCohomologyDeltaFunctor_obj U 𝒰 h𝒰 0) ≫
                    τ₀ ≫ σ₀) ∧
        τ =
          eqToHom (moduleCechCohomologyDeltaFunctor_obj U 𝒰 h𝒰 p).symm ≫
            δτ.app p ≫
              eqToHom (hT.2 p)

/-- Lemma 20.11.2: for each degree `p`, there is a unique Čech-to-cohomology comparison natural
transformation valued in `Γ(U, 𝒪_X)`-modules. -/
@[stacks 01EQ]
theorem existsUnique_moduleCechToModuleCohomologyNatTrans
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ) :
    ∃! τ : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj ⟶
        moduleCohomologyDegreeAtOpen U p,
      IsModuleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p τ := by
  sorry

/-- There exists a degree-`p` Čech-to-cohomology comparison natural transformation valued in
`Γ(U, 𝒪_X)`-modules. -/
theorem exists_moduleCechToModuleCohomologyNatTrans
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ) :
    ∃ τ : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj ⟶ moduleCohomologyDegreeAtOpen U p,
      IsModuleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p τ :=
  ExistsUnique.exists (existsUnique_moduleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p)

theorem moduleCechToModuleCohomologyNatTrans_eq_of_spec
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (p : ℕ)
    {τ τ' : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj ⟶
        moduleCohomologyDegreeAtOpen U p}
    (hτ : IsModuleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p τ)
    (hτ' : IsModuleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p τ') :
    τ = τ' :=
  (existsUnique_moduleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p).unique hτ hτ'

/-- The component morphism at `ℱ` induced by a degree-`p` Čech-to-cohomology comparison natural
transformation. -/
def moduleCechToModuleCohomologyMapOfNatTrans
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ)
    (τ : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj ⟶
      moduleCohomologyDegreeAtOpen U p) :
    moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p :=
  eqToHom (moduleCechCohomologyDegreeAtOpen_obj U 𝒰 h𝒰 p ℱ).symm ≫
    τ.app ℱ ≫
      eqToHom (moduleCohomologyDegreeAtOpen_obj U p ℱ)

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] in
/-- A morphism on the degree-`p` cohomology object of one module is a Čech-to-cohomology
comparison if it is induced by a degree-`p` Čech-to-cohomology comparison natural
transformation. -/
def IsModuleCechToModuleCohomologyMap
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ)
    (f : moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p) : Prop :=
  ∃ τ : (moduleCechCohomologyDegreeAtOpen U 𝒰 h𝒰 p).obj ⟶ moduleCohomologyDegreeAtOpen U p,
    IsModuleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p τ ∧
      f = moduleCechToModuleCohomologyMapOfNatTrans U 𝒰 h𝒰 ℱ p τ

theorem moduleCechToModuleCohomologyMap_eq_of_spec
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ)
    {f g : moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p}
    (hf : IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p f)
    (hg : IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p g) :
    f = g := by
  rcases hf with ⟨τ, hτ, rfl⟩
  rcases hg with ⟨τ', hτ', rfl⟩
  have hτeq : τ = τ' :=
    moduleCechToModuleCohomologyNatTrans_eq_of_spec U 𝒰 h𝒰 p hτ hτ'
  subst hτeq
  rfl

/-- Lemma 20.11.2: for each `ℱ` and each degree `p`, there is a unique Čech-to-cohomology
comparison morphism valued in `Γ(U, 𝒪_X)`-modules. -/
@[stacks 01EQ]
theorem existsUnique_moduleCechToModuleCohomologyMap
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ) :
    ∃! f : moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p,
      IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p f := by
  rcases exists_moduleCechToModuleCohomologyNatTrans U 𝒰 h𝒰 p with ⟨τ, hτ⟩
  refine ⟨moduleCechToModuleCohomologyMapOfNatTrans U 𝒰 h𝒰 ℱ p τ, ?_⟩
  refine ⟨⟨τ, hτ, rfl⟩, ?_⟩
  intro g hg
  exact moduleCechToModuleCohomologyMap_eq_of_spec U 𝒰 h𝒰 ℱ p hg ⟨τ, hτ, rfl⟩

theorem moduleCechCohomologyAtOpenForget_obj_eq
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ) :
    (forget₂ ΓModU AddCommGrpCat.{u}).obj (moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p) =
      ((moduleUnderlyingPresheaf X ⋙
          cechComplexFunctor 𝒰 ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj ℱ) := by
  sorry

theorem moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology
    (ℱ : ModX) (p : ℕ) :
    (forget₂ ΓModU AddCommGrpCat.{u}).obj (moduleCohomologyAtOpen U ℱ p) =
      ((moduleUnderlyingSheaf X).obj ℱ).H' p U := by
  /- Proof sketch: forget the `Γ(U, 𝒪_X)`-module structure on the degree-`p`
  right-derived sections object, then identify the resulting additive-group object with the
  sheaf-cohomology owner `H'` of the underlying abelian sheaf on `U`. -/
  sorry

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] in
/-- A morphism to the cohomology of the underlying additive sheaf is a Čech-to-sheaf-cohomology
comparison if it is induced from a Čech-to-module-cohomology comparison by the canonical
identifications of forgotten module Čech cohomology and forgotten module cohomology with the
corresponding underlying-sheaf cohomology objects. -/
def IsModuleCechToUnderlyingSheafCohomologyMap
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ)
    (f : moduleCechCohomology 𝒰 ℱ p ⟶ ((moduleUnderlyingSheaf X).obj ℱ).H' p U) : Prop :=
  ∃ g : moduleCechCohomologyAtOpen U 𝒰 h𝒰 ℱ p ⟶ moduleCohomologyAtOpen U ℱ p,
    IsModuleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p g ∧
      f =
        (eqToIso (moduleCechCohomologyAtOpenForget_obj_eq U 𝒰 h𝒰 ℱ p)).inv ≫
          (forget₂ ΓModU AddCommGrpCat.{u}).map g ≫
            (eqToIso (moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology U ℱ p)).hom

theorem moduleCechToUnderlyingSheafCohomologyMap_eq_of_spec
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ)
    {f g : moduleCechCohomology 𝒰 ℱ p ⟶ ((moduleUnderlyingSheaf X).obj ℱ).H' p U}
    (hf : IsModuleCechToUnderlyingSheafCohomologyMap U 𝒰 h𝒰 ℱ p f)
    (hg : IsModuleCechToUnderlyingSheafCohomologyMap U 𝒰 h𝒰 ℱ p g) :
    f = g := by
  rcases hf with ⟨f', hf', rfl⟩
  rcases hg with ⟨g', hg', rfl⟩
  have hfg : f' = g' :=
    moduleCechToModuleCohomologyMap_eq_of_spec U 𝒰 h𝒰 ℱ p hf' hg'
  subst hfg
  rfl

/-- Lemma 20.11.2: for each `ℱ` and each degree `p`, there is a unique Čech-to-sheaf-cohomology
comparison morphism on the underlying additive sheaf of `ℱ` over `U`. -/
@[stacks 01EQ]
theorem existsUnique_moduleCechToUnderlyingSheafCohomologyMap
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ) :
    ∃! f : moduleCechCohomology 𝒰 ℱ p ⟶ ((moduleUnderlyingSheaf X).obj ℱ).H' p U,
      IsModuleCechToUnderlyingSheafCohomologyMap U 𝒰 h𝒰 ℱ p f := by
  rcases existsUnique_moduleCechToModuleCohomologyMap U 𝒰 h𝒰 ℱ p with ⟨g, hg, huniq⟩
  let f₀ : moduleCechCohomology 𝒰 ℱ p ⟶ ((moduleUnderlyingSheaf X).obj ℱ).H' p U :=
    (eqToIso (moduleCechCohomologyAtOpenForget_obj_eq U 𝒰 h𝒰 ℱ p)).inv ≫
      (forget₂ ΓModU AddCommGrpCat.{u}).map g ≫
        (eqToIso (moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology U ℱ p)).hom
  refine ⟨f₀, ?_⟩
  · refine ⟨⟨g, hg, rfl⟩, ?_⟩
    intro f hf
    exact moduleCechToUnderlyingSheafCohomologyMap_eq_of_spec U 𝒰 h𝒰 ℱ p hf ⟨g, hg, rfl⟩

/-- There exists a Čech-to-sheaf-cohomology comparison from `moduleCechCohomology 𝒰 ℱ p` to the
cohomology of the underlying additive sheaf of `ℱ` on `U`. -/
theorem exists_moduleCechToUnderlyingSheafCohomologyMap
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (ℱ : ModX) (p : ℕ) :
    ∃ f : moduleCechCohomology 𝒰 ℱ p ⟶ ((moduleUnderlyingSheaf X).obj ℱ).H' p U,
      IsModuleCechToUnderlyingSheafCohomologyMap U 𝒰 h𝒰 ℱ p f :=
  ExistsUnique.exists (existsUnique_moduleCechToUnderlyingSheafCohomologyMap U 𝒰 h𝒰 ℱ p)

end Comparison

end AlgebraicGeometry.RingedSpace
