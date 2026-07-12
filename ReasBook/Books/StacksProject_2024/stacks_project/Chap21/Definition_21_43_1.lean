import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/- This file owns the Section `21.43.1` source-facing object property `isQuasiCoherent` and the
associated full subcategory `QC`, together with the chaotic-site specialization data used by later
files. -/

/-
Domain-style sampling for the chaotic-site specialization:
- primary domain: canonical derived sections on a chaotic site and the canonical derived
  restriction/base-change functors on the corresponding section rings, viewed as the primitive
  inputs for the Section `21.43` owner `isQuasiCoherent`;
- sampled owner declarations:
  `SheafOfModules.evaluation`,
  `Functor.totalRightDerived`,
  `CategoryTheory.derivedTensorWithAlgebra`,
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`;
- best owner abstraction:
  `source-facing`: the canonical chaotic-site derived sections functor `chaoticRGamma` and the
    canonical derived tensor restriction expression
    `f ↦ derivedTensorWithAlgebra ((𝒪.1.map f.op).hom)`, which are the primitive specialization
    data for the Section `21.43` owner `isQuasiCoherent`;
  `core/canonical`: `SheafOfModules.evaluation`, `Functor.totalRightDerived`, and
    `derivedTensorWithAlgebra`, together with the general owners
    `CategoryTheory.ModulesOnCategory.isQuasiCoherent` and `QC`;
  `bridge/view`: later files supply comparison natural transformations between these functors and
    then reuse `isQuasiCoherent` / `QC` directly instead of introducing parallel specialization
    aliases.
- primitive vs. derived split:
  primitive data: the evaluation functor on module sheaves at `U` and the ring map
    `𝒪(V) → 𝒪(U)` attached to `f : U ⟶ V`;
  derived API: `chaoticRGamma 𝒪 U` as the derived sections owner and
    `derivedTensorWithAlgebra ((𝒪.1.map f.op).hom)` as the derived tensor restriction owner; the
    Section `21.43` property and full subcategory are then obtained by specializing the general
    owners `isQuasiCoherent` and `QC`.
-/

section

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

/-- The source-facing Section `21.43` object property cutting out those derived objects whose
comparison morphisms are isomorphisms on every arrow of `C`. -/
def isQuasiCoherent : ObjectProperty D :=
  fun K ↦ ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)

/-- Helper for Definition 21.43.1: unpacking `isQuasiCoherent` says exactly that every comparison
map attached to `K` is an isomorphism. -/
@[simp] theorem isQuasiCoherent_iff (K : D) :
    isQuasiCoherent 𝒪 RGamma derivedRestrict comparison K ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K) := by
  -- Unpack the owner definition; this is the source-facing criterion verbatim.
  rfl

/-- Definition 21.43.1: `QC(C, 𝒪)` is the canonical full subcategory attached to the
Section `21.43` comparison property. Concretely, its objects are those `K` for which, for every
arrow `f : U ⟶ V` in `C`, the derived base-change map encoded by
`(comparison f).app K :
  (derivedRestrict f).obj ((RGamma V).obj K) ⟶ (RGamma U).obj K`
is an isomorphism. -/
abbrev QC :=
  (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).FullSubcategory

/-- Helper for Definition 21.43.1: the underlying object of an element of `QC` satisfies the
comparison-isomorphism criterion. -/
@[simp] theorem qc_obj_isQuasiCoherent
    (K : QC 𝒪 RGamma derivedRestrict comparison) :
    isQuasiCoherent 𝒪 RGamma derivedRestrict comparison K.obj := by
  -- Objects of the full subcategory carry the defining property by construction.
  exact K.property

/-- Helper for Definition 21.43.1: every comparison map attached to an object of `QC` is an
isomorphism. -/
theorem qc_isIso_comparison
    (K : QC 𝒪 RGamma derivedRestrict comparison)
    {U V : C} (f : U ⟶ V) :
    IsIso ((comparison f).app K.obj) := by
  -- Evaluate the stored quasi-coherence property on the chosen arrow.
  exact (qc_obj_isQuasiCoherent 𝒪 RGamma derivedRestrict comparison K) f

end

section ChaoticSite

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

local notation "J" => (⊥ : GrothendieckTopology C)
local notation "𝒪J" => ringSheaf J 𝒪
local notation "Mod𝒪" => SheafOfModules 𝒪J
local notation "DMod𝒪" => DerivedCategory Mod𝒪
local notation "Qis𝒪" => HomotopyCategory.quasiIso Mod𝒪 (ComplexShape.up ℤ)

/-- The ordinary sections functor `Γ(U,-)` for modules over the chaotic site. -/
abbrev chaoticSections (U : C) : Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U)) :=
  SheafOfModules.evaluation 𝒪J (op U)

/-- The canonical derived sections functor `RΓ(U,-)` for the sheaf of rings `𝒪` on the
chaotic site of `C`. -/
noncomputable abbrev chaoticRGamma
    [∀ U : C, (chaoticSections 𝒪 U).Additive]
    [∀ U : C,
      Functor.HasRightDerivedFunctor (mapHomotopyCategoryToDerived (chaoticSections 𝒪 U)) Qis𝒪]
    (U : C) :
    DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
  Functor.totalRightDerived
    (mapHomotopyCategoryToDerived (chaoticSections 𝒪 U))
    (DerivedCategory.Qh : HomotopyCategory Mod𝒪 (ComplexShape.up ℤ) ⥤ DMod𝒪)
    Qis𝒪

/-- For `f : U ⟶ V`, the chaotic-site derived restriction functor is the canonical specialization
of `derivedTensorWithAlgebra` along the ring map `𝒪(V) ⟶ 𝒪(U)`. This abbreviation is the stable
Section `21.43` owner spelling for the repeatedly used specialization. -/
abbrev chaoticDerivedRestrict {U V : C} (f : U ⟶ V) :
    DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
      DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
  derivedTensorWithAlgebra ((𝒪.1.map f.op).hom)

end ChaoticSite

end CategoryTheory.ModulesOnCategory
