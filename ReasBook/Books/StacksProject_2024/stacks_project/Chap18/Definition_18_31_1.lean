import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap18.Definition_18_13_1
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Definition 18.31.1:
- primary domain: flat morphisms of ringed sites, with the commutative inverse-image
  structure-sheaf map only as a later bridge;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `RingedSite.Hom.(^*)`,
  `exactFunctor`,
  `SheafOfModules.RingedSite.IsFlatHom`,
- best owner abstraction: the source-facing owner is the bundled ringed-site morphism
  `f : X ⟶ Y`, with `RingedSite.Hom.IsFlat` expressed directly by exactness of the canonical
  pullback functor `f^*`; the commutative owner `IsFlatHom` is only a bridge under stronger
  assumptions;
- primitive data: the bundled morphism `f : X ⟶ Y`;
- derived API: the pullback notation `f^*`, the exactness owner `exactFunctor _ _ (f^*)`, and,
  in the commutative bridge layer, the inverse-image structure sheaf and map `f^♯`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.Hom.IsFlat`;
- `core/canonical`: `exactFunctor _ _ (f^*)`;
- `bridge/view`: the commutative inverse-image structure-sheaf map `f^♯` and the companion
  reformulation `isFlat_iff_isFlatHom`. -/

open scoped RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}}

/-- Definition 18.31.1: a morphism of ringed sites is flat when the canonical pullback functor on
sheaves of modules is exact. -/
abbrev IsFlat (f : X ⟶ Y)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint] : Prop :=
  exactFunctor
    (SheafOfModules.{max u v} Y.structureSheaf)
    (SheafOfModules.{max u v} X.structureSheaf)
    (f^*)

/-- Lemma 18.31.2 (2): flatness of a morphism of ringed sites is exactly exactness of pullback on
module sheaves. -/
theorem IsFlat.pullback_exact (f : X ⟶ Y)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
    (hf : IsFlat f) :
    exactFunctor
      (SheafOfModules.{max u v} Y.structureSheaf)
      (SheafOfModules.{max u v} X.structureSheaf)
      (f^*) := by
  simpa [IsFlat] using hf

instance instExactFunctor_modulePullback_of_isFlat
    (f : X ⟶ Y) [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
    [hf : Fact (IsFlat f)] :
    exactFunctor
      (SheafOfModules.{max u v} Y.structureSheaf)
      (SheafOfModules.{max u v} X.structureSheaf)
      (f^*) := by
  simpa using IsFlat.pullback_exact f hf.1

end

end RingedSite.Hom

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Helper for Definition 18.31.1: a sheaf of modules on a commutative ringed site is flat when
tensoring on the right with it is an exact endofunctor. -/
class IsFlat
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Tensoring on the right by `ℱ` is exact on sheaves of `\mathcal O`-modules. -/
  exact_tensor :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪)
      (ringedSiteModuleCategory J 𝒪)
      (CategoryTheory.MonoidalCategory.tensorRight ℱ)

/-- Helper for Definition 18.31.1: a same-site morphism of structure sheaves is flat when the
target unit module, viewed by restriction of scalars, is flat over the source. -/
def IsFlatHom
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat 𝒪 ((restrictionAlong α).obj (unitModule J 𝒪'))

/-- Helper for Definition 18.31.1: unfolding same-site flatness gives flatness of the restricted
unit module. -/
theorem isFlatHom_iff
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (α : 𝒪 ⟶ 𝒪') :
    IsFlatHom α ↔ IsFlat 𝒪 ((restrictionAlong α).obj (unitModule J 𝒪')) := by
  -- Proof comment: `IsFlatHom` was introduced as the source-facing wrapper around the flatness
  -- of the restricted target unit module, so the statement is definitional.
  rfl

end

end SheafOfModules.RingedSite

namespace RingedSite.Hom

section CommPresentations

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JC.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

local instance base_isContinuous_comm (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

/-- Helper for Definition 18.31.1: the intermediate ringed site with structure sheaf
`f^{-1}\mathcal O_Y` over the source site of `f`. -/
private abbrev inverseImagePresentationSite (f : X ⟶ Y) :
    RingedSite.{u, u} :=
  RingedSite.ofCommRingSheaf JC
    ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪')

/-- Helper for Definition 18.31.1: the inverse-image presentation morphism carries
`(X, f^{-1}\mathcal O_Y)` back to `Y` with adjoint structure-sheaf map the identity on
`f^{-1}\mathcal O_Y`. -/
private abbrev inverseImagePresentationHom (f : X ⟶ Y) :
    inverseImagePresentationSite (JC := JC) f ⟶ Y :=
  { base := f.base
    isMorphismOfSites := f.isMorphismOfSites
    structureSheafMap :=
      (sheafCompose JD (forget₂ CommRingCat RingCat)).map
        (((f.base.sheafAdjunctionContinuous CommRingCat.{u} JD JC).homEquiv
          𝒪' ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪')) (𝟙 _)) }

/-- Helper for Definition 18.31.1: exactness transports across a natural isomorphism of
functors. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A] {B : Type*} [Category B]
    {F G : A ⥤ B} (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both
  -- properties transport along a natural isomorphism of functors.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Definition 18.31.1: exactness is stable under composition of functors. -/
private theorem exactFunctorComp
    {A : Type*} [Category A] {B : Type*} [Category B] {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both halves
  -- compose functorially.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- The inverse-image commutative structure sheaf `f^{-1}\mathcal O_Y` attached to a morphism of
commutative ringed sites presented by `f : X ⟶ Y`. -/
abbrev inverseImageStructureSheaf (f : X ⟶ Y) :
    Sheaf JC CommRingCat.{u} :=
  (f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪'

/- Textbook notation for the inverse-image commutative structure sheaf `f^{-1}\mathcal O_Y`. -/
scoped notation:max f:max "⁻¹𝒪" => inverseImageStructureSheaf f

/-- The adjoint same-site form `f^\sharp : f^{-1}\mathcal O_Y \to \mathcal O_X` of the
structure-sheaf map of a morphism of commutative ringed sites. -/
abbrev inverseImageStructureSheafMap (f : X ⟶ Y) :
    f⁻¹𝒪 ⟶ 𝒪 :=
  ((f.base.sheafAdjunctionContinuous CommRingCat.{u} JD JC).homEquiv _ _).symm
    (Functor.preimage (sheafCompose JD (forget₂ CommRingCat RingCat))
      (show (sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
          (sheafCompose JD (forget₂ CommRingCat RingCat)).obj
            ((f.base.sheafPushforwardContinuous CommRingCat.{u} JD JC).obj 𝒪) from
        f.structureSheafMap))

/- Bridge notation for the inverse-image structure-sheaf map `f^\sharp`. -/
scoped notation:max f:max "^♯" => inverseImageStructureSheafMap f

/-- Helper for Definition 18.31.1: forgetting module structure to additive sheaves reflects and
preserves short exactness on a fixed commutative ringed site. -/
private theorem shortExact_toSheaf_iff
    {𝒪₀ : Sheaf JC CommRingCat.{u}}
    (S : ShortComplex (SheafOfModules (SheafOfModules.RingedSite.ringSheaf JC 𝒪₀))) :
    (S.map (SheafOfModules.toSheaf (SheafOfModules.RingedSite.ringSheaf JC 𝒪₀))).ShortExact ↔
      S.ShortExact := by
  sorry

/-- In the commutative presentation, flatness of a morphism of ringed sites is equivalently
expressed by flatness of the inverse-image structure-sheaf map `f^\sharp`. -/
theorem isFlat_iff_isFlatHom (f : X ⟶ Y)
    [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory JC (f⁻¹𝒪))]
    :
    RingedSite.Hom.IsFlat f ↔ SheafOfModules.RingedSite.IsFlatHom (f^♯) := by
  sorry

end CommPresentations

end RingedSite.Hom
