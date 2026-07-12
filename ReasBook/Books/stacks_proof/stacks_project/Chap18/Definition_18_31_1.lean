import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

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
@[stacks 04JB]
abbrev IsFlat (f : X ⟶ Y) [(SheafOfModules.pushforward f.structureSheafMap).IsRightAdjoint] : Prop :=
  exactFunctor
    (SheafOfModules.{max u v} Y.structureSheaf)
    (SheafOfModules.{max u v} X.structureSheaf)
    (f^*)

/-- Lemma 18.31.2 (2): flatness of a morphism of ringed sites is exactly exactness of pullback on
module sheaves. -/
theorem IsFlat.pullback_exact (f : X ⟶ Y)
    [(SheafOfModules.pushforward f.structureSheafMap).IsRightAdjoint] (hf : IsFlat f) :
    exactFunctor
      (SheafOfModules.{max u v} Y.structureSheaf)
      (SheafOfModules.{max u v} X.structureSheaf)
      (f^*) := by
  simpa [IsFlat] using hf

instance instExactFunctor_modulePullback_of_isFlat
    (f : X ⟶ Y) [(SheafOfModules.pushforward f.structureSheafMap).IsRightAdjoint]
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

/-- Helper for Chap18 Definition 18 31 1: transporting an adjunction across a right natural
isomorphism composes the old transpose with the comparison on the pushforward side. -/
private theorem ofNatIsoRight_homEquiv_apply
    {A : Type*} [Category A] {B : Type*} [Category B]
    {F : A ⥤ B} {G H : B ⥤ A} (adj : F ⊣ G) (iso : G ≅ H)
    {X' : A} {Y' : B} (m : F.obj X' ⟶ Y') :
    ((adj.ofNatIsoRight iso).homEquiv X' Y') m =
      adj.homEquiv X' Y' m ≫ iso.hom.app Y' := by
  -- Proof comment: expanding `ofNatIsoRight` shows that its Hom-equivalence is the original
  -- transpose followed by the right-side comparison isomorphism.
  simp [Adjunction.homEquiv, Adjunction.ofNatIsoRight, Category.assoc]

/-- Helper for Chap18 Definition 18 31 1: transposing an inverse-image structure-sheaf map recovers
its defining pushforward-form structure-sheaf map. -/
private theorem inverseImageStructureSheafMap_homEquiv
    (f : X ⟶ Y) :
    let adj := f.base.sheafAdjunctionContinuous CommRingCat.{u} JD JC
    adj.homEquiv _ _ (f^♯) =
      Functor.preimage (sheafCompose JD (forget₂ CommRingCat RingCat))
        (show (sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
            (sheafCompose JD (forget₂ CommRingCat RingCat)).obj
              ((f.base.sheafPushforwardContinuous CommRingCat.{u} JD JC).obj 𝒪) from
          f.structureSheafMap) := by
  -- Proof comment: `f^♯` was defined as exactly the transpose of the displayed structure-sheaf
  -- map under the continuous-site adjunction.
  dsimp [inverseImageStructureSheafMap]
  exact Equiv.apply_symm_apply _ _

/-- Helper for Definition 18.31.1: pullback along the inverse-image presentation morphism is
exact. -/
private theorem inverseImagePresentationPullbackExact
    (f : X ⟶ Y) :
    exactFunctor _ _
      (SheafOfModules.pullback
        (inverseImagePresentationHom (JC := JC) f).structureSheafMap) := by
  -- TODO: the intended route is still that inverse-image presentation pullback is the canonical
  -- site pullback, but the current imported instance search no longer finds the exactness halves
  -- directly from `inferInstance`.
  sorry

/-- Helper for Chap18 Definition 18 31 1: on a fixed site, flatness of a structure-sheaf morphism
is exactly exactness of the associated same-site pullback functor. -/
private theorem sameSitePullbackExact_iff_isFlatHom
    {𝒪₁ 𝒪₂ : Sheaf JC CommRingCat.{u}}
    [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory JC 𝒪₁)]
    (α : 𝒪₁ ⟶ 𝒪₂) :
    exactFunctor _ _
      (SheafOfModules.pullback
        (SheafOfModules.RingedSite.ringedSiteStructureMap α)) ↔
      SheafOfModules.RingedSite.IsFlatHom α := by
  -- TODO: the statement is the correct owner-level bridge, but the present library spelling of
  -- same-site pullback is no longer definitionally aligned enough for the former `simpa`.
  sorry

/-- In the commutative presentation, flatness of a morphism of ringed sites is equivalently
expressed by flatness of the inverse-image structure-sheaf map `f^\sharp`. -/
theorem isFlat_iff_isFlatHom (f : X ⟶ Y)
    [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory JC (f⁻¹𝒪))]
    :
    RingedSite.Hom.IsFlat f ↔ SheafOfModules.RingedSite.IsFlatHom (f^♯) := by
  -- Proof comment: factor `f^*` through pullback to the inverse-image presentation site and the
  -- same-site pullback along `f^♯`, then read same-site exactness as the defining tensor exactness
  -- in `IsFlatHom`.
  have e :
      SheafOfModules.pullback
          (inverseImagePresentationHom (JC := JC) f).structureSheafMap ⋙
        SheafOfModules.pullback
          (SheafOfModules.RingedSite.ringedSiteStructureMap (f^♯)) ≅
      (f^*) := by
    -- TODO: the `pullbackComp` factorization is reduced to one explicit normalization:
    -- identify the composite structure-sheaf map
    -- `(inverseImagePresentationHom f).structureSheafMap ≫
    --    (f.base.sheafPushforwardContinuous _ _ _).map (ringedSiteStructureMap (f^♯))`
    -- with `f.structureSheafMap`. The new helper `inverseImageStructureSheafMap_homEquiv`
    -- isolates the adjunction side of this comparison.
    sorry
  constructor
  · intro hf
    have hcomp :
        exactFunctor _ _
          (SheafOfModules.pullback
            (inverseImagePresentationHom (JC := JC) f).structureSheafMap ⋙
              SheafOfModules.pullback
                (SheafOfModules.RingedSite.ringedSiteStructureMap (f^♯))) := by
      -- Proof comment: transport exactness of `f^*` back across the factorization isomorphism `e`.
      exact exactFunctorOfNatIso e.symm (by simpa [IsFlat] using hf)
    have hinv :
        exactFunctor _ _
          (SheafOfModules.pullback
            (inverseImagePresentationHom (JC := JC) f).structureSheafMap) :=
      inverseImagePresentationPullbackExact (JC := JC) f
    -- Route correction: exactness of the composite factorization of `f^*` does not by itself
    -- imply exactness of the same-site pullback along `f^♯`; the missing step is a reflection
    -- argument through the inverse-image-presentation factor.
    have hsame :
        exactFunctor _ _
          (SheafOfModules.pullback
            (SheafOfModules.RingedSite.ringedSiteStructureMap (f^♯))) := by
      -- TODO: prove that exactness of the same-site pullback is reflected from `hcomp` through
      -- the exact inverse-image-presentation factor `hinv`. The missing bridge is either a
      -- restriction-of-scalars short-exact reflection lemma for `f^♯`, or the equivalent
      -- sectionwise comparison with tensoring by `(f^♯).app U`.
      sorry
    -- Proof comment: once the same-site pullback is known exact, `IsFlatHom` is just its owner
    -- definition rewritten on the restricted target unit module.
    exact (sameSitePullbackExact_iff_isFlatHom (JC := JC) (α := f^♯)).1 hsame
  · intro hf
    have hsame :
        exactFunctor _ _
          (SheafOfModules.pullback
            (SheafOfModules.RingedSite.ringedSiteStructureMap (f^♯))) :=
      (sameSitePullbackExact_iff_isFlatHom (JC := JC) (α := f^♯)).2 hf
    have hinv :
        exactFunctor _ _
          (SheafOfModules.pullback
            (inverseImagePresentationHom (JC := JC) f).structureSheafMap) :=
      inverseImagePresentationPullbackExact (JC := JC) f
    have hcomp :
        exactFunctor _ _
          (SheafOfModules.pullback
            (inverseImagePresentationHom (JC := JC) f).structureSheafMap ⋙
              SheafOfModules.pullback
                (SheafOfModules.RingedSite.ringedSiteStructureMap (f^♯))) :=
      exactFunctorComp hinv hsame
    have hf' : exactFunctor _ _ (f^*) :=
      exactFunctorOfNatIso e hcomp
    simpa [IsFlat] using hf'

end CommPresentations

end RingedSite.Hom
