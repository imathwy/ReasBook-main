import Mathlib
import StacksProject_2024.Chap20.Lemma_20_32_2

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The support of an abelian sheaf on a topological space, defined by nonzero stalks. -/
def abelianSheafSupport {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) : Set X :=
  { x | ¬ IsZero (ℱ.presheaf.stalk x) }

/-- The cohomology sheaf of a derived module over a sheaf of rings on a topological space. -/
abbrev moduleDerivedCohomologySheaf
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf 𝒪).obj
    ((DerivedCategory.homologyFunctor (SheafOfModules 𝒪) q).obj K)

/-- A derived module has cohomology supported on `T` when every cohomology sheaf is supported on
`T`. -/
def moduleDerivedCohomologySupportedOn
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (T : Set X) : Prop :=
  ∀ q : ℤ, abelianSheafSupport (moduleDerivedCohomologySheaf 𝒪 K q) ⊆ T

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  (RingedSpace.Modules X)

/-- The structural ring-sheaf morphism attached to the inclusion of the open subspace `U`. -/
noncomputable abbrev ringedSpaceOpenSubsetStructureSheafHom
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (RingedSpace.ringCatSheaf X) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} U.inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
    (RingedSpace.ringCatSheaf X)

/-- Pushforward of modules from the open subspace `U` back to the ambient ringed space. -/
noncomputable abbrev modulePushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pushforward (ringedSpaceOpenSubsetStructureSheafHom U)

/-- Pushforward from an open subspace is additive on module sheaves. -/
instance modulePushforwardFromOpen_additive
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive := sorry

/-- Pushforward from an open subspace preserves finite limits on module sheaves. -/
instance modulePushforwardFromOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (modulePushforwardFromOpen U) := sorry

/-- Pushforward from an open subspace preserves finite colimits on module sheaves. -/
instance modulePushforwardFromOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (modulePushforwardFromOpen U) := sorry

/-- The derived pushforward functor from the open subspace `U` back to `X`. -/
noncomputable abbrev moduleDerivedPushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (RingedSpace.Modules X) :=
  (modulePushforwardFromOpen U).mapDerivedCategory

/-- Extension by zero from the open subspace `U` is additive on module sheaves. -/
instance moduleExtensionByZeroFromOpen_additive
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

/-- Extension by zero from the open subspace `U` preserves finite limits on module sheaves. -/
instance moduleExtensionByZeroFromOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

/-- Extension by zero from the open subspace `U` preserves finite colimits on module sheaves. -/
instance moduleExtensionByZeroFromOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

/-- The derived extension-by-zero functor attached to the open immersion `j : U ↪ X`. -/
noncomputable abbrev moduleExtensionByZeroFromOpenDerived
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (RingedSpace.Modules X) :=
  (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory

section

variable {X : RingedSpace.{u}}

-- Proof sketch: let `V = X \ T`. The support hypothesis implies that every cohomology sheaf of
-- `E` restricts to zero on `V`, hence `E|_V = 0`. By Lemma `20.32.4`, the restriction of
-- `Rj_* (E|_U)` to `V` is also zero, while its restriction to `U` identifies with `E|_U`.
-- Comparing on the open cover `X = U ∪ V` gives the claimed isomorphism.
/-- Lemma 20.33.6 (1): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`E ∈ D(\mathcal O_X)` is supported on a closed subset `T ⊆ U`, then `E` is canonically
isomorphic to `Rj_*(E|_U)`. In this formalization `Rj_*` is represented by the exact pushforward
functor from the open subspace to `X`. -/
theorem isIsomorphic_pushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier) {T : Set X.carrier} (hT_closed : IsClosed T)
    (hTU : T ⊆ (U : Set X.carrier))
    (E : DerivedCategory (ambientModuleCategory X))
    (hE : moduleDerivedCohomologySupportedOn (RingedSpace.ringCatSheaf X) E T) :
    IsIsomorphic E
      ((moduleDerivedPushforwardFromOpen U).obj
        ((moduleRestrictionToOpenDerived X U).obj E)) := sorry

-- Proof sketch: let `V = X \ T` and `W = U ∩ V`. The support hypothesis implies that the
-- restriction of `F` to `W` has zero cohomology sheaves, hence vanishes in the derived category.
-- Lemma `20.32.4` then gives `(Rj_* F)|_V = 0`, while ordinary extension by zero also restricts
-- to zero on `V`. Both `j_! F` and `Rj_* F` restrict to `F` on `U`, so comparison on the cover
-- `X = U ∪ V` yields the isomorphism.
/-- Lemma 20.33.6 (2): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`F ∈ D(\mathcal O_U)` is supported on a closed subset `T ⊆ U`, then `j_! F` is canonically
isomorphic to `Rj_* F`. Here `j_!` is the derived extension-by-zero functor on module sheaves. -/
theorem extensionByZeroDerived_isIsomorphic_pushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier) {T : Set X.carrier} (hT_closed : IsClosed T)
    (hTU : T ⊆ (U : Set X.carrier))
    (F : DerivedCategory (openSubspaceModuleCategory X U))
    (hF : moduleDerivedCohomologySupportedOn
      ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))
      F
      (Subtype.val ⁻¹' T)) :
    IsIsomorphic
      ((moduleExtensionByZeroFromOpenDerived U).obj F)
      ((moduleDerivedPushforwardFromOpen U).obj F) := sorry

end

end AlgebraicGeometry.RingedSpace
