import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The category of `\mathcal O_U`-modules obtained by pulling the structure sheaf of `X` back to
the open subspace `U`. -/
abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X))

/-- The open complement `X \setminus Z` of a closed subset `Z`. -/
abbrev closedSubsetOpenComplement {X : RingedSpace.{u}} {Z : Set X.carrier}
    (hZ : IsClosed Z) : Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The structural ring-sheaf morphism attached to the inclusion of the open subspace `U`. -/
noncomputable abbrev ringedSpaceOpenSubsetStructureSheafHom
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    ringedSpaceRingCatSheaf X ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} U.inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
    (ringedSpaceRingCatSheaf X)

/-- Pushforward of modules from the open subspace `U` back to the ambient ringed space. -/
noncomputable abbrev modulePushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ ambientModuleCategory X :=
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
      DerivedCategory (ambientModuleCategory X) :=
  (modulePushforwardFromOpen U).mapDerivedCategory

/-- The support of an abelian sheaf on a topological space, defined by nonzero stalks. -/
def abelianSheafSupport {Y : TopCat.{u}} (ℱ : Y.Sheaf AddCommGrpCat.{u}) : Set Y :=
  { y | ¬ IsZero (ℱ.presheaf.stalk y) }

/-- The cohomology sheaf of a derived module over a sheaf of rings on a topological space. -/
abbrev moduleDerivedCohomologySheaf
    {Y : TopCat.{u}} (𝒪 : Y.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf 𝒪).obj
    ((DerivedCategory.homologyFunctor (SheafOfModules 𝒪) q).obj K)

/-- A derived module has cohomology supported on `T` when every cohomology sheaf is supported on
`T`. -/
def moduleDerivedCohomologySupportedOn
    {Y : TopCat.{u}} (𝒪 : Y.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (T : Set Y) : Prop :=
  ∀ q : ℤ, abelianSheafSupport (moduleDerivedCohomologySheaf 𝒪 K q) ⊆ T

-- Proof sketch: represent `K` by a K-injective complex on the open subspace `U`. Since
-- pushforward from an open immersion is exact, `Rj_* K` is computed by ordinary pushforward of
-- that representative. Stalks of the pushed-forward complex vanish outside `U`, hence in
-- particular on the closed subset `Z`; therefore every cohomology sheaf is supported in
-- `X \setminus Z`.
/-- Lemma 20.34.7: if `Z` is a closed subset of a ringed space `X` and `j : U \to X` is the
inclusion of an open subset with `U ∩ Z = ∅`, then for every `K ∈ D(\mathcal O_U)` the object
`Rj_* K` has cohomology sheaves supported in the open complement `X \setminus Z`. This is the
support-theoretic form used to express the vanishing of `R\mathcal H_Z(Rj_*K)`. -/
theorem pushforwardFromOpen_cohomologySupportedOn_complement_of_disjoint
    {Z : Set X.carrier} (hZ : IsClosed Z) (U : Opens X.carrier)
    (hUZ : Disjoint (U : Set X.carrier) Z)
    (K : DerivedCategory (openSubspaceModuleCategory X U)) :
    moduleDerivedCohomologySupportedOn
      (ringedSpaceRingCatSheaf X)
      ((moduleDerivedPushforwardFromOpen U).obj K)
      (closedSubsetOpenComplement hZ : Set X.carrier) := sorry

end

end AlgebraicGeometry.RingedSpace
