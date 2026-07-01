import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The restricted `RingCat`-valued structure sheaf on the open subset `U`. -/
private abbrev restrictedRingCatSheaf (U : Opens X.carrier) :=
  (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X)

local notation "ModX" => SheafOfModules (ringedSpaceRingCatSheaf X)
local notation "ModU" => SheafOfModules (restrictedRingCatSheaf U)
local notation "DModX" => DerivedCategory ModX
local notation "DModU" => DerivedCategory ModU
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DModX)
local notation "QU" => (DerivedCategory.Q : CochainComplex ModU ℤ ⥤ DModU)
local notation "QisX" => HomologicalComplex.quasiIso ModX (up ℤ)
local notation "QisU" => HomologicalComplex.quasiIso ModU (up ℤ)

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
private abbrev moduleRestrictionToOpen :
    ModX ⥤ ModU :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

-- Proof sketch: for an open immersion, module restriction is the inverse-image functor on module
-- sheaves. Its left adjoint is extension by zero, so this restriction functor is a right
-- adjoint.
/-- Restriction of module sheaves to an open subspace is a right adjoint. -/
private instance moduleRestrictionToOpen_isRightAdjoint :
    (moduleRestrictionToOpen U).IsRightAdjoint := sorry

/-- Extension by zero of `\mathcal O_U`-modules from the open subspace `U` back to `X`. -/
private noncomputable abbrev moduleExtensionByZeroFromOpen :
    ModU ⥤ ModX :=
  (moduleRestrictionToOpen U).leftAdjoint

-- Proof sketch: extension by zero is the chosen left adjoint to restriction to the open
-- subspace. The corresponding adjunction is obtained formally from
-- `Adjunction.ofIsRightAdjoint`.
/-- The chosen extension-by-zero functor is left adjoint to restriction to the open subspace. -/
private noncomputable abbrev moduleExtensionByZeroFromOpenAdjunction :
    moduleExtensionByZeroFromOpen U ⊣ moduleRestrictionToOpen U :=
  Adjunction.ofIsRightAdjoint (moduleRestrictionToOpen U)

-- Proof sketch: restriction to an open subspace is exact on the underlying abelian sheaves, and
-- the forgetful functor from module sheaves to abelian sheaves reflects finite limits and finite
-- colimits. Hence the module-valued restriction functor preserves both finite limits and finite
-- colimits.
/-- Restriction to an open subspace is exact on sheaves of modules. -/
private theorem moduleRestrictionToOpen_exact :
    exactFunctor ModX ModU (moduleRestrictionToOpen U) := sorry

-- Proof sketch: extension by zero is exact on underlying abelian sheaves for an open immersion,
-- and the module structure is transported functorially, so finite limits and finite colimits are
-- preserved on module sheaves as well.
/-- Extension by zero from an open subspace is exact on sheaves of modules. -/
private theorem moduleExtensionByZeroFromOpen_exact :
    exactFunctor ModU ModX (moduleExtensionByZeroFromOpen U) := sorry

/-- Restriction to an open subspace preserves finite limits. -/
private noncomputable instance moduleRestrictionToOpen_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestrictionToOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen U)).mp
    (moduleRestrictionToOpen_exact U)).1

/-- Restriction to an open subspace preserves finite colimits. -/
private noncomputable instance moduleRestrictionToOpen_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestrictionToOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen U)).mp
    (moduleRestrictionToOpen_exact U)).2

/-- Extension by zero from an open subspace preserves finite limits. -/
private noncomputable instance moduleExtensionByZeroFromOpen_preservesFiniteLimits :
    PreservesFiniteLimits (moduleExtensionByZeroFromOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleExtensionByZeroFromOpen U)).mp
    (moduleExtensionByZeroFromOpen_exact U)).1

/-- Extension by zero from an open subspace preserves finite colimits. -/
private noncomputable instance moduleExtensionByZeroFromOpen_preservesFiniteColimits :
    PreservesFiniteColimits (moduleExtensionByZeroFromOpen U) :=
  ((CategoryTheory.exactFunctor_iff (moduleExtensionByZeroFromOpen U)).mp
    (moduleExtensionByZeroFromOpen_exact U)).2

-- Proof sketch: any left exact or right exact functor between abelian categories is additive. The
-- exactness statement for restriction provides both hypotheses.
/-- Restriction to an open subspace is additive. -/
private instance moduleRestrictionToOpen_additive :
    (moduleRestrictionToOpen U).Additive := sorry

-- Proof sketch: any left exact or right exact functor between abelian categories is additive. The
-- exactness statement for extension by zero provides both hypotheses.
/-- Extension by zero from an open subspace is additive. -/
private instance moduleExtensionByZeroFromOpen_additive :
    (moduleExtensionByZeroFromOpen U).Additive := sorry

-- Proof sketch: exact extension by zero preserves quasi-isomorphisms, so the induced functor on
-- derived categories is the left derived functor of the cochain-level extension-by-zero functor.
/-- The derived functor induced by exact extension by zero is its left derived functor. -/
private theorem moduleExtensionByZeroFromOpen_mapDerivedCategory_isLeftDerivedFunctor :
    (moduleExtensionByZeroFromOpen U).mapDerivedCategory.IsLeftDerivedFunctor
      ((moduleExtensionByZeroFromOpen U).mapDerivedCategoryFactors.hom)
      QisU := sorry

attribute [local instance] moduleExtensionByZeroFromOpen_mapDerivedCategory_isLeftDerivedFunctor

/-- Exact open-subspace extension by zero has an everywhere-defined total left derived functor. -/
private noncomputable instance moduleExtensionByZeroFromOpen_hasLeftDerivedFunctor :
    ((moduleExtensionByZeroFromOpen U).mapHomologicalComplex (up ℤ) ⋙ QX).HasLeftDerivedFunctor
      QisU :=
  Functor.HasLeftDerivedFunctor.mk'
    ((moduleExtensionByZeroFromOpen U).mapDerivedCategory)
    ((moduleExtensionByZeroFromOpen U).mapDerivedCategoryFactors.hom)

-- Proof sketch: exact restriction to an open subspace preserves quasi-isomorphisms, so the
-- induced functor on derived categories is the right derived functor of the cochain-level
-- restriction functor.
/-- The derived functor induced by exact restriction to an open subspace is its right derived
functor. -/
private theorem moduleRestrictionToOpen_mapDerivedCategory_isRightDerivedFunctor :
    (moduleRestrictionToOpen U).mapDerivedCategory.IsRightDerivedFunctor
      ((moduleRestrictionToOpen U).mapDerivedCategoryFactors.inv)
      QisX := sorry

attribute [local instance] moduleRestrictionToOpen_mapDerivedCategory_isRightDerivedFunctor

/-- Exact open-subspace restriction has an everywhere-defined total right derived functor. -/
private noncomputable instance moduleRestrictionToOpen_hasRightDerivedFunctor :
    ((moduleRestrictionToOpen U).mapHomologicalComplex (up ℤ) ⋙ QU).HasRightDerivedFunctor
      QisX :=
  Functor.HasRightDerivedFunctor.mk'
    ((moduleRestrictionToOpen U).mapDerivedCategory)
    ((moduleRestrictionToOpen U).mapDerivedCategoryFactors.inv)

/-- The left derived extension-by-zero functor attached to the open immersion `j : U ↪ X`. -/
noncomputable abbrev moduleExtensionByZeroFromOpenDerived :
    DModU ⥤ DModX :=
  (((moduleExtensionByZeroFromOpen U).mapHomologicalComplex (up ℤ)) ⋙ QX).totalLeftDerived
    QU
    QisU

/-- The right derived restriction functor attached to the open immersion `j : U ↪ X`. -/
noncomputable abbrev moduleRestrictionToOpenDerived :
    DModX ⥤ DModU :=
  (((moduleRestrictionToOpen U).mapHomologicalComplex (up ℤ)) ⋙ QU).totalRightDerived
    QX
    QisX

-- Proof sketch: start from the underived adjunction
-- `openSubsetModuleSheafExtensionByZero U (ringedSpaceRingCatSheaf X) ⊣
-- moduleSheafRestrictionToOpen U (ringedSpaceRingCatSheaf X)`. Exactness of both functors
-- identifies extension by zero with its total left derived functor and restriction with its total
-- right derived functor; then apply the generic derived-adjunction theorem of Lemma `13.30.3`.
/-- Lemma 20.32.8: for a ringed space `(X, \mathcal O_X)` and an open subset `U \subset X`, the
restriction functor on derived categories is right adjoint to extension by zero along the open
immersion `j : (U, \mathcal O_U) \to (X, \mathcal O_X)`. In the present formalization this is the
adjunction between the derived extension-by-zero functor and the derived restriction functor on
sheaves of modules. -/
theorem moduleRestrictionToOpenDerived_rightAdjoint_to_extensionByZeroFromOpenDerived :
    Nonempty
      (moduleExtensionByZeroFromOpenDerived U ⊣
        moduleRestrictionToOpenDerived U) := sorry

end

end AlgebraicGeometry.RingedSpace
