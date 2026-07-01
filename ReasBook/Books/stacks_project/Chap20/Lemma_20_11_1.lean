import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying additive presheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev ringedSpaceModuleUnderlyingAddPresheaf
    {X : RingedSpace.{u}} (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℐ).1

/-- The additive group of sections of an `\mathcal O_X`-module over an open subset `U`. -/
private noncomputable abbrev ringedSpaceModuleSections
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) : AddCommGrpCat.{u} :=
  ((CategoryTheory.sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)).obj
    ((SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℐ)

/-- The Čech cohomology of the underlying additive presheaf of an `\mathcal O_X`-module with
respect to an indexed family of opens. -/
private noncomputable abbrev ringedSpaceModuleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) : AddCommGrpCat.{u} :=
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  letI : HasFiniteProducts (Opens X.carrier) := inferInstance
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
    ((CategoryTheory.cechComplexFunctor 𝒰).obj (ringedSpaceModuleUnderlyingAddPresheaf ℐ))

-- Proof sketch: the cover condition `iSup 𝒰 = U` identifies the union of the members of the cover
-- with `U`, and degree-zero Čech cohomology of the underlying additive sheaf computes the equalizer
-- of the sheaf gluing diagram. For a sheaf this equalizer is exactly the additive group of sections
-- on `U`.
/-- Lemma 20.11.1 (1): if `\mathcal I` is an injective `\mathcal O_X`-module and `\mathcal U`
is an open covering of `U`, then the degree-zero Čech cohomology of `\mathcal I` with respect to
`\mathcal U` identifies with the section group `\mathcal I(U)`. -/
theorem cech_cohomology_zero_iso_sections_of_injective
    {X : RingedSpace.{u}} {ι : Type u} (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) (hℐ : Injective ℐ) :
    Nonempty (ringedSpaceModuleCechCohomology 𝒰 ℐ 0 ≅
      ringedSpaceModuleSections U ℐ) := sorry

-- Proof sketch: an injective `\mathcal O_X`-module is injective in the ambient presheaf-module
-- category, so Lemma `20.10.5` applies to the Čech cohomology `δ`-functor of the covering. The
-- higher right derived functors of degree-zero sections vanish on injective objects, hence every
-- positive Čech cohomology group is zero.
/-- Lemma 20.11.1 (2): if `\mathcal I` is an injective `\mathcal O_X`-module and `\mathcal U`
is an open covering of `U`, then the positive-degree Čech cohomology of `\mathcal I` with respect
to `\mathcal U` vanishes. -/
theorem cech_cohomology_isZero_of_injective_succ
    {X : RingedSpace.{u}} {ι : Type u} (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) (hℐ : Injective ℐ)
    (p : ℕ) :
    IsZero (ringedSpaceModuleCechCohomology 𝒰 ℐ (p + 1)) := sorry

end AlgebraicGeometry.RingedSpace
