import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying additive sheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℱ

/-- The underlying additive presheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev moduleUnderlyingPresheaf {X : RingedSpace.{u}}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).1

/-- The lattice of opens of a ringed space has finite limits, so Čech complexes of open covers are
available. -/
private instance basisOpensHasFiniteLimits (X : RingedSpace.{u}) :
    HasFiniteLimits (Opens X.carrier) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The category of opens of a ringed space has finite products. -/
private instance basisOpensHasFiniteProducts (X : RingedSpace.{u}) :
    HasFiniteProducts (Opens X.carrier) :=
  inferInstance

/-- A cover of a basis open by basis opens whose finite intersections remain in the basis. -/
structure BasisStableOpenCover {X : RingedSpace.{u}}
    (B : Set (Opens X.carrier)) (U : Opens X.carrier) where
  /-- The index type of the covering family. -/
  ι : Type u
  /-- The covering family of opens. -/
  cover : ι → Opens X.carrier
  /-- The covering family covers `U`. -/
  iSup_eq : iSup cover = U
  /-- Each member of the covering family belongs to the basis `B`. -/
  mem_basis : ∀ i, cover i ∈ B
  /-- Every finite intersection of members of the covering family still belongs to the basis. -/
  intersections_mem_basis : ∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (cover ∘ σ) ∈ B

namespace BasisStableOpenCover

/-- A basis-stable open cover refines another indexed open cover if each of its members is
contained in one member of the target cover. -/
def Refines {X : RingedSpace.{u}} {B : Set (Opens X.carrier)} {U : Opens X.carrier}
    (𝒰 : BasisStableOpenCover B U) {κ : Type u} (𝒱 : κ → Opens X.carrier) : Prop :=
  ∃ refine : 𝒰.ι → κ, ∀ i, 𝒰.cover i ≤ 𝒱 (refine i)

end BasisStableOpenCover

/-- An `\mathcal O_X`-module has a cofinal system of basis-stable coverings on which all positive
Čech cohomology groups vanish. -/
def HasCofinalBasisCechAcyclicCoverings
    {X : RingedSpace.{u}} (B : Set (Opens X.carrier))
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ B →
    ∀ {κ : Type u} (𝒱 : κ → Opens X.carrier), iSup 𝒱 = U →
      ∃ 𝒰 : BasisStableOpenCover B U,
        BasisStableOpenCover.Refines 𝒰 𝒱 ∧
          ∀ p : ℕ, 0 < p →
            IsZero
              ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
                ((cechComplexFunctor 𝒰.cover).obj (moduleUnderlyingPresheaf ℱ)))

-- Proof sketch: this is exactly the defining content of
-- `HasCofinalBasisCechAcyclicCoverings`, evaluated at the basis open `U` and the cover `𝒱`.
/-- Unfolding the cofinal basis-cover hypothesis produces a refining basis-stable cover with
vanishing positive Čech cohomology. -/
theorem hasCofinalBasisCechAcyclicCoverings_apply
    {X : RingedSpace.{u}} {B : Set (Opens X.carrier)}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X))
    (hℱ : HasCofinalBasisCechAcyclicCoverings B ℱ)
    {U : Opens X.carrier} (hU : U ∈ B)
    {κ : Type u} (𝒱 : κ → Opens X.carrier) (h𝒱 : iSup 𝒱 = U) :
    ∃ 𝒰 : BasisStableOpenCover B U,
      BasisStableOpenCover.Refines 𝒰 𝒱 ∧
        ∀ p : ℕ, 0 < p →
          IsZero
            ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
              ((cechComplexFunctor 𝒰.cover).obj (moduleUnderlyingPresheaf ℱ))) := sorry

-- Proof sketch: embed `ℱ` into an injective `\mathcal O_X`-module, use Lemmas `20.11.1` and
-- `20.11.7` together with the basis-stable cover hypothesis to propagate vanishing to the
-- quotient, and then induct on the cohomological degree via the long exact sequence attached to
-- `0 ⟶ ℱ ⟶ ℐ ⟶ ℚ ⟶ 0`. The basis assumption ensures the Čech complexes for covers in the cofinal
-- system are built from sections on opens still lying in `B`.
/-- Lemma 20.11.9: if `B` is a basis of a ringed space `X` and an `\mathcal O_X`-module
`\mathcal F` has vanishing positive Čech cohomology on a cofinal system of basis-stable coverings
of each basis open, then every higher cohomology group `H^p(U, \mathcal F)` vanishes for
`p > 0` and every basis open `U ∈ B`. -/
theorem higherCohomology_isZero_of_vanishingHigherCech_on_basisCoverings
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X))
    (hℱ : HasCofinalBasisCechAcyclicCoverings B ℱ)
    (U : Opens X.carrier) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf ℱ).H' p U) := sorry

end AlgebraicGeometry.RingedSpace
