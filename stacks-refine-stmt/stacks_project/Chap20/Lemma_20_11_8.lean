import Mathlib
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The underlying abelian sheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ

/-- The underlying additive presheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingPresheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).1

/-- The lattice of opens of a ringed space has finite limits, so Čech complexes of open covers are
available. -/
instance opensHasFiniteLimits (X : RingedSpace.{u}) :
    HasFiniteLimits (Opens X.carrier) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The category of opens of a ringed space has finite products. -/
instance opensHasFiniteProducts (X : RingedSpace.{u}) :
    HasFiniteProducts (Opens X.carrier) :=
  inferInstance

/-- An `\mathcal O_X`-module has vanishing higher Čech cohomology on every open covering when the
positive-degree Čech cohomology of its underlying additive presheaf vanishes for every cover of
every open subset. -/
def HasVanishingHigherCechOnOpenCoverings
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) : Prop :=
  ∀ {U : Opens X.carrier} {ι : Type u} (𝒰 : ι → Opens X.carrier), iSup 𝒰 = U →
    ∀ p : ℕ, 0 < p →
      IsZero
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
          ((cechComplexFunctor 𝒰).obj (moduleUnderlyingPresheaf ℱ)))

-- Proof sketch: this is the defining expansion of
-- `HasVanishingHigherCechOnOpenCoverings`; apply the hypothesis to the chosen cover `𝒰`.
/-- Unfolding the higher Čech-vanishing hypothesis on a chosen cover yields vanishing of the
corresponding positive-degree Čech cohomology group. -/
theorem hasVanishingHigherCechOnOpenCoverings_apply
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X))
    (hℱ : HasVanishingHigherCechOnOpenCoverings ℱ)
    {U : Opens X.carrier} {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
        ((cechComplexFunctor 𝒰).obj (moduleUnderlyingPresheaf ℱ))) := sorry

-- Proof sketch: embed `ℱ` into an injective `\mathcal O_X`-module `ℐ`, let `ℚ := ℐ/ℱ`, and use
-- Lemmas `20.11.1`, `20.11.7`, `20.10.2`, and `13.20.4` to propagate the higher Čech-vanishing
-- hypothesis from `ℱ` to `ℚ`. The long exact cohomology sequence of
-- `0 ⟶ ℱ ⟶ ℐ ⟶ ℚ ⟶ 0` then gives the vanishing of `H^p(U, ℱ)` for every `p > 0` by induction.
/-- Lemma 20.11.8: if an `\mathcal O_X`-module has vanishing higher Čech cohomology for every
open covering of every open subset of `X`, then every higher sheaf cohomology group
`H^p(U, \mathcal F)` with `p > 0` is zero. -/
theorem higherCohomology_isZero_of_vanishingHigherCech_on_openCoverings
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : (RingedSpace.Modules X)) (hℱ : HasVanishingHigherCechOnOpenCoverings ℱ)
    (U : Opens X.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf ℱ).H' p U) := sorry

end AlgebraicGeometry.RingedSpace
