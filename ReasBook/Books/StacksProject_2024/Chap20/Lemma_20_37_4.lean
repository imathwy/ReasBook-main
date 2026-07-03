import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap19.Lemma_19_13_6

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
variable [IsGrothendieckAbelian.{v} (Modules X)]
variable [CategoryWithHomology (Modules X)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory (Modules X)) n)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance sheafModulesAbelian : Abelian (Modules X) := inferInstance

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
local instance sheafModulesHasDerivedCategory : HasDerivedCategory (Modules X) :=
  HasDerivedCategory.standard (Modules X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor
    (U : Opens X.carrier) :
    Modules X ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor U).Additive] :
    DerivedCategory (Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor U)

/-- The degree-`m` cohomology group `H^m(U, K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev moduleCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor U).Additive]
    (K : DerivedCategory (Modules X)) (m : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
    ((moduleSectionsAsAbelianDerived U).obj K)

/-- The inverse system `n ↦ \mathcal F_n(U)` of underlying abelian groups over a fixed open set
`U`. -/
abbrev moduleUnderlyingSectionsTowerAtOpen
    (ℱ : ℕᵒᵖ ⥤ Modules X) (U : Opens X.carrier) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ℱ ⋙ SheafOfModules.toSheaf (ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The Milnor cokernel model for `R^1 \!\varprojlim_n \mathcal F_n(U)` on the underlying
abelian groups of sections. -/
abbrev moduleUnderlyingSectionsFirstDerivedLimitAtOpen
    (ℱ : ℕᵒᵖ ⥤ Modules X) (U : Opens X.carrier) :
    AddCommGrpCat.{u} :=
  cokernel (derivedLimitDifferenceMap (moduleUnderlyingSectionsTowerAtOpen ℱ U))

variable (ℱ : ℕᵒᵖ ⥤ Modules X) (ℬ : Set (Opens X.carrier))

variable
  (hcover :
    ∀ U : Opens X.carrier,
      ∃ ι : Type u, ∃ 𝒰 : ι → Opens X.carrier, iSup 𝒰 = U ∧ ∀ i, 𝒰 i ∈ ℬ)
  (hacyclic :
    ∀ (U : Opens X.carrier), U ∈ ℬ →
      ∀ (n p : ℕ), 0 < p →
        IsZero
          (moduleCohomologyAtOpen U
            ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
              (ℱ.obj (op n)))
            (p : ℤ)))
  (hR1 :
    ∀ (U : Opens X.carrier), U ∈ ℬ →
      IsZero (moduleUnderlyingSectionsFirstDerivedLimitAtOpen ℱ U))

-- Proof sketch: apply the openwise Milnor short exact sequence from `20.37.3.1` to the tower
-- `\mathcal F_n[0]`. On each `U ∈ ℬ`, positive stagewise cohomology vanishes by `hacyclic`, while
-- the `R^1 \!\varprojlim` term for sections vanishes by `hR1`, so the objectwise cohomology of the
-- derived limit is concentrated in degree `0` with degree-zero part equal to the ordinary inverse
-- limit presheaf. Since every open is covered by members of `ℬ`, sheafification gives the same
-- statement for cohomology sheaves, hence the derived limit is represented by `lim ℱ` in degree
-- zero.
/-- Lemma 20.37.4 (1): if every open subset of `X` is covered by opens in `ℬ`, if
`H^p(U, \mathcal F_n) = 0` for every `U ∈ ℬ`, every `n`, and every `p > 0`, and if the inverse
system of sections `\mathcal F_n(U)` has vanishing `R^1 \!\varprojlim` for every `U ∈ ℬ`, then
the ordinary inverse limit sheaf `\varprojlim_n \mathcal F_n` computes the derived inverse limit
of the tower `(\mathcal F_n)`. -/
theorem single_limit_isDerivedLimit_of_basis_acyclicity :
    IsDerivedLimit
      (ℱ ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ))
      ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj (limit ℱ)) := sorry

-- Proof sketch: apply the Milnor short exact sequence from `20.37.3.1` to the degree-zero tower
-- `\mathcal F_n[0]` and to the derived limit identified in part `(1)` with `(\varprojlim_n
-- \mathcal F_n)[0]`. For `U ∈ ℬ` and `p > 0`, the right term `\varprojlim_n H^p(U,\mathcal F_n)`
-- vanishes by `hacyclic`, and the left `R^1 \!\varprojlim` term vanishes by `hR1` when `p = 1`
-- and by the stagewise vanishing in degree `p - 1` when `p > 1`. Hence `H^p(U, \varprojlim_n
-- \mathcal F_n) = 0`.
/-- Lemma 20.37.4 (2): under the same hypotheses, the inverse limit sheaf
`\varprojlim_n \mathcal F_n` has vanishing higher cohomology on every open set `U ∈ ℬ`; that is,
`H^p(U, \varprojlim_n \mathcal F_n) = 0` for all `p > 0`. -/
theorem higherCohomologyAtBasisOpen_isZero_of_basis_acyclicity
    (U : Opens X.carrier) (hU : U ∈ ℬ) (p : ℕ) (hp : 0 < p) :
    IsZero
      (moduleCohomologyAtOpen U
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj (limit ℱ))
        (p : ℤ)) := sorry

end

end AlgebraicGeometry.RingedSpace
