import Mathlib

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

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) :=
  inferInstance

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor
    (U : Opens X.carrier) :
    ringedSpaceModuleCat X ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The cochain-level functor underlying derived sections over `U`. -/
abbrev moduleSectionsAsAbelianToDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    CochainComplex (ringedSpaceModuleCat X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

-- Proof sketch: the category `Mod(\mathcal O_X)` is Grothendieck abelian, so K-injective
-- resolutions compute right derived functors. Applying this to the additive sections functor
-- `\Gamma(U,-)` produces the total right derived functor defining `R\Gamma(U,-)`.
/-- The cochain-level sections functor over `U` admits a total right derived functor. -/
theorem moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    (moduleSectionsAsAbelianToDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ringedSpaceModuleCat X) (ComplexShape.up ℤ)) := sorry

attribute [local instance] moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    DerivedCategory (ringedSpaceModuleCat X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (moduleSectionsAsAbelianToDerived X U).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ringedSpaceModuleCat X) (ComplexShape.up ℤ))

/-- The degree-`m` cohomology group `H^m(U, K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev moduleCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (K : DerivedCategory (ringedSpaceModuleCat X)) (m : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
    ((moduleSectionsAsAbelianDerived X U).obj K)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(K)` of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

-- Proof sketch: apply Lemma `20.37.9` with `d = 0` to identify `K` with the derived limit of its
-- truncation tower. For `U ∈ ℬ`, use the Milnor short exact sequence from `20.37.3.1` for that
-- tower. Example `20.29.3` computes the cohomology of each bounded-below truncation
-- `τ_{\ge -n} K` from its cohomology sheaves, and the hypothesis forces the resulting spectral
-- sequence to degenerate at `E₂`, giving `H^q(U, τ_{\ge -n} K) = H^0(U, H^q(τ_{\ge -n} K))`.
-- Once `n > -q`, these groups stabilize to `H^0(U, H^q(K))`, so the `R^1 \!\varprojlim` term
-- vanishes and the limit term is canonically `H^0(U, H^q(K))`.
/-- Lemma 20.37.10: let `(X, \mathcal O_X)` be a ringed space, let `K ∈ D(\mathcal O_X)`, and
let `ℬ` be a set of opens such that every open subset of `X` admits a covering by members of
`ℬ`. If for every `U ∈ ℬ`, every `q : ℤ`, and every `p > 0` one has
`H^p(U, H^q(K)) = 0`, then for every `U ∈ ℬ` and every `q : ℤ` the hypercohomology group
`H^q(U, K)` is canonically isomorphic to the degree-zero cohomology
`H^0(U, H^q(K))` of the cohomology sheaf. -/
theorem cohomologyOverBasisOpen_iso_zeroDegreeCohomologySheafSections
    (K : DerivedCategory (ringedSpaceModuleCat X))
    (ℬ : Set (Opens X.carrier))
    (hcover :
      ∀ V : Opens X.carrier,
        ∃ ι : Type u, ∃ 𝒰 : ι → Opens X.carrier, iSup 𝒰 = V ∧ ∀ i, 𝒰 i ∈ ℬ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ ℬ →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ, IsZero ((ringedSpaceCohomologySheaf X K q).H' p U))
    (U : Opens X.carrier) (hU : U ∈ ℬ) (q : ℤ) :
    IsIsomorphic
      (moduleCohomologyAtOpen X U K q)
      ((ringedSpaceCohomologySheaf X K q).H' 0 U) := sorry

end

end AlgebraicGeometry.RingedSpace
