import Mathlib
import stacks_project.Chap20.Lemma_20_11_11
import stacks_project.Chap20.Lemma_20_32_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [IsGrothendieckAbelian.{v} (RingedSpace.Modules X)]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
private abbrev moduleSectionsAsAbelianFunctor
    (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
private abbrev moduleSectionsAsAbelianDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor X U)

/-- The degree-`m` cohomology group `H^m(U, K)` of a derived `\mathcal O_X`-module `K`. -/
private abbrev moduleCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (K : DerivedCategory (RingedSpace.Modules X)) (m : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
    ((moduleSectionsAsAbelianDerived X U).obj K)

/-- The sequential inverse system `n ↦ H^m(U, K_n)` attached to a tower in
`D(\mathcal O_X)`. -/
private abbrev moduleCohomologyTowerAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X)) (m : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Ksys ⋙ moduleSectionsAsAbelianDerived X U) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} m

/-- A model for `R^1 \!\varprojlim H^q(U, K_n)`, given by the cokernel of the Milnor difference
map on the tower `n ↦ H^q(U, K_n)`. -/
private abbrev firstDerivedLimitCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X)) (q : ℤ) :
    AddCommGrpCat.{u} :=
  cokernel (derivedLimitDifferenceMap (moduleCohomologyTowerAtOpen X U Ksys q))

/-- The transition map `H^m(U, K_n) → H^m(U, K_i)` for `i ≤ n` in the tower of objectwise
cohomology groups attached to a sequential inverse system in `D(\mathcal O_X)`. -/
private abbrev moduleCohomologyToEventualStageAtOpen
    (U : Opens X.carrier)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (m : ℤ) (i n : ℕ) (hin : i ≤ n) :
    moduleCohomologyAtOpen X U (Ksys.obj (op n)) m ⟶
      moduleCohomologyAtOpen X U (Ksys.obj (op i)) m :=
  (moduleCohomologyTowerAtOpen X U Ksys m).map ((homOfLE hin).op)

/-- The map on cohomology sheaves induced by a morphism in `D(\mathcal O_X)`. -/
private abbrev cohomologySheafMap
    {K L : DerivedCategory (RingedSpace.Modules X)} (m : ℤ) (c : K ⟶ L) :
    ringedSpaceCohomologySheaf X K m ⟶ ringedSpaceCohomologySheaf X L m :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map
    ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) m).map c)

/-- The induced map on stalks of degree-`m` cohomology sheaves. -/
private abbrev cohomologySheafStalkMap
    (x : X) {K L : DerivedCategory (RingedSpace.Modules X)} (m : ℤ) (c : K ⟶ L) :
    TopCat.Presheaf.stalk (ringedSpaceCohomologySheaf X K m).1 x ⟶
      TopCat.Presheaf.stalk (ringedSpaceCohomologySheaf X L m).1 x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (cohomologySheafMap X m c).1

/-- A morphism `c : K ⟶ K_n` is the canonical comparison from a chosen derived limit `K` to the
`n`th stage if it comes from the Milnor product map defining that derived limit. -/
private def IsDerivedLimitStageComparison
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (K : DerivedCategory (RingedSpace.Modules X)) (n : ℕ) (c : K ⟶ Ksys.obj (op n)) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang
          (DerivedCategory (RingedSpace.Modules X)) ∧
        c = ι ≫ Pi.π (inverseSystemFamily Ksys) n

/-- A neighborhood `U ⊆ W` of `x` satisfies the local Milnor vanishing and eventual injectivity
hypotheses appearing in the stalkwise Milnor criterion. -/
private class LocalMilnorNeighborhoodCondition
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (x : X) (m : ℤ) (nx : ℕ) (W U : Opens X.carrier) : Prop where
  /-- The chosen neighborhood still contains the point `x`. -/
  mem : x ∈ U
  /-- The chosen neighborhood is contained in the ambient neighborhood `W`. -/
  le : U ≤ W
  /-- The local `R^1 \!\varprojlim` term vanishes on the chosen neighborhood. -/
  r1_vanish :
    IsZero (firstDerivedLimitCohomologyAtOpen X U Ksys (m - 1))
  /-- The transition maps into stage `n(x)` are monomorphisms on the chosen neighborhood. -/
  transition_mono :
    ∀ n : ℕ, ∀ hn : nx ≤ n,
      Mono (moduleCohomologyToEventualStageAtOpen X U Ksys m nx n hn)

-- Proof sketch: represent a germ in the stalk of `H^m(K)` by a section over an open neighborhood
-- coming from the cofinal neighborhood system in the hypotheses. Using the sheafification
-- description of cohomology sheaves from Lemma `20.32.3`, shrink so that its image in the stage
-- `n(x)` stalk is already zero on that neighborhood. Then apply the Milnor short exact sequence
-- from `20.37.3.1`: the local `R^1 lim` term vanishes, and the local transition maps into stage
-- `n(x)` are injective, forcing the representing section itself to vanish.
/-- Lemma 20.37.5: let `(X, \mathcal O_X)` be a ringed space, let `(K_n)` be a sequential inverse
system in `D(\mathcal O_X)`, let `x ∈ X`, and let `m ∈ \mathbf Z`. Assume there is an index
`n(x)` such that every open neighborhood of `x` contains a smaller open neighborhood `U` with
`R^1 \!\varprojlim_n H^{m-1}(U, K_n) = 0` and such that the transition maps
`H^m(U, K_n) → H^m(U, K_{n(x)})` are injective for all `n ≥ n(x)`. Then the induced map on
stalks `H^m(R \!\varprojlim_n K_n)_x → H^m(K_{n(x)})_x`, formalized using a chosen compatible
comparison morphism `c : K ⟶ K_{n(x)}`, is injective. -/
theorem cohomologyStalkMap_injective_to_eventual_stage_of_local_milnor_conditions
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (K : DerivedCategory (RingedSpace.Modules X))
    (x : X) (m : ℤ) (nx : ℕ)
    (c : K ⟶ Ksys.obj (op nx))
    (hc : IsDerivedLimitStageComparison X Ksys K nx c)
    (hlocal :
      ∀ (W : Opens X.carrier), x ∈ W →
        ∃ U : Opens X.carrier,
          LocalMilnorNeighborhoodCondition X Ksys x m nx W U) :
    Function.Injective (cohomologySheafStalkMap X x m c) := sorry

end

end AlgebraicGeometry.RingedSpace
