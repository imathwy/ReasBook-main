import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.Topology.Covering.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

open CategoryTheory
open AlgebraicTopology
open scoped Manifold TensorProduct Topology

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` surfaced `FundamentalGroup`,
-- `HomologicalComplex.coinvariantsTensorObj`, and `ChainComplex.linearYonedaObj` as the relevant
-- current owners. Local repository precedent from `Theorem_20_3_2` already records
-- local-coefficient homology through a chosen based representation and a chosen equivariant lifted
-- chain complex, so this file states the duality theorem on the corresponding honest based
-- homology/cohomology owners attached to the fiber of `π` at a chosen basepoint.

section localSystemFiber

variable {R : Type u} [CommRing R]
variable {M : Type u} [TopologicalSpace M]

/-- Transport along the inverse of the trivial loop acts as the identity on the local-system
fiber over the chosen basepoint `x`. -/
theorem localSystemFiberRepresentation_map_one
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M) :
    (π.map (CategoryTheory.inv (1 : FundamentalGroup M x))).hom = 1 := sorry

/-- Transport along inverse loops is multiplicative on the local-system fiber over the chosen
basepoint `x`, giving the monoid law for the associated representation. -/
theorem localSystemFiberRepresentation_map_mul
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (γ δ : FundamentalGroup M x) :
    (π.map (CategoryTheory.inv (γ * δ))).hom =
      (π.map (CategoryTheory.inv γ)).hom *
        (π.map (CategoryTheory.inv δ)).hom := sorry

/-- The fiber of the local system `π` at the chosen basepoint `x`, viewed as the associated
`π₁(M, x)`-representation via transport along inverse loops. This inverse matches the standard
left-action convention for representations extracted from a covariant groupoid functor. -/
noncomputable def localSystemFiberRepresentation
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M) :
    Representation R (FundamentalGroup M x) (π.obj (FundamentalGroupoid.mk x)) where
  toFun γ := (π.map (CategoryTheory.inv γ)).hom
  map_one' := localSystemFiberRepresentation_map_one π x
  map_mul' γ δ := localSystemFiberRepresentation_map_mul π x γ δ

/-- The fiber of a local coefficient system at the chosen basepoint `x`, viewed as the associated
`π₁(M, x)`-representation. -/
noncomputable abbrev localSystemFiberRep
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M) :
    Rep.{u} R (FundamentalGroup M x) :=
  Rep.of (localSystemFiberRepresentation π x)

/-- The action in `localSystemFiberRep π x` is induced by the local-system transport map on the
inverse loop `γ⁻¹`, matching the standard left-action convention. -/
theorem localSystemFiberRep_ρ_apply
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M) (γ : FundamentalGroup M x)
    (v : localSystemFiberRep π x) :
    (localSystemFiberRep π x).ρ γ v =
      (π.map (CategoryTheory.inv γ)).hom v := sorry

end localSystemFiber

/-- The degree-`p` cohomology group of a chosen based local-coefficient cochain model for `M`.
Here `coverChains` is a chosen `π₁(M, x)`-equivariant chain complex modeling the universal cover,
and the coefficient representation is the fiber of the local system `π` at the basepoint `x`. -/
abbrev chosenLocalCoefficientCochainComplex
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  coverChains.linearYonedaObj R (localSystemFiberRep π x)

/-- Unfolding `chosenLocalCoefficientCochainComplex π x coverChains` recovers the canonical
`ModuleCat R`-valued cochain complex on the chosen equivariant chain model `coverChains`. -/
theorem chosenLocalCoefficientCochainComplex_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) :
    chosenLocalCoefficientCochainComplex π x coverChains =
      coverChains.linearYonedaObj R (localSystemFiberRep π x) := rfl

/-- The degree-`p` cohomology group of a chosen based local-coefficient cochain model for `M`.
Here `coverChains` is a chosen `π₁(M, x)`-equivariant chain complex modeling the universal cover,
and the coefficient representation is the fiber of the local system `π` at the basepoint `x`. -/
abbrev chosenLocalCoefficientCohomology
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) (p : ℕ) :
    ModuleCat.{u} R :=
  (chosenLocalCoefficientCochainComplex π x coverChains).homology p

/-- Unfolding `chosenLocalCoefficientCohomology` recovers the homology of the canonical cochain
complex `coverChains.linearYonedaObj R (localSystemFiberRep π x)`. -/
theorem chosenLocalCoefficientCohomology_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) (p : ℕ) :
    chosenLocalCoefficientCohomology π x coverChains p =
      (chosenLocalCoefficientCochainComplex π x coverChains).homology p := rfl

/-- The degree-`q` homology group of a chosen based local-coefficient chain model for `M`. Here
`coverChains` is a chosen `π₁(M, x)`-equivariant chain complex modeling the universal cover, and
the coefficient representation is the fiber of the local system `π` at the basepoint `x`. -/
abbrev chosenLocalCoefficientChainComplex
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) coverChains

/-- Unfolding `chosenLocalCoefficientChainComplex π x coverChains` recovers the canonical
coinvariants chain complex attached to the chosen equivariant chain model `coverChains`. -/
theorem chosenLocalCoefficientChainComplex_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) :
    chosenLocalCoefficientChainComplex π x coverChains =
      HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) coverChains := rfl

/-- The degree-`q` homology group of a chosen based local-coefficient chain model for `M`. Here
`coverChains` is a chosen `π₁(M, x)`-equivariant chain complex modeling the universal cover, and
the coefficient representation is the fiber of the local system `π` at the basepoint `x`. -/
abbrev chosenLocalCoefficientHomology
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) (q : ℕ) :
    ModuleCat.{u} R :=
  (chosenLocalCoefficientChainComplex π x coverChains).homology q

/-- Unfolding `chosenLocalCoefficientHomology` recovers the homology of the canonical chain
complex `HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) coverChains`. -/
theorem chosenLocalCoefficientHomology_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) (q : ℕ) :
    chosenLocalCoefficientHomology π x coverChains q =
      (chosenLocalCoefficientChainComplex π x coverChains).homology q := rfl

/-- Forgetting the `π₁(M, x)`-action on an equivariant chain complex yields its underlying
`ModuleCat R`-valued chain complex. -/
abbrev forgottenEquivariantCoverChains
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (x : M) (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((forget₂ (Rep.{u} R (FundamentalGroup M x)) (ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj coverChains)

/-- Unfolding `forgottenEquivariantCoverChains x coverChains` recovers the chain complex obtained
from `coverChains` by forgetting its `π₁(M, x)`-action. -/
theorem forgottenEquivariantCoverChains_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (x : M) (coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ) :
    forgottenEquivariantCoverChains x coverChains =
      (((forget₂ (Rep.{u} R (FundamentalGroup M x)) (ModuleCat.{u} R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj coverChains) := rfl

/-- The ordinary singular chain complex of a topological space `cover` with coefficients in `R`,
viewed in `ModuleCat R`. -/
abbrev universalCoverSingularChains
    (R : Type u) [CommRing R] (cover : Type u) [TopologicalSpace cover] :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of.{u} R R)).obj (TopCat.of cover)

/-- Unfolding `universalCoverSingularChains R cover` recovers the ordinary singular chain complex
owner on `cover`. -/
theorem universalCoverSingularChains_def
    (R : Type u) [CommRing R] (cover : Type u) [TopologicalSpace cover] :
    universalCoverSingularChains R cover =
      ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of.{u} R R)).obj
        (TopCat.of cover) := rfl

/-- A chosen `π₁(M, x)`-equivariant chain complex modeling the universal cover of `M` at the
basepoint `x`. -/
structure ChosenUniversalCoverChainModel
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M) where
  cover : Type u
  coverTopologicalSpace : TopologicalSpace cover
  coverMap : cover → M
  isCoveringMap_coverMap : IsCoveringMap coverMap
  coverSimplyConnected : SimplyConnectedSpace cover
  baseLift : cover
  baseLift_map : coverMap baseLift = x
  coverChains : ChainComplex (Rep.{u} R (FundamentalGroup M x)) ℕ
  coverChainsIsoToSingularChains :
    forgottenEquivariantCoverChains x coverChains ≅
      universalCoverSingularChains R cover

/-- The chosen universal cover carried by `C` has its recorded topology. -/
instance ChosenUniversalCoverChainModel.instTopologicalSpaceCover
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) :
    TopologicalSpace C.cover :=
  C.coverTopologicalSpace

/-- The chosen universal cover carried by `C` is simply connected. -/
instance ChosenUniversalCoverChainModel.instSimplyConnectedSpaceCover
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) :
    SimplyConnectedSpace C.cover :=
  C.coverSimplyConnected

/-- The chosen lift `C.baseLift` lies over the basepoint `x`. -/
theorem ChosenUniversalCoverChainModel.coverMap_baseLift
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) :
    C.coverMap C.baseLift = x :=
  C.baseLift_map

/-- Forgetting the `π₁(M, x)`-action on `C.coverChains` identifies it with the ordinary singular
chain complex of the chosen cover `C.cover`. -/
abbrev ChosenUniversalCoverChainModel.coverChainsIsoToSingularChains_spec
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) :
    forgottenEquivariantCoverChains x C.coverChains ≅
      universalCoverSingularChains R C.cover :=
  C.coverChainsIsoToSingularChains

/-- The degree-`p` local-coefficient cohomology owner attached to the chosen universal-cover chain
model `C`. -/
abbrev ChosenUniversalCoverChainModel.cohomology
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (p : ℕ) :
    ModuleCat.{u} R :=
  chosenLocalCoefficientCohomology π x C.coverChains p

/-- Unfolding `C.cohomology p` recovers the cohomology of `C.coverChains` with coefficients in the
fiber representation of `π` at `x`. -/
theorem ChosenUniversalCoverChainModel.cohomology_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (C : ChosenUniversalCoverChainModel π x) (p : ℕ) :
    C.cohomology p = chosenLocalCoefficientCohomology π x C.coverChains p := rfl

/-- A chosen universal-cover chain model `C` computes a local-coefficient cohomology owner
`Hcoh` when each degree-`p` chosen cohomology object is identified with `Hcoh p` by an explicit
comparison isomorphism. -/
abbrev ChosenUniversalCoverChainModel.ComputesCohomology
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (Hcoh : ℕ → ModuleCat.{u} R) :
    Type u :=
  ∀ p : ℕ, C.cohomology p ≅ Hcoh p

/-- Unfolding `C.ComputesCohomology Hcoh` gives the degreewise comparison isomorphisms from the
chosen cohomology owner `C.cohomology p` to `Hcoh p`. -/
theorem ChosenUniversalCoverChainModel.computesCohomology_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (Hcoh : ℕ → ModuleCat.{u} R) :
    C.ComputesCohomology Hcoh = (∀ p : ℕ, C.cohomology p ≅ Hcoh p) := rfl

/-- The degree-`q` local-coefficient homology owner attached to the chosen universal-cover chain
model `C`. -/
abbrev ChosenUniversalCoverChainModel.homology
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (q : ℕ) :
    ModuleCat.{u} R :=
  chosenLocalCoefficientHomology π x C.coverChains q

/-- Unfolding `C.homology q` recovers the homology of the coinvariants complex built from
`C.coverChains`. -/
theorem ChosenUniversalCoverChainModel.homology_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R) (x : M)
    (C : ChosenUniversalCoverChainModel π x) (q : ℕ) :
    C.homology q = chosenLocalCoefficientHomology π x C.coverChains q := rfl

/-- A chosen universal-cover chain model `C` computes a local-coefficient homology owner `Hhom`
when each degree-`q` chosen homology object is identified with `Hhom q` by an explicit
comparison isomorphism. -/
abbrev ChosenUniversalCoverChainModel.ComputesHomology
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (Hhom : ℕ → ModuleCat.{u} R) :
    Type u :=
  ∀ q : ℕ, C.homology q ≅ Hhom q

/-- Unfolding `C.ComputesHomology Hhom` gives the degreewise comparison isomorphisms from the
chosen homology owner `C.homology q` to `Hhom q`. -/
theorem ChosenUniversalCoverChainModel.computesHomology_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (Hhom : ℕ → ModuleCat.{u} R) :
    C.ComputesHomology Hhom = (∀ q : ℕ, C.homology q ≅ Hhom q) := rfl

/-- A chosen realization of capping with the fundamental class `z` on the based local-coefficient
owners attached to the chosen universal-cover chain model `C`. The parameter `z` records which
fundamental class this degreewise cap-product family is intended to represent. -/
structure ChosenUniversalCoverChainModel.CapWithFundamentalClass
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x)
    (n : ℕ) (z : rSingularHomology R n (TopCat.of.{u} M)) where
  /-- A degreewise cap-product pairing on the chosen local-coefficient model `C`, linear in the
  homology-class variable. -/
  capPairing :
    ∀ q : ℕ,
      ModuleCat.of.{u} R
          (C.cohomology q ⊗[R] rSingularHomology R n (TopCat.of.{u} M)) ⟶
        C.homology (n - q)
  /-- The degreewise cap-product morphisms on the chosen model `C`. -/
  toMap : ∀ q : ℕ, C.cohomology q ⟶ C.homology (n - q)
  /-- The degreewise maps `toMap q` are obtained by evaluating the cap-product pairing
  `capPairing q` on the chosen fundamental class `z`, so this realization is not merely an
  arbitrary family of maps. -/
  toMap_eq :
    ∀ q : ℕ,
      toMap q =
        ModuleCat.ofHom
            ((TensorProduct.mk R (C.cohomology q)
              (rSingularHomology R n (TopCat.of.{u} M))).flip z) ≫
          capPairing q

/-- A chosen cap-with-`z` realization can be used as its underlying degreewise family of
morphisms. -/
instance ChosenUniversalCoverChainModel.instCoeFunCapWithFundamentalClass
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    {C : ChosenUniversalCoverChainModel π x}
    {n : ℕ}
    {z : rSingularHomology R n (TopCat.of.{u} M)} :
    CoeFun (C.CapWithFundamentalClass n z) (fun _ ↦ ∀ q : ℕ, C.cohomology q ⟶ C.homology (n - q))
    where
  coe capWithZ := capWithZ.toMap

/-- The degree-`p` cap-with-`z` morphism on the chosen local-coefficient owners of `C`. -/
abbrev ChosenUniversalCoverChainModel.CapWithFundamentalClass.map
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    {C : ChosenUniversalCoverChainModel π x}
    {n : ℕ} {z : rSingularHomology R n (TopCat.of.{u} M)}
    (capWithZ : C.CapWithFundamentalClass n z) (p : ℕ) :
    C.cohomology p ⟶ C.homology (n - p) :=
  capWithZ.toMap p

/-- Unfolding `capWithZ.map p` recovers the chosen degree-`p` cap-with-`z` morphism. -/
theorem ChosenUniversalCoverChainModel.CapWithFundamentalClass.map_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    {C : ChosenUniversalCoverChainModel π x}
    {n : ℕ} {z : rSingularHomology R n (TopCat.of.{u} M)}
    (capWithZ : C.CapWithFundamentalClass n z) (p : ℕ) :
    capWithZ.map p = capWithZ.toMap p := rfl

/-- The degree-`p` cap-with-`z` morphism is obtained by evaluating the underlying degreewise
cap-product pairing at the chosen fundamental class `z`. -/
theorem ChosenUniversalCoverChainModel.CapWithFundamentalClass.map_eq_capPairing_apply
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    {C : ChosenUniversalCoverChainModel π x}
    {n : ℕ} {z : rSingularHomology R n (TopCat.of.{u} M)}
    (capWithZ : C.CapWithFundamentalClass n z) (p : ℕ) :
    capWithZ.map p =
      ModuleCat.ofHom
          ((TensorProduct.mk R (C.cohomology p)
            (rSingularHomology R n (TopCat.of.{u} M))).flip z) ≫
        capWithZ.capPairing p :=
  capWithZ.toMap_eq p

/-- The auxiliary degree-`p` local-coefficient Poincare duality morphism induced from a chosen
realization `capWithZ` of capping with the fundamental class on the based chain model `C`,
transported to the owners `Hcoh` and `Hhom` by the explicit comparison isomorphisms. -/
abbrev localCoefficientPoincareDualityMap
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (n : ℕ)
    (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (cohomologyIso : C.ComputesCohomology Hcoh)
    (homologyIso : C.ComputesHomology Hhom)
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (capWithZ : C.CapWithFundamentalClass n z) (p : ℕ) :
    Hcoh p ⟶ Hhom (n - p) :=
  (cohomologyIso p).inv ≫ capWithZ p ≫ (homologyIso (n - p)).hom

/-- Unfolding `localCoefficientPoincareDualityMap C n Hcoh Hhom cohomologyIso homologyIso
capWithZ p` gives the comparison-isomorphism conjugate of the chosen-model cap-with-`z`
morphism `capWithZ p`. -/
theorem localCoefficientPoincareDualityMap_def
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {π : FundamentalGroupoid M ⥤ ModuleCat.{u} R} {x : M}
    (C : ChosenUniversalCoverChainModel π x) (n : ℕ)
    (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (cohomologyIso : C.ComputesCohomology Hcoh)
    (homologyIso : C.ComputesHomology Hhom)
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (capWithZ : C.CapWithFundamentalClass n z) (p : ℕ) :
    localCoefficientPoincareDualityMap C n Hcoh Hhom cohomologyIso homologyIso capWithZ p =
      (cohomologyIso p).inv ≫ capWithZ p ≫ (homologyIso (n - p)).hom :=
  rfl

/-- A source-facing family `D` realizes local-coefficient Poincare duality for the fundamental
class `z` when `z` is an `R`-fundamental class for the orientation `o` and `D` is induced from
some chosen based realization of capping with `z`, transported to the owners `Hcoh` and `Hhom`
by explicit comparison isomorphisms. -/
abbrev IsLocalCoefficientPoincareDualityMap
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {n : ℕ} [Fact (Module.finrank ℝ E = n)]
    [ChartedSpace H M] [CompactSpace M]
    (o : ROrientedManifold R I n M) (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R)
    (z : rSingularHomology R n (TopCat.of.{u} M)) (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (D : ∀ p : ℕ, Hcoh p ⟶ Hhom (n - p)) : Prop :=
  IsRFundamentalClassFor o z ∧
    ∃ x : M,
      ∃ C : ChosenUniversalCoverChainModel π x,
        ∃ cohomologyIso : C.ComputesCohomology Hcoh,
          ∃ homologyIso : C.ComputesHomology Hhom,
            ∃ capWithZ : C.CapWithFundamentalClass n z,
              ∀ p : ℕ,
                D p = localCoefficientPoincareDualityMap C n Hcoh Hhom
                  cohomologyIso homologyIso capWithZ p

/-- A local-coefficient Poincare duality family is only defined from a class `z` that is
compatible with the orientation `o`. -/
theorem isRFundamentalClassFor_of_isLocalCoefficientPoincareDualityMap
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {n : ℕ} [Fact (Module.finrank ℝ E = n)]
    [ChartedSpace H M] [CompactSpace M]
    (o : ROrientedManifold R I n M) (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R)
    (z : rSingularHomology R n (TopCat.of.{u} M)) (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (D : ∀ p : ℕ, Hcoh p ⟶ Hhom (n - p))
    (hD : IsLocalCoefficientPoincareDualityMap o π z Hcoh Hhom D) :
    IsRFundamentalClassFor o z :=
  hD.1

/-- The specification `IsLocalCoefficientPoincareDualityMap o π z Hcoh Hhom D` provides a chosen
based model, comparison isomorphisms, and cap-with-`z` realization whose transported degreewise
maps are exactly `D`. -/
theorem isLocalCoefficientPoincareDualityMap_spec
    {R : Type u} [CommRing R] {M : Type u} [TopologicalSpace M]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {n : ℕ} [Fact (Module.finrank ℝ E = n)]
    [ChartedSpace H M] [CompactSpace M]
    (o : ROrientedManifold R I n M) (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R)
    (z : rSingularHomology R n (TopCat.of.{u} M)) (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (D : ∀ p : ℕ, Hcoh p ⟶ Hhom (n - p))
    (hD : IsLocalCoefficientPoincareDualityMap o π z Hcoh Hhom D) :
    ∃ x : M,
      ∃ C : ChosenUniversalCoverChainModel π x,
        ∃ cohomologyIso : C.ComputesCohomology Hcoh,
          ∃ homologyIso : C.ComputesHomology Hhom,
            ∃ capWithZ : C.CapWithFundamentalClass n z,
              ∀ p : ℕ,
                D p = localCoefficientPoincareDualityMap C n Hcoh Hhom
                  cohomologyIso homologyIso capWithZ p :=
  hD.2

section

variable {R : Type u} [CommRing R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

/-- The concrete cap-with-`z` local-coefficient Poincare duality morphism is an isomorphism when
`z` is an `R`-fundamental class on `M`. This is the automation-facing core of Theorem 20.1.2. -/
instance localCoefficientPoincareDualityMap_isIso
    (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R)
    (z : rSingularHomology R n (TopCat.of.{u} M))
    [hz : Fact (IsRFundamentalClass R n M z)]
    {x : M} (C : ChosenUniversalCoverChainModel π x)
    (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (cohomologyIso : C.ComputesCohomology Hcoh)
    (homologyIso : C.ComputesHomology Hhom)
    (capWithZ : C.CapWithFundamentalClass n z)
    (p : ℕ) :
    IsIso (localCoefficientPoincareDualityMap C n Hcoh Hhom
      cohomologyIso homologyIso capWithZ p) := sorry

section

omit [CompactSpace M]

/-- Theorem 20.1.2. For a compact `R`-oriented `n`-manifold `M`, a local coefficient system
`π : FundamentalGroupoid M ⥤ ModuleCat R`, an `R`-fundamental class `z` compatible with the
orientation `o`, and a chosen realization `capWithZ` of capping with `z` on a chosen based
universal-cover chain model `C`, the induced degree-`p` local-coefficient Poincare duality map
`localCoefficientPoincareDualityMap C n Hcoh Hhom cohomologyIso homologyIso capWithZ p` is an
isomorphism. -/
theorem localCoefficientPoincareDuality
    (o : ROrientedManifold R I n M) (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R)
    (z : rSingularHomology R n (TopCat.of.{u} M))
    (hz : IsRFundamentalClassFor o z)
    {x : M} (C : ChosenUniversalCoverChainModel π x)
    (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (cohomologyIso : C.ComputesCohomology Hcoh)
    (homologyIso : C.ComputesHomology Hhom)
    (capWithZ : C.CapWithFundamentalClass n z)
    (p : ℕ) :
    IsIso (localCoefficientPoincareDualityMap C n Hcoh Hhom
      cohomologyIso homologyIso capWithZ p) := by
  letI : Fact (IsRFundamentalClass R n M z) := ⟨hz.isRFundamentalClass⟩
  infer_instance

end

/-- Any source-facing family `D` satisfying `IsLocalCoefficientPoincareDualityMap o π z Hcoh Hhom
D` has degree-`p` component an isomorphism, by applying Theorem 20.1.2 to the concrete cap-with-`z`
map furnished by the specification. -/
theorem isIso_of_isLocalCoefficientPoincareDualityMap
    (o : ROrientedManifold R I n M) (π : FundamentalGroupoid M ⥤ ModuleCat.{u} R)
    (z : rSingularHomology R n (TopCat.of.{u} M))
    (Hcoh Hhom : ℕ → ModuleCat.{u} R)
    (D : ∀ p : ℕ, Hcoh p ⟶ Hhom (n - p))
    (hD : IsLocalCoefficientPoincareDualityMap o π z Hcoh Hhom D)
    (p : ℕ) :
    IsIso (D p) := by
  rcases isLocalCoefficientPoincareDualityMap_spec o π z Hcoh Hhom D hD with
    ⟨x, C, cohomologyIso, homologyIso, capWithZ, hcapWithZ⟩
  rw [hcapWithZ p]
  exact
    localCoefficientPoincareDuality o π z
      (isRFundamentalClassFor_of_isLocalCoefficientPoincareDualityMap o π z Hcoh Hhom D hD)
      C Hcoh Hhom cohomologyIso homologyIso capWithZ p

end
