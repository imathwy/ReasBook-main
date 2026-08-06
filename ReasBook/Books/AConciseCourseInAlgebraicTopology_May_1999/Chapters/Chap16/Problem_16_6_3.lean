import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_1_6

open AlgebraicTopology CategoryTheory Limits
open scoped SingularChains

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: `SSet.toTop`,
-- `AlgebraicTopology.SSet.singularChainComplexFunctor`, and
-- `AlgebraicTopology.singularChainComplexFunctor` are the canonical owners for geometric
-- realization and simplicial/topological singular chains, while
-- `HomologicalComplex.coinvariantsTensorObj` is the project's canonical owner for the
-- local-coefficient chain complexes recalled in Problem 16.6.1.

/-- Singular chains on a simplicial set with coefficients in a chosen `R`-module object `M`. -/
abbrev simplicialSingularChainsWithCoefficients
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    SSet ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (SSet.singularChainComplexFunctor (ModuleCat.{u} R)).obj M

/-- Singular chains on a topological space with coefficients in a chosen `R`-module object
`M`. -/
abbrev topologicalSingularChainsWithCoefficients
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    TopCat ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} R)).obj M

/-- The relative simplicial singular chain complex of a morphism `i : A ⟶ X`, modeled as the
cokernel of the induced chain map. -/
def relativeSimplicialSingularChains {A X : SSet} (i : A ⟶ X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (integralSimplicialSingularChains.map i)

/-- The relative singular chain complex of the realized pair `|A| ⟶ |X|`, modeled as the cokernel
of the induced chain map. -/
def relativeRealizationSingularChains {A X : SSet} (i : A ⟶ X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (integralTopologicalSingularChains.map (SSet.toTop.map i))

/-- The relative simplicial singular chain complex of `i : A ⟶ X` with coefficients in the
chosen `R`-module object `M`. -/
def relativeSimplicialSingularChainsWithCoefficients
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) {A X : SSet} (i : A ⟶ X) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  cokernel ((simplicialSingularChainsWithCoefficients M).map i)

/-- The relative singular chain complex of the realized pair `|A| ⟶ |X|` with coefficients in the
chosen `R`-module object `M`. -/
def relativeRealizationSingularChainsWithCoefficients
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) {A X : SSet} (i : A ⟶ X) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  cokernel ((topologicalSingularChainsWithCoefficients M).map (SSet.toTop.map i))

/-- The chain map from simplicial singular chains to the singular chains of the geometric
realization, induced by the adjunction unit `X ⟶ TopCat.toSSet.obj |X|`. -/
abbrev simplicialToRealizationSingularChains (X : SSet) :
    simplicialSingularChains X ⟶ C_*(SSet.toTop.obj X) :=
  integralSimplicialSingularChains.map (sSetTopAdj.unit.app X)

/-- The chain map from simplicial singular chains with coefficients in `M` to the singular chains
of the geometric realization with the same coefficients. -/
abbrev simplicialToRealizationSingularChainsWithCoefficients
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (X : SSet) :
    (simplicialSingularChainsWithCoefficients M).obj X ⟶
      (topologicalSingularChainsWithCoefficients M).obj (SSet.toTop.obj X) :=
  (simplicialSingularChainsWithCoefficients M).map (sSetTopAdj.unit.app X)

/-- Naturality of `simplicialToRealizationSingularChains` with respect to a map of simplicial
sets. -/
theorem relativeSingularChainGeometricRealizationComparison_naturality
    {A X : SSet} (i : A ⟶ X) :
    CommSq
      (integralSimplicialSingularChains.map i)
      (simplicialToRealizationSingularChains A)
      (simplicialToRealizationSingularChains X)
      (integralTopologicalSingularChains.map (SSet.toTop.map i)) := by
  refine ⟨?_⟩
  -- Rewrite the comparison maps so the square is expressed through the adjunction unit.
  rw [simplicialToRealizationSingularChains, simplicialToRealizationSingularChains]
  -- Normalize the realized-chain leg to the simplicial chain functor on the whiskered map.
  change
    integralSimplicialSingularChains.map i ≫
        integralSimplicialSingularChains.map (sSetTopAdj.unit.app X) =
      integralSimplicialSingularChains.map (sSetTopAdj.unit.app A) ≫
        integralSimplicialSingularChains.map ((SSet.toTop ⋙ TopCat.toSSet).map i)
  -- Turn both composites into a single functor image and apply unit naturality.
  rw [← integralSimplicialSingularChains.map_comp, ← integralSimplicialSingularChains.map_comp]
  simpa using congrArg integralSimplicialSingularChains.map (sSetTopAdj.unit.naturality i)

namespace SimplicialToRealizationWithCoefficients

/-- Naturality of `simplicialToRealizationSingularChainsWithCoefficients` with respect to a map
of simplicial sets. -/
theorem naturality
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) {A X : SSet} (i : A ⟶ X) :
    CommSq
      ((simplicialSingularChainsWithCoefficients M).map i)
      (simplicialToRealizationSingularChainsWithCoefficients M A)
      (simplicialToRealizationSingularChainsWithCoefficients M X)
      ((topologicalSingularChainsWithCoefficients M).map (SSet.toTop.map i)) := by
  refine ⟨?_⟩
  -- Rewrite the comparison maps so the square is expressed through the adjunction unit.
  rw [simplicialToRealizationSingularChainsWithCoefficients,
    simplicialToRealizationSingularChainsWithCoefficients]
  -- Normalize the realized-chain leg to the simplicial chain functor on the whiskered map.
  change
    (simplicialSingularChainsWithCoefficients M).map i ≫
        (simplicialSingularChainsWithCoefficients M).map (sSetTopAdj.unit.app X) =
      (simplicialSingularChainsWithCoefficients M).map (sSetTopAdj.unit.app A) ≫
        (simplicialSingularChainsWithCoefficients M).map ((SSet.toTop ⋙ TopCat.toSSet).map i)
  -- Turn both composites into a single functor image and apply unit naturality.
  rw [← (simplicialSingularChainsWithCoefficients M).map_comp,
    ← (simplicialSingularChainsWithCoefficients M).map_comp]
  simpa using
    congrArg (simplicialSingularChainsWithCoefficients M).map (sSetTopAdj.unit.naturality i)

end SimplicialToRealizationWithCoefficients

/-- The comparison chain map from relative simplicial singular chains to the relative singular
chains of the geometric realization. -/
def relativeSingularChainGeometricRealizationComparisonMap {A X : SSet} (i : A ⟶ X) :
    relativeSimplicialSingularChains i ⟶ relativeRealizationSingularChains i :=
  cokernel.map
    (integralSimplicialSingularChains.map i)
    (integralTopologicalSingularChains.map (SSet.toTop.map i))
    (simplicialToRealizationSingularChains A)
    (simplicialToRealizationSingularChains X)
    (relativeSingularChainGeometricRealizationComparison_naturality i).w

/-- The comparison chain map from relative simplicial singular chains with coefficients in `M` to
the relative singular chains of the geometric realization with the same coefficients. -/
def relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) {A X : SSet} (i : A ⟶ X) :
    relativeSimplicialSingularChainsWithCoefficients M i ⟶
      relativeRealizationSingularChainsWithCoefficients M i :=
  cokernel.map
    ((simplicialSingularChainsWithCoefficients M).map i)
    ((topologicalSingularChainsWithCoefficients M).map (SSet.toTop.map i))
    (simplicialToRealizationSingularChainsWithCoefficients M A)
    (simplicialToRealizationSingularChainsWithCoefficients M X)
    (SimplicialToRealizationWithCoefficients.naturality M i).w

/-- The relative-pair comparison in Problem 16.6.3 (1) extends the
singular-chain/geometric-realization comparison to relative
pairs. Here the relative pair determined by a morphism `i : A ⟶ X` is formalized by the
cokernel of the induced map on simplicial singular chains, and similarly after geometric
realization. -/
abbrev relativeSingularChainGeometricRealizationComparison
    {A X : SSet} (i : A ⟶ X) :
    relativeSimplicialSingularChains i ⟶ relativeRealizationSingularChains i :=
  relativeSingularChainGeometricRealizationComparisonMap i

/-- The underlying `R`-module of a representation `L : Rep R G`. -/
abbrev representationUnderlyingModule
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G) :
    ModuleCat.{u} R :=
  (forget₂ (Rep.{u} R G) (ModuleCat R)).obj L

/-- The transported local-coefficient comparison isomorphism obtained from a chosen
representation-valued comparison and explicit identifications with the coefficient chain
complexes. -/
def transportedRelativeLocalCoefficientComparisonIso
    {A X : SSet} (i : A ⟶ X)
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G)
    {relativeSimplicialLiftedChains relativeRealizationLiftedChains :
      ChainComplex (Rep.{u} R G) ℕ}
    (simplicialIdentification :
      relativeSimplicialSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeSimplicialLiftedChains)
    (realizationIdentification :
      relativeRealizationSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeRealizationLiftedChains)
    (comparison : relativeSimplicialLiftedChains ≅ relativeRealizationLiftedChains) :
    relativeSimplicialSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
      relativeRealizationSingularChainsWithCoefficients (representationUnderlyingModule L) i :=
  simplicialIdentification ≪≫
    ((((Rep.coinvariantsTensor R G).obj L).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapIso comparison) ≪≫
    realizationIdentification.symm

namespace RelativeLocalCoeffComparison

/-- Applying `HomologicalComplex.coinvariantsTensorObj` to a comparison map between chosen
representation-valued relative chain models induces the corresponding map on the canonical
local-coefficient chain complexes. -/
abbrev map
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G)
    (relativeSimplicialLiftedChains relativeRealizationLiftedChains :
      ChainComplex (Rep.{u} R G) ℕ)
    (comparison :
      relativeSimplicialLiftedChains ⟶ relativeRealizationLiftedChains) :
    HomologicalComplex.coinvariantsTensorObj L relativeSimplicialLiftedChains ⟶
      HomologicalComplex.coinvariantsTensorObj L relativeRealizationLiftedChains :=
  ((((Rep.coinvariantsTensor R G).obj L).mapHomologicalComplex
    (ComplexShape.down ℕ)).map comparison)

/-- The local-coefficient comparison in Problem 16.6.3 (2) extends the
singular-chain/geometric-realization comparison to
relative chains with local coefficients. For chosen representation-valued relative simplicial and
realized chain models of the pair `i`, together with a chosen lifted
singular-chain/geometric-realization comparison realizing the canonical comparison on the
coefficient chain complexes, the induced morphism on
`HomologicalComplex.coinvariantsTensorObj L ...` is the local-coefficient comparison. -/
abbrev comparison
    {A X : SSet} (i : A ⟶ X)
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G)
    (relativeSimplicialLiftedChains relativeRealizationLiftedChains :
      ChainComplex (Rep.{u} R G) ℕ)
    (simplicialIdentification :
      relativeSimplicialSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeSimplicialLiftedChains)
    (realizationIdentification :
      relativeRealizationSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeRealizationLiftedChains)
    (liftedComparison :
      relativeSimplicialLiftedChains ⟶ relativeRealizationLiftedChains)
    (liftedComparison_spec :
      simplicialIdentification.inv ≫
          relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
            (representationUnderlyingModule L) i ≫
          realizationIdentification.hom =
        map L relativeSimplicialLiftedChains
          relativeRealizationLiftedChains liftedComparison) :
    HomologicalComplex.coinvariantsTensorObj L relativeSimplicialLiftedChains ⟶
      HomologicalComplex.coinvariantsTensorObj L relativeRealizationLiftedChains :=
  let _ := liftedComparison_spec
  map L relativeSimplicialLiftedChains relativeRealizationLiftedChains liftedComparison

/-- The source-facing local-coefficient comparison is, by construction, the induced morphism of
the chosen lifted singular-chain/geometric-realization comparison. -/
theorem comparison_spec
    {A X : SSet} (i : A ⟶ X)
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G)
    (relativeSimplicialLiftedChains relativeRealizationLiftedChains :
      ChainComplex (Rep.{u} R G) ℕ)
    (simplicialIdentification :
      relativeSimplicialSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeSimplicialLiftedChains)
    (realizationIdentification :
      relativeRealizationSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeRealizationLiftedChains)
    (liftedComparison :
      relativeSimplicialLiftedChains ⟶ relativeRealizationLiftedChains)
    (liftedComparison_spec :
      simplicialIdentification.inv ≫
          relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
            (representationUnderlyingModule L) i ≫
          realizationIdentification.hom =
        map L relativeSimplicialLiftedChains
          relativeRealizationLiftedChains liftedComparison) :
    simplicialIdentification.inv ≫
        relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
          (representationUnderlyingModule L) i ≫
        realizationIdentification.hom =
      RelativeLocalCoeffComparison.comparison i L relativeSimplicialLiftedChains
        relativeRealizationLiftedChains simplicialIdentification realizationIdentification
        liftedComparison liftedComparison_spec :=
  liftedComparison_spec

/-- Unfolding `RelativeLocalCoeffComparison.map L ... comparison` recovers the morphism
induced by `comparison` on `HomologicalComplex.coinvariantsTensorObj L ...`. -/
theorem map_def
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G)
    (relativeSimplicialLiftedChains relativeRealizationLiftedChains :
      ChainComplex (Rep.{u} R G) ℕ)
    (comparison :
      relativeSimplicialLiftedChains ⟶ relativeRealizationLiftedChains) :
    map L relativeSimplicialLiftedChains relativeRealizationLiftedChains comparison =
      ((((Rep.coinvariantsTensor R G).obj L).mapHomologicalComplex
        (ComplexShape.down ℕ)).map comparison) :=
  rfl

/-- Problem 16.6.3: if a chosen lifted comparison isomorphism realizes the transported
canonical local-coefficient comparison, then transporting that isomorphism back to the canonical
relative chain complexes recovers the source-specific comparison map with coefficients. -/
theorem eq_transport
    {A X : SSet} (i : A ⟶ X)
    {R G : Type u} [CommRing R] [Group G] (L : Rep.{u} R G)
    {relativeSimplicialLiftedChains relativeRealizationLiftedChains :
      ChainComplex (Rep.{u} R G) ℕ}
    (simplicialIdentification :
      relativeSimplicialSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeSimplicialLiftedChains)
    (realizationIdentification :
      relativeRealizationSingularChainsWithCoefficients (representationUnderlyingModule L) i ≅
        HomologicalComplex.coinvariantsTensorObj L relativeRealizationLiftedChains)
    (comparison : relativeSimplicialLiftedChains ≅ relativeRealizationLiftedChains)
    (comparison_eq :
      simplicialIdentification.inv ≫
          relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
            (representationUnderlyingModule L) i ≫
          realizationIdentification.hom =
        map L relativeSimplicialLiftedChains
          relativeRealizationLiftedChains comparison.hom) :
    (transportedRelativeLocalCoefficientComparisonIso i L
        simplicialIdentification realizationIdentification comparison).hom =
      relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
        (representationUnderlyingModule L) i := by
  calc
    (transportedRelativeLocalCoefficientComparisonIso i L
        simplicialIdentification realizationIdentification comparison).hom =
        simplicialIdentification.hom ≫
          map L relativeSimplicialLiftedChains
            relativeRealizationLiftedChains comparison.hom ≫
          realizationIdentification.inv := by
      -- Normalize the transported comparison isomorphism to the functorial middle map.
      simp only [transportedRelativeLocalCoefficientComparisonIso, Iso.trans_hom,
        Iso.symm_hom, Functor.mapIso_hom, map_def]
    _ =
        relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
          (representationUnderlyingModule L) i := by
      -- Rewrite the middle factor using the chosen comparison and cancel the transports.
      rw [← comparison_eq]
      calc
        simplicialIdentification.hom ≫
            simplicialIdentification.inv ≫
            relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
              (representationUnderlyingModule L) i ≫
            realizationIdentification.hom ≫ realizationIdentification.inv =
          relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
              (representationUnderlyingModule L) i ≫
            realizationIdentification.hom ≫ realizationIdentification.inv := by
            simpa only [Category.assoc] using
              simplicialIdentification.hom_inv_id_assoc
                (relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
                  (representationUnderlyingModule L) i ≫
                  realizationIdentification.hom ≫ realizationIdentification.inv)
        _ =
          relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
            (representationUnderlyingModule L) i := by
            simpa only [Category.assoc] using
              congrArg
                (fun k ↦
                  relativeSingularChainGeometricRealizationComparisonMapWithCoefficients
                    (representationUnderlyingModule L) i ≫ k)
                realizationIdentification.hom_inv_id

end RelativeLocalCoeffComparison
