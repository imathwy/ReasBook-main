module

public import Topology_Munkres_2000.Book.Remark_60_1.IntegralSingularCohomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.AlgebraicTopology.EilenbergSteenrod
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.Category.TopCat.EpiMono

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory CategoryTheory.Limits

/-- Helper for Remark 60.1: integral singular chains as a functor of the space. -/
abbrev integralSingularChainComplexFunctor :
    TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Helper for Remark 60.1: the natural inclusion from chains on the subspace to
chains on the ambient space of a topological pair. -/
@[expose]
def integralSingularChainPairInclusion :
    TopPair.proj₂ ⋙ integralSingularChainComplexFunctor ⟶
      TopPair.proj₁ ⋙ integralSingularChainComplexFunctor :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤)
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc))
    integralSingularChainComplexFunctor

/-- Helper for Remark 60.1: at a pair, the natural chain inclusion is the chain map
induced by its embedded subspace map. -/
lemma integralSingularChainPairInclusion_app (P : TopPair) :
    integralSingularChainPairInclusion.app P =
      integralSingularChainComplexFunctor.map P.map := by
  -- Whiskering the universal arrow natural transformation evaluates to the pair map.
  rfl

/-- Helper for Remark 60.1: integral singular chains carry every morphism of
topological pairs to a commutative square. -/
lemma integralSingularChainPairMap_square {P Q : TopPair} (f : P ⟶ Q) :
    integralSingularChainComplexFunctor.map P.map ≫
        integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) =
      integralSingularChainComplexFunctor.map (TopPair.Hom.snd f) ≫
        integralSingularChainComplexFunctor.map Q.map := by
  -- Functoriality reduces the chain-level square to the defining square of `f`.
  rw [← Functor.map_comp, ← Functor.map_comp, ← TopPair.Hom.w]

/-- Helper for Remark 60.1: the objectwise relative-chain map induced by a
morphism of topological pairs. -/
noncomputable def relativeIntegralSingularChainMapExplicit {P Q : TopPair}
    (f : P ⟶ Q) :
    cokernel (integralSingularChainComplexFunctor.map P.map) ⟶
      cokernel (integralSingularChainComplexFunctor.map Q.map) :=
  cokernel.map
    (integralSingularChainComplexFunctor.map P.map)
    (integralSingularChainComplexFunctor.map Q.map)
    (integralSingularChainComplexFunctor.map (TopPair.Hom.snd f))
    (integralSingularChainComplexFunctor.map (TopPair.Hom.fst f))
    (integralSingularChainPairMap_square f)

/-- Helper for Remark 60.1: the explicit relative-chain map commutes with the
canonical objectwise cokernel projections. -/
lemma relativeIntegralSingularChainMapExplicit_π {P Q : TopPair} (f : P ⟶ Q) :
    cokernel.π (integralSingularChainComplexFunctor.map P.map) ≫
        relativeIntegralSingularChainMapExplicit f =
      integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
        cokernel.π (integralSingularChainComplexFunctor.map Q.map) := by
  -- This is the projection computation rule of the defining cokernel map.
  dsimp only [relativeIntegralSingularChainMapExplicit, cokernel.map]
  rw [cokernel.π_desc]

/-- Helper for Remark 60.1: the natural relative-chain quotient projection
commutes with the ambient component of a morphism of topological pairs. -/
@[reassoc]
lemma relativeIntegralSingularChainQuotient_π_naturality
    {P Q : TopPair} (f : P ⟶ Q) :
    integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
        (cokernel.π integralSingularChainPairInclusion).app Q =
      (cokernel.π integralSingularChainPairInclusion).app P ≫
        (cokernel integralSingularChainPairInclusion).map f := by
  -- This is naturality of the functor-category cokernel projection in explicit components.
  exact (cokernel.π integralSingularChainPairInclusion).naturality f

/-- Helper for Remark 60.1: singular chains preserve the embedded inclusion in every
topological pair. -/
lemma integralSingularChainPairInclusion_mono :
    Mono integralSingularChainPairInclusion := by
  -- Each pair inclusion is injective, hence monic, and singular chains preserve monos.
  suffices ∀ P, Mono (integralSingularChainPairInclusion.app P) from
    NatTrans.mono_of_mono_app _
  intro P
  letI : Mono P.map :=
    (TopCat.mono_iff_injective P.map).mpr P.isEmbedding_map.injective
  have hmono : Mono (integralSingularChainComplexFunctor.map P.map) := inferInstance
  rwa [integralSingularChainPairInclusion_app]

/-- Helper for Remark 60.1: relative integral singular chains are the categorical
cokernel of the subspace-chain inclusion. -/
@[expose]
def relativeIntegralSingularChainComplexFunctor :
    TopPair ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel integralSingularChainPairInclusion

/-- Helper for Remark 60.1: evaluation identifies the functor-category relative-chain
cokernel with the cokernel of the chain map for one pair. -/
def relativeIntegralSingularChainComplexObjIso (P : TopPair) :
    (cokernel integralSingularChainPairInclusion).obj P ≅
      cokernel (integralSingularChainComplexFunctor.map P.map) :=
  PreservesCokernel.iso ((evaluation TopPair (ChainComplex (ModuleCat ℤ) ℕ)).obj P)
    integralSingularChainPairInclusion

/-- Helper for Remark 60.1: the quotient projection defining relative chains agrees,
after objectwise comparison, with the ordinary cokernel projection. -/
lemma relativeIntegralSingularChainComplexObjIso_π (P : TopPair) :
    (cokernel.π integralSingularChainPairInclusion).app P ≫
        (relativeIntegralSingularChainComplexObjIso P).hom =
      cokernel.π (integralSingularChainComplexFunctor.map P.map) := by
  -- This is the computation rule for a cokernel preserved by evaluation.
  exact PreservesCokernel.π_iso_hom
    ((evaluation TopPair (ChainComplex (ModuleCat ℤ) ℕ)).obj P)
    integralSingularChainPairInclusion

/-- Helper for Remark 60.1: after the target object comparison, naturality of
the functor-category quotient is expressed by the ambient chain map. -/
lemma relativeIntegralSingularChainQuotient_π_naturality_objIso
    {P Q : TopPair} (f : P ⟶ Q) :
    integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
        ((cokernel.π integralSingularChainPairInclusion).app Q ≫
          (relativeIntegralSingularChainComplexObjIso Q).hom) =
      (cokernel.π integralSingularChainPairInclusion).app P ≫
        ((cokernel integralSingularChainPairInclusion).map f ≫
          (relativeIntegralSingularChainComplexObjIso Q).hom) := by
  -- Reassociate once, apply naturality, and restore the stable right-associated form.
  calc
    integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
          ((cokernel.π integralSingularChainPairInclusion).app Q ≫
            (relativeIntegralSingularChainComplexObjIso Q).hom) =
        (integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
          (cokernel.π integralSingularChainPairInclusion).app Q) ≫
            (relativeIntegralSingularChainComplexObjIso Q).hom :=
      (Category.assoc _ _ _).symm
    _ = ((cokernel.π integralSingularChainPairInclusion).app P ≫
          (cokernel integralSingularChainPairInclusion).map f) ≫
            (relativeIntegralSingularChainComplexObjIso Q).hom :=
      relativeIntegralSingularChainQuotient_π_naturality_assoc f _
    _ = (cokernel.π integralSingularChainPairInclusion).app P ≫
          ((cokernel integralSingularChainPairInclusion).map f ≫
            (relativeIntegralSingularChainComplexObjIso Q).hom) :=
      Category.assoc _ _ _

/-- Helper for Remark 60.1: the objectwise cokernel model intertwines the
explicit relative-chain map with the relative-chain functor map. -/
lemma relativeIntegralSingularChainComplexObjIso_naturality
    {P Q : TopPair} (f : P ⟶ Q) :
    (relativeIntegralSingularChainComplexObjIso P).hom ≫
        relativeIntegralSingularChainMapExplicit f =
      relativeIntegralSingularChainComplexFunctor.map f ≫
        (relativeIntegralSingularChainComplexObjIso Q).hom := by
  -- Normalize the relative-chain functor abbreviation before categorical cancellation.
  dsimp only [relativeIntegralSingularChainComplexFunctor]
  -- Cancel the functor-category quotient projection and compare both maps objectwise.
  apply (cancel_epi ((cokernel.π integralSingularChainPairInclusion).app P)).mp
  -- Move each side to the same ambient-chain map followed by the target quotient.
  have hleft :
      (cokernel.π integralSingularChainPairInclusion).app P ≫
          ((relativeIntegralSingularChainComplexObjIso P).hom ≫
            relativeIntegralSingularChainMapExplicit f) =
        integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
          ((cokernel.π integralSingularChainPairInclusion).app Q ≫
            (relativeIntegralSingularChainComplexObjIso Q).hom) := by
    calc
      (cokernel.π integralSingularChainPairInclusion).app P ≫
            ((relativeIntegralSingularChainComplexObjIso P).hom ≫
              relativeIntegralSingularChainMapExplicit f) =
          ((cokernel.π integralSingularChainPairInclusion).app P ≫
            (relativeIntegralSingularChainComplexObjIso P).hom) ≫
            relativeIntegralSingularChainMapExplicit f :=
        (Category.assoc _ _ _).symm
      _ = cokernel.π (integralSingularChainComplexFunctor.map P.map) ≫
            relativeIntegralSingularChainMapExplicit f :=
        congrArg (fun k ↦ k ≫ relativeIntegralSingularChainMapExplicit f)
          (relativeIntegralSingularChainComplexObjIso_π P)
      _ = integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
            cokernel.π (integralSingularChainComplexFunctor.map Q.map) :=
        relativeIntegralSingularChainMapExplicit_π f
      _ = integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫
            ((cokernel.π integralSingularChainPairInclusion).app Q ≫
              (relativeIntegralSingularChainComplexObjIso Q).hom) :=
        congrArg
          (fun k ↦ integralSingularChainComplexFunctor.map (TopPair.Hom.fst f) ≫ k)
          (relativeIntegralSingularChainComplexObjIso_π Q).symm
  exact hleft.trans (relativeIntegralSingularChainQuotient_π_naturality_objIso f)

/-- Helper for Remark 60.1: the canonical chain inclusion and relative quotient form
a short complex, naturally in the topological pair. -/
@[expose]
def relativeIntegralSingularChainShortComplex :
    ShortComplex (TopPair ⥤ ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk integralSingularChainPairInclusion
    (cokernel.π integralSingularChainPairInclusion)
    (cokernel.condition integralSingularChainPairInclusion)

/-- Helper for Remark 60.1: subspace chains, ambient chains, and relative chains form
a natural short exact sequence. -/
lemma relativeIntegralSingularChainShortExact :
    relativeIntegralSingularChainShortComplex.ShortExact := by
  -- A monomorphism followed by its cokernel is the canonical short exact sequence.
  letI : Mono integralSingularChainPairInclusion :=
    integralSingularChainPairInclusion_mono
  dsimp only [relativeIntegralSingularChainShortComplex]
  exact ⟨ShortComplex.exact_cokernel _⟩

/-- Helper for Remark 60.1: evaluating the natural relative-chain sequence at one
topological pair remains short exact. -/
lemma relativeIntegralSingularChainShortExact_obj (P : TopPair) :
    (relativeIntegralSingularChainShortComplex.map
      ((evaluation TopPair (ChainComplex (ModuleCat ℤ) ℕ)).obj P)).ShortExact := by
  -- Evaluation preserves the finite limits and colimits that express short exactness.
  exact relativeIntegralSingularChainShortExact.map_of_exact _

/-- Helper for Remark 60.1: relative integral singular homology is the homology of
the relative singular-chain cokernel. -/
def relativeIntegralSingularHomologyFunctor (n : ℕ) : TopPair ⥤ ModuleCat ℤ :=
  relativeIntegralSingularChainComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n

end AlgebraicTopology
