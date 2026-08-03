module

public import Topology_Munkres_2000.Book.Remark_60_1.SmallSingularChains
public import Topology_Munkres_2000.Book.Theorem_63_8.ModTwoSingularCohomology
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Simplicial

/-- Helper for Theorem 63.8: the mod-two chain inclusion from cover-small
singular simplices to all singular simplices. -/
abbrev modTwoSmallSingularChainInclusion
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    (smallSingularSubcomplex X U : SSet).chainComplex
        (ModuleCat.of (ZMod 2) (ZMod 2)) ⟶
      (TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of (ZMod 2) (ZMod 2)) :=
  SSet.chainComplexMap (smallSingularSubcomplex X U).ι
    (ModuleCat.of (ZMod 2) (ZMod 2))

/-- Helper for Theorem 63.8: free mod-two simplicial chains preserve
monomorphisms of simplicial sets. -/
lemma modTwoSimplicialChainComplex_preservesMonomorphisms :
    ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).PreservesMonomorphisms := by
  -- Freeness preserves injections degreewise, and the alternating-chain
  -- construction preserves those degreewise monomorphisms.
  constructor
  intro X Y f hf
  have hfree :
      Mono
        (((CategoryTheory.Limits.sigmaConst ⋙
          SimplicialObject.whiskering (Type) (ModuleCat (ZMod 2))).obj
            (ModuleCat.of (ZMod 2) (ZMod 2))).map f) := by
    have happ : ∀ n,
        Mono
          ((((CategoryTheory.Limits.sigmaConst ⋙
            SimplicialObject.whiskering (Type) (ModuleCat (ZMod 2))).obj
              (ModuleCat.of (ZMod 2) (ZMod 2))).map f).app n) := by
      intro n
      change Mono
        ((CategoryTheory.Limits.sigmaConst.obj
          (ModuleCat.of (ZMod 2) (ZMod 2))).map (f.app n))
      apply Functor.map_mono
    exact (NatTrans.mono_iff_mono_app _).mpr happ
  exact Functor.map_mono (alternatingFaceMapComplex (ModuleCat (ZMod 2))) _

/-- Helper for Theorem 63.8: the cover-small mod-two chain inclusion is
monic. -/
lemma modTwoSmallSingularChainInclusion_mono
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    Mono (modTwoSmallSingularChainInclusion X U) := by
  -- Apply preservation of monomorphisms to the defining subcomplex inclusion.
  letI := modTwoSimplicialChainComplex_preservesMonomorphisms
  infer_instance

/-- Helper for Theorem 63.8: the cover-small mod-two chain inclusion is
injective in every degree. -/
lemma modTwoSmallSingularChainInclusion_injective
    {ι : Type} (X : TopCat) (U : ι → Set X) (n : ℕ) :
    Function.Injective ((modTwoSmallSingularChainInclusion X U).f n) := by
  -- Evaluate the monic chain map and use the concrete criterion for module maps.
  letI : Mono (modTwoSmallSingularChainInclusion X U) :=
    modTwoSmallSingularChainInclusion_mono X U
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- Helper for Theorem 63.8: the small-chain inclusion sends a small simplex
generator to the corresponding ambient singular-simplex generator. -/
lemma modTwoSmallSingularChainInclusion_ι
    {ι : Type} (X : TopCat) (U : ι → Set X) (n : ℕ)
    (σ : (smallSingularSubcomplex X U : SSet) _⦋n⦌) :
    (smallSingularSubcomplex X U : SSet).ιChainComplex σ ≫
        (modTwoSmallSingularChainInclusion X U).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ.1 := by
  -- Compute the simplicial chain map on the chosen generator.
  exact SSet.ι_chainComplexMap_f
    (smallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X)
      (smallSingularSubcomplex X U).ι
      (ModuleCat.of (ZMod 2) (ZMod 2)) σ

end AlgebraicTopology

end

end
