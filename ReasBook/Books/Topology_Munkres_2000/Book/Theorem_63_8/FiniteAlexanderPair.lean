module

public import Topology_Munkres_2000.Book.Theorem_62_1.CechDiagram
public import Topology_Munkres_2000.Book.Theorem_62_1.ReducedHomologyZero
public import Mathlib.LinearAlgebra.Dimension.Finite

public section

namespace InvarianceOfDomainSupport

open CategoryTheory

/-- Helper for Theorem 63.8: a selected pair at one raw finite Čech stage can
be continued beyond every refinement and compared with two reduced-H₀ classes. -/
structure CofinalFiniteAlexanderPairDetection
    (K X : Type) [TopologicalSpace K] [TopologicalSpace X] (q : ℕ)
    (v : Fin 2 → reducedHomologyZeroModTwo (TopCat.of X)) where
  /-- The finite cover carrying the two selected source classes. -/
  base : CechFiniteOpenCover.{0, 0} K
  /-- The two raw finite-stage Čech classes to be continued. -/
  source : Fin 2 → CechFiniteOpenCover.reducedFaceNerveCohomology base q
  /-- Every refinement has a further stage where the selected classes compare
  with the prescribed reduced-H₀ pair. -/
  continuation : ∀ (W : CechFiniteOpenCover.{0, 0} K) (hBaseW : base ≤ W),
    ∃ (V : CechFiniteOpenCover.{0, 0} K) (hWV : W ≤ V)
        (comparison :
          CechFiniteOpenCover.reducedFaceNerveCohomology V q →ₗ[ZMod 2]
            reducedHomologyZeroModTwo (TopCat.of X)),
      ∀ i,
        comparison
            (CechFiniteOpenCover.reducedFaceNerveCohomologyMapOfLE
              (hBaseW.trans hWV) q (source i)) =
          v i

/-- Helper for Theorem 63.8: a refinement of a raw Čech stage whose selected
cohomology group is finite-dimensional of rank at most one. -/
structure FiniteRankOneCechRefinement
    (K : Type) [TopologicalSpace K] (q : ℕ)
    (U : CechFiniteOpenCover.{0, 0} K) where
  /-- The controlled refinement. -/
  cover : CechFiniteOpenCover.{0, 0} K
  /-- The controlled cover refines the prescribed base cover. -/
  refines : U ≤ cover
  /-- Its raw finite-stage cohomology is finite-dimensional. -/
  [finite : Module.Finite (ZMod 2)
    (CechFiniteOpenCover.reducedFaceNerveCohomology cover q)]
  /-- Its raw finite-stage cohomology has rank at most one. -/
  finrank_le_one :
    Module.finrank (ZMod 2)
        (CechFiniteOpenCover.reducedFaceNerveCohomology cover q) ≤ 1

/-- Helper for Theorem 63.8: selected-pair continuation through a rank-one
Čech stage rules out linear independence of the compared reduced-H₀ pair. -/
lemma CofinalFiniteAlexanderPairDetection.not_linearIndependent_of_rankOneRefinement
    {K X : Type} [TopologicalSpace K] [TopologicalSpace X] {q : ℕ}
    {v : Fin 2 → reducedHomologyZeroModTwo (TopCat.of X)}
    (D : CofinalFiniteAlexanderPairDetection K X q v)
    (R : FiniteRankOneCechRefinement K q D.base) :
    ¬ LinearIndependent (ZMod 2) v := by
  -- Continue the selected pair beyond the controlled rank-one stage.
  letI : Module.Finite (ZMod 2)
      (CechFiniteOpenCover.reducedFaceNerveCohomology R.cover q) := R.finite
  obtain ⟨V, hRV, comparison, hcomparison⟩ :=
    D.continuation R.cover R.refines
  let baseToRankOne :=
    CechFiniteOpenCover.reducedFaceNerveCohomologyMapOfLE R.refines q
  let rankOneToLater :=
    CechFiniteOpenCover.reducedFaceNerveCohomologyMapOfLE hRV q
  let atRankOne : Fin 2 →
      CechFiniteOpenCover.reducedFaceNerveCohomology R.cover q :=
    fun i ↦ baseToRankOne (D.source i)
  let continued : Fin 2 →
      CechFiniteOpenCover.reducedFaceNerveCohomology V q :=
    fun i ↦ rankOneToLater (atRankOne i)
  have hdirect (i : Fin 2) :
      CechFiniteOpenCover.reducedFaceNerveCohomologyMapOfLE
          (R.refines.trans hRV) q (D.source i) =
        continued i := by
    -- Expose the direct transition as the composite through the rank-one cover.
    have hmaps := congrArg
      (fun f ↦ f (D.source i))
      (CechFiniteOpenCover.reducedFaceNerveCohomologyMapOfLE_trans
        R.refines hRV (R.refines.trans hRV) q)
    simpa only [CategoryTheory.comp_apply, baseToRankOne, rankOneToLater,
      atRankOne, continued] using hmaps
  have hcontinuedComparison (i : Fin 2) :
      comparison (continued i) = v i := by
    -- Replace the composite transition by the detector's direct-transition law.
    rw [← hdirect i]
    exact hcomparison i
  intro hv
  have hcomparisonIndependent :
      LinearIndependent (ZMod 2) (fun i ↦ comparison (continued i)) := by
    -- The comparison identifies the continued family with the assumed pair.
    simpa only [hcontinuedComparison] using hv
  have hcontinuedIndependent :
      LinearIndependent (ZMod 2) continued := by
    -- Independence after comparison reflects to the continued family.
    apply LinearIndependent.of_comp comparison
    change LinearIndependent (ZMod 2)
      (fun i ↦ comparison (continued i))
    exact hcomparisonIndependent
  have hRankOneIndependent :
      LinearIndependent (ZMod 2) atRankOne := by
    -- Reflect once more across the transition out of the rank-one stage.
    apply LinearIndependent.of_comp rankOneToLater.hom
    change LinearIndependent (ZMod 2)
      (fun i ↦ rankOneToLater (atRankOne i))
    exact hcontinuedIndependent
  -- Two independent vectors cannot lie in a finite-dimensional module of rank one.
  have htwo : 2 ≤ Module.finrank (ZMod 2)
      (CechFiniteOpenCover.reducedFaceNerveCohomology R.cover q) := by
    simpa using hRankOneIndependent.fintype_card_le_finrank
  have hlt : Module.finrank (ZMod 2)
      (CechFiniteOpenCover.reducedFaceNerveCohomology R.cover q) < 2 :=
    lt_of_le_of_lt R.finrank_le_one (by decide)
  exact (not_lt_of_ge htwo) hlt

end InvarianceOfDomainSupport

end
