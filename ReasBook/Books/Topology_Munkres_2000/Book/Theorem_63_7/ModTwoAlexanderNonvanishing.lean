module

public import Topology_Munkres_2000.Book.Theorem_62_1.BoundaryOpenStars
public import Topology_Munkres_2000.Book.Theorem_62_1.FiniteRelativeDuality
public import Topology_Munkres_2000.Book.Theorem_62_1.ReducedHomologyZero

public section

namespace InvarianceOfDomainSupport

open CategoryTheory CategoryTheory.Limits

universe u

-- Route correction: separation only needs finite-stage nonvanishing.  Thus a
-- failure of exactness in the primal cochain complex can be used directly,
-- without first constructing an explicit Alexander isomorphism.
/-- Helper for Theorem 63.7: a finite graph-dual cochain model has nontrivial
reduced graph homology exactly when its primal complex is not exact. -/
lemma FiniteGraphDualCochainModel.graphHomologyNontrivial_iff_not_exact
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] {low middle high : Type u}
    [Fintype low] [Fintype middle] [Fintype high]
    (M : FiniteGraphDualCochainModel G low middle high) :
    (¬ Subsingleton (graphReducedHomologyZeroModTwo G)) ↔
      ¬ Function.Exact M.lower.mulVecLin M.upper.mulVecLin := by
  -- Negate the existing finite dual-incidence exactness criterion.
  exact (not_congr M.exact_iff_graphHomologySubsingleton).symm

/-- Helper for Theorem 63.7: a relative open-star model detects vanishing of
reduced homology precisely by triviality of its outside-face graph homology. -/
lemma BoundaryComplementOpenStarModel.isZero_reducedHomologyZeroModTwo_iff
    {n : ℕ} {K : SSet.Subcomplex.{0} (SSet.boundary (n + 1)).toSSet}
    (M : BoundaryComplementOpenStarModel n K) :
    IsZero
        (reducedHomologyZeroModTwo
          (TopCat.of (boundaryRealizationComplement n K))) ↔
      Subsingleton (outsideFaceGraphReducedHomologyZeroModTwo K) := by
  -- Normalize singular reduced `H₀` and graph reduced `H₀` to the same
  -- augmentation kernel on path components of the realized complement.
  obtain ⟨eComplement⟩ :=
    nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel
      (TopCat.of (boundaryRealizationComplement n K))
  obtain ⟨eGraph⟩ := M.graphReducedHomologyZeroModTwoEquiv
  calc
    IsZero
        (reducedHomologyZeroModTwo
          (TopCat.of (boundaryRealizationComplement n K))) ↔
        Subsingleton
          (reducedHomologyZeroModTwo
            (TopCat.of (boundaryRealizationComplement n K))) :=
      ModuleCat.isZero_iff_subsingleton
    _ ↔ Subsingleton
        (LinearMap.ker
          (componentAugmentationModTwo
            (ZerothHomotopy (boundaryRealizationComplement n K)))) :=
      eComplement.toEquiv.subsingleton_congr
    _ ↔ Subsingleton (outsideFaceGraphReducedHomologyZeroModTwo K) :=
      eGraph.toEquiv.subsingleton_congr.symm

end InvarianceOfDomainSupport

end
