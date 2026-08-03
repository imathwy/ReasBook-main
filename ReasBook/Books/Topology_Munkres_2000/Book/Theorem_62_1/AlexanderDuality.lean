module

public import Topology_Munkres_2000.Book.Theorem_62_1.BoundaryOpenStars
public import Topology_Munkres_2000.Book.Theorem_62_1.CechDiagram
public import Topology_Munkres_2000.Book.Theorem_62_1.CechDuality
public import Topology_Munkres_2000.Book.Theorem_62_1.CechCompactum
public import Topology_Munkres_2000.Book.Theorem_62_1.FiniteRelativeDuality
public import Topology_Munkres_2000.Book.Theorem_62_1.ReducedHomologyZero
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.MetricSpace.ProperSpace

public section

namespace InvarianceOfDomainSupport

open CategoryTheory CategoryTheory.Limits

/-- Helper for Theorem 62.1: the canonical module universe lift reflects and
preserves zero objects. -/
private lemma isZero_uliftFunctor_obj_iff (M : ModuleCat.{0} (ZMod 2)) :
    IsZero ((ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj M) ↔ IsZero M := by
  -- Reduce both categorical zero conditions to subsingleton carriers, then
  -- remove the universe lift through its canonical type equivalence.
  calc
    IsZero ((ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj M) ↔
        Subsingleton ((ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj M) :=
      ModuleCat.isZero_iff_subsingleton
    _ ↔ Subsingleton M := Equiv.ulift.subsingleton_congr
    _ ↔ IsZero M := ModuleCat.isZero_iff_subsingleton.symm

/-- Helper for Theorem 62.1: reduced mod-two homology lifted to the universe of
the finite-cover Čech colimit. -/
private noncomputable abbrev liftedReducedHomologyZeroModTwo (X : TopCat.{0}) :
    ModuleCat.{1} (ZMod 2) :=
  (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj (reducedHomologyZeroModTwo X)

/-- Helper for Theorem 62.1: in dimensions at least two, the Alexander
cohomological degree is positive. -/
private lemma pred_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < n - 1 := by
  -- Removing one from a dimension at least two leaves a positive degree.
  omega

/-- Helper for Theorem 62.1: restricting an embedded closed ball to its
metric boundary is still an embedding. -/
private lemma sphereBoundaryRestriction_isEmbedding {n : ℕ}
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (g : Metric.closedBall c r → OnePoint (EuclideanSpace ℝ (Fin n)))
    (hg : Topology.IsEmbedding g) :
    Topology.IsEmbedding
      (fun x : Metric.sphere c r ↦
        g (Set.inclusion Metric.sphere_subset_closedBall x)) := by
  -- Compose the canonical subtype inclusion with the given embedding.
  exact hg.comp (Topology.IsEmbedding.inclusion Metric.sphere_subset_closedBall)

/-- Helper for Theorem 62.1: the range of the boundary restriction lies in
the range of the embedded closed ball. -/
private lemma range_sphereBoundaryRestriction_subset {n : ℕ}
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (g : Metric.closedBall c r → OnePoint (EuclideanSpace ℝ (Fin n))) :
    Set.range
        (fun x : Metric.sphere c r ↦
          g (Set.inclusion Metric.sphere_subset_closedBall x)) ⊆
      Set.range g := by
  -- A boundary point has the same image after its canonical inclusion in the ball.
  rintro _ ⟨x, rfl⟩
  exact ⟨Set.inclusion Metric.sphere_subset_closedBall x, rfl⟩

/-- Helper for Theorem 62.1: an epimorphic Alexander comparison transfers
vanishing of a Čech source to the unlifted complement invariant. -/
private lemma isZero_reducedHomologyZeroModTwo_of_epiCechComparison
    (K X : TopCat.{0}) (q : ℕ)
    (f : reducedCechCohomologyModTwo.{0, 0} (X := K) q ⟶
      liftedReducedHomologyZeroModTwo X) [Epi f]
    (hSource : IsZero (reducedCechCohomologyModTwo.{0, 0} (X := K) q)) :
    IsZero (reducedHomologyZeroModTwo X) := by
  -- Epimorphicity first kills the lifted target; the canonical lift then
  -- reflects the zero-object property back to ordinary reduced homology.
  apply (isZero_uliftFunctor_obj_iff (reducedHomologyZeroModTwo X)).mp
  exact IsZero.of_epi f hSource

/-- Helper for Theorem 62.1: a monomorphic Alexander comparison transfers
nonvanishing of a Čech source to the unlifted complement invariant. -/
private lemma not_isZero_reducedHomologyZeroModTwo_of_monoCechComparison
    (K X : TopCat.{0}) (q : ℕ)
    (f : reducedCechCohomologyModTwo.{0, 0} (X := K) q ⟶
      liftedReducedHomologyZeroModTwo X) [Mono f]
    (hSource : ¬ IsZero (reducedCechCohomologyModTwo.{0, 0} (X := K) q)) :
    ¬ IsZero (reducedHomologyZeroModTwo X) := by
  -- If the target vanished, its lift would vanish and monomorphicity would
  -- force the assumed nonzero Čech source to vanish as well.
  intro hTarget
  apply hSource
  have hLiftedTarget : IsZero (liftedReducedHomologyZeroModTwo X) :=
    (isZero_uliftFunctor_obj_iff (reducedHomologyZeroModTwo X)).mpr hTarget
  exact IsZero.of_mono f hLiftedTarget

/-- Helper for Theorem 62.1: a finite relative open-star model identifies the
complement's reduced mod-two `H₀` with the incidence homology of the outside-face graph. -/
lemma BoundaryComplementOpenStarModel.reducedHomologyZeroModTwoEquivGraph
    {n : ℕ} {K : (SSet.boundary (n + 1)).toSSet.Subcomplex}
    (M : BoundaryComplementOpenStarModel n K) :
    Nonempty
      (reducedHomologyZeroModTwo
          (TopCat.of (boundaryRealizationComplement n K)) ≃ₗ[ZMod 2]
        outsideFaceGraphReducedHomologyZeroModTwo K) := by
  -- Normalize both theories to the same augmentation kernel on complement components.
  obtain ⟨eComplement⟩ :=
    nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel
      (TopCat.of (boundaryRealizationComplement n K))
  obtain ⟨eGraph⟩ := M.graphReducedHomologyZeroModTwoEquiv
  exact ⟨eComplement.trans eGraph.symm⟩

end InvarianceOfDomainSupport

end
