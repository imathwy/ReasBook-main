module

public import Topology_Munkres_2000.Book.Theorem_63_6.FiniteCellPatch
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

open Set
open scoped Topology

universe u

namespace Schoenflies

/-- Helper for Theorem 63.6: two parametrized circles are uniformly close after
an arbitrary homeomorphic reparametrization of the source circle. -/
structure CyclicTraceApproximation {X : Type u} [PseudoMetricSpace X]
    (f g : Circle → X) (epsilon : ℝ) where
  reparam : Circle ≃ₜ Circle
  dist_lt : ∀ z, dist (f z) (g (reparam z)) < epsilon

namespace CyclicTraceApproximation

/-- Helper for Theorem 63.6: cyclic trace approximation bounds the Hausdorff
distance between the two unparametrized trace ranges. -/
theorem hausdorffDist_range_le {X : Type u} [PseudoMetricSpace X]
    {f g : Circle → X} {epsilon : ℝ}
    (A : CyclicTraceApproximation f g epsilon) (hepsilon : 0 ≤ epsilon) :
    Metric.hausdorffDist (Set.range f) (Set.range g) ≤ epsilon := by
  -- Match forward points using the stored reparametrization.
  apply Metric.hausdorffDist_le_of_mem_dist hepsilon
  · rintro _ ⟨z, rfl⟩
    exact ⟨g (A.reparam z), Set.mem_range_self _, (A.dist_lt z).le⟩
  · rintro _ ⟨w, rfl⟩
    -- Surjectivity of the circle homeomorphism supplies the reverse match.
    refine ⟨f (A.reparam.symm w), Set.mem_range_self _, ?_⟩
    rw [dist_comm]
    simpa only [A.reparam.apply_symm_apply] using
      (A.dist_lt (A.reparam.symm w)).le

end CyclicTraceApproximation

/-- Helper for Theorem 63.6: a finite supported patch carries one complete
circle trace to another. -/
structure FiniteTracePatch {X : Type u} [TopologicalSpace X]
    (alpha beta : Circle → X) where
  n : ℕ
  patch : FiniteClosedCellPatch X n
  source_mem : ∀ z, alpha z ∈ patch.support
  forward_trace : ∀ z, patch.forward (alpha z) = beta z

namespace FiniteTracePatch

/-- Helper for Theorem 63.6: composing an ambient homeomorphism with a finite
trace patch gives the exact new trace and inherits both displacement bounds. -/
theorem refineAmbientHomeomorph {X : Type u} [PseudoMetricSpace X]
    {gamma beta : Circle → X} (h : X ≃ₜ X)
    (T : FiniteTracePatch (fun z ↦ h (gamma z)) beta)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (htargetBounded : ∀ i, Bornology.IsBounded (T.patch.cell i))
    (htargetDiam : ∀ i, Metric.diam (T.patch.cell i) ≤ epsilon)
    (hsourceBounded : ∀ i, Bornology.IsBounded (h.symm '' T.patch.cell i))
    (hsourceDiam : ∀ i, Metric.diam (h.symm '' T.patch.cell i) ≤ epsilon) :
    ∃ h' : X ≃ₜ X,
      (∀ z, h' (gamma z) = beta z) ∧
        (∀ x, dist (h' x) (h x) ≤ epsilon) ∧
        ∀ y, dist (h'.symm y) (h.symm y) ≤ epsilon := by
  -- Apply the finite-cell refinement to the patch bundled by `T`.
  obtain ⟨h', honSupport, _, hforward, hinverse⟩ :=
    refineAmbientHomeomorphInFiniteCells h T.patch epsilon hepsilon
      htargetBounded htargetDiam hsourceBounded hsourceDiam
  refine ⟨h', ?_, hforward, hinverse⟩
  intro z
  -- On the source trace the supported correction is exactly the patch map.
  calc
    h' (gamma z) = T.patch.forward (h (gamma z)) :=
      honSupport (gamma z) (T.source_mem z)
    _ = beta z := T.forward_trace z

end FiniteTracePatch

end Schoenflies

end
