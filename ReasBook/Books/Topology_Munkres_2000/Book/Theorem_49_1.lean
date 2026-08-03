import Topology_Munkres_2000.Book.Proposition_49_1
import Topology_Munkres_2000.Book.Proposition_49_2
import Topology_Munkres_2000.Book.Proposition_49_3
import Mathlib.Topology.Baire.CompleteMetrizable

open UnitIntervalSecant

namespace ClosedUnitInterval

/-- Continuous nowhere-differentiable functions are dense in the continuous
real-valued functions on the closed unit interval. -/
theorem dense_setOf_isNowhereDifferentiable :
    Dense {f : C(unitInterval, ℝ) | IsNowhereDifferentiable f} := by
  refine (BaireSpace.baire_property (fun n ↦ U_{n + 2}) ?_ ?_).mono ?_
  · exact fun n ↦ isOpen_largeSecantSet (n + 2)
  · exact fun n ↦ dense_largeSecantSet (n + 2) (Nat.le_add_left 2 n)
  · intro f hf
    apply largeSecantSet_iInter_nondifferentiable f
    intro n hn
    simpa [Nat.sub_add_cancel hn] using Set.mem_iInter.mp hf (n - 2)

end ClosedUnitInterval

/-- Theorem 49.1: every continuous real-valued function on the closed unit interval
can be approximated pointwise within any positive error by a continuous function
that is nowhere differentiable relative to the interval. -/
theorem exists_continuous_nowhereDifferentiable_close (h : C(unitInterval, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(unitInterval, ℝ),
      (∀ x, |h x - g x| < ε) ∧ ClosedUnitInterval.IsNowhereDifferentiable g := by
  obtain ⟨g, hg, hdist⟩ :=
    ClosedUnitInterval.dense_setOf_isNowhereDifferentiable.exists_dist_lt h hε
  exact ⟨g, (ContinuousMap.dist_lt_iff hε).mp hdist, hg⟩
