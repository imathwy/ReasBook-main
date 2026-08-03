module

import Mathlib.Topology.Algebra.Module.PerfectSpace
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- Exercise 18.2: A continuous map need not send a limit point of a set to a
limit point of its image. The constant-zero map on `ℝ`, the set `Set.univ`, and
the point `0` give a counterexample. -/
theorem continuous_const_derivedSet_counterexample :
    Continuous (fun _ : ℝ ↦ (0 : ℝ)) ∧
      (0 : ℝ) ∈ derivedSet (Set.univ : Set ℝ) ∧
        (0 : ℝ) ∉ derivedSet ((fun _ : ℝ ↦ (0 : ℝ)) '' Set.univ) := by
  refine ⟨continuous_const, PerfectSpace.univ_preperfect 0 (Set.mem_univ 0), ?_⟩
  rw [show (fun _ : ℝ ↦ (0 : ℝ)) '' Set.univ = {0} by ext; simp]
  rw [mem_derivedSet, accPt_principal_iff_nhdsWithin]
  simp
