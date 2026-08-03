module

public import Mathlib.Topology.DerivedSet

public section

universe u

/-- Theorem 17.9. In a T₁ space, `x` is a limit point of `A` if and only if every
neighborhood `U` of `x` has infinitely many points in `U ∩ A`. -/
theorem mem_derivedSet_iff_infinite_inter_nhds {X : Type u} [TopologicalSpace X] [T1Space X]
    {A : Set X} {x : X} :
    x ∈ derivedSet A ↔ ∀ U ∈ nhds x, (U ∩ A).Infinite := by
  constructor
  · intro hx U hU
    exact Set.Infinite.of_accPt ((mem_derivedSet.mp hx).nhds_inter hU)
  · intro h
    rw [mem_derivedSet, accPt_iff_nhds]
    intro U hU
    obtain ⟨y, hy, z, hz, hyz⟩ := (h U hU).nontrivial
    by_cases hyx : y = x
    · exact ⟨z, hz, fun hzx ↦ hyz (hyx.trans hzx.symm)⟩
    · exact ⟨y, hy, hyx⟩
