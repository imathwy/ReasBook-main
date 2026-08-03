module

public import Topology_Munkres_2000.Book.Definition_33_1.FunctionalSeparation
public import Mathlib.Topology.UrysohnsLemma

public section

universe u

open Set

/-- Helper for Theorem 33.3: a continuous real-valued function equal to zero and one on
two sets gives those sets disjoint open neighborhoods. -/
lemma separatedNhds_of_eqOn_zero_one {X : Type u} [TopologicalSpace X] {A B : Set X}
    (f : C(X, ℝ)) (hA : EqOn f 0 A) (hB : EqOn f 1 B) : SeparatedNhds A B := by
  -- Use the inverse images of the two open half-lines separated by the midpoint.
  refine ⟨f ⁻¹' Iio (1 / 2 : ℝ), f ⁻¹' Ioi (1 / 2 : ℝ),
    f.continuous.isOpen_preimage _ isOpen_Iio,
    f.continuous.isOpen_preimage _ isOpen_Ioi, ?_, ?_, ?_⟩
  · intro x hx
    -- On `A`, the function value is zero, hence lies below the midpoint.
    simp only [mem_preimage, mem_Iio]
    rw [hA hx]
    norm_num
  · intro x hx
    -- On `B`, the function value is one, hence lies above the midpoint.
    simp only [mem_preimage, mem_Ioi]
    rw [hB hx]
    norm_num
  · -- No value can lie strictly on both sides of the midpoint.
    rw [Set.disjoint_left]
    intro x hxBelow hxAbove
    simp only [mem_preimage, mem_Iio] at hxBelow
    simp only [mem_preimage, mem_Ioi] at hxAbove
    exact (not_lt_of_ge (le_of_lt hxAbove)) hxBelow

namespace FunctionallySeparated

/-- Helper for Theorem 33.3: functionally separated sets have disjoint open neighborhoods. -/
lemma separatedNhds {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : FunctionallySeparated A B) : SeparatedNhds A B := by
  -- Forget the interval-valued range and apply the midpoint construction.
  obtain ⟨f, hA, hB, _⟩ := iff_exists_continuousMap_real.1 h
  exact separatedNhds_of_eqOn_zero_one f hA hB

end FunctionallySeparated

/-- Theorem 33.3: A topological space is normal exactly when every pair of disjoint closed
sets is functionally separated. -/
theorem normalSpace_iff_forall_functionallySeparated {X : Type u} [TopologicalSpace X] :
    NormalSpace X ↔ ∀ (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
      (hAB : Disjoint A B), FunctionallySeparated A B := by
  constructor
  · intro hNormal A B hA hB hAB
    -- Urysohn's lemma supplies exactly the real-valued functional-separation witness.
    letI : NormalSpace X := hNormal
    exact FunctionallySeparated.iff_exists_continuousMap_real.2
      (exists_continuous_zero_one_of_isClosed hA hB hAB)
  · intro hSeparated
    -- Convert each functional separator into the required disjoint open neighborhoods.
    refine ⟨?_⟩
    intro A B _ _ _
    exact (hSeparated A B ‹IsClosed A› ‹IsClosed B› ‹Disjoint A B›).separatedNhds

end
