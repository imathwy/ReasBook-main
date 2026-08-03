module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.NumberTheory.Real.Irrational

public section

open Set

universe u v

/- Exercise 17.6 (a): Closure is monotone with respect to set inclusion. -/
#check closure_mono

/- Exercise 17.6 (b): Closure preserves binary unions. -/
#check closure_union

/-- Exercise 17.6 (c): The union of the closures of an indexed family is contained in
the closure of its union. -/
theorem iUnion_closure_subset_closure_iUnion {X : Type u} [TopologicalSpace X]
    {ι : Sort v} (A : ι → Set X) :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  -- Each member is contained in the total union, so monotonicity applies before taking the union.
  refine iUnion_subset fun i ↦ ?_
  exact closure_mono (subset_iUnion A i)

/-- The family of rational singleton subsets of `ℝ`. -/
def rationalSingletons (q : ℚ) : Set ℝ := {(q : ℝ)}

/-- Helper for Exercise 17.6: the rational points form a proper subset of `ℝ`. -/
lemma rationalCastRange_ssubset_univ :
    Set.range ((↑) : ℚ → ℝ) ⊂ (Set.univ : Set ℝ) := by
  -- The irrational point `√2` witnesses that the rational-cast range is not all of `ℝ`.
  rw [Set.ssubset_univ_iff]
  intro hRange
  apply irrational_sqrt_two
  rw [hRange]
  exact Set.mem_univ (Real.sqrt 2)

/-- The rational singleton family witnesses that equality can fail in Exercise 17.6 (c):
the union of the closures is strictly contained in the closure of the union. -/
theorem iUnion_closure_rationalSingletons_ssubset :
    (⋃ q : ℚ, closure (rationalSingletons q)) ⊂
      closure (⋃ q : ℚ, rationalSingletons q) := by
  -- Singleton closures give the rational range, whose closure is all of `ℝ` by density.
  simpa only [rationalSingletons, closure_singleton, Set.iUnion_singleton_eq_range,
    Rat.denseRange_cast.closure_range] using rationalCastRange_ssubset_univ
