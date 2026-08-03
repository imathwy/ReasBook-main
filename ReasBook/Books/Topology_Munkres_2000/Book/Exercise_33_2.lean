module

import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular

public section

universe u

namespace ConnectedSpace

/-- Helper for Exercise 33.2: the real unit interval cannot lie in the range of a
map whose domain is countable. -/
private lemma unitInterval_not_subset_range_of_countable {α : Type*} [Countable α] (f : α → ℝ) :
    ¬ Set.Icc (0 : ℝ) 1 ⊆ Set.range f := by
  -- A subset of a countable range would itself be countable.
  intro hsubset
  have hcountable : (Set.Icc (0 : ℝ) 1).Countable :=
    (Set.countable_range f).mono hsubset
  -- The cardinality criterion for real intervals contradicts `0 < 1`.
  have hle : (1 : ℝ) ≤ 0 := Cardinal.Real.Icc_countable_iff.mp hcountable
  norm_num at hle

/-- Exercise 33.2 (2): A connected `T3Space` with more than one point is uncountable.
Here `T3Space` expresses the book's convention for a regular space. -/
instance uncountable_of_t3Space {X : Type u} [TopologicalSpace X] [ConnectedSpace X]
    [T3Space X] [Nontrivial X] : Uncountable X := by
  -- Assume countability, which supplies Lindelöfness and hence normality.
  rw [← not_countable_iff]
  intro hcountable
  letI : Countable X := hcountable
  -- Separate two distinct points by a continuous Urysohn function.
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hdisjoint : Disjoint ({x} : Set X) {y} := Set.disjoint_singleton.2 hxy
  obtain ⟨f, hfx, hfy, _⟩ :=
    exists_continuous_zero_one_of_isClosed isClosed_singleton isClosed_singleton hdisjoint
  have hfx0 : f x = 0 := hfx (Set.mem_singleton x)
  have hfy1 : f y = 1 := hfy (Set.mem_singleton y)
  -- Connectedness forces every value in `[0, 1]` into the range of `f`.
  have hinterval : Set.Icc (0 : ℝ) 1 ⊆ Set.range f := by
    simpa only [hfx0, hfy1] using intermediate_value_univ x y f.continuous
  -- This interval inclusion is impossible for a function on a countable type.
  exact unitInterval_not_subset_range_of_countable f hinterval

/- Exercise 33.2 (1): A connected normal space with more than one point is uncountable.
In the book's convention, normal spaces are `T4Space`s; this is the specialization of
part (2) along the canonical instance `T4Space.t3Space`. -/
#check fun (X : Type u) [TopologicalSpace X] [ConnectedSpace X] [T4Space X]
    [Nontrivial X] ↦ (inferInstance : Uncountable X)

end ConnectedSpace
