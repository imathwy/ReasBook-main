module

public import Topology_Munkres_2000.Book.Definition_3_6
public import Topology_Munkres_2000.Book.Exercise_3_1.Parabola

public section

/-- The relation used in Exercise 3.1: two real-plane points are equivalent when
their values of `y - x ^ 2` agree. -/
def parabolaOffsetSetoid : Setoid (ℝ × ℝ) :=
  Setoid.ker parabolaOffset

/-- Two points are related by `parabolaOffsetSetoid` exactly when their values of
`y - x ^ 2` agree. -/
theorem parabolaOffsetSetoid_rel_iff (p q : ℝ × ℝ) :
    parabolaOffsetSetoid p q ↔ p.2 - p.1 ^ 2 = q.2 - q.1 ^ 2 := by
  rfl

/-- Helper for Exercise 3.1: every real number occurs as the vertical offset of a point. -/
lemma parabolaOffset_surjective : Function.Surjective parabolaOffset := by
  -- The point `(0, c)` realizes the prescribed offset `c`.
  intro c
  refine ⟨(0, c), ?_⟩
  simp [parabolaOffset]

/-- Helper for Exercise 3.1: a parabola translate is the fiber of its offset parameter. -/
lemma parabolaTranslate_eq_fiber (c : ℝ) :
    parabolaTranslate c = {q | parabolaOffset q = c} := by
  -- Use the public membership description rather than unfolding the opaque translate definition.
  ext q
  simp only [mem_parabolaTranslate, Set.mem_setOf_eq, parabolaOffset_apply, sub_eq_iff_eq_add,
    add_comm]

/-- Helper for Exercise 3.1: the translate through a point is its kernel equivalence class. -/
lemma parabolaTranslate_offset_eq_class (p : ℝ × ℝ) :
    parabolaTranslate (parabolaOffset p) = {q | parabolaOffsetSetoid q p} := by
  -- Rewrite the translate as a fiber, which is exactly the kernel class at `p`.
  rw [parabolaTranslate_eq_fiber]
  ext q
  exact Setoid.ker_def.symm

/-- Exercise 3.1 (2): The equivalence classes are exactly the vertical translates
`y = x ^ 2 + c` of the standard parabola. -/
theorem parabolaOffsetSetoid_classes :
    parabolaOffsetSetoid.classes = Set.range parabolaTranslate := by
  -- Kernel classes are fibers, hence vertical translates of the parabola.
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨c, hc⟩ := Setoid.classes_ker_subset_fiber_set parabolaOffset hs
    refine ⟨c, ?_⟩
    rw [parabolaTranslate_eq_fiber]
    exact hc
  -- Surjectivity ensures that every translate is the class of an actual point.
  · rintro _ ⟨c, rfl⟩
    obtain ⟨p, rfl⟩ := parabolaOffset_surjective c
    rw [parabolaTranslate_offset_eq_class]
    exact parabolaOffsetSetoid.mem_classes p
