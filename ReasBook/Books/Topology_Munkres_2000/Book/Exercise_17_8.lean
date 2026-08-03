module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

universe u v

/- Exercise 17.8 (1): The closure of a binary intersection is contained in the
intersection of the closures. -/
#check closure_inter_subset_inter_closure

/-- Helper for Exercise 17.8 (2): Equality can fail for binary intersections: the closure of
`Iio 0 ∩ Ioi 0` is strictly contained in `closure (Iio 0) ∩ closure (Ioi 0)`. -/
theorem closure_inter_ssubset_inter_closure_real :
    closure (Iio (0 : ℝ) ∩ Ioi 0) ⊂ closure (Iio 0) ∩ closure (Ioi 0) := by
  -- The two open rays are disjoint, so their intersection has empty closure.
  have hInterEmpty : Iio (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false]
    intro hx
    exact (lt_asymm hx.1 hx.2)
  -- The general inclusion is strict because both closed rays still contain zero.
  rw [Set.ssubset_iff_exists]
  constructor
  · exact closure_inter_subset_inter_closure (Iio (0 : ℝ)) (Ioi 0)
  · refine ⟨0, ?_, ?_⟩
    · constructor
      · rw [closure_Iio]
        simpa only [mem_Iic] using (le_refl (0 : ℝ))
      · rw [closure_Ioi]
        simpa only [mem_Ici] using (le_refl (0 : ℝ))
    · rw [hInterEmpty, closure_empty]
      simp only [mem_empty_iff_false, not_false_eq_true]

/-- Exercise 17.8 (3): The closure of an arbitrary intersection is contained in
the intersection of the closures. -/
theorem closure_iInter_subset_iInter_closure {X : Type u} [TopologicalSpace X]
    {ι : Sort v} (A : ι → Set X) :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  -- Project the intersection into each member, then use monotonicity of closure.
  refine subset_iInter fun i ↦ ?_
  exact closure_mono (iInter_subset A i)

/-- Helper for Exercise 17.8 (4): Equality can fail for indexed intersections, even for a
family indexed by `Bool`. -/
theorem closure_iInter_ssubset_iInter_closure_real :
    closure (⋂ b : Bool, if b then Iio (0 : ℝ) else Ioi 0) ⊂
      ⋂ b : Bool, closure (if b then Iio (0 : ℝ) else Ioi 0) := by
  -- Evaluating the family at both Boolean indices gives two disjoint open rays.
  have hInterEmpty : (⋂ b : Bool, if b then Iio (0 : ℝ) else Ioi 0) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxTrue : x ∈ Iio (0 : ℝ) := by
        have hxMember := mem_iInter.mp hx true
        simpa using hxMember
      have hxFalse : x ∈ Ioi (0 : ℝ) := by
        have hxMember := mem_iInter.mp hx false
        simpa using hxMember
      have hxLt : x < 0 := hxTrue
      have hxGt : 0 < x := hxFalse
      exact (lt_asymm hxLt hxGt)
    · intro hx
      exact hx.elim
  -- Zero belongs to every member's closure, witnessing strictness.
  rw [Set.ssubset_iff_exists]
  constructor
  · exact closure_iInter_subset_iInter_closure _
  · refine ⟨0, ?_, ?_⟩
    · rw [mem_iInter]
      intro b
      by_cases hb : b = true
      · rw [if_pos hb, closure_Iio]
        simpa only [mem_Iic] using (le_refl (0 : ℝ))
      · rw [if_neg hb, closure_Ioi]
        simpa only [mem_Ici] using (le_refl (0 : ℝ))
    · rw [hInterEmpty, closure_empty]
      simp only [mem_empty_iff_false, not_false_eq_true]

/- Exercise 17.8 (5): Equivalently to the source's `⊇` formulation,
`closure A \ closure B ⊆ closure (A \ B)`. -/
#check closure_sdiff

/-- Helper for Exercise 17.8 (6): Equality can fail for set difference: removing `0` from
`ℝ` before taking closure gives a strict superset of the difference of closures. -/
theorem diff_closure_ssubset_closure_sdiff_real :
    closure (Set.univ : Set ℝ) \ closure ({0} : Set ℝ) ⊂
      closure ((Set.univ : Set ℝ) \ {0}) := by
  -- The standard difference inclusion becomes strict at the removed point zero.
  rw [Set.ssubset_iff_exists]
  constructor
  · exact closure_sdiff
  · refine ⟨0, ?_, ?_⟩
    · rw [← compl_eq_univ_sdiff, closure_compl_singleton]
      exact mem_univ 0
    · intro hZero
      exact hZero.2 (subset_closure (mem_singleton 0))
