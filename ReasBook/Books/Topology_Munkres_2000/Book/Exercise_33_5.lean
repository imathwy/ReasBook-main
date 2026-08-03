module

public import Topology_Munkres_2000.Book.Exercise_33_5.PreciseSeparation
public import Topology_Munkres_2000.Book.Exercise_33_4
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Separation.Regular

public section

open Set

universe u

/-- Helper for Exercise 33.5: if `a` and `b` are nonnegative and have positive sum,
then `a / (a + b)` belongs to the closed unit interval. -/
private theorem ratio_self_add_mem_Icc (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) : a / (a + b) ∈ Icc (0 : ℝ) 1 := by
  -- Positivity of the denominator gives the lower and upper quotient bounds.
  constructor
  · exact div_nonneg ha (le_of_lt hab)
  · exact (div_le_one hab).2 (le_add_of_nonneg_right hb)

/-- Helper for Exercise 33.5: if `a` and `b` are positive, then `a / (a + b)`
belongs to the open unit interval. -/
private theorem ratio_self_add_mem_Ioo (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / (a + b) ∈ Ioo (0 : ℝ) 1 := by
  -- Strict positivity of both summands gives strict bounds for the normalized ratio.
  constructor
  · exact div_pos ha (add_pos ha hb)
  · exact (div_lt_one (add_pos ha hb)).2 (lt_add_of_pos_right a hb)

/-- Helper for Exercise 33.5: with positive denominator, `a / (a + b)` vanishes
exactly when `a` vanishes. -/
private theorem ratio_self_add_eq_zero_iff (a b : ℝ) (hab : 0 < a + b) :
    a / (a + b) = 0 ↔ a = 0 := by
  -- The positive denominator rules out the extra zero-denominator alternative.
  rw [div_eq_zero_iff]
  exact or_iff_left (ne_of_gt hab)

/-- Helper for Exercise 33.5: with positive denominator, `a / (a + b)` equals one
exactly when `b` vanishes. -/
private theorem ratio_self_add_eq_one_iff (a b : ℝ) (hab : 0 < a + b) :
    a / (a + b) = 1 ↔ b = 0 := by
  -- Clear the nonzero denominator and reduce the endpoint identity to linear arithmetic.
  rw [div_eq_iff (ne_of_gt hab)]
  constructor
  · intro h
    linarith
  · intro h
    linarith

namespace ContinuousMap.VanishesPreciselyOn

/-- Helper for Exercise 33.5: exact zero-set maps for disjoint sets have pointwise
positive sum. -/
private theorem add_pos_of_disjoint {X : Type u} [TopologicalSpace X]
    {g h : C(X, Icc (0 : ℝ) 1)} {A B : Set X} (hg : g.VanishesPreciselyOn A)
    (hh : h.VanishesPreciselyOn B) (hAB : Disjoint A B) (x : X) :
    0 < (g x : ℝ) + (h x : ℝ) := by
  -- At least one summand is positive because a point cannot lie in both zero sets.
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := Set.disjoint_left.1 hAB hxA
    exact add_pos_of_nonneg_of_pos (g x).property.1 ((hh.positive_iff_notMem x).2 hxB)
  · exact add_pos_of_pos_of_nonneg ((hg.positive_iff_notMem x).2 hxA) (h x).property.1

end ContinuousMap.VanishesPreciselyOn

/-- Exercise 33.5: Strong form of the Urysohn lemma. In a normal space, a
continuous map to `Set.Icc 0 1` separates `A` and `B` precisely if and only if
`A` and `B` are disjoint closed `Gδ` sets. Here `T4Space` expresses the book's
convention for a normal space. -/
theorem ContinuousMap.exists_separatesPrecisely_iff {X : Type u} [TopologicalSpace X]
    [T4Space X] (A B : Set X) :
    (∃ f : C(X, Icc (0 : ℝ) 1), f.SeparatesPrecisely A B) ↔
      Disjoint A B ∧ IsClosed A ∧ IsGδ A ∧ IsClosed B ∧ IsGδ B := by
  constructor
  · rintro ⟨f, hf⟩
    -- The exact endpoint fibers are disjoint, and each is a closed `Gδ` preimage.
    have hfEndpoints := ContinuousMap.SeparatesPrecisely.iff_eqOn_and_mem_Ioo.mp hf
    have hDisjoint : Disjoint A B := by
      rw [Set.disjoint_left]
      intro x hxA hxB
      have hZero : (f x : ℝ) = 0 := hfEndpoints.1 hxA
      have hOne : (f x : ℝ) = 1 := hfEndpoints.2.1 hxB
      linarith
    have hBClosed : IsClosed B := by
      rw [← hf.oneSet_eq]
      exact isClosed_singleton.preimage (continuous_subtype_val.comp f.continuous)
    have hBGdelta : IsGδ B := by
      rw [← hf.oneSet_eq]
      exact (IsGδ.singleton (1 : ℝ)).preimage (continuous_subtype_val.comp f.continuous)
    exact ⟨hDisjoint, hf.vanishesPreciselyOn.isClosed, hf.vanishesPreciselyOn.isGδ,
      hBClosed, hBGdelta⟩
  · rintro ⟨hDisjoint, hAClosed, hAGdelta, hBClosed, hBGdelta⟩
    -- Obtain exact zero-set maps and normalize them by their everywhere-positive sum.
    obtain ⟨g, hg⟩ :=
      (ContinuousMap.exists_vanishesPreciselyOn_iff_closed_isGδ A).2 ⟨hAClosed, hAGdelta⟩
    obtain ⟨h, hh⟩ :=
      (ContinuousMap.exists_vanishesPreciselyOn_iff_closed_isGδ B).2 ⟨hBClosed, hBGdelta⟩
    have hSumPos (x : X) : 0 < (g x : ℝ) + (h x : ℝ) :=
      hg.add_pos_of_disjoint hh hDisjoint x
    have hGContinuous : Continuous fun x ↦ (g x : ℝ) :=
      continuous_subtype_val.comp g.continuous
    have hHContinuous : Continuous fun x ↦ (h x : ℝ) :=
      continuous_subtype_val.comp h.continuous
    have hRatioContinuous :
        Continuous fun x ↦ (g x : ℝ) / ((g x : ℝ) + (h x : ℝ)) := by
      -- Division is continuous because the denominator is pointwise nonzero.
      exact hGContinuous.div (hGContinuous.add hHContinuous) fun x ↦ ne_of_gt (hSumPos x)
    have hRatioRange (x : X) :
        (g x : ℝ) / ((g x : ℝ) + (h x : ℝ)) ∈ Icc (0 : ℝ) 1 :=
      ratio_self_add_mem_Icc (g x : ℝ) (h x : ℝ) (g x).property.1 (h x).property.1
        (hSumPos x)
    have hContinuous : Continuous fun x ↦
        (⟨(g x : ℝ) / ((g x : ℝ) + (h x : ℝ)), hRatioRange x⟩ : Icc (0 : ℝ) 1) :=
      hRatioContinuous.subtype_mk _
    let f : C(X, Icc (0 : ℝ) 1) :=
      ⟨fun x ↦ ⟨(g x : ℝ) / ((g x : ℝ) + (h x : ℝ)), hRatioRange x⟩, hContinuous⟩
    refine ⟨f, ?_⟩
    -- The quotient has the prescribed endpoint values and is strict away from both sets.
    apply ContinuousMap.SeparatesPrecisely.iff_eqOn_and_mem_Ioo.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro x hxA
      have hZero : (g x : ℝ) = 0 :=
        ((ContinuousMap.vanishesPreciselyOn_iff g A).1 hg x).2 hxA
      have hRatio : (g x : ℝ) / ((g x : ℝ) + (h x : ℝ)) = 0 :=
        (ratio_self_add_eq_zero_iff (g x : ℝ) (h x : ℝ) (hSumPos x)).2 hZero
      simpa [f] using hRatio
    · intro x hxB
      have hZero : (h x : ℝ) = 0 :=
        ((ContinuousMap.vanishesPreciselyOn_iff h B).1 hh x).2 hxB
      have hRatio : (g x : ℝ) / ((g x : ℝ) + (h x : ℝ)) = 1 :=
        (ratio_self_add_eq_one_iff (g x : ℝ) (h x : ℝ) (hSumPos x)).2 hZero
      simpa [f] using hRatio
    · intro x hxA hxB
      have hGPos : 0 < (g x : ℝ) := (hg.positive_iff_notMem x).2 hxA
      have hHPos : 0 < (h x : ℝ) := (hh.positive_iff_notMem x).2 hxB
      simpa [f] using ratio_self_add_mem_Ioo (g x : ℝ) (h x : ℝ) hGPos hHPos
