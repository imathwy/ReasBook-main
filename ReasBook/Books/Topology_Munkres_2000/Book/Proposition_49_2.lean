import Topology_Munkres_2000.Book.Example_49_1.LargeSecants

open Set

namespace UnitIntervalSecant

/-- Helper for Proposition 49.2: a pointwise lower bound for all secant
magnitudes is a lower bound for their infimum. -/
private lemma le_infMagnitude_of_forall (f : Icc (0 : ℝ) 1 → ℝ) (h α : ℝ)
    (hall : ∀ x, α ≤ Δ f (x, h)) :
    α ≤ Δ_{h} f := by
  -- Supply the universal lower bound directly to the `sInf` characterization.
  unfold infMagnitude
  refine le_csInf (Set.range_nonempty _) ?_
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  exact hall x

/-- Helper for Proposition 49.2: a positive secant infimum lies below every
pointwise secant magnitude, without a restriction on the scale. -/
private lemma infMagnitude_le_maxMagnitude_of_pos
    (f : Icc (0 : ℝ) 1 → ℝ) (h : ℝ) (hpos : 0 < Δ_{h}f)
    (x : Icc (0 : ℝ) 1) :
    Δ_{h} f ≤ Δ f (x, h) := by
  -- Positivity rules out the unbounded-below case, where the real infimum is zero.
  unfold infMagnitude at hpos ⊢
  by_contra hnot
  have hnotbdd : ¬ BddBelow (Set.range (fun y ↦ Δ f (y, h))) := by
    intro hbdd
    exact hnot (csInf_le hbdd (Set.mem_range_self x))
  rw [Real.sInf_of_not_bddBelow hnotbdd] at hpos
  linarith

/-- Helper for Proposition 49.2: uniform distance controls the change in the
absolute secant quotient between any two endpoints. -/
private lemma secantQuotient_le_add_uniformError
    (f g : C(unitInterval, ℝ)) (x y : unitInterval) (d : ℝ) (hd : d ≠ 0) :
    |(f y - f x) / d| ≤ |(g y - g x) / d| + 2 * dist f g / |d| := by
  -- Bound the two endpoint errors by the uniform metric.
  have hy : |f y - g y| ≤ dist f g := by
    simpa only [Real.dist_eq] using
      (ContinuousMap.dist_apply_le_dist (f := f) (g := g) y)
  have hx : |f x - g x| ≤ dist f g := by
    simpa only [Real.dist_eq] using
      (ContinuousMap.dist_apply_le_dist (f := f) (g := g) x)
  have hnumerator : |(f y - f x) - (g y - g x)| ≤ 2 * dist f g := by
    calc
      |(f y - f x) - (g y - g x)| = |(f y - g y) - (f x - g x)| := by
        congr 1
        ring
      _ ≤ |f y - g y| + |f x - g x| := abs_sub _ _
      _ ≤ 2 * dist f g := by linarith
  have hdenominator : 0 < |d| := abs_pos.mpr hd
  have hquotient :
      |(f y - f x) / d - (g y - g x) / d| ≤ 2 * dist f g / |d| := by
    calc
      |(f y - f x) / d - (g y - g x) / d| =
          |((f y - f x) - (g y - g x)) / d| := by rw [div_sub_div_same]
      _ = |(f y - f x) - (g y - g x)| / |d| := abs_div _ _
      _ ≤ 2 * dist f g / |d| :=
        div_le_div_of_nonneg_right hnumerator hdenominator.le
  -- The reverse triangle inequality turns quotient control into magnitude control.
  linarith [abs_sub_abs_le_abs_sub ((f y - f x) / d) ((g y - g x) / d)]

/-- Helper for Proposition 49.2: a pointwise secant lower bound persists, with
half the margin, under a sufficiently small uniform perturbation. -/
private lemma maxMagnitude_lower_of_dist_lt
    (f g : C(unitInterval, ℝ)) (x : unitInterval) (h a m : ℝ)
    (hpos : 0 < h) (ha : 0 ≤ a) (ham : a < m)
    (hm : m ≤ Δ f (x, h)) (hdist : dist f g < h * (m - a) / 4) :
    (m + a) / 2 ≤ Δ g (x, h) := by
  -- Convert the radius bound into the half-margin allowed for a secant quotient.
  have herr : 2 * dist f g / h < (m - a) / 2 := by
    rw [div_lt_iff₀ hpos]
    nlinarith
  have hmpos : 0 < m := lt_of_le_of_lt ha ham
  have hmidpos : 0 < (m + a) / 2 := by linarith
  -- Select the endpoint of `f` carrying the lower bound and reuse it for `g`.
  rw [le_maxMagnitude_iff g hmidpos x h]
  rcases (le_maxMagnitude_iff f hmpos x h).mp hm with
    ⟨y, hy, hybound⟩ | ⟨y, hy, hybound⟩
  · left
    refine ⟨y, hy, ?_⟩
    have hcompare := secantQuotient_le_add_uniformError f g x y h hpos.ne'
    rw [abs_of_pos hpos] at hcompare
    linarith
  · right
    refine ⟨y, hy, ?_⟩
    have hcompare :=
      secantQuotient_le_add_uniformError f g x y (-h) (neg_ne_zero.mpr hpos.ne')
    rw [abs_neg, abs_of_pos hpos] at hcompare
    linarith

/-- Proposition 49.2: The set of continuous real-valued functions on
`unitInterval` whose infimum secant magnitude exceeds `n` at some scale
`0 < h ≤ 1 / n` is open in the uniform topology. The source uses this for
`2 ≤ n`, but openness holds for every `n`. -/
theorem isOpen_largeSecantSet (n : ℕ) :
    IsOpen U_{n} := by
  -- Fix a function and retain the scale witnessing its large secant infimum.
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨h, hpos, hle, hninf⟩ := mem_largeSecantSet.mp hf
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hinfpos : 0 < Δ_{h}f := lt_of_le_of_lt hnnonneg hninf
  -- Use one quarter of the strict secant margin as the uniform ball radius.
  refine ⟨h * (Δ_{h}f - (n : ℝ)) / 4, ?_, ?_⟩
  · positivity
  · intro g hg
    have hdist : dist f g < h * (Δ_{h}f - (n : ℝ)) / 4 := by
      rw [Metric.mem_ball] at hg
      simpa only [dist_comm] using hg
    rw [mem_largeSecantSet]
    refine ⟨h, hpos, hle, ?_⟩
    -- Every secant magnitude of `g` retains at least half the original margin.
    have hpointwise : ∀ x, (Δ_{h}f + (n : ℝ)) / 2 ≤ Δ g (x, h) := by
      intro x
      exact maxMagnitude_lower_of_dist_lt f g x h (n : ℝ) (Δ_{h}f) hpos
        hnnonneg hninf (infMagnitude_le_maxMagnitude_of_pos f h hinfpos x) hdist
    have hinfbound : (Δ_{h}f + (n : ℝ)) / 2 ≤ Δ_{h}g :=
      le_infMagnitude_of_forall g h ((Δ_{h}f + (n : ℝ)) / 2) hpointwise
    -- The midpoint is still strictly above `n` because the original infimum was.
    linarith

end UnitIntervalSecant
