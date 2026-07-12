import Mathlib

open Set

open scoped Topology unitInterval

/-- Helper for Cartan section28 0001_Theorem_2: if an initial segment of the unit interval lies in
an open reachable-time set, then that initial segment can be extended a bit further to the right
before time `1`. -/
theorem initialSegmentSubset_rightExtension
    {R : Set I} (hRopen : IsOpen R)
    {t : I}
    (ht : Set.Icc (0 : I) t ⊆ R)
    (htlt : (t : ℝ) < 1) :
    ∃ s : I, t < s ∧ Set.Icc (0 : I) s ⊆ R := by
  have htR : t ∈ R := ht <| by simp
  have hRt : R ∈ 𝓝 t := hRopen.mem_nhds htR
  rcases Metric.mem_nhds_iff.mp hRt with ⟨ε, hεpos, hεsub⟩
  let δ : ℝ := min (ε / 2) ((1 - (t : ℝ)) / 2)
  have hδpos : 0 < δ := by
    have hgap : 0 < (1 : ℝ) - t := sub_pos.mpr htlt
    exact lt_min (half_pos hεpos) (half_pos hgap)
  let s : I := ⟨(t : ℝ) + δ, by
    refine ⟨?_, ?_⟩
    · linarith [t.2.1, hδpos]
    · have hδle : δ ≤ ((1 : ℝ) - t) / 2 := min_le_right _ _
      linarith⟩
  refine ⟨s, ?_, ?_⟩
  · -- Move the endpoint slightly to the right by the positive increment `δ`.
    change (t : ℝ) < (s : ℝ)
    simp [s, δ, hδpos]
  · intro u hu
    by_cases hu_le_t : u ≤ t
    · -- Earlier points stay inside the already-known initial segment.
      exact ht ⟨hu.1, hu_le_t⟩
    · -- Later points still lie in the small ball around `t`, hence remain reachable.
      have ht_lt_u : t < u := lt_of_not_ge hu_le_t
      have huBall : u ∈ Metric.ball t ε := by
        have hδle : δ ≤ ε / 2 := min_le_left _ _
        have hu_le_s : (u : ℝ) ≤ s := hu.2
        have hdist : dist (u : I) t < ε := by
          rw [Subtype.dist_eq, Real.dist_eq]
          have habs : |(u : ℝ) - t| = (u : ℝ) - t := by
            exact abs_of_nonneg <| sub_nonneg.mpr <| le_of_lt ht_lt_u
          rw [habs]
          linarith
        simpa [Metric.mem_ball] using hdist
      exact hεsub huBall

/-- Helper for Cartan section28 0001_Theorem_2: the initial-segment invariant is monotone in its
endpoint. -/
theorem initialSegmentSubset_mono
    {R : Set I} {s u : I}
    (hs : Set.Icc (0 : I) s ⊆ R)
    (hu : u ≤ s) :
    Set.Icc (0 : I) u ⊆ R := by
  -- Any point of the smaller initial segment also belongs to the larger one.
  intro v hv
  exact hs ⟨hv.1, le_trans hv.2 hu⟩

/-- Helper for Cartan section28 0001_Theorem_2: the first bad time of a nonempty complement has
the expected `csInf` bounds, and every strictly earlier time is already good. -/
theorem initialSegmentBadTimes_csInfData
    {A B : Set I}
    (hB : B = {t : I | t ∉ A})
    (hBne : B.Nonempty) :
    let m : ℝ := sInf (Subtype.val '' B)
    0 ≤ m ∧ m ≤ 1 ∧ ∀ u : I, (u : ℝ) < m → u ∈ A := by
  let S : Set ℝ := Subtype.val '' B
  have hSne : S.Nonempty := by
    rcases hBne with ⟨t, ht⟩
    exact ⟨(t : ℝ), ⟨t, ht, rfl⟩⟩
  have hSbd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact t.2.1
  refine ⟨?_, ?_, ?_⟩
  · -- Every bad time lies in the unit interval, so the infimum is nonnegative.
    exact le_csInf hSne fun y hy ↦ by
      rcases hy with ⟨t, ht, rfl⟩
      exact t.2.1
  · -- Any explicit bad time bounds the infimum from above, and every bad time is at most `1`.
    rcases hBne with ⟨t, ht⟩
    have hmle : sInf S ≤ (t : ℝ) :=
      csInf_le hSbd ⟨t, ⟨ht, rfl⟩⟩
    exact le_trans hmle t.2.2
  · intro u hu
    by_contra huA
    have huB : u ∈ B := by
      simpa [hB] using huA
    have hmle : sInf S ≤ (u : ℝ) :=
      csInf_le hSbd ⟨u, ⟨huB, rfl⟩⟩
    exact not_le_of_gt hu hmle

/-- Helper for Cartan section28 0001_Theorem_2: once the first bad time itself lies in the open
reachable set `R`, openness propagates the initial-segment invariant a little further right. -/
theorem initialSegmentBoundaryNeighborhood
    {R : Set I} (hRopen : IsOpen R)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hPrefix : ∀ u : I, (u : ℝ) < m → Set.Icc (0 : I) u ⊆ R)
    (hmR : (⟨m, ⟨hm0, hm1⟩⟩ : I) ∈ R) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ v : I, m ≤ v → (v : ℝ) ≤ min 1 (m + δ) → Set.Icc (0 : I) v ⊆ R := by
  let mI : I := ⟨m, ⟨hm0, hm1⟩⟩
  have hRm : R ∈ 𝓝 mI := hRopen.mem_nhds hmR
  rcases Metric.mem_nhds_iff.mp hRm with ⟨ε, hεpos, hεsub⟩
  let δ : ℝ := ε / 2
  refine ⟨δ, half_pos hεpos, ?_⟩
  intro v hmv hvδ u hu
  by_cases hu_lt_m : (u : ℝ) < m
  · -- Points strictly before the boundary stay good by the prefix hypothesis.
    exact hPrefix u hu_lt_m (by simp)
  · -- Points from `m` up to `v` stay inside the small metric ball around the boundary time.
    have hmu : m ≤ (u : ℝ) := le_of_not_gt hu_lt_m
    have huBall : u ∈ Metric.ball mI ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have habs : |(u : ℝ) - m| = (u : ℝ) - m := by
        exact abs_of_nonneg (sub_nonneg.mpr hmu)
      rw [habs]
      have hu_le_v : (u : ℝ) ≤ v := hu.2
      have hv_le_mδ : (v : ℝ) ≤ m + δ := le_trans hvδ (min_le_right _ _)
      have hδlt : δ < ε := by
        dsimp [δ]
        linarith
      linarith
    exact hεsub huBall

/-- Helper for Cartan section28 0001_Theorem_2: a first-bad-time contradiction closes the initial
segment invariant once every boundary time admits a short good neighborhood to its right. -/
theorem initialSegmentTop_ofFirstBadTime
    {A : Set I}
    (hBoundary :
      ∀ {m : ℝ}, 0 ≤ m → m ≤ 1 →
        (∀ u : I, (u : ℝ) < m → u ∈ A) →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ v : I, m ≤ v → (v : ℝ) ≤ min 1 (m + δ) → v ∈ A) :
    (1 : I) ∈ A := by
  by_contra h1notA
  let B : Set I := {t : I | t ∉ A}
  let S : Set ℝ := Subtype.val '' B
  let m : ℝ := sInf S
  have hBne : B.Nonempty := ⟨1, by simpa [B] using h1notA⟩
  have hSne : S.Nonempty := by
    rcases hBne with ⟨t, ht⟩
    exact ⟨(t : ℝ), ⟨t, ht, rfl⟩⟩
  have hSbd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact t.2.1
  obtain ⟨hm0, hm1, hltA⟩ :=
    initialSegmentBadTimes_csInfData (A := A) (B := B) rfl hBne
  obtain ⟨δ, hδpos, hδA⟩ := hBoundary hm0 hm1 hltA
  let mI : I := ⟨m, ⟨hm0, hm1⟩⟩
  have hmA : mI ∈ A := by
    have hmMin : m ≤ min 1 (m + δ) := by
      refine le_min hm1 ?_
      linarith
    have hmSelf : sInf (Subtype.val '' B) ≤ (mI : ℝ) := by
      simpa [mI, m, S]
    exact hδA mI hmSelf hmMin
  by_cases hmEq1 : m = 1
  · have h1A : (1 : I) ∈ A := by
      simpa [mI, hmEq1] using hmA
    exact h1notA h1A
  · have hmLt1 : m < 1 := lt_of_le_of_ne hm1 hmEq1
    let ε : ℝ := min (δ / 2) ((1 - m) / 2)
    have hεpos : 0 < ε := by
      refine lt_min ?_ ?_
      · exact half_pos hδpos
      · exact half_pos (sub_pos.mpr hmLt1)
    have hmLt : m < m + ε := by
      have : 0 < ε := hεpos
      linarith
    have hglb : IsGLB S m := isGLB_csInf hSne hSbd
    rcases (isGLB_lt_iff hglb).1 hmLt with ⟨y, hyS, hyLt⟩
    rcases hyS with ⟨v, hvB, rfl⟩
    have hmle_v : m ≤ (v : ℝ) := hglb.1 ⟨v, ⟨hvB, rfl⟩⟩
    have hvMin : (v : ℝ) ≤ min 1 (m + δ) := by
      refine le_min v.2.2 ?_
      have hεle : ε ≤ δ / 2 := min_le_left _ _
      linarith
    have hvA : v ∈ A := hδA v hmle_v hvMin
    exact hvB hvA
