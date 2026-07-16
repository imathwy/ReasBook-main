import Mathlib.Geometry.Manifold.PartitionOfUnity
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Definition_2_11_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM

/-- Proposition 2.28: every smooth manifold with or without boundary admits a smooth
real-valued function that is everywhere positive and has compact closed sublevel sets. -/
-- Proof sketch: use a countable precompact open cover and a smooth partition of unity subordinate
-- to it; the weighted sum `∑ j, j • ψ_j` is smooth and positive, and the usual sublevel-set
-- estimate shows that each set `f ⁻¹' Set.Iic c` is contained in a finite union of compact
-- closures from the cover.
theorem exists_positive_smooth_exhaustion_function
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I (∞ : ℕ∞ω) M] [T2Space M] [SigmaCompactSpace M] :
    ∃ f : C^∞⟮I, M; ℝ⟯, (∀ x : M, 0 < f x) ∧ (f : M → ℝ).IsExhaustionFunction := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let K : CompactExhaustion M := default
  let t : M → Set ℝ := fun x ↦ Set.Ioi (K.find x : ℝ)
  -- The target set at each point is the open ray above the compact-exhaustion rank.
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    simp only [t]
    exact convex_Ioi (K.find x : ℝ)
  -- Near `x`, the constant `(K.find x : ℝ) + 2` stays above all nearby target thresholds.
  have hloc : ∀ x : M, ∃ c : ℝ, ∀ᶠ y in nhds x, c ∈ t y := by
    intro x
    refine ⟨(K.find x : ℝ) + 2, ?_⟩
    have hK : K (K.find x + 1) ∈ nhds x := by
      exact mem_interior_iff_mem_nhds.mp (K.subset_interior_succ _ (K.mem_find x))
    filter_upwards [hK] with y hy
    simp only [t, Set.mem_Ioi]
    have hy_find : K.find y ≤ K.find x + 1 := (K.mem_iff_find_le).1 hy
    exact_mod_cast lt_of_le_of_lt hy_find (Nat.lt_succ_self (K.find x + 1))
  -- A smooth partition-of-unity gluing theorem produces a smooth function in all targets.
  obtain ⟨f, hf⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, ∀ x : M, f x ∈ t x := by
    simpa only [t] using exists_contMDiffMap_forall_mem_convex_of_local_const I ht hloc
  refine ⟨f, ?_⟩
  constructor
  · -- Positivity follows because the compact-exhaustion rank is nonnegative everywhere.
    intro x
    have h_find_nonneg : 0 ≤ (K.find x : ℝ) := by
      exact_mod_cast Nat.zero_le (K.find x)
    have h_find_lt : (K.find x : ℝ) < f x := by
      simpa [t, Set.mem_Ioi] using hf x
    exact lt_of_le_of_lt h_find_nonneg h_find_lt
  · -- Each closed sublevel set is contained in a compact stage of the compact exhaustion.
    refine ⟨f.contMDiff.continuous, ?_⟩
    intro c
    refine
      (K.isCompact ⌈c⌉₊).of_isClosed_subset (isClosed_Iic.preimage f.contMDiff.continuous) ?_
    intro x hx
    have h_find_lt : (K.find x : ℝ) < f x := by
      simpa [t, Set.mem_Ioi] using hf x
    have h_find_lt_c : (K.find x : ℝ) < c := h_find_lt.trans_le hx
    apply (K.mem_iff_find_le).2
    exact (Nat.lt_ceil.2 h_find_lt_c).le
