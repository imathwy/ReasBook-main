import DifferentialForms_Cartan_1970.cartan.IV.section13.«0003_Definition_IV_1_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {𝕜 : Type u} [SeminormedAddCommGroup 𝕜]

/-- Helper for Proposition 2.I: the convergence locus `Γ` is coordinatewise downward closed inside
the nonnegative quadrant. -/
lemma formalSeriesConvergenceLocus_mono
    (a : ℕ → ℕ → 𝕜) {R₁ R₂ ρ₁ ρ₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus a)
    (hρ₁_nonneg : 0 ≤ ρ₁) (hρ₁_le : ρ₁ ≤ R₁)
    (hρ₂_nonneg : 0 ≤ ρ₂) (hρ₂_le : ρ₂ ≤ R₂) :
    (ρ₁, ρ₂) ∈ formalSeriesConvergenceLocus a := by
  -- Unfold `Γ` and compare the smaller weighted terms with the larger summable ones.
  rw [mem_formalSeriesConvergenceLocus_iff] at hR ⊢
  rcases hR with ⟨hR₁_nonneg, hR₂_nonneg, hsumR⟩
  refine ⟨hρ₁_nonneg, hρ₂_nonneg, ?_⟩
  refine hsumR.of_nonneg_of_le ?_ ?_
  · intro n
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg hρ₁_nonneg _))
      (pow_nonneg hρ₂_nonneg _)
  · intro n
    have hpow₁ : ρ₁ ^ n.1 ≤ R₁ ^ n.1 :=
      pow_le_pow_left₀ hρ₁_nonneg hρ₁_le _
    have hpow₂ : ρ₂ ^ n.2 ≤ R₂ ^ n.2 :=
      pow_le_pow_left₀ hρ₂_nonneg hρ₂_le _
    have hmul₁ :
        ‖a n.1 n.2‖ * ρ₁ ^ n.1 ≤ ‖a n.1 n.2‖ * R₁ ^ n.1 :=
      mul_le_mul_of_nonneg_left hpow₁ (norm_nonneg _)
    exact mul_le_mul hmul₁ hpow₂ (pow_nonneg hρ₂_nonneg _)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hR₁_nonneg _))

/-- Helper for Proposition 2.I: every point of `Γ` contains the smaller positive rectangle below
it inside `Γ`. -/
lemma Ioo_prod_subset_formalSeriesConvergenceLocus_of_mem
    (a : ℕ → ℕ → 𝕜) {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus a) :
    Set.Ioo 0 R₁ ×ˢ Set.Ioo 0 R₂ ⊆ formalSeriesConvergenceLocus a := by
  -- Package the monotonicity lemma in the open-rectangle form used by the interior argument.
  intro ρ hρ
  rcases Set.mem_prod.mp hρ with ⟨hρ₁, hρ₂⟩
  exact formalSeriesConvergenceLocus_mono a hR hρ₁.1.le hρ₁.2.le hρ₂.1.le hρ₂.2.le

/-- Proposition 2.I (1): a pair `(r₁, r₂)` belongs to the domain of convergence `Δ` exactly when
both radii are strictly positive and there are larger radii `r₁' > r₁` and `r₂' > r₂` whose pair
belongs to the convergence locus `Γ`. -/
theorem mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus
    (a : ℕ → ℕ → 𝕜) (r₁ r₂ : ℝ) :
    (r₁, r₂) ∈ formalSeriesConvergenceDomain a ↔
      0 < r₁ ∧ 0 < r₂ ∧
        ∃ r₁' > r₁, ∃ r₂' > r₂, (r₁', r₂') ∈ formalSeriesConvergenceLocus a := by
  constructor
  · intro hr
    -- From interior membership, extract a ball contained in `Γ` and test three nearby points.
    rw [mem_formalSeriesConvergenceDomain_iff, mem_interior_iff_mem_nhds] at hr
    rcases Metric.mem_nhds_iff.1 hr with ⟨ε, hε_pos, hε_subset⟩
    have hhalf_pos : 0 < ε / 2 := by
      linarith
    have hleft_mem : (r₁ - ε / 2, r₂) ∈ formalSeriesConvergenceLocus a := by
      apply hε_subset
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        have hneg : r₁ - ε / 2 - r₁ < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith
      · simpa using hε_pos
    have hdown_mem : (r₁, r₂ - ε / 2) ∈ formalSeriesConvergenceLocus a := by
      apply hε_subset
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · simpa using hε_pos
      · rw [Real.dist_eq]
        have hneg : r₂ - ε / 2 - r₂ < 0 := by
          linarith
        rw [abs_of_neg hneg]
        linarith
    have hupright_mem : (r₁ + ε / 2, r₂ + ε / 2) ∈ formalSeriesConvergenceLocus a := by
      apply hε_subset
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        have hnonneg : 0 ≤ r₁ + ε / 2 - r₁ := by
          linarith
        rw [abs_of_nonneg hnonneg]
        linarith
      · rw [Real.dist_eq]
        have hnonneg : 0 ≤ r₂ + ε / 2 - r₂ := by
          linarith
        rw [abs_of_nonneg hnonneg]
        linarith
    have hleft_nonneg : 0 ≤ r₁ - ε / 2 := by
      rcases (mem_formalSeriesConvergenceLocus_iff a (r₁ - ε / 2, r₂)).1 hleft_mem with
        ⟨hnonneg, -, -⟩
      exact hnonneg
    have hdown_nonneg : 0 ≤ r₂ - ε / 2 := by
      rcases (mem_formalSeriesConvergenceLocus_iff a (r₁, r₂ - ε / 2)).1 hdown_mem with
        ⟨-, hnonneg, -⟩
      exact hnonneg
    have hr₁_pos : 0 < r₁ := by
      linarith
    have hr₂_pos : 0 < r₂ := by
      linarith
    have hr₁_lt : r₁ < r₁ + ε / 2 := by
      linarith
    have hr₂_lt : r₂ < r₂ + ε / 2 := by
      linarith
    exact ⟨hr₁_pos, hr₂_pos, r₁ + ε / 2, hr₁_lt, r₂ + ε / 2, hr₂_lt, hupright_mem⟩
  · rintro ⟨hr₁_pos, hr₂_pos, r₁', hr₁_lt, r₂', hr₂_lt, hr_mem⟩
    -- A larger point of `Γ` contributes an open rectangle inside `Γ`, so `(r₁, r₂)` is interior.
    rw [mem_formalSeriesConvergenceDomain_iff]
    refine mem_interior.2 ?_
    refine ⟨Set.Ioo 0 r₁' ×ˢ Set.Ioo 0 r₂', ?_, isOpen_Ioo.prod isOpen_Ioo, ?_⟩
    · exact Ioo_prod_subset_formalSeriesConvergenceLocus_of_mem a hr_mem
    · exact Set.mem_prod.mpr ⟨⟨hr₁_pos, hr₁_lt⟩, ⟨hr₂_pos, hr₂_lt⟩⟩

/-- Proposition 2.I (2): the domain of convergence `Δ` is nonempty exactly when the coefficient
series is absolutely summable at some pair of strictly positive radii. -/
theorem formalSeriesConvergenceDomain_nonempty_iff
    (a : ℕ → ℕ → 𝕜) :
    Set.Nonempty (formalSeriesConvergenceDomain a) ↔
      ∃ r₁ > (0 : ℝ), ∃ r₂ > (0 : ℝ), (r₁, r₂) ∈ formalSeriesConvergenceLocus a := by
  constructor
  · rintro ⟨r, hr⟩
    -- Extract a strictly positive witness in `Γ` from any interior point via Proposition 2.I (1).
    rcases
      (mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus
        a r.1 r.2).1 hr with
      ⟨hr₁_base, hr₂_base, r₁, hr₁_gt, r₂, hr₂_gt, hr_mem⟩
    have hr₁_pos : 0 < r₁ := lt_trans hr₁_base hr₁_gt
    have hr₂_pos : 0 < r₂ := lt_trans hr₂_base hr₂_gt
    exact ⟨r₁, hr₁_pos, r₂, hr₂_pos, hr_mem⟩
  · rintro ⟨R₁, hR₁_pos, R₂, hR₂_pos, hR_mem⟩
    -- Conversely, halve a positive point of `Γ` to obtain a smaller interior point of `Δ`.
    refine ⟨(R₁ / 2, R₂ / 2), ?_⟩
    rw [mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus]
    have hR₁_half_pos : 0 < R₁ / 2 := by
      linarith
    have hR₂_half_pos : 0 < R₂ / 2 := by
      linarith
    have hR₁_half_lt : R₁ / 2 < R₁ := by
      linarith
    have hR₂_half_lt : R₂ / 2 < R₂ := by
      linarith
    exact ⟨hR₁_half_pos, hR₂_half_pos, R₁, hR₁_half_lt, R₂, hR₂_half_lt, hR_mem⟩
