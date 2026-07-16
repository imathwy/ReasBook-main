import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section10.«0011_Theorem_III_4_extra_9»

-- Semantic recall note: `lean_leansearch` was unavailable in this runner, so the statement shape
-- was checked against the local isolated/essential-singularity owner API together with mathlib's
-- standard `Metric.ball` and `Set.InjOn` interfaces.

-- Declarations for this item will be appended below by the statement pipeline.

open Set Metric Filter
open scoped Topology

section

variable {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}

/-- Helper for Exercise 16: the radii `ρ / 2^n` remain positive while `ρ` is positive. -/
lemma div_pow_two_pos (hρ : 0 < ρ) (n : ℕ) : 0 < ρ / (2 : ℝ) ^ n := by
  -- The geometric radii stay positive because both the numerator and denominator are positive.
  exact div_pos hρ (pow_pos (by norm_num) _)

/-- Helper for Exercise 16: the radii `ρ / 2^n` stay bounded above by the initial radius `ρ`. -/
lemma div_pow_two_le_self (hρ : 0 ≤ ρ) (n : ℕ) : ρ / (2 : ℝ) ^ n ≤ ρ := by
  -- Since `2^n ≥ 1`, dividing a nonnegative radius by `2^n` only shrinks it.
  have hpow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa using (one_le_pow₀ (a := (2 : ℝ)) (show (1 : ℝ) ≤ 2 by norm_num) : 1 ≤ (2 : ℝ) ^ n)
  exact div_le_self hρ hpow_ge

/-- Helper for Exercise 16: after shrinking to an analytic punctured ball, the image still omits
at most one complex value. -/
lemma small_punctured_ball_image_eq_univ_or_compl_singleton
    (hess : HasEssentialSingularityAt f c)
    (hρ : 0 < ρ) :
    ∃ ρ' > 0, ρ' ≤ ρ ∧
      AnalyticOnNhd ℂ f (ball c ρ' \ ({c} : Set ℂ)) ∧
      (f '' (ball c ρ' \ ({c} : Set ℂ)) = univ ∨
        ∃ a : ℂ, f '' (ball c ρ' \ ({c} : Set ℂ)) = ({a} : Set ℂ)ᶜ) := by
  -- Shrink the requested radius to one on which punctured-ball analyticity is available.
  rcases
      (HasIsolatedSingularityAt.iff_exists_analyticOnNhd_punctured_ball.mp hess.isolated) with
    ⟨R, hR, hRanalytic⟩
  let ρ' := min ρ R
  have hρ' : 0 < ρ' := by
    exact lt_min hρ hR
  have hρ'le : ρ' ≤ ρ := by
    exact min_le_left _ _
  have hanalytic : AnalyticOnNhd ℂ f (ball c ρ' \ ({c} : Set ℂ)) := by
    -- Restrict the analytic punctured ball to the smaller radius `ρ'`.
    exact hRanalytic.mono <| by
      intro z hz
      refine ⟨?_, hz.2⟩
      simpa [ρ'] using lt_of_lt_of_le hz.1 (min_le_right ρ R)
  have himage :=
    punctured_ball_image_eq_univ_or_compl_singleton_of_essential_singularity hess hρ' hanalytic
  exact ⟨ρ', hρ', hρ'le, hanalytic, himage⟩

/-- Helper for Exercise 16: every ball in `ℂ` contains a point avoiding any prescribed singleton. -/
lemma exists_mem_ball_ne_singleton (γ a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ ball γ ε, y ≠ a := by
  -- The two symmetric points `γ ± ε / 2` cannot both coincide with the omitted value.
  have hplus_mem : γ + (ε / 2 : ℝ) ∈ ball γ ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hminus_mem : γ - (ε / 2 : ℝ) ∈ ball γ ε := by
    rw [mem_ball] at hplus_mem ⊢
    have hdist :
        dist (γ - (ε / 2 : ℝ)) γ = dist (γ + (ε / 2 : ℝ)) γ := by
      rw [dist_eq_norm, dist_eq_norm]
      simp [sub_eq_add_neg, Complex.norm_real, Real.norm_eq_abs]
    simpa [hdist] using hplus_mem
  by_cases hplus : γ + (ε / 2 : ℝ) = a
  · refine ⟨γ - (ε / 2 : ℝ), hminus_mem, ?_⟩
    intro hminus
    have hneq : γ + (ε / 2 : ℝ) ≠ γ - (ε / 2 : ℝ) := by
      intro hEq
      have hRe : γ.re + ε / 2 = γ.re - ε / 2 := by
        simpa using congrArg Complex.re hEq
      linarith
    exact hneq (hplus.trans hminus.symm)
  · exact ⟨γ + (ε / 2 : ℝ), hplus_mem, hplus⟩

/-- Exercise 16 (1): for an essential singularity `c`, every target disc around `γ` contains a
closed disc lying in the image of the punctured disc `0 < ‖z - c‖ < ρ`. -/
theorem exists_closedBall_subset_image_inter_ball_of_essentialSingularity
    (hess : HasEssentialSingularityAt f c)
    (hρ : 0 < ρ)
    {γ : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    ∃ z ∈ ball c ρ \ ({c} : Set ℂ), ∃ ε' > 0,
      closedBall (f z) ε' ⊆ f '' (ball c ρ \ ({c} : Set ℂ)) ∩ ball γ ε := by
  -- First shrink to a punctured ball where the Picard-type image theorem applies.
  rcases small_punctured_ball_image_eq_univ_or_compl_singleton hess hρ with
    ⟨ρ', hρ'pos, hρ'le, _, himage⟩
  let smallSet : Set ℂ := ball c ρ' \ ({c} : Set ℂ)
  let bigSet : Set ℂ := ball c ρ \ ({c} : Set ℂ)
  have hsmall_subset : smallSet ⊆ bigSet := by
    intro z hz
    refine ⟨lt_of_lt_of_le hz.1 hρ'le, hz.2⟩
  have himage_subset : f '' smallSet ⊆ f '' bigSet := by
    exact image_mono hsmall_subset
  rcases himage with hsmall_image | ⟨a, hsmall_image⟩
  · -- If the small image is all of `ℂ`, center the target closed ball at `γ` itself.
    have hγ_image : γ ∈ f '' smallSet := by
      rw [hsmall_image]
      exact mem_univ γ
    rcases hγ_image with ⟨z, hz, rfl⟩
    refine ⟨z, hsmall_subset hz, ε / 2, half_pos hε, ?_⟩
    intro w hw
    constructor
    · have hw_image : w ∈ f '' smallSet := by
        rw [hsmall_image]
        exact mem_univ w
      exact himage_subset hw_image
    · exact closedBall_subset_ball (half_lt_self hε) hw
  · -- Otherwise choose a point of the target ball that is not the omitted value.
    obtain ⟨y, hy_ball, hy_ne⟩ := exists_mem_ball_ne_singleton γ a hε
    have hy_image_mem : y ∈ f '' smallSet := by
      rw [hsmall_image]
      simpa [mem_compl_iff, mem_singleton_iff] using hy_ne
    have hy_mem : y ∈ f '' smallSet ∩ ball γ ε := by
      exact ⟨hy_image_mem, hy_ball⟩
    rcases hy_image_mem with ⟨z, hz, hzy⟩
    have hopen : IsOpen (f '' smallSet ∩ ball γ ε) := by
      rw [hsmall_image]
      exact isClosed_singleton.isOpen_compl.inter isOpen_ball
    rcases Metric.isOpen_iff.mp hopen y hy_mem with ⟨δ, hδpos, hδsubset⟩
    have hclosed :
        closedBall y (δ / 2) ⊆ f '' bigSet ∩ ball γ ε := by
      intro w hw
      have hw_ball : w ∈ ball y δ := by
        exact closedBall_subset_ball (half_lt_self hδpos) hw
      have hw_mem : w ∈ f '' smallSet ∩ ball γ ε := hδsubset hw_ball
      exact ⟨himage_subset hw_mem.1, hw_mem.2⟩
    refine ⟨z, hsmall_subset hz, δ / 2, half_pos hδpos, ?_⟩
    simpa [hzy] using hclosed

/-- Helper for Exercise 16: the closed ball from part (1) can be chosen with radius strictly
smaller than the target ball radius. -/
lemma exists_closedBall_subset_image_inter_ball_of_essentialSingularity_lt
    (hess : HasEssentialSingularityAt f c)
    (hρ : 0 < ρ)
    {γ : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    ∃ z ∈ ball c ρ \ ({c} : Set ℂ), ∃ ε' > 0, ε' < ε ∧
      closedBall (f z) ε' ⊆ f '' (ball c ρ \ ({c} : Set ℂ)) ∩ ball γ ε := by
  -- Shrink the closed-ball radius from part (1) further so that it is strictly less than `ε`.
  obtain ⟨z, hz, η, hηpos, hηsubset⟩ :=
    exists_closedBall_subset_image_inter_ball_of_essentialSingularity hess hρ (γ := γ) hε
  let ε' := min η (ε / 2)
  have hε'pos : 0 < ε' := by
    exact lt_min hηpos (half_pos hε)
  have hε'lt : ε' < ε := by
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
  have hsubset :
      closedBall (f z) ε' ⊆ f '' (ball c ρ \ ({c} : Set ℂ)) ∩ ball γ ε := by
    exact (closedBall_subset_closedBall (min_le_left _ _)).trans hηsubset
  exact ⟨z, hz, ε', hε'pos, hε'lt, hsubset⟩

/-- Exercise 16 (2): starting from a target disc around `γ₀`, one can choose points in shrinking
punctured discs around `c` and nested closed discs in their images. -/
theorem exists_nested_closedBalls_in_shrinking_puncturedDiscImages
    (hess : HasEssentialSingularityAt f c)
    (hρ : 0 < ρ)
    {γ₀ : ℂ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    ∃ z : ℕ → ℂ, ∃ ε : ℕ → ℝ,
      (∀ n, z n ∈ ball c (ρ / (2 : ℝ) ^ n) \ ({c} : Set ℂ)) ∧
      (∀ n, 0 < ε n) ∧
      ε 0 < ε₀ ∧
      StrictAnti ε ∧
      closedBall (f (z 0)) (ε 0) ⊆
        f '' (ball c ρ \ ({c} : Set ℂ)) ∩ ball γ₀ ε₀ ∧
      ∀ n,
        closedBall (f (z (n + 1))) (ε (n + 1)) ⊆
          f '' (ball c (ρ / (2 : ℝ) ^ (n + 1)) \ ({c} : Set ℂ)) ∩ ball (f (z n)) (ε n) := by
  classical
  -- Start from part (1), already shrinking the first image-disc radius below `ε₀`.
  obtain ⟨z₀, hz₀, ε₀', hε₀'pos, hε₀'lt, hbase⟩ :=
    exists_closedBall_subset_image_inter_ball_of_essentialSingularity_lt
      hess hρ (γ := γ₀) hε₀
  have hstep :
      ∀ n (p : {p : ℂ × ℝ // 0 < p.2}),
        ∃ q : {q : ℂ × ℝ // 0 < q.2},
          q.1.1 ∈ ball c (ρ / (2 : ℝ) ^ (n + 1)) \ ({c} : Set ℂ) ∧
          q.1.2 < p.1.2 ∧
          closedBall (f q.1.1) q.1.2 ⊆
            f '' (ball c (ρ / (2 : ℝ) ^ (n + 1)) \ ({c} : Set ℂ)) ∩
              ball (f p.1.1) p.1.2 := by
    intro n p
    -- Apply part (1) at the next smaller punctured radius and around the previous image center.
    obtain ⟨z, hz, ε', hε'pos, hε'lt, hsubset⟩ :=
      exists_closedBall_subset_image_inter_ball_of_essentialSingularity_lt
        hess (div_pow_two_pos hρ (n + 1)) (γ := f p.1.1) (ε := p.1.2) p.2
    exact ⟨⟨(z, ε'), hε'pos⟩, hz, hε'lt, hsubset⟩
  let u : ℕ → {p : ℂ × ℝ // 0 < p.2} :=
    Nat.rec ⟨(z₀, ε₀'), hε₀'pos⟩ fun n prev ↦ Classical.choose (hstep n prev)
  let z : ℕ → ℂ := fun n ↦ (u n).1.1
  let ε : ℕ → ℝ := fun n ↦ (u n).1.2
  have hz_mem : ∀ n, z n ∈ ball c (ρ / (2 : ℝ) ^ n) \ ({c} : Set ℂ) := by
    intro n
    cases n with
    | zero =>
        simpa [z, u] using hz₀
    | succ n =>
        rcases Classical.choose_spec (hstep n (u n)) with ⟨hz, _, _⟩
        simpa [z, u] using hz
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    simpa [ε] using (u n).2
  have hε_succ_lt : ∀ n, ε (n + 1) < ε n := by
    intro n
    rcases Classical.choose_spec (hstep n (u n)) with ⟨_, hlt, _⟩
    simpa [ε, u] using hlt
  have hrec :
      ∀ n,
        closedBall (f (z (n + 1))) (ε (n + 1)) ⊆
          f '' (ball c (ρ / (2 : ℝ) ^ (n + 1)) \ ({c} : Set ℂ)) ∩ ball (f (z n)) (ε n) := by
    intro n
    rcases Classical.choose_spec (hstep n (u n)) with ⟨_, _, hsubset⟩
    simpa [z, ε, u] using hsubset
  refine ⟨z, ε, hz_mem, hε_pos, ?_, strictAnti_nat_of_succ_lt hε_succ_lt, ?_, hrec⟩
  · -- The initial closed-ball radius was explicitly chosen below `ε₀`.
    simpa [ε, u] using hε₀'lt
  · -- The base closed-ball inclusion comes directly from the first application of part (1).
    simpa [z, ε, u] using hbase

/-- Exercise 16 (3): every neighborhood of `γ₀` contains a value `γ` assumed by `f` along a
sequence in the punctured disc converging to the essential singularity `c`. -/
theorem exists_fiber_sequence_tending_to_essentialSingularity
    (hess : HasEssentialSingularityAt f c)
    (hρ : 0 < ρ)
    {γ₀ : ℂ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    ∃ γ ∈ ball γ₀ ε₀, ∃ cseq : ℕ → ℂ,
      Tendsto cseq atTop (𝓝 c) ∧
      (∀ n, cseq n ∈ ball c ρ \ ({c} : Set ℂ)) ∧
      ∀ n, f (cseq n) = γ := by
  classical
  -- Build the nested closed image-discs from part (2).
  obtain ⟨z, ε, hz_mem, hε_pos, _, _, hbase, hrec⟩ :=
    exists_nested_closedBalls_in_shrinking_puncturedDiscImages hess hρ (γ₀ := γ₀) hε₀
  let K : ℕ → Set ℂ := fun n ↦ closedBall (f (z n)) (ε n)
  have hdecr : ∀ n, K (n + 1) ⊆ K n := by
    intro n w hw
    have hw_ball : w ∈ ball (f (z n)) (ε n) := (hrec n hw).2
    simpa [K] using le_of_lt hw_ball
  have hnonempty : ∀ n, (K n).Nonempty := by
    intro n
    refine ⟨f (z n), ?_⟩
    exact mem_closedBall_self (hε_pos n).le
  have hcompact : IsCompact (K 0) := by
    simpa [K] using isCompact_closedBall (f (z 0)) (ε 0)
  have hclosed : ∀ n, IsClosed (K n) := by
    intro n
    simpa [K] using isClosed_closedBall
  -- Cantor intersection yields one value lying in all the nested closed image-discs.
  rcases
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        K hdecr hnonempty hcompact hclosed with
    ⟨γ, hγ⟩
  have hγ_mem : ∀ n, γ ∈ K n := by
    simpa [Set.mem_iInter] using hγ
  have hγ_ball : γ ∈ ball γ₀ ε₀ := by
    exact (hbase (hγ_mem 0)).2
  have hcseq_exists :
      ∀ n, ∃ w ∈ ball c (ρ / (2 : ℝ) ^ (n + 1)) \ ({c} : Set ℂ), f w = γ := by
    intro n
    have himage : γ ∈ f '' (ball c (ρ / (2 : ℝ) ^ (n + 1)) \ ({c} : Set ℂ)) := by
      exact (hrec n (hγ_mem (n + 1))).1
    rcases himage with ⟨w, hw, hwγ⟩
    exact ⟨w, hw, hwγ⟩
  choose cseq hcseq_small_mem hcseq_eq using hcseq_exists
  have hcseq_mem : ∀ n, cseq n ∈ ball c ρ \ ({c} : Set ℂ) := by
    intro n
    refine ⟨lt_of_lt_of_le (hcseq_small_mem n).1 (div_pow_two_le_self hρ.le (n + 1)),
      (hcseq_small_mem n).2⟩
  have hpow :
      Tendsto (fun n : ℕ ↦ ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hpow_succ :
      Tendsto (fun n : ℕ ↦ ((1 / 2 : ℝ) ^ (n + 1))) atTop (𝓝 0) := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hpow.const_mul (1 / 2 : ℝ)
  have hbound_tendsto :
      Tendsto (fun n : ℕ ↦ ρ * ((1 / 2 : ℝ) ^ (n + 1))) atTop (𝓝 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow_succ.const_mul ρ
  have hcseq_tendsto : Tendsto cseq atTop (𝓝 c) := by
    -- The chosen preimages lie in punctured balls of radii `ρ / 2^(n+1)`.
    -- Those radii tend to `0`, so the preimages converge to `c`.
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) ?_ hbound_tendsto
    intro n
    have hdist_lt : dist (cseq n) c < ρ / (2 : ℝ) ^ (n + 1) := (hcseq_small_mem n).1
    have hradius :
        ρ / (2 : ℝ) ^ (n + 1) = ρ * ((1 / 2 : ℝ) ^ (n + 1)) := by
      simp [div_eq_mul_inv, inv_pow]
    exact le_of_lt (hradius ▸ hdist_lt)
  exact ⟨γ, hγ_ball, cseq, hcseq_tendsto, hcseq_mem, hcseq_eq⟩

/-- Exercise 16 (4): a holomorphic function with an essential singularity at `c` is not injective
on any punctured disc `0 < ‖z - c‖ < r` around `c`. -/
theorem not_injOn_on_any_smaller_puncturedDisc_of_essentialSingularity
    (hess : HasEssentialSingularityAt f c)
    {r : ℝ} (hr : 0 < r) :
    ¬ InjOn f (ball c r \ ({c} : Set ℂ)) := by
  intro hinj
  have hr_half : 0 < r / 2 := by
    linarith
  -- Apply part (3) inside the smaller punctured disc `0 < ‖z - c‖ < r / 2`.
  obtain ⟨γ, _, cseq, hcseq_tendsto, hcseq_mem, hcseq_eq⟩ :=
    exists_fiber_sequence_tending_to_essentialSingularity
      (ρ := r / 2) hess hr_half (γ₀ := 0) (ε₀ := 1) zero_lt_one
  have hsmall_subset : ball c (r / 2) \ ({c} : Set ℂ) ⊆ ball c r \ ({c} : Set ℂ) := by
    intro z hz
    have hz_lt : dist z c < r / 2 := by
      simpa [mem_ball] using hz.1
    have hr_le : r / 2 ≤ r := by
      linarith [hr]
    refine ⟨?_, hz.2⟩
    simpa [mem_ball] using lt_of_lt_of_le hz_lt hr_le
  have hinj_small : InjOn f (ball c (r / 2) \ ({c} : Set ℂ)) := by
    exact hinj.mono hsmall_subset
  have hconst : ∀ n, cseq n = cseq 0 := by
    intro n
    apply hinj_small (hcseq_mem n) (hcseq_mem 0)
    simp [hcseq_eq n, hcseq_eq 0]
  have hconst_tendsto : Tendsto cseq atTop (𝓝 (cseq 0)) := by
    -- Injectivity forces the whole sequence to be constant.
    have hcseq_const : cseq = fun _ : ℕ ↦ cseq 0 := by
      funext n
      exact hconst n
    rw [hcseq_const]
    exact tendsto_const_nhds
  have hc0_eq_c : cseq 0 = c := by
    exact tendsto_nhds_unique hconst_tendsto hcseq_tendsto
  have hc0_ne_c : cseq 0 ≠ c := by
    simpa using (hcseq_mem 0).2
  exact hc0_ne_c hc0_eq_c

end
