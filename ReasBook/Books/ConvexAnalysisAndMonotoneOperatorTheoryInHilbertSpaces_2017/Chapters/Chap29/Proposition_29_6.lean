import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2

open scoped InnerProductSpace Pointwise

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C D : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
variable (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "hD_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex

local notation "P_C" => P[C, hC_cheb]
local notation "P_D" => P[D, hD_cheb]

-- Semantic recall: `lean_leansearch` surfaced orthogonal-projection results for subspaces, but no
-- direct owner for the closedness and projector-splitting clauses at this set level. This file
-- therefore keeps clauses (1) and (3) source-facing, while clause (2) is the canonical owner
-- `Convex.add`.

/-- Helper for Proposition 29.6: differences of points of `C` remain orthogonal to every point of
`D`. -/
private lemma inner_sub_right_eq_zero_of_pairwise_orthogonal
    (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0)
    {c₁ c₂ d : H} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hd : d ∈ D) :
    ⟪c₁ - c₂, d⟫_ℝ = 0 := by
  -- Expand the difference and cancel both summands with the pointwise orthogonality hypothesis.
  rw [inner_sub_left, hCD_orth c₁ hc₁ d hd, hCD_orth c₂ hc₂ d hd]
  simp

/-- Helper for Proposition 29.6: orthogonal decompositions satisfy the textbook Pythagorean
identity for squared norms. -/
private lemma norm_add_sub_sq_eq_add_norm_sub_sq_of_pairwise_orthogonal
    (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0)
    {c₁ c₂ d₁ d₂ : H}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) :
    ‖(c₁ + d₁) - (c₂ + d₂)‖ ^ 2 = ‖c₁ - c₂‖ ^ 2 + ‖d₁ - d₂‖ ^ 2 := by
  -- The mixed inner product vanishes because each difference of `C`-points is orthogonal to each
  -- point of `D`.
  have horth : ⟪c₁ - c₂, d₁ - d₂⟫_ℝ = 0 := by
    rw [inner_sub_right]
    rw [inner_sub_right_eq_zero_of_pairwise_orthogonal (C := C) (D := D) hCD_orth hc₁ hc₂ hd₁]
    rw [inner_sub_right_eq_zero_of_pairwise_orthogonal (C := C) (D := D) hCD_orth hc₁ hc₂ hd₂]
    simp
  have hsplit : (c₁ + d₁) - (c₂ + d₂) = (c₁ - c₂) + (d₁ - d₂) := by
    abel_nf
  calc
    ‖(c₁ + d₁) - (c₂ + d₂)‖ ^ 2 = ‖(c₁ - c₂) + (d₁ - d₂)‖ ^ 2 := by
      rw [hsplit]
    _ = ‖c₁ - c₂‖ ^ 2 + ‖d₁ - d₂‖ ^ 2 := by
      simpa [horth] using norm_add_sq_real (c₁ - c₂) (d₁ - d₂)

/-- Helper for Proposition 29.6: the `C`-component distance is bounded by the distance of the
orthogonal sums. -/
private lemma dist_left_le_dist_add_of_pairwise_orthogonal
    (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0)
    {c₁ c₂ d₁ d₂ : H}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) :
    dist c₁ c₂ ≤ dist (c₁ + d₁) (c₂ + d₂) := by
  have hsplit :
      dist (c₁ + d₁) (c₂ + d₂) ^ 2 = dist c₁ c₂ ^ 2 + dist d₁ d₂ ^ 2 := by
    simpa [dist_eq_norm] using
      norm_add_sub_sq_eq_add_norm_sub_sq_of_pairwise_orthogonal
        (C := C) (D := D) hCD_orth hc₁ hc₂ hd₁ hd₂
  have hsq : dist c₁ c₂ ^ 2 ≤ dist (c₁ + d₁) (c₂ + d₂) ^ 2 := by
    have hle : dist c₁ c₂ ^ 2 ≤ dist c₁ c₂ ^ 2 + dist d₁ d₂ ^ 2 := by
      exact le_add_of_nonneg_right (sq_nonneg (dist d₁ d₂))
    simpa [hsplit] using hle
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).1 hsq

/-- Helper for Proposition 29.6: the `D`-component distance is bounded by the distance of the
orthogonal sums. -/
private lemma dist_right_le_dist_add_of_pairwise_orthogonal
    (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0)
    {c₁ c₂ d₁ d₂ : H}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) :
    dist d₁ d₂ ≤ dist (c₁ + d₁) (c₂ + d₂) := by
  have hsplit :
      dist (c₁ + d₁) (c₂ + d₂) ^ 2 = dist c₁ c₂ ^ 2 + dist d₁ d₂ ^ 2 := by
    simpa [dist_eq_norm] using
      norm_add_sub_sq_eq_add_norm_sub_sq_of_pairwise_orthogonal
        (C := C) (D := D) hCD_orth hc₁ hc₂ hd₁ hd₂
  have hsq : dist d₁ d₂ ^ 2 ≤ dist (c₁ + d₁) (c₂ + d₂) ^ 2 := by
    have hle : dist d₁ d₂ ^ 2 ≤ dist c₁ c₂ ^ 2 + dist d₁ d₂ ^ 2 := by
      exact le_add_of_nonneg_left (sq_nonneg (dist c₁ c₂))
    simpa [hsplit, add_comm, add_left_comm, add_assoc] using hle
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).1 hsq

/-- Proposition 29.6 (1): if `C` and `D` are closed subsets of a real Hilbert space and every
`c ∈ C` is orthogonal to every `d ∈ D`, then the Minkowski sum `C + D` is closed. -/
theorem isClosed_minkowski_sum_of_pairwise_orthogonal
    (hC_closed : IsClosed C) (hD_closed : IsClosed D)
    (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0) :
    IsClosed (C + D) := by
  refine (isSeqClosed_iff_isClosed).1 ?_
  intro u x hu hx
  classical
  have hdecomp : ∀ n, ∃ c d, c ∈ C ∧ d ∈ D ∧ u n = c + d := by
    intro n
    rcases Set.mem_add.1 (hu n) with ⟨c, hc, d, hd, hsum⟩
    exact ⟨c, d, hc, hd, hsum.symm⟩
  choose c d hc hd hud using hdecomp
  have hu_cauchy : CauchySeq u := hx.cauchySeq
  have hc_cauchy : CauchySeq c := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    rcases (Metric.cauchySeq_iff'.1 hu_cauchy) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hc_le :
        dist (c n) (c N) ≤ dist (u n) (u N) := by
      simpa [hud n, hud N] using
        dist_left_le_dist_add_of_pairwise_orthogonal
          (C := C) (D := D) hCD_orth (hc n) (hc N) (hd n) (hd N)
    exact lt_of_le_of_lt hc_le (hN n hn)
  have hd_cauchy : CauchySeq d := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    rcases (Metric.cauchySeq_iff'.1 hu_cauchy) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hd_le :
        dist (d n) (d N) ≤ dist (u n) (u N) := by
      simpa [hud n, hud N] using
        dist_right_le_dist_add_of_pairwise_orthogonal
          (C := C) (D := D) hCD_orth (hc n) (hc N) (hd n) (hd N)
    exact lt_of_le_of_lt hd_le (hN n hn)
  rcases cauchySeq_tendsto_of_isComplete hC_closed.isComplete (fun n ↦ hc n) hc_cauchy with
    ⟨cLim, hcLim, hc_tendsto⟩
  rcases cauchySeq_tendsto_of_isComplete hD_closed.isComplete (fun n ↦ hd n) hd_cauchy with
    ⟨dLim, hdLim, hd_tendsto⟩
  have hu_eq : u = fun n ↦ c n + d n := by
    funext n
    exact hud n
  have hsum_tendsto : Filter.Tendsto u Filter.atTop (nhds (cLim + dLim)) := by
    simpa [hu_eq] using hc_tendsto.add hd_tendsto
  have hx_eq : x = cLim + dLim := tendsto_nhds_unique hx hsum_tendsto
  exact Set.mem_add.2 ⟨cLim, hcLim, dLim, hdLim, hx_eq.symm⟩

/- Proposition 29.6 (2): the Minkowski sum of two convex subsets of a real Hilbert space is
convex, canonically formalized by `Convex.add`. -/
recall Convex.add

local notation "hCD_nonempty" =>
  Set.Nonempty.add hC_nonempty hD_nonempty

local notation "hCD_closed" =>
  isClosed_minkowski_sum_of_pairwise_orthogonal hC_closed hD_closed hCD_orth

local notation "hCD_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hCD_nonempty hCD_closed (hC_convex.add hD_convex)

/-- Helper for Proposition 29.6: every point of `C + D` satisfies the variational inequality at
`P_C z + P_D z`. -/
private lemma sum_projection_variational_inequality
    (hCD_orth : ∀ c ∈ C, ∀ d ∈ D, ⟪c, d⟫_ℝ = 0) (z u : H) (hu : u ∈ C + D) :
    ⟪u - (P_C z + P_D z), z - (P_C z + P_D z)⟫_ℝ ≤ 0 := by
  rcases Set.mem_add.1 hu with ⟨x, hx, y, hy, rfl⟩
  let p := P_C z
  let q := P_D z
  have hp_proj :
      p ∈ C ∧ ∀ c ∈ C, ⟪c - p, z - p⟫_ℝ ≤ 0 := by
    -- The Chapter 3 characterization packages both membership and the variational inequality.
    simpa [p] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex (x := z) (p := P_C z)).mp rfl
  have hq_proj :
      q ∈ D ∧ ∀ d ∈ D, ⟪d - q, z - q⟫_ℝ ≤ 0 := by
    -- The same characterization applies independently on `D`.
    simpa [q] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hD_nonempty hD_closed hD_convex (x := z) (p := P_D z)).mp rfl
  have hDC_orth : ∀ d ∈ D, ∀ c ∈ C, ⟪d, c⟫_ℝ = 0 := by
    -- Commuting the real inner product swaps the roles of `C` and `D`.
    intro d hd c hc
    simpa [real_inner_comm] using hCD_orth c hc d hd
  have hleft_mixed : ⟪x - p, q⟫_ℝ = 0 := by
    -- Differences of `C`-points remain orthogonal to every point of `D`.
    exact inner_sub_right_eq_zero_of_pairwise_orthogonal
      (C := C) (D := D) hCD_orth hx hp_proj.1 hq_proj.1
  have hright_mixed : ⟪y - q, p⟫_ℝ = 0 := by
    -- After commuting the orthogonality hypothesis, the same difference lemma applies on `D`.
    exact inner_sub_right_eq_zero_of_pairwise_orthogonal
      (C := D) (D := C) hDC_orth hy hq_proj.1 hp_proj.1
  have hleft_eq : ⟪x - p, z - (p + q)⟫_ℝ = ⟪x - p, z - p⟫_ℝ := by
    -- The `D`-component of the second factor disappears by orthogonality.
    have hsplit : z - (p + q) = (z - p) + (-q) := by
      abel_nf
    calc
      ⟪x - p, z - (p + q)⟫_ℝ = ⟪x - p, (z - p) + (-q)⟫_ℝ := by
        rw [hsplit]
      _ = ⟪x - p, z - p⟫_ℝ + ⟪x - p, -q⟫_ℝ := by
        rw [inner_add_right]
      _ = ⟪x - p, z - p⟫_ℝ := by
        simp [inner_neg_right, hleft_mixed]
  have hright_eq : ⟪y - q, z - (p + q)⟫_ℝ = ⟪y - q, z - q⟫_ℝ := by
    -- Symmetrically, the `C`-component disappears from the second factor.
    have hsplit : z - (p + q) = (-p) + (z - q) := by
      abel_nf
    calc
      ⟪y - q, z - (p + q)⟫_ℝ = ⟪y - q, (-p) + (z - q)⟫_ℝ := by
        rw [hsplit]
      _ = ⟪y - q, -p⟫_ℝ + ⟪y - q, z - q⟫_ℝ := by
        rw [inner_add_right]
      _ = ⟪y - q, z - q⟫_ℝ := by
        simp [inner_neg_right, hright_mixed]
  have hleft_nonpos : ⟪x - p, z - (p + q)⟫_ℝ ≤ 0 := by
    -- The projection inequality on `C` survives the previous orthogonality simplification.
    rw [hleft_eq]
    exact hp_proj.2 x hx
  have hright_nonpos : ⟪y - q, z - (p + q)⟫_ℝ ≤ 0 := by
    -- The same reduction on `D` yields the second sign control from the source proof.
    rw [hright_eq]
    exact hq_proj.2 y hy
  -- Route correction: keep the textbook decomposition into the `C` and `D` variational
  -- inequalities, rather than switching to a different projector identity.
  have hsplit : x + y - (p + q) = (x - p) + (y - q) := by
    abel_nf
  calc
    ⟪x + y - (p + q), z - (p + q)⟫_ℝ = ⟪(x - p) + (y - q), z - (p + q)⟫_ℝ := by
      rw [hsplit]
    _ = ⟪x - p, z - (p + q)⟫_ℝ + ⟪y - q, z - (p + q)⟫_ℝ := by
      rw [inner_add_left]
    _ ≤ 0 + 0 := add_le_add hleft_nonpos hright_nonpos
    _ = 0 := by
      simp

/-- Proposition 29.6 (3): if `C` and `D` are nonempty closed convex subsets of a real Hilbert
space and every `c ∈ C` is orthogonal to every `d ∈ D`, then the metric projector onto `C + D`
splits as the sum of the metric projectors onto `C` and `D`, i.e.
`P[C + D, hCD_cheb] = P[C, hC_cheb] + P[D, hD_cheb]`. -/
theorem projectionPoint_minkowski_sum_eq_add_of_nonempty_isClosed_convex_of_pairwise_orthogonal :
    P[C + D, hCD_cheb] = P_C + P_D := by
  funext z
  -- Characterize the projection onto `C + D` by the Chapter 3 variational inequality.
  symm
  refine
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      hCD_nonempty hCD_closed (hC_convex.add hD_convex)).2 ?_
  constructor
  · -- The candidate point already lies in the Minkowski sum.
    exact Set.mem_add.2 ⟨P_C z, projectionPoint_mem C hC_cheb z,
      P_D z, projectionPoint_mem D hD_cheb z, rfl⟩
  · -- The remaining source-faithful blocker is the mixed-term cancellation helper above.
    intro u hu
    exact sum_projection_variational_inequality
      hC_nonempty hC_closed hC_convex hD_nonempty hD_closed hD_convex hCD_orth z u hu

end
