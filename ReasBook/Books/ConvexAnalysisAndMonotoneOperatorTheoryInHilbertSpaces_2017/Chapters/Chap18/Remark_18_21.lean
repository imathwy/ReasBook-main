import Mathlib
import BauschkeLean.Chap12.Proposition_12_14
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap14.Definition_14_6
import BauschkeLean.Chap14.Proposition_14_7
import BauschkeLean.Chap16.Remark_16_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v} [Fintype I]

/- Source/core/bridge triage:
- `source-facing`: Remark 18.21 identifies the equal-weight specialization of the Chapter 18
  shifted conjugate with the Chapter 14 proximal average.
- `core/canonical`: the owner declarations here are the equal-weight specializations of the
  Chapter 18 weighted Moreau-average potential and its shifted conjugate, together with the
  Chapter 14 theta identities for the proximal average.
- `bridge/view`: the proof compares both sides through the same theta owner and then removes the
  common quadratic shift. -/

omit [CompleteSpace H] in
/-- Helper for Remark 18 21: subtracting the reciprocal quadratic kernel from the Fenchel
conjugate of a real-valued function still lands in `]-∞,+∞]`. -/
lemma conjugate_sub_invHalfSquaredNorm_gt_bot
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    ⊥ < f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u := by
  -- The Fenchel conjugate of a finite-valued function is never `-∞`, and the quadratic term is
  -- always finite.
  refine bot_lt_iff_ne_bot.mpr ?_
  have hconj : f.toEReal.asEReal∗ u ≠ ⊥ := by
    exact conjugate_ne_bot_of_effectiveDomain_nonempty (by simp) u
  have hkernel : (moreauQuadraticKernel γ u : EReal) ≠ ⊤ := by
    simpa using
      (EReal.coe_ne_top (((1 / (2 * (γ : ℝ))) * ‖u‖ ^ (2 : ℕ) : ℝ)))
  change f.toEReal.asEReal∗ u + -↑(moreauQuadraticKernel γ u) ≠ ⊥
  rw [EReal.add_ne_bot_iff]
  constructor
  · exact hconj
  · intro hneg
    exact hkernel (EReal.neg_eq_bot_iff.mp hneg)

/-- Helper for Remark 18 21: the Chapter 18 weighted Moreau-average potential is the finite
weighted sum of the unit Moreau envelopes of the Fenchel conjugates. -/
abbrev weightedConjugateMoreauAverage
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ) (x : H) : ℝ :=
  ∑ i, α i * (({}^[(1 : PosReal)] (gammaZeroConjugate (f i) (hf i)) x).toReal)

/-- Helper for Remark 18 21: the Chapter 18 shifted conjugate is the unit-parameter
`conjugateSubInvHalfSquaredNorm` of the weighted Moreau-average potential. -/
abbrev weightedMoreauAverageShiftedConjugate
    (f : I → H → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H)) (α : I → ℝ) :
    H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨(weightedConjugateMoreauAverage f hf α).toEReal.asEReal∗ u -
        moreauQuadraticKernel (1 : PosReal) u,
      conjugate_sub_invHalfSquaredNorm_gt_bot
        (weightedConjugateMoreauAverage f hf α) (1 : PosReal) u⟩

/-- Helper for Remark 18 21: the scalar `2 : ℝ` is nonzero. -/
lemma two_ne_zero_real : (2 : ℝ) ≠ 0 := by
  -- The doubling map is invertible because `2` is a nonzero scalar.
  norm_num

/-- Helper for Remark 18 21: multiplication by `2` is a continuous linear equivalence. -/
noncomputable abbrev double_scale_equiv : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero_real)

/-- Helper for Remark 18 21: adding a finite real constant commutes with an indexed infimum in
`EReal`. -/
lemma iInf_add_real_const (Φ : H → EReal) (c : ℝ) :
    (⨅ y : H, Φ y + ((c : ℝ) : EReal)) = (⨅ y : H, Φ y) + ((c : ℝ) : EReal) := by
  -- Bound the shifted infimum from above termwise, then subtract the shift to recover the reverse
  -- inequality.
  have hright :
      (⨅ y : H, Φ y) + ((c : ℝ) : EReal) ≤ (⨅ y : H, Φ y + ((c : ℝ) : EReal)) := by
    refine le_iInf fun y ↦ ?_
    exact add_le_add (iInf_le Φ y) le_rfl
  have hleft_sub :
      (⨅ y : H, Φ y + ((c : ℝ) : EReal)) - ((c : ℝ) : EReal) ≤ (⨅ y : H, Φ y) := by
    refine le_iInf fun y ↦ ?_
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).2
      (iInf_le (fun y : H ↦ Φ y + ((c : ℝ) : EReal)) y)
  have hleft :
      (⨅ y : H, Φ y + ((c : ℝ) : EReal)) ≤ (⨅ y : H, Φ y) + ((c : ℝ) : EReal) := by
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).1 hleft_sub
  exact le_antisymm hleft hright

/-- Helper for Remark 18 21: the unit quadratic kernel belongs to `Γ₀(H)`. -/
lemma halfSquaredNorm_mem_gammaZero :
    (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
  let q : H → ℝ := fun x : H ↦ (‖x‖ ^ 2) / 2
  have hq_eq :
      q.toEReal = (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    -- The quadratic owner is exactly the unit Moreau kernel.
    funext x
    simp [q, halfSquaredNorm, moreauQuadraticKernel, div_eq_mul_inv, mul_comm]
  rw [← hq_eq]
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha0 ha1
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖ ^ 2) :=
      (convexOn_univ_norm :
          _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖)).pow
        (fun z _ ↦ norm_nonneg z) 2
    have hquad :
        ‖a • x + (1 - a) • y‖ ^ 2 / 2 ≤
          a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) := by
      have hquad' :
          ‖a • x + (1 - a) • y‖ ^ 2 ≤
            a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 := by
        simpa [smul_eq_mul] using
          hnorm_sq.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
      nlinarith
    change (((‖a • x + (1 - a) • y‖ ^ 2) / 2 : ℝ) : EReal) ≤
      ((a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) : ℝ) : EReal)
    exact_mod_cast hquad
  · have hcont : Continuous q := by
      simpa [q, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_norm.pow 2).const_mul (1 / 2 : ℝ)
    simpa [q] using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Remark 18 21: the shifted summand `f + q` belongs to `Γ₀(H)`. -/
lemma pointwiseAdd_halfSquaredNorm_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    f + halfSquaredNorm ∈ Γ₀(H) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  have hhalf_dom : x ∈ effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top (((‖x‖ ^ 2) / 2 : ℝ))
  -- The sum stays in `Γ₀(H)` because the two effective domains meet at `x`.
  exact pointwiseAdd_mem_gammaZero
    f halfSquaredNorm hf halfSquaredNorm_mem_gammaZero ⟨x, hx, hhalf_dom⟩

/-- Helper for Remark 18 21: every `Γ₀(H)` function admits a global affine lower bound in the
norm. -/
lemma exists_linear_lower_bound_of_mem_gammaZero_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)) := by
  -- Reuse the normed-space lower-bound bridge already provided by Chapter 14.
  exact exists_linear_lower_bound_of_mem_gammaZero_on_normed_space hf

/-- Helper for Remark 18 21: a global linear lower bound yields a tail lower bound after
division by the norm. -/
lemma linear_lower_bound_div_norm_local
    {f : H → Set.Ioi (⊥ : EReal)} {R C : ℝ}
    (hbound : ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    {x : H} (hnorm : (1 : ℝ) ≤ ‖x‖) :
    ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ := by
  have hnorm_pos_real : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact EReal.coe_pos.2 hnorm_pos_real
  have hreal :
      (-(R + |C|)) * ‖x‖ ≤ -R * ‖x‖ - C := by
    have hC_le : C ≤ ‖x‖ * |C| := by
      have habs_le : |C| ≤ ‖x‖ * |C| := by
        simpa [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hnorm (abs_nonneg C)
      exact le_trans (le_abs_self C) habs_le
    have hC_scaled : -(‖x‖ * |C|) ≤ -C := by
      simpa [mul_comm] using neg_le_neg hC_le
    calc
      (-(R + |C|)) * ‖x‖ = -(R * ‖x‖) + -(‖x‖ * |C|) := by ring
      _ ≤ -R * ‖x‖ - C := by linarith
  have hcast :
      ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hmul_le :
      ((((-(R + |C|) : ℝ) : EReal) * ‖x‖)) ≤ (f x : EReal) := by
    calc
      (((-(R + |C|) : ℝ) : EReal) * ‖x‖)
          = ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) := by
              rw [← EReal.coe_mul]
      _ ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := hcast
      _ ≤ (f x : EReal) := hbound x
  -- Divide the affine lower bound by the positive norm.
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

/-- Helper for Remark 18 21: adding a summand with a linear minorant to a supercoercive summand
preserves supercoercivity. -/
lemma pointwiseAdd_supercoercive_of_linear_lower_bound_local
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hbound : ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    (hg_super : Supercoercive g.asEReal) :
    Supercoercive (f + g).asEReal := by
  rcases hbound with ⟨R, C, hbound⟩
  rw [Supercoercive, EReal.tendsto_nhds_top_iff_real] at hg_super ⊢
  intro ξ
  have hnorm_tail : ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖ := by
    simpa using
      (eventually_cobounded_le_norm (1 : ℝ) :
        ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖)
  have hg_tail :
      ∀ᶠ x in Bornology.cobounded H, ((ξ + (R + |C|) : ℝ) : EReal) < g.asEReal x / ‖x‖ :=
    hg_super (ξ + (R + |C|))
  filter_upwards [hnorm_tail, hg_tail] with x hnorm hxg
  have hf_tail :
      ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ :=
    linear_lower_bound_div_norm_local hbound hnorm
  have hsum :
      (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) = (ξ : EReal) := by
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  have hquot_split :
      ((f + g).asEReal x) / ‖x‖ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by
    have hnorm_nonneg : (0 : EReal) ≤ (‖x‖ : EReal) := by
      exact_mod_cast norm_nonneg x
    rw [Function.asEReal_apply]
    simpa using
      (EReal.add_div_of_nonneg_right
        (a := (f x : EReal)) (b := (g x : EReal)) (c := (‖x‖ : EReal)) hnorm_nonneg)
  have hadd :
      (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) <
        (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := by
    have hright_bot : (f x : EReal) / ‖x‖ ≠ ⊥ := by
      exact ne_bot_of_le_ne_bot (by simp) hf_tail
    exact EReal.add_lt_add_of_lt_of_le' hxg hf_tail hright_bot (by
      intro _ hz
      exact (EReal.coe_ne_top _ hz).elim)
  calc
    (ξ : EReal)
        = (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) := hsum.symm
    _ < (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := hadd
    _ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by rw [add_comm]
    _ = ((f + g).asEReal x) / ‖x‖ := hquot_split.symm

/-- Helper for Remark 18 21: the unit quadratic kernel is supercoercive. -/
lemma halfSquaredNorm_supercoercive_local :
    Supercoercive ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal) := by
  let pTwo : Set.Ici (1 : ℝ) := ⟨(2 : ℝ), by norm_num⟩
  have hpTwo : (1 : ℝ) < pTwo := by
    change (1 : ℝ) < (2 : ℝ)
    norm_num
  have hkernel_eq :
      normPowerKernel (H := H) pTwo (1 : PosReal) = halfSquaredNorm := by
    ext x
    rw [normPowerKernel_apply, halfSquaredNorm_apply]
    congr 1
    norm_num [Real.rpow_natCast]
  simpa [hkernel_eq] using
    (supercoercive_normPowerKernel (H := H) pTwo (1 : PosReal) hpTwo :
      Supercoercive ((normPowerKernel (H := H) pTwo (1 : PosReal) : H → Set.Ioi (⊥ : EReal)).asEReal))

/-- Helper for Remark 18 21: the shifted summand `f + q` is supercoercive. -/
lemma pointwiseAdd_halfSquaredNorm_supercoercive
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Supercoercive (f + halfSquaredNorm).asEReal := by
  rcases exists_linear_lower_bound_of_mem_gammaZero_local hf with ⟨R, C, _, hbound⟩
  -- Combine the affine lower bound for `f` with the supercoercivity of the quadratic kernel.
  exact pointwiseAdd_supercoercive_of_linear_lower_bound_local
    ⟨R, C, hbound⟩ halfSquaredNorm_supercoercive_local

/-- Helper for Remark 18 21: the infimal-convolution core `(f + q) □ (g + q)` is proper and
belongs to `Γ(H)`. -/
lemma proximal_average_theta_core_isProper_and_mem_gamma
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper ((f + halfSquaredNorm) □ (g + halfSquaredNorm)) ∧
      ((f + halfSquaredNorm) □ (g + halfSquaredNorm)) ∈ gamma H := by
  have hf_shift : f + halfSquaredNorm ∈ Γ₀(H) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero f hf
  have hg_shift : g + halfSquaredNorm ∈ Γ₀(H) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero g hg
  have hsuper : Supercoercive (f + halfSquaredNorm).asEReal :=
    pointwiseAdd_halfSquaredNorm_supercoercive f hf
  simpa using
    (isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
      (f := f + halfSquaredNorm)
      (g := g + halfSquaredNorm)
      (hf := hf_shift)
      (hg := hg_shift)
      (hcase := Or.inl hsuper))

/-- Helper for Remark 18 21: the canonical `Γ₀(H)` packaging of `(f + q) □ (g + q)`. -/
noncomputable abbrev proximal_average_theta_core
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi
    ((f + halfSquaredNorm) □ (g + halfSquaredNorm))
    (proximal_average_theta_core_isProper_and_mem_gamma f g hf hg).1

/-- Helper for Remark 18 21: the source theta owner is the half-scaled core evaluated at `2 • x`.
-/
noncomputable abbrev proximal_average_theta
    (f g : H → Set.Ioi (⊥ : EReal)) (_hf : f ∈ Γ₀(H)) (_hg : g ∈ Γ₀(H)) :
    H → EReal :=
  fun x : H ↦
    ((1 / 2 : ℝ) : EReal) *
      (((f + halfSquaredNorm) □ (g + halfSquaredNorm)) ((2 : ℝ) • x))

/-- Helper for Remark 18 21: packaging `Θ(f, g)` as a `Γ₀(H)` function. -/
noncomputable abbrev proximal_average_theta_packaged
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  ((((⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal) • proximal_average_theta_core f g hf hg) ∘
    double_scale_equiv))

/-- Helper for Remark 18 21: coercing the packaged theta owner back to `EReal` recovers
`Θ(f, g)`. -/
@[simp] lemma proximal_average_theta_packaged_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (x : H) :
    (proximal_average_theta_packaged f g hf hg x : EReal) = proximal_average_theta f g hf hg x := by
  -- Unpack the positive scaling and precomposition by the doubling equivalence.
  simp [proximal_average_theta_packaged, proximal_average_theta, proximal_average_theta_core,
    Function.comp]

/-- Helper for Remark 18 21: the source-faithful theta owner belongs to `Γ₀(H)`. -/
lemma proximal_average_theta_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    proximal_average_theta_packaged f g hf hg ∈ Γ₀(H) := by
  have hcore :
      proximal_average_theta_core f g hf hg ∈ Γ₀(H) := by
    exact properIoi_mem_gammaZero_of_mem_gamma
      (proximal_average_theta_core_isProper_and_mem_gamma f g hf hg).1
      (proximal_average_theta_core_isProper_and_mem_gamma f g hf hg).2
  have hscaled :
      (((⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal) • proximal_average_theta_core f g hf hg)) ∈ Γ₀(H) := by
    simpa using
      (smul_mem_gammaZero
        (proximal_average_theta_core f g hf hg)
        hcore
        (⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal))
  have hdom :
      (Set.range (double_scale_equiv.toContinuousLinearMap) ∩
        effectiveDomain
          (((⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal) • proximal_average_theta_core f g hf hg))).Nonempty := by
    rcases hscaled.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_, hx⟩
    refine ⟨(double_scale_equiv.symm x), ?_⟩
    simp
  simpa [proximal_average_theta_packaged] using
    (comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty
      (((⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal) • proximal_average_theta_core f g hf hg))
      hscaled
      double_scale_equiv.toContinuousLinearMap
      hdom)

/-- Helper for Remark 18 21: the midpoint quadratic identity underlying `Θ(f, g)`. -/
lemma doubled_shift_quadratic_identity
    (x y : H) :
    ‖y‖ ^ 2 / 2 + ‖(2 : ℝ) • x - y‖ ^ 2 / 2 = ‖x - y‖ ^ 2 + ‖x‖ ^ 2 := by
  have hy : y = x + (y - x) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hy]
  have hshift : (2 : ℝ) • x - (x + (y - x)) = x - (y - x) := by
    simp [two_smul, sub_eq_add_neg, add_assoc]
  rw [hshift]
  have hright : x - (x + (y - x)) = -(y - x) := by
    simp [sub_eq_add_neg, add_assoc]
  rw [hright, norm_neg]
  have hadd : ‖x + (y - x)‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    simpa using norm_add_sq_real x (y - x)
  have hsub : ‖x - (y - x)‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    simpa using norm_sub_sq_real x (y - x)
  nlinarith

/-- Helper for Remark 18 21: evaluating `Θ(f, g)` rewrites the shifted infimal-convolution
integrand into the midpoint form. -/
lemma proximal_average_theta_pointwise_normalization
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (x : H) :
    proximal_average_theta f g hf hg x =
      ((1 / 2 : ℝ) : EReal) *
        (⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          (((‖x - y‖ ^ 2 + ‖x‖ ^ 2 : ℝ) : EReal))) := by
  -- Expand the shifted infimal convolution at `2 • x` and isolate the two quadratic summands.
  rw [proximal_average_theta, infimalConvolution_apply]
  congr 1
  refine iInf_congr fun y ↦ ?_
  have hleft :
      ((pointwiseAdd f halfSquaredNorm y : Set.Ioi (⊥ : EReal)) : EReal) =
        (f y : EReal) + ((((‖y‖ ^ 2) / 2 : ℝ) : EReal)) := by
    simpa [halfSquaredNorm_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      pointwiseAdd_apply f halfSquaredNorm y
  have hright :
      ((pointwiseAdd g halfSquaredNorm ((2 : ℝ) • x - y) : Set.Ioi (⊥ : EReal)) : EReal) =
        (g ((2 : ℝ) • x - y) : EReal) +
          ((((‖(2 : ℝ) • x - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
    simpa [halfSquaredNorm_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      pointwiseAdd_apply g halfSquaredNorm ((2 : ℝ) • x - y)
  have hquad :
      ((((‖y‖ ^ 2) / 2 : ℝ) : EReal) +
          ((((‖(2 : ℝ) • x - y‖ ^ 2) / 2 : ℝ) : EReal))) =
        (((‖x - y‖ ^ 2 + ‖x‖ ^ 2 : ℝ) : EReal)) := by
    rw [← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ (t : EReal))
      (doubled_shift_quadratic_identity (x := x) (y := y))
  calc
    ((pointwiseAdd f halfSquaredNorm y : Set.Ioi (⊥ : EReal)) : EReal) +
        ((pointwiseAdd g halfSquaredNorm ((2 : ℝ) • x - y) : Set.Ioi (⊥ : EReal)) : EReal) =
        (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          ((((‖y‖ ^ 2) / 2 : ℝ) : EReal) +
            ((((‖(2 : ℝ) • x - y‖ ^ 2) / 2 : ℝ) : EReal))) := by
          rw [hleft, hright]
          simp [add_assoc, add_left_comm, add_comm]
    _ = (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          (((‖x - y‖ ^ 2 + ‖x‖ ^ 2 : ℝ) : EReal)) := by
          rw [hquad]

/-- Helper for Remark 18 21: multiplying by `1 / 2` distributes across a finite real shift in
`EReal`. -/
lemma ereal_one_half_mul_add_real_const
    (a : EReal) (c : ℝ) :
    ((1 / 2 : ℝ) : EReal) * (a + ((c : ℝ) : EReal)) =
      ((1 / 2 : ℝ) : EReal) * a + (((c / 2 : ℝ) : EReal)) := by
  have hhalf_nonneg : (0 : EReal) ≤ (((1 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
  calc
    ((1 / 2 : ℝ) : EReal) * (a + ((c : ℝ) : EReal)) =
        ((1 / 2 : ℝ) : EReal) * a + ((1 / 2 : ℝ) : EReal) * ((c : ℝ) : EReal) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg (EReal.coe_ne_top (1 / 2 : ℝ))]
    _ = ((1 / 2 : ℝ) : EReal) * a + (((c / 2 : ℝ) : EReal)) := by
          congr 1
          rw [← EReal.coe_mul]
          norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Remark 18 21: `Θ(f, g)` is the proximal average plus the quadratic kernel `q`. -/
lemma proximal_average_theta_eq_add_halfSquaredNorm
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    proximal_average_theta f g hf hg =
      fun x : H ↦ pav(f, g) x + halfSquaredNorm.asEReal x := by
  funext x
  -- Normalize `Θ(f, g)(x)` to the `pav(f, g)(x)` integrand plus one finite quadratic shift.
  calc
    proximal_average_theta f g hf hg x =
        ((1 / 2 : ℝ) : EReal) *
          (⨅ y : H, ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
              (((‖x - y‖ ^ 2 : ℝ) : EReal))) + ((‖x‖ ^ 2 : ℝ) : EReal)) := by
            rw [proximal_average_theta_pointwise_normalization f g hf hg]
            congr 1
            refine iInf_congr fun y ↦ ?_
            rw [EReal.coe_add]
            ac_rfl
    _ = ((1 / 2 : ℝ) : EReal) *
          ((⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
              (((‖x - y‖ ^ 2 : ℝ) : EReal))) + ((‖x‖ ^ 2 : ℝ) : EReal)) := by
            rw [iInf_add_real_const
              (Φ := fun y : H ↦ (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
                (((‖x - y‖ ^ 2 : ℝ) : EReal)))
              (c := ‖x‖ ^ 2)]
    _ = ((1 / 2 : ℝ) : EReal) *
          (⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
            (((‖x - y‖ ^ 2 : ℝ) : EReal))) + (((‖x‖ ^ 2) / 2 : ℝ) : EReal) := by
            rw [ereal_one_half_mul_add_real_const]
    _ = pav(f, g) x + (((‖x‖ ^ 2) / 2 : ℝ) : EReal) := by
          rw [proximalAverage_apply]
    _ = pav(f, g) x + halfSquaredNorm.asEReal x := by
          rw [Function.asEReal_apply, halfSquaredNorm_apply]

/-- Helper for Remark 18 21: the normalized form `pav(f, g) = Θ(f, g) - q`. -/
lemma proximal_average_eq_theta_sub_halfSquaredNorm
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g) =
      fun x : H ↦ proximal_average_theta f g hf hg x - halfSquaredNorm.asEReal x := by
  funext x
  rw [congrFun (proximal_average_theta_eq_add_halfSquaredNorm f g hf hg) x]
  rw [Function.asEReal_apply, halfSquaredNorm_apply]
  simpa using
    (EReal.add_sub_cancel_right (a := pav(f, g) x) (b := (‖x‖ ^ 2) / 2)).symm

/-- Helper for Remark 18 21: conjugating `f + q` yields the unit Moreau envelope of `f*`. -/
lemma conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (f + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (gammaZeroConjugate f hf) := by
  have hconj : gammaZeroConjugate f hf ∈ Γ₀(H) :=
    gammaZeroConjugate_mem_gammaZero hf
  have hmoreau :
      IsProper ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) ∧
        ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) ∈ gamma H := by
    have hkernel_eq : (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) = moreauQuadraticKernel (1 : PosReal) := by
      ext x
      simp [halfSquaredNorm_apply, moreauQuadraticKernel_apply]
    have hraw :
        IsProper (halfSquaredNorm □ gammaZeroConjugate f hf) ∧
          (halfSquaredNorm □ gammaZeroConjugate f hf) ∈ gamma H := by
      exact
        isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
          (f := halfSquaredNorm)
          (g := gammaZeroConjugate f hf)
          (hf := halfSquaredNorm_mem_gammaZero)
          (hg := hconj)
          (hcase := Or.inl halfSquaredNorm_supercoercive_local)
    have hmoreau_eq :
        ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) =
          (halfSquaredNorm □ gammaZeroConjugate f hf) := by
      funext x
      rw [hkernel_eq, moreauEnvelope_apply, infimalConvolution_comm, infimalConvolution_apply]
      refine iInf_congr fun y ↦ ?_
      change ((gammaZeroConjugate f hf y : EReal) +
        ((((1 / (2 * (((1 : PosReal) : ℝ)))) * ‖x - y‖ ^ 2 : ℝ) : EReal))) =
        ((⨆ x, (((⟪x, y⟫_ℝ : ℝ) : EReal) - (f x : EReal))) +
          (moreauQuadraticKernel (1 : PosReal) (x - y) : EReal))
      rw [gammaZeroConjugate_apply]
      simp [moreauQuadraticKernel_apply]
    simpa [hmoreau_eq] using hraw
  have hmoreau_biconj :
      ({}^[(1 : PosReal)] (gammaZeroConjugate f hf))∗∗ =
        {}^[(1 : PosReal)] (gammaZeroConjugate f hf) :=
    (mem_gamma_iff_eq_biconjugate_of_is_proper hmoreau.1).mp hmoreau.2
  have hconj_moreau :
      ({}^[(1 : PosReal)] (gammaZeroConjugate f hf))∗ =
        f.asEReal + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
    calc
      ({}^[(1 : PosReal)] (gammaZeroConjugate f hf))∗ =
          (gammaZeroConjugate f hf).asEReal∗ +
            (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
              simpa using
                (conjugate_moreauEnvelope_eq (f := gammaZeroConjugate f hf) (γ := (1 : PosReal)))
      _ = f.asEReal∗∗ + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
            rfl
      _ = f.asEReal + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
            rw [biconjugate_eq_of_mem_gammaZero hf]
  calc
    (f + halfSquaredNorm).asEReal∗ =
        (f.asEReal + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal))∗ := by
          have hadd :
              (f + halfSquaredNorm).asEReal =
                f.asEReal + (((1 : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
            funext x
            simp [Function.asEReal_apply]
          rw [hadd]
    _ = (({}^[(1 : PosReal)] (gammaZeroConjugate f hf))∗)∗ := by
          rw [hconj_moreau]
    _ = {}^[(1 : PosReal)] (gammaZeroConjugate f hf) := by
          simpa using hmoreau_biconj

/-- Helper for Remark 18 21: the unit Moreau envelope of a `Γ₀(H)` function never attains
either `+∞` or `-∞`. -/
lemma unitMoreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    ({}^[(1 : PosReal)] f) x ≠ ⊤ ∧ ({}^[(1 : PosReal)] f) x ≠ ⊥ := by
  have hvalue :
      ({}^[(1 : PosReal)] f) x =
        (f (Prox[(1 : PosReal), f, hf] x) : EReal) +
          ((((‖x - Prox[(1 : PosReal), f, hf] x‖ ^ 2) / (2 * (((1 : PosReal) : ℝ))) : ℝ) : EReal)) := by
    exact
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := f) (hf := hf) (γ := (1 : PosReal)) (x := x)
  constructor
  · rcases hf.2.nonempty with ⟨y, hy⟩
    have hupper :
        ({}^[(1 : PosReal)] f) x ≤
          (f y : EReal) +
            ((((1 / (2 * (((1 : PosReal) : ℝ)))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
      rw [moreauEnvelope_apply]
      exact iInf_le _ y
    exact ne_of_lt (lt_of_le_of_lt hupper <| by
      exact EReal.add_lt_top (ne_of_lt (mem_effectiveDomain_iff.mp hy)) (EReal.coe_ne_top _))
  · rw [hvalue]
    exact EReal.add_ne_bot_iff.2 ⟨ne_of_gt (f (Prox[(1 : PosReal), f, hf] x)).2, EReal.coe_ne_bot _⟩

/-- Helper for Remark 18 21: the conjugate of `Θ(f, g)` is the half-sum of the unit Moreau
envelopes of the conjugates of `f` and `g`. -/
lemma conjugate_proximal_average_theta_eq_half_sum_shifted_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (proximal_average_theta f g hf hg)∗ =
      fun u : H ↦
        ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) u +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) u := by
  let α : Set.Ioi (0 : ℝ) := ⟨(1 / 2 : ℝ), by simpa using one_half_pos⟩
  have hcore_conj :
      (proximal_average_theta_core f g hf hg).asEReal∗ =
        (f + halfSquaredNorm).asEReal∗ + (g + halfSquaredNorm).asEReal∗ := by
    have hcore_eq :
        (proximal_average_theta_core f g hf hg).asEReal =
          ((f + halfSquaredNorm) □ (g + halfSquaredNorm)) := rfl
    rw [hcore_eq]
    exact conjugate_infimalConvolution_eq (f + halfSquaredNorm) (g + halfSquaredNorm)
  have hf_conj :
      (f + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (gammaZeroConjugate f hf) :=
    conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate f hf
  have hg_conj :
      (g + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (gammaZeroConjugate g hg) :=
    conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate g hg
  have hhalf_nonneg : (0 : EReal) ≤ ((α : ℝ) : EReal) := by
    exact_mod_cast (show (0 : ℝ) ≤ (α : ℝ) by exact le_of_lt α.2)
  have htheta_eq :
      proximal_average_theta f g hf hg =
        fun x : H ↦
          ((α : ℝ) : EReal) *
            (proximal_average_theta_core f g hf hg).asEReal (((α : ℝ)⁻¹) • x) := by
    funext x
    simp [proximal_average_theta, α, proximal_average_theta_core, Function.asEReal_apply]
  ext u
  calc
    (proximal_average_theta f g hf hg)∗ u =
        ((α : ℝ) : EReal) * ((proximal_average_theta_core f g hf hg).asEReal∗ u) := by
          rw [htheta_eq]
          simpa using
            congrFun
              (conjugate_pos_smul_precompose_inv_smul
                (f := (proximal_average_theta_core f g hf hg).asEReal)
                α)
              u
    _ = ((α : ℝ) : EReal) *
          (((f + halfSquaredNorm).asEReal∗ + (g + halfSquaredNorm).asEReal∗) u) := by
            rw [hcore_conj]
    _ = ((α : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) u +
          ((α : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) u := by
            rw [Pi.add_apply, hf_conj, hg_conj,
              EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg (EReal.coe_ne_top (α : ℝ))]
    _ = ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) u +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) u := by
            simp [α]

/-- Helper for Remark 18 21: coercing the equal-weight Chapter 18 potential to `EReal` recovers
the half-sum of the unit Moreau envelopes of the Fenchel conjugates. -/
lemma equal_weight_weightedConjugateMoreauAverage_asEReal
    (f₁ f₂ : H → Set.Ioi (⊥ : EReal)) (hf₁ : f₁ ∈ Γ₀(H)) (hf₂ : f₂ ∈ Γ₀(H)) :
    (weightedConjugateMoreauAverage
      ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
      ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).toEReal.asEReal =
      fun x : H ↦
        (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f₁ hf₁) x)) +
          (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f₂ hf₂) x)) := by
  ext x
  have h₁ :=
    unitMoreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
      (gammaZeroConjugate f₁ hf₁) (gammaZeroConjugate_mem_gammaZero hf₁) x
  have h₂ :=
    unitMoreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
      (gammaZeroConjugate f₂ hf₂) (gammaZeroConjugate_mem_gammaZero hf₂) x
  rcases h₁ with ⟨h₁_top, h₁_bot⟩
  rcases h₂ with ⟨h₂_top, h₂_bot⟩
  -- Expand the `Fin 2` sum and convert the finite unit-envelope values back from `toReal`.
  simp [weightedConjugateMoreauAverage, Fin.sum_univ_two, Function.asEReal,
    Function.toEReal_apply, EReal.coe_add, EReal.coe_mul, EReal.coe_toReal h₁_top h₁_bot,
    EReal.coe_toReal h₂_top h₂_bot]

/-- Helper for Remark 18 21: the packaged theta owner is exactly the unbundled theta function
after coercion to `EReal`. -/
lemma proximal_average_theta_packaged_asEReal
    (f₁ f₂ : H → Set.Ioi (⊥ : EReal)) (hf₁ : f₁ ∈ Γ₀(H)) (hf₂ : f₂ ∈ Γ₀(H)) :
    (proximal_average_theta_packaged f₁ f₂ hf₁ hf₂).asEReal =
      proximal_average_theta f₁ f₂ hf₁ hf₂ := by
  funext x
  simpa [Function.asEReal_apply] using
    proximal_average_theta_packaged_apply f₁ f₂ hf₁ hf₂ x

/-- Remark 18 21: the equal-weight specialization of `(18.40)`, viewed in the canonical
`]-∞, +∞]`-valued packaging, is exactly the proximal average `pav(f₁, f₂)`. -/
theorem equalWeight_shiftedConjugate_eq_proximalAverage
    (f₁ f₂ : H → Set.Ioi (⊥ : EReal)) (hf₁ : f₁ ∈ Γ₀(H)) (hf₂ : f₂ ∈ Γ₀(H)) :
    weightedMoreauAverageShiftedConjugate
        ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
        ![(1 / 2 : ℝ), (1 / 2 : ℝ)] =
      properIoi (pav(f₁, f₂)) (isProper_proximalAverage f₁ f₂ hf₁ hf₂) := by
  let θpack : H → Set.Ioi (⊥ : EReal) := proximal_average_theta_packaged f₁ f₂ hf₁ hf₂
  have hθpack : θpack ∈ Γ₀(H) := by
    simpa [θpack] using proximal_average_theta_mem_gammaZero f₁ f₂ hf₁ hf₂
  have hθpack_apply :
      θpack.asEReal = proximal_average_theta f₁ f₂ hf₁ hf₂ := by
    simpa [θpack] using proximal_average_theta_packaged_asEReal f₁ f₂ hf₁ hf₂
  have hweighted :
      (weightedConjugateMoreauAverage
        ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
        ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).toEReal.asEReal =
        (proximal_average_theta f₁ f₂ hf₁ hf₂)∗ := by
    calc
      (weightedConjugateMoreauAverage
        ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
        ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).toEReal.asEReal =
          fun x : H ↦
            (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f₁ hf₁) x)) +
              (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f₂ hf₂) x)) := by
            exact equal_weight_weightedConjugateMoreauAverage_asEReal f₁ f₂ hf₁ hf₂
      _ = (proximal_average_theta f₁ f₂ hf₁ hf₂)∗ := by
            symm
            exact conjugate_proximal_average_theta_eq_half_sum_shifted_conjugates
              f₁ f₂ hf₁ hf₂
  have hweighted_conj :
      ((weightedConjugateMoreauAverage
        ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
        ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).toEReal.asEReal)∗ =
        (proximal_average_theta f₁ f₂ hf₁ hf₂)∗∗ :=
    congrArg (fun φ : H → EReal ↦ φ∗) hweighted
  have htheta_biconj :
      (proximal_average_theta f₁ f₂ hf₁ hf₂)∗∗ =
        proximal_average_theta f₁ f₂ hf₁ hf₂ := by
    calc
      (proximal_average_theta f₁ f₂ hf₁ hf₂)∗∗ = θpack.asEReal∗∗ := by
        rw [hθpack_apply]
      _ = θpack.asEReal := by
            simpa using biconjugate_eq_of_mem_gammaZero hθpack
      _ = proximal_average_theta f₁ f₂ hf₁ hf₂ := hθpack_apply
  funext x
  apply Subtype.ext
  -- Identify both sides with the same theta owner and then remove the common quadratic shift.
  calc
    (weightedMoreauAverageShiftedConjugate
      ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
      ![(1 / 2 : ℝ), (1 / 2 : ℝ)] x : EReal) =
        (((weightedConjugateMoreauAverage
          ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
          ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).toEReal.asEReal)∗ x) - halfSquaredNorm.asEReal x := by
            simp
    _ = (proximal_average_theta f₁ f₂ hf₁ hf₂) x - halfSquaredNorm.asEReal x := by
          calc
            (((weightedConjugateMoreauAverage
              ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
              ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).toEReal.asEReal)∗ x) - halfSquaredNorm.asEReal x =
                ((proximal_average_theta f₁ f₂ hf₁ hf₂)∗∗ x) - halfSquaredNorm.asEReal x := by
                  rw [congrFun hweighted_conj x]
            _ = (proximal_average_theta f₁ f₂ hf₁ hf₂) x - halfSquaredNorm.asEReal x := by
                  rw [congrFun htheta_biconj x]
    _ = pav(f₁, f₂) x := by
          simpa using
            (congrFun (proximal_average_eq_theta_sub_halfSquaredNorm f₁ f₂ hf₁ hf₂) x).symm

/-- Evaluating the equal-weight specialization of `(18.40)` recovers the proximal average
pointwise. -/
@[simp] theorem equalWeight_shiftedConjugate_eq_proximalAverage_apply
    (f₁ f₂ : H → Set.Ioi (⊥ : EReal)) (hf₁ : f₁ ∈ Γ₀(H)) (hf₂ : f₂ ∈ Γ₀(H)) (x : H) :
    (weightedMoreauAverageShiftedConjugate
      ![f₁, f₂] (Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩)
      ![(1 / 2 : ℝ), (1 / 2 : ℝ)] x : EReal) =
      pav(f₁, f₂) x := by
  -- Evaluate the function equality from Remark 18.21 at the point `x`.
  exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal))
    (congrFun (equalWeight_shiftedConjugate_eq_proximalAverage f₁ f₂ hf₁ hf₂) x)

end StrongerDifferentiabilityNotions

end ERealFunction
