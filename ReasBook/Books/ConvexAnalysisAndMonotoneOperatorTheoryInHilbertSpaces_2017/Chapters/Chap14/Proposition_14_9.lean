import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap14.Definition_14_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.9 records the two-sided bounds for the proximal average.
- `core/canonical`: the owner abstraction is `proximalAverage`/`pav` from Definition 14.6; the
  lower bound additionally uses Fenchel conjugation `∗` from Definition 13.1.
- `bridge/view`: `Function.asEReal` is only the codomain bridge from `H → Set.Ioi (⊥ : EReal)` to
  the canonical `EReal`-valued function API, so the half-sum expressions below are derived
  pointwise function operations rather than primitive data. -/

section ProximalAverage

variable {H : Type u} [NormedAddCommGroup H] [Module ℝ H]

omit [Module ℝ H] in
/-- Helper for Proposition 14 9: evaluating the proximal-average kernel at the diagonal point
`(x, x)` removes the quadratic term and recovers the half-sum of `f x` and `g x`. -/
lemma diagonal_proximalAverageKernel_eq_half_sum
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (proximalAverageKernel f g (x, x) : EReal) =
      (((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal) x := by
  -- The diagonal kernel has zero quadratic correction and both function values are taken at `x`.
  simp [proximalAverageKernel_apply, Pi.smul_apply]

-- Proof sketch: evaluate the defining infimum of `pav(f, g)` at the diagonal choice `y = x`.
/-- Upper bound from Proposition 14 9: the proximal average is bounded above by the half-sum of
`f` and `g`. -/
theorem proximalAverage_upper_bound
    (f g : H → Set.Ioi (⊥ : EReal)) :
    pav(f, g) ≤
      ((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal := by
  intro x
  -- Route correction: work directly with the defining infimal postcomposition and test it on the
  -- diagonal fiber point `(x, x)`, rather than routing through the blocked single-variable formula.
  rw [proximalAverage]
  change
    sInf ((fun p : H × H ↦ (proximalAverageKernel f g p : EReal)) ''
      (proximalAverageMidpointMap ⁻¹' ({x} : Set H))) ≤
      (((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal) x
  have hdiag_mem : (x, x) ∈ proximalAverageMidpointMap ⁻¹' ({x} : Set H) := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, proximalAverageMidpointMap_apply]
    calc
      (1 / 2 : ℝ) • (x + x) = (1 / 2 : ℝ) • ((2 : ℝ) • x) := by simp [two_smul]
      _ = x := by
        rw [smul_smul, show (1 / 2 : ℝ) * (2 : ℝ) = 1 by norm_num, one_smul]
  have hsInf_le :
      sInf ((fun p : H × H ↦ (proximalAverageKernel f g p : EReal)) ''
        (proximalAverageMidpointMap ⁻¹' ({x} : Set H))) ≤
        (proximalAverageKernel f g (x, x) : EReal) := by
    exact sInf_le ⟨(x, x), hdiag_mem, rfl⟩
  calc
    sInf ((fun p : H × H ↦ (proximalAverageKernel f g p : EReal)) ''
        (proximalAverageMidpointMap ⁻¹' ({x} : Set H)))
      ≤ (proximalAverageKernel f g (x, x) : EReal) := hsInf_le
    _ = (((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal) x := by
        exact diagonal_proximalAverageKernel_eq_half_sum f g x

end ProximalAverage

section ProximalAverageConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 14 9: adding a finite real shift commutes with `iSup` in `EReal`. -/
lemma ereal_iSup_add_of_real_shift_local
    {ι : Sort*} (r : ℝ) (φ : ι → EReal) :
    (⨆ i, φ i + ((r : ℝ) : EReal)) =
      (⨆ i, φ i) + ((r : ℝ) : EReal) := by
  -- Each shifted term already lies below the shifted supremum, and conversely the supremum is an
  -- upper bound for every shifted term.
  have hright :
      (⨆ i, φ i) + ((r : ℝ) : EReal) ≤
        (⨆ i, φ i + ((r : ℝ) : EReal)) := by
    have hsub :
        (⨆ i, φ i) ≤ (⨆ i, φ i + ((r : ℝ) : EReal)) - ((r : ℝ) : EReal) := by
      refine iSup_le fun i ↦ ?_
      exact (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot r))
        (Or.inl (EReal.coe_ne_top r))).2 (le_iSup (fun i ↦ φ i + ((r : ℝ) : EReal)) i)
    exact (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot r))
      (Or.inl (EReal.coe_ne_top r))).1 hsub
  have hleft :
      (⨆ i, φ i + ((r : ℝ) : EReal)) ≤
        (⨆ i, φ i) + ((r : ℝ) : EReal) := by
    refine iSup_le fun i ↦ ?_
    exact add_le_add (le_iSup φ i) le_rfl
  exact le_antisymm hleft hright

/-- Helper for Proposition 14 9: subtracting an indexed infimum from a finite real scalar equals
the supremum of the corresponding pointwise affine defects. -/
lemma ereal_realCast_sub_iInf_eq_iSup_sub_local
    {ι : Sort*} (a : ℝ) (φ : ι → EReal) :
    ((a : EReal) - ⨅ i, φ i) = ⨆ i, ((a : EReal) - φ i) := by
  -- Rewrite subtraction as addition with negation, turn the negated infimum into a supremum,
  -- and then move the finite real shift through the supremum.
  calc
    ((a : EReal) - ⨅ i, φ i) = ((a : EReal) + -(⨅ i, φ i)) := by
      rw [sub_eq_add_neg]
    _ = ((a : EReal) + ⨆ i, -φ i) := by
      congr 1
      exact OrderIso.map_iInf EReal.negOrderIso φ
    _ = ((⨆ i, -φ i) + (a : EReal)) := by
      rw [add_comm]
    _ = ⨆ i, (-φ i) + (a : EReal) := by
      symm
      simpa using ereal_iSup_add_of_real_shift_local a (fun i ↦ -φ i)
    _ = ⨆ i, ((a : EReal) - φ i) := by
      refine iSup_congr fun i ↦ ?_
      simp [sub_eq_add_neg, add_comm]

/-- Helper for Proposition 14 9: evaluating `pav(f, g)` at `x` rewrites the midpoint
infimal postcomposition as an indexed infimum over the concrete midpoint fiber above `x`. -/
lemma proximalAverage_apply_eq_iInf_midpoint_fiber
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    pav(f, g) x =
      ⨅ p : {p // proximalAverageMidpointMap p = x}, (proximalAverageKernel f g p.1 : EReal) := by
  -- Replace the image of the midpoint fiber by the range of the corresponding subtype-valued map.
  rw [proximalAverage]
  change sInf ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
    (proximalAverageMidpointMap ⁻¹' ({x} : Set H))) =
      ⨅ p : {p // proximalAverageMidpointMap p = x}, (proximalAverageKernel f g p.1 : EReal)
  rw [show ((fun p ↦ (proximalAverageKernel f g p : EReal)) ''
      (proximalAverageMidpointMap ⁻¹' ({x} : Set H))) =
      Set.range (fun p : {p // proximalAverageMidpointMap p = x} ↦
        (proximalAverageKernel f g p.1 : EReal)) by
    ext a
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpx : proximalAverageMidpointMap p = x := by
        simpa using hp
      exact ⟨⟨p, hpx⟩, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, by simp, rfl⟩]
  exact sInf_range

/-- Helper for Proposition 14 9: every affine defect of `f.asEReal` is bounded by the Fenchel
conjugate `f.asEReal∗`. -/
lemma affine_defect_le_conjugate_asEReal
    (f : H → Set.Ioi (⊥ : EReal)) (y u : H) :
    (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) ≤ f.asEReal∗ u := by
  -- Expand the conjugate and bound it below by the `y`-term in the defining supremum.
  rw [conjugate_apply]
  exact le_iSup_of_le y le_rfl

/-- Helper for Proposition 14 9: if the conjugate value of `f.asEReal` is `⊥` at `u`, then every
value of `f` is `⊤`. -/
lemma value_eq_top_of_conjugate_eq_bot
    (f : H → Set.Ioi (⊥ : EReal)) {u y : H} (hu : f.asEReal∗ u = ⊥) :
    (f y : EReal) = ⊤ := by
  -- The affine defect at `y` is then forced to be `⊥`, which can only happen when `f y = ⊤`.
  have hdefect_le :
      (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) ≤ ⊥ := by
    have hdefect_le' := affine_defect_le_conjugate_asEReal f y u
    rw [hu] at hdefect_le'
    exact hdefect_le'
  have hdefect_eq :
      (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) = ⊥ :=
    le_bot_iff.mp hdefect_le
  by_cases htop : (f y : EReal) = ⊤
  · exact htop
  · have hdefect_ne_bot :
        (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) ≠ ⊥ := by
      rw [sub_eq_add_neg]
      refine EReal.add_ne_bot_iff.2 ?_
      constructor
      · exact EReal.coe_ne_bot _
      · simpa [EReal.neg_eq_bot_iff] using htop
    exact (hdefect_ne_bot hdefect_eq).elim

/-- Helper for Proposition 14 9: every midpoint-fiber affine defect of the proximal-average
kernel is bounded above by the half-sum of the Fenchel conjugates. -/
lemma midpoint_kernel_affine_defect_le_half_sum_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (x u y z : H)
    (hmid : proximalAverageMidpointMap (y, z) = x) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (proximalAverageKernel f g (y, z) : EReal)) ≤
      ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) := by
  have hhalf_nonneg : 0 ≤ (((1 / 2 : ℝ) : EReal)) :=
    EReal.coe_nonneg.mpr (by norm_num)
  have hhalf_ne_top : (((1 / 2 : ℝ) : EReal)) ≠ ⊤ :=
    EReal.coe_ne_top (1 / 2 : ℝ)
  have hhalf_ne_bot : (((1 / 2 : ℝ) : EReal)) ≠ ⊥ :=
    EReal.coe_ne_bot (1 / 2 : ℝ)
  by_cases hfbot : f.asEReal∗ u = ⊥
  · -- If `f∗ u = ⊥`, then every value of `f` is `⊤`, so the kernel affine defect is `⊥`.
    have hfy : (f y : EReal) = ⊤ :=
      value_eq_top_of_conjugate_eq_bot f hfbot
    have hhalf_g_ne_bot :
        (((1 / 2 : ℝ) : EReal) * (g z : EReal)) ≠ ⊥ := by
      refine (EReal.mul_ne_bot _ _).2 ?_
      exact ⟨Or.inl hhalf_ne_bot, Or.inr (ne_of_gt (g z).2), Or.inl hhalf_ne_top,
        Or.inl hhalf_nonneg⟩
    have hquad_ne_bot :
        ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ :=
      EReal.coe_ne_bot _
    have hkernel_top :
        (proximalAverageKernel f g (y, z) : EReal) = ⊤ := by
      rw [proximalAverageKernel_apply]
      calc
        (((1 / 2 : ℝ) : EReal) * (f y : EReal) +
            ((1 / 2 : ℝ) : EReal) * (g z : EReal) +
            ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)))
          = ⊤ + ((((1 / 2 : ℝ) : EReal) * (g z : EReal)) +
              ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal))) := by
              rw [hfy, EReal.coe_mul_top_of_pos (x := (1 / 2 : ℝ)) (by norm_num), add_assoc]
        _ = ⊤ := by
            rw [EReal.top_add_of_ne_bot]
            exact EReal.add_ne_bot_iff.2 ⟨hhalf_g_ne_bot, hquad_ne_bot⟩
    calc
      (((⟪x, u⟫_ℝ : ℝ) : EReal) - (proximalAverageKernel f g (y, z) : EReal)) = ⊥ := by
        rw [hkernel_top, EReal.sub_top]
      _ ≤ ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) :=
        bot_le
  · by_cases hgbot : g.asEReal∗ u = ⊥
    · -- The symmetric pathological branch again collapses the affine defect to `⊥`.
      have hgz : (g z : EReal) = ⊤ :=
        value_eq_top_of_conjugate_eq_bot g hgbot
      have hhalf_f_ne_bot :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal)) ≠ ⊥ := by
        refine (EReal.mul_ne_bot _ _).2 ?_
        exact ⟨Or.inl hhalf_ne_bot, Or.inr (ne_of_gt (f y).2), Or.inl hhalf_ne_top,
          Or.inl hhalf_nonneg⟩
      have hquad_ne_bot :
          ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ :=
        EReal.coe_ne_bot _
      have hkernel_top :
          (proximalAverageKernel f g (y, z) : EReal) = ⊤ := by
        rw [proximalAverageKernel_apply]
        calc
          (((1 / 2 : ℝ) : EReal) * (f y : EReal) +
              ((1 / 2 : ℝ) : EReal) * (g z : EReal) +
              ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)))
            = ((((1 / 2 : ℝ) : EReal) * (f y : EReal)) + ⊤) +
                ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) := by
                  rw [hgz, EReal.coe_mul_top_of_pos (x := (1 / 2 : ℝ)) (by norm_num), add_assoc]
          _ = ⊤ + ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) := by
                congr 1
                rw [EReal.add_top_of_ne_bot hhalf_f_ne_bot]
          _ = ⊤ := by
                rw [EReal.top_add_of_ne_bot hquad_ne_bot]
      calc
        (((⟪x, u⟫_ℝ : ℝ) : EReal) - (proximalAverageKernel f g (y, z) : EReal)) = ⊥ := by
          rw [hkernel_top, EReal.sub_top]
        _ ≤ ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) :=
          bot_le
    · -- In the proper branch, compare the midpoint pairing against the kernel plus the
      -- half-sum of conjugates.
      have hy_le :
          (((⟪y, u⟫_ℝ : ℝ) : EReal)) ≤ (f y : EReal) + f.asEReal∗ u := by
        simpa [add_comm] using
          (EReal.sub_le_iff_le_add
            (Or.inl (ne_of_gt (f y).2))
            (Or.inr hfbot)).1 (affine_defect_le_conjugate_asEReal f y u)
      have hz_le :
          (((⟪z, u⟫_ℝ : ℝ) : EReal)) ≤ (g z : EReal) + g.asEReal∗ u := by
        simpa [add_comm] using
          (EReal.sub_le_iff_le_add
            (Or.inl (ne_of_gt (g z).2))
            (Or.inr hgbot)).1 (affine_defect_le_conjugate_asEReal g z u)
      have hy_scaled :
          ((1 / 2 : ℝ) : EReal) * (((⟪y, u⟫_ℝ : ℝ) : EReal)) ≤
            ((1 / 2 : ℝ) : EReal) * ((f y : EReal) + f.asEReal∗ u) :=
        mul_le_mul_of_nonneg_left hy_le hhalf_nonneg
      have hz_scaled :
          ((1 / 2 : ℝ) : EReal) * (((⟪z, u⟫_ℝ : ℝ) : EReal)) ≤
            ((1 / 2 : ℝ) : EReal) * ((g z : EReal) + g.asEReal∗ u) :=
        mul_le_mul_of_nonneg_left hz_le hhalf_nonneg
      have hmidpoint_real :
          (1 / 2 : ℝ) * ⟪y, u⟫_ℝ + (1 / 2 : ℝ) * ⟪z, u⟫_ℝ = ⟪x, u⟫_ℝ := by
        calc
          (1 / 2 : ℝ) * ⟪y, u⟫_ℝ + (1 / 2 : ℝ) * ⟪z, u⟫_ℝ
            = ⟪(1 / 2 : ℝ) • y, u⟫_ℝ + ⟪(1 / 2 : ℝ) • z, u⟫_ℝ := by
                simp [real_inner_smul_left]
          _ = ⟪(1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z, u⟫_ℝ := by
                rw [inner_add_left]
          _ = ⟪(1 / 2 : ℝ) • (y + z), u⟫_ℝ := by rw [smul_add]
          _ = ⟪proximalAverageMidpointMap (y, z), u⟫_ℝ := by
                rw [proximalAverageMidpointMap_apply]
          _ = ⟪x, u⟫_ℝ := by rw [hmid]
      have hmidpoint :
          ((1 / 2 : ℝ) : EReal) * (((⟪y, u⟫_ℝ : ℝ) : EReal)) +
              ((1 / 2 : ℝ) : EReal) * (((⟪z, u⟫_ℝ : ℝ) : EReal)) =
            ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hmidpoint_real]
      have hsum :
          ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
            ((1 / 2 : ℝ) : EReal) * ((f y : EReal) + f.asEReal∗ u) +
              ((1 / 2 : ℝ) : EReal) * ((g z : EReal) + g.asEReal∗ u) := by
        rw [← hmidpoint]
        exact add_le_add hy_scaled hz_scaled
      have hsplit :
          ((1 / 2 : ℝ) : EReal) * ((f y : EReal) + f.asEReal∗ u) +
              ((1 / 2 : ℝ) : EReal) * ((g z : EReal) + g.asEReal∗ u) =
            ((((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
                (((1 / 2 : ℝ) : EReal) * (g z : EReal))) +
              ((((1 / 2 : ℝ) : EReal) * f.asEReal∗ u) +
                (((1 / 2 : ℝ) : EReal) * g.asEReal∗ u)) := by
        rw [EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg hhalf_ne_top,
          EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg hhalf_ne_top]
        simp [add_assoc, add_left_comm]
      have hconj_apply :
          ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) =
            (((1 / 2 : ℝ) : EReal) * f.asEReal∗ u) +
              (((1 / 2 : ℝ) : EReal) * g.asEReal∗ u) := by
        simp [Pi.smul_apply]
      have hquad_nonneg : 0 ≤ ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) :=
        EReal.coe_nonneg.mpr (by positivity)
      have hkernel_mono :
          ((((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
              (((1 / 2 : ℝ) : EReal) * (g z : EReal))) ≤
            (proximalAverageKernel f g (y, z) : EReal) := by
        rw [proximalAverageKernel_apply]
        have hmono :
            ((((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
                (((1 / 2 : ℝ) : EReal) * (g z : EReal))) ≤
              ((((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
                  (((1 / 2 : ℝ) : EReal) * (g z : EReal))) +
                ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) :=
          le_add_of_nonneg_right hquad_nonneg
        simpa [add_assoc] using hmono
      have hle_add :
          ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
            (proximalAverageKernel f g (y, z) : EReal) +
              ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) := by
        calc
          ((⟪x, u⟫_ℝ : ℝ) : EReal)
            ≤ ((((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
                (((1 / 2 : ℝ) : EReal) * (g z : EReal))) +
                ((((1 / 2 : ℝ) : EReal) * f.asEReal∗ u) +
                  (((1 / 2 : ℝ) : EReal) * g.asEReal∗ u)) := by
                    rw [← hsplit]
                    exact hsum
          _ ≤ (proximalAverageKernel f g (y, z) : EReal) +
                ((((1 / 2 : ℝ) : EReal) * f.asEReal∗ u) +
                  (((1 / 2 : ℝ) : EReal) * g.asEReal∗ u)) := by
                    exact add_le_add hkernel_mono le_rfl
          _ = (proximalAverageKernel f g (y, z) : EReal) +
                ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) := by
                  rw [hconj_apply]
      -- Convert the additive estimate back into the desired affine-defect inequality.
      have hle_add' :
          ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
            ((((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u) +
              (proximalAverageKernel f g (y, z) : EReal) := by
        simpa [add_comm] using hle_add
      exact EReal.sub_le_of_le_add hle_add'

/-- Helper for Proposition 14 9: the conjugate of the proximal average is bounded above by the
half-sum of the conjugates of `f` and `g`. -/
lemma conjugate_proximalAverage_le_half_sum_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) :
    pav(f, g)∗ ≤
      ((1 / 2 : ℝ) : EReal) • f.asEReal∗ + ((1 / 2 : ℝ) : EReal) • g.asEReal∗ := by
  intro u
  rw [conjugate_apply]
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - pav(f, g) x) =
        (((⟪x, u⟫_ℝ : ℝ) : EReal) -
          ⨅ p : {p // proximalAverageMidpointMap p = x},
            (proximalAverageKernel f g p.1 : EReal)) := by
          exact congrArg
            (fun t : EReal ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - t))
            (proximalAverage_apply_eq_iInf_midpoint_fiber f g x)
    _ = ⨆ p : {p // proximalAverageMidpointMap p = x},
          (((⟪x, u⟫_ℝ : ℝ) : EReal) - (proximalAverageKernel f g p.1 : EReal)) := by
            simpa using
              (ereal_realCast_sub_iInf_eq_iSup_sub_local
                (a := ⟪x, u⟫_ℝ)
                (φ := fun p : {p // proximalAverageMidpointMap p = x} ↦
                  (proximalAverageKernel f g p.1 : EReal)))
    _ ≤ ((((1 / 2 : ℝ) : EReal) • f.asEReal∗) + ((1 / 2 : ℝ) : EReal) • g.asEReal∗) u := by
          refine iSup_le fun p ↦ ?_
          rcases p with ⟨⟨y, z⟩, hp⟩
          exact midpoint_kernel_affine_defect_le_half_sum_conjugates f g x u y z hp

-- Proof sketch: use the Chapter 14 proximal-average formula together with the Chapter 13 Fenchel
-- conjugation calculus to the pointwise half-sum of `f*` and `g*`.
/-- Lower bound from Proposition 14 9: the proximal average dominates the conjugate of the
half-sum of `f*` and `g*`. -/
theorem proximalAverage_lower_bound
    (f g : H → Set.Ioi (⊥ : EReal)) :
    ((((1 / 2 : ℝ) : EReal) • f.asEReal∗) + ((1 / 2 : ℝ) : EReal) • g.asEReal∗)∗ ≤
      pav(f, g) := by
  -- First bound `pav(f, g)∗` above by the half-sum of the conjugates, then dualize back once
  -- more and apply the universal inequality `h∗∗ ≤ h`.
  calc
    ((((1 / 2 : ℝ) : EReal) • f.asEReal∗) + ((1 / 2 : ℝ) : EReal) • g.asEReal∗)∗
      ≤ pav(f, g)∗∗ := by
        exact conjugate_antitone (conjugate_proximalAverage_le_half_sum_conjugates f g)
    _ ≤ pav(f, g) := by
        exact biconjugate_le (pav(f, g))

-- Proof sketch: combine the preceding lower and upper bounds.
/-- Proposition 14 9: equation `(14.18)` sandwiches `pav(f, g)` between the conjugate of the
half-sum of `f*` and `g*` and the half-sum of `f` and `g`. -/
theorem proximalAverage_bounds
    (f g : H → Set.Ioi (⊥ : EReal)) :
    ((((1 / 2 : ℝ) : EReal) • f.asEReal∗) + ((1 / 2 : ℝ) : EReal) • g.asEReal∗)∗ ≤
      pav(f, g) ∧
    pav(f, g) ≤
      ((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal := by
  exact ⟨proximalAverage_lower_bound f g, proximalAverage_upper_bound f g⟩

end ProximalAverageConjugation

end ERealFunction
