import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Proposition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Set
open scoped Pointwise

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The `p`-power norm kernel `x ↦ ‖x‖^p / (γ p)` as an `]-∞,+∞]`-valued function. -/
noncomputable def normPowerKernel (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ ‖x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))).toEReal

/-- Coercing the `p`-power norm kernel to `EReal` recovers the formula `‖x‖^p / (γ p)`. -/
@[simp]
theorem normPowerKernel_apply (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (normPowerKernel p γ x : EReal) =
      (((‖x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  -- Unfold the `toEReal` packaging to recover the defining real-valued formula.
  simp [normPowerKernel]

/-- The `p`-power infimal-convolution regularization `g_γ = f □ (‖·‖^p / (γ p))`. -/
noncomputable def normPowerEnvelope {α : Type v} [CoeTC α EReal] (f : H → α)
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) : H → EReal :=
  f □ normPowerKernel p γ

/-- The value of the `p`-power envelope at `x` is the defining infimum over translated `p`-power
norm penalizations. -/
theorem normPowerEnvelope_apply {α : Type v} [CoeTC α EReal] (f : H → α)
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) (x : H) :
    normPowerEnvelope f p γ x =
      ⨅ y : H, (f y : EReal) +
        (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  -- Expand the infimal convolution and rewrite the kernel at the translated point `x - y`.
  simp [normPowerEnvelope, infimalConvolution_apply]

/-- Helper for Proposition 12 9: the exponent `2` belongs to `Set.Ici (1 : ℝ)`. -/
theorem two_mem_Ici_one : (2 : ℝ) ∈ Set.Ici (1 : ℝ) := by
  -- The exponent `2` is visibly at least `1`.
  norm_num

/-- Helper for Proposition 12 9: at exponent `p = 2`, the `p`-power kernel agrees with the
quadratic Moreau kernel. -/
theorem normPowerKernel_two_eq_moreauQuadraticKernel
    (γ : Set.Ioi (0 : ℝ)) :
    (normPowerKernel ⟨(2 : ℝ), two_mem_Ici_one⟩ γ : H → Set.Ioi (⊥ : EReal)) =
      moreauQuadraticKernel γ := by
  -- Compare the two kernels pointwise and normalize the scalar coefficient.
  funext x
  apply Subtype.ext
  rw [normPowerKernel_apply, moreauQuadraticKernel_apply]
  norm_num
  rw [← EReal.coe_mul]
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
    field_simp [hγ_ne]

/-- For the quadratic exponent `p = 2`, the `p`-power envelope is exactly the canonical Moreau
envelope `{}^[γ] f`. -/
theorem normPowerEnvelope_two_eq_moreauEnvelope
    {α : Type v} [CoeTC α EReal] (f : H → α) (γ : Set.Ioi (0 : ℝ)) :
    normPowerEnvelope f ⟨(2 : ℝ), two_mem_Ici_one⟩ γ = {}^[γ] f := by
  -- Once the kernels agree at `p = 2`, the infimal convolutions agree as functions.
  simp [normPowerEnvelope, moreauEnvelope, normPowerKernel_two_eq_moreauQuadraticKernel]

/-- Helper for Proposition 12 9: the `p`-power kernel is finite everywhere, so its effective
domain is all of `H`. -/
theorem effectiveDomain_normPowerKernel_eq_univ
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    effectiveDomain (normPowerKernel p γ : H → Set.Ioi (⊥ : EReal)) = Set.univ := by
  -- The kernel comes from a real-valued map, so it is finite everywhere.
  simp [normPowerKernel]

/-- Proposition 12.9 (1): clause (i), the `p`-power envelope has full domain, equivalently it
never attains the value `+∞`. -/
theorem dom_normPowerEnvelope_eq_univ
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    dom (normPowerEnvelope f p γ) = Set.univ := by
  -- Proposition 12.6 identifies the domain with a Minkowski sum of effective domains.
  calc
    dom (normPowerEnvelope f p γ) =
        effectiveDomain f +
          effectiveDomain (normPowerKernel p γ : H → Set.Ioi (⊥ : EReal)) := by
      simpa [normPowerEnvelope] using dom_infimalConvolution_ioi f (normPowerKernel p γ)
    _ = effectiveDomain f + Set.univ := by
      rw [effectiveDomain_normPowerKernel_eq_univ]
    _ = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rcases hdom with ⟨y, hy⟩
        exact Set.mem_add.2 ⟨y, hy, x - y, by simp, by abel⟩

/-- Helper for Proposition 12 9: evaluating the defining infimum at a chosen point gives an upper
bound for the envelope. -/
theorem normPowerEnvelope_le_test_point
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) (x y : H) :
    normPowerEnvelope f p γ x ≤
      (f y : EReal) +
        (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  -- Evaluating the defining infimum at the chosen point `y` gives the required upper bound.
  rw [normPowerEnvelope_apply]
  exact iInf_le _ y

/-- Helper for Proposition 12 9: the `p`-power penalty vanishes when the test point is `x`
itself. -/
theorem normPowerEnvelope_self_penalty_eq_zero
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (((‖x - x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) = 0 := by
  have hp_ne : (p : ℝ) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one p.2)
  -- At the test point `y = x`, the translated norm is zero.
  rw [sub_self, norm_zero, Real.zero_rpow hp_ne]
  simp

/-- Helper for Proposition 12 9: increasing the regularization parameter decreases the penalty
coefficient pointwise. -/
theorem normPowerEnvelope_penalty_antitone_parameter
    (p : Set.Ici (1 : ℝ)) (γ μ : Set.Ioi (0 : ℝ)) (hγμ : (γ : ℝ) < μ)
    (x y : H) :
    (((‖x - y‖ ^ (p : ℝ) / ((μ : ℝ) * (p : ℝ)) : ℝ) : EReal)) ≤
      (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  have hp_pos : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one p.2
  have hnum_nonneg : 0 ≤ ‖x - y‖ ^ (p : ℝ) := by
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hγp_pos : 0 < ((γ : ℝ) * (p : ℝ)) := mul_pos γ.2 hp_pos
  have hden_le : ((γ : ℝ) * (p : ℝ)) ≤ (μ : ℝ) * (p : ℝ) := by
    nlinarith [hγμ, p.2]
  -- The numerator is nonnegative, so enlarging the denominator decreases the quotient.
  exact EReal.coe_le_coe <|
    div_le_div_of_nonneg_left hnum_nonneg hγp_pos hden_le

/-- Helper for Proposition 12 9: the `p`-power envelope is antitone in the parameter `γ`. -/
theorem normPowerEnvelope_antitone_parameter
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ))
    (γ μ : Set.Ioi (0 : ℝ)) (hγμ : (γ : ℝ) < μ) (x : H) :
    normPowerEnvelope f p μ x ≤ normPowerEnvelope f p γ x := by
  rw [normPowerEnvelope_apply, normPowerEnvelope_apply]
  -- Compare the two infima pointwise using the antitonicity of the penalty coefficient.
  refine le_iInf fun y ↦ ?_
  have hsum_le :
      (f y : EReal) +
          (((‖x - y‖ ^ (p : ℝ) / ((μ : ℝ) * (p : ℝ)) : ℝ) : EReal)) ≤
        (f y : EReal) +
          (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (normPowerEnvelope_penalty_antitone_parameter p γ μ hγμ x y)
        (f y : EReal)
  exact le_trans
    (iInf_le
      (fun z : H ↦
        (f z : EReal) +
          (((‖x - z‖ ^ (p : ℝ) / ((μ : ℝ) * (p : ℝ)) : ℝ) : EReal)))
      y)
    hsum_le

/-- Helper for Proposition 12 9: every envelope value dominates the infimum of the original
function range. -/
theorem sInf_range_le_normPowerEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) (x : H) :
    sInf (Set.range f.asEReal) ≤ normPowerEnvelope f p γ x := by
  rw [normPowerEnvelope_apply]
  refine le_iInf fun y ↦ ?_
  have hp_nonneg : 0 ≤ (p : ℝ) := le_trans (by norm_num) p.2
  have hpen_nonneg :
      (0 : EReal) ≤
        (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
    refine EReal.coe_nonneg.mpr ?_
    refine div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) ?_
    exact mul_nonneg γ.2.le hp_nonneg
  -- Each summand dominates `f y`, and `sInf` is below every value of `f`.
  exact le_trans (sInf_le ⟨y, rfl⟩) <|
    by simpa using
      (le_add_of_nonneg_right hpen_nonneg :
        (f y : EReal) ≤
          (f y : EReal) +
            (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)))

/-- Proposition 12.9 (2): clause (ii), assuming `effectiveDomain f` is nonempty, if `γ < μ`, then
the `μ`-envelope is pointwise below the `γ`-envelope, while the `γ`-envelope value lies between
the infimum of `f` and `f x`. -/
theorem normPowerEnvelope_mono_and_mem_Icc
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (p : Set.Ici (1 : ℝ))
    (γ μ : Set.Ioi (0 : ℝ)) (hγμ : (γ : ℝ) < μ) (x : H) :
    normPowerEnvelope f p μ x ∈
        Set.Icc (sInf (Set.range f.asEReal)) (normPowerEnvelope f p γ x) ∧
      normPowerEnvelope f p γ x ≤ (f x : EReal) := by
  let _ := hdom
  constructor
  · constructor
    · -- The lower bound is the global infimum lower bound from the defining infimum.
      exact sInf_range_le_normPowerEnvelope f p μ x
    · -- Antitonicity in the parameter gives the upper endpoint of the interval.
      exact normPowerEnvelope_antitone_parameter f p γ μ hγμ x
  · -- Evaluating the infimum at `y = x` recovers the `g_γ(x) ≤ f(x)` bound.
    have htest := normPowerEnvelope_le_test_point f p γ x x
    calc
      normPowerEnvelope f p γ x ≤
          (f x : EReal) +
            (((‖x - x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := htest
      _ = (f x : EReal) := by
        rw [normPowerEnvelope_self_penalty_eq_zero p γ x, add_zero]

/-- Proposition 12.9 (3): clause (iii), assuming `effectiveDomain f` is nonempty, the `p`-power
envelope has the same infimum over `H` as `f`. -/
theorem sInf_range_normPowerEnvelope_eq_sInf_range (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    sInf (Set.range (normPowerEnvelope f p γ)) = sInf (Set.range f.asEReal) := by
  let _ := hdom
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨x, rfl⟩
    have htest := normPowerEnvelope_le_test_point f p γ x x
    have hupper : normPowerEnvelope f p γ x ≤ (f x : EReal) := by
      calc
        normPowerEnvelope f p γ x ≤
            (f x : EReal) +
              (((‖x - x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := htest
        _ = (f x : EReal) := by
          rw [normPowerEnvelope_self_penalty_eq_zero p γ x, add_zero]
    exact le_trans (sInf_le ⟨x, rfl⟩) hupper
  · refine le_sInf ?_
    rintro _ ⟨x, rfl⟩
    exact sInf_range_le_normPowerEnvelope f p γ x

/-- Helper for Proposition 12 9: the `EReal`-cast reciprocal-decay map `γ ↦ c / γ` tends to `0`
along `γ → +∞` through `Ioi 0`. -/
theorem ereal_coe_div_tendsto_zero_atTop (c : ℝ) :
    Filter.Tendsto
      (fun γ : Set.Ioi (0 : ℝ) ↦ (((c / (γ : ℝ) : ℝ) : EReal)))
      Filter.atTop (nhds (0 : EReal)) := by
  have hcoe : Filter.Tendsto (fun γ : Set.Ioi (0 : ℝ) ↦ (γ : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Filter.Tendsto] using (Filter.map_val_Ioi_atTop (0 : ℝ))
  have hreal :
      Filter.Tendsto (fun γ : Set.Ioi (0 : ℝ) ↦ (c / (γ : ℝ) : ℝ))
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_const_nhds.div_atTop hcoe
  -- Coercion `ℝ → EReal` is continuous, so the real convergence transfers directly.
  exact (continuous_coe_real_ereal.tendsto 0).comp hreal

/-- Helper for Proposition 12 9: for fixed `x` and `z`, the translated `p`-power penalty tends to
`0` as the parameter tends to `+∞`. -/
theorem translated_normPowerPenalty_tendsto_zero_atTop
    (p : Set.Ici (1 : ℝ)) (x z : H) :
    Filter.Tendsto
      (fun γ : Set.Ioi (0 : ℝ) ↦
        (((‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)))
      Filter.atTop (nhds (0 : EReal)) := by
  have hp_ne : (p : ℝ) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one p.2)
  -- Rewrite the penalty as a fixed real constant divided by `γ`, then invoke reciprocal decay.
  have hrewrite :
      (fun γ : Set.Ioi (0 : ℝ) ↦
        (((‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal))) =
      fun γ : Set.Ioi (0 : ℝ) ↦
        (((((‖x - z‖ ^ (p : ℝ)) / (p : ℝ)) / (γ : ℝ) : ℝ) : EReal)) := by
    funext γ
    congr 1
    have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    field_simp [hp_ne, hγ_ne]
  rw [hrewrite]
  exact ereal_coe_div_tendsto_zero_atTop ((‖x - z‖ ^ (p : ℝ)) / (p : ℝ))

/-- Helper for Proposition 12 9: at a finite test point, the envelope bound can be rewritten as a
single real cast. -/
theorem normPowerEnvelope_le_test_point_toReal_bound
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) (x z : H) (hz : z ∈ effectiveDomain f) :
    normPowerEnvelope f p γ x ≤
      ((((f z : EReal).toReal +
          (‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))) : ℝ) : EReal)) := by
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
  have hcoe : ((((f z : EReal).toReal : ℝ) : EReal)) = (f z : EReal) := by
    rw [EReal.coe_toReal hz_top hz_bot]
  -- Replace the finite value `f z` by its real representative and combine the two real terms.
  calc
    normPowerEnvelope f p γ x ≤
        (f z : EReal) +
          (((‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) :=
      normPowerEnvelope_le_test_point f p γ x z
    _ =
        ((((f z : EReal).toReal +
            (‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))) : ℝ) : EReal)) := by
      rw [← hcoe]
      simp

/-- Helper for Proposition 12 9: any strict upper bound above `inf f(H)` eventually dominates the
`p`-power envelope values. -/
theorem eventually_normPowerEnvelope_lt_of_lt_upper_bound
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ)) (x : H) {ξ : EReal}
    (hξ : sInf (Set.range f.asEReal) < ξ) :
    ∀ᶠ γ : Set.Ioi (0 : ℝ) in Filter.atTop, normPowerEnvelope f p γ x < ξ := by
  rcases (sInf_lt_iff).1 hξ with ⟨_, ⟨z, rfl⟩, hzlt⟩
  have hz : z ∈ effectiveDomain f := mem_effectiveDomain_iff.mpr (lt_of_lt_of_le hzlt le_top)
  by_cases hξ_top : ξ = ⊤
  · filter_upwards with γ
    have hfinite := normPowerEnvelope_le_test_point_toReal_bound f p γ x z hz
    exact lt_of_le_of_lt hfinite <|
      by
        simpa [hξ_top] using
          (EReal.coe_lt_top
            (((f z : EReal).toReal +
              ‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))) : ℝ))
  · have hξ_bot : ξ ≠ ⊥ := ne_of_gt <| lt_of_lt_of_le (f z).2 hzlt.le
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
    have hz_real_lt : (f z : EReal).toReal < ξ.toReal := by
      have hcast :
          ((((f z : EReal).toReal : ℝ) : EReal)) < (((ξ.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal hz_top hz_bot, EReal.coe_toReal hξ_top hξ_bot]
        exact hzlt
      exact EReal.coe_lt_coe_iff.mp hcast
    let ε : Set.Ioi (0 : ℝ) := ⟨ξ.toReal - (f z : EReal).toReal, sub_pos.mpr hz_real_lt⟩
    have hpenalty_lt :
        ∀ᶠ γ : Set.Ioi (0 : ℝ) in Filter.atTop,
          (((‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) < (ε : ℝ) := by
      exact (translated_normPowerPenalty_tendsto_zero_atTop p x z).eventually
        (Iio_mem_nhds (by exact_mod_cast ε.2))
    -- The finite test-point bound plus the vanishing penalty force the eventual strict inequality.
    filter_upwards [hpenalty_lt] with γ hγ
    have hfinite := normPowerEnvelope_le_test_point_toReal_bound f p γ x z hz
    have hγ_real :
        ‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) < (ε : ℝ) :=
      EReal.coe_lt_coe_iff.mp hγ
    have hsum_real :
        (f z : EReal).toReal + ‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) < ξ.toReal := by
      linarith
    have hsum_ereal :
        ((((f z : EReal).toReal +
            ‖x - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) < ξ := by
      rw [← EReal.coe_toReal hξ_top hξ_bot]
      exact EReal.coe_lt_coe_iff.mpr hsum_real
    exact lt_of_le_of_lt hfinite hsum_ereal

/-- Proposition 12.9 (4): clause (iv), assuming `effectiveDomain f` is nonempty, for each `x`,
the `p`-power envelope values decrease to the infimum of `f` as `γ → +∞`. -/
theorem tendsto_normPowerEnvelope_atTop (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) (p : Set.Ici (1 : ℝ)) (x : H) :
    Antitone (fun γ : Set.Ioi (0 : ℝ) ↦ normPowerEnvelope f p γ x) ∧
      Filter.Tendsto (fun γ : Set.Ioi (0 : ℝ) ↦ normPowerEnvelope f p γ x) Filter.atTop
        (nhds (sInf (Set.range f.asEReal))) := by
  let _ := hdom
  refine ⟨?_, ?_⟩
  · intro γ μ hγμ
    rcases lt_or_eq_of_le hγμ with hlt | rfl
    · exact normPowerEnvelope_antitone_parameter f p γ μ hlt x
    · exact le_rfl
  · -- Order convergence follows from the global lower bound and eventual strict upper bounds.
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact Filter.Eventually.of_forall fun γ ↦
        lt_of_lt_of_le ha (sInf_range_le_normPowerEnvelope f p γ x)
    · intro ξ hξ
      exact eventually_normPowerEnvelope_lt_of_lt_upper_bound f p x hξ

/-- Helper for Proposition 12 9: on a fixed ball, evaluating the infimal convolution at one
effective-domain point gives a uniform real-cast upper bound. -/
theorem normPowerEnvelope_le_ball_test_point_bound
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) (x z y : H) (ρ : Set.Ioi (0 : ℝ))
    (hz : z ∈ effectiveDomain f) (hy : y ∈ Metric.ball x (ρ : ℝ)) :
    normPowerEnvelope f p γ y ≤
      ((((f z : EReal).toReal +
          (((‖x - z‖ + (ρ : ℝ)) ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))) : ℝ)) : ℝ) : EReal) := by
  have hy_norm : ‖y - x‖ < (ρ : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hdist_le : ‖y - z‖ ≤ ‖x - z‖ + (ρ : ℝ) := by
    have hsplit : y - z = (y - x) + (x - z) := by
      abel
    calc
      ‖y - z‖ = ‖(y - x) + (x - z)‖ := by rw [hsplit]
      _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
      _ ≤ (ρ : ℝ) + ‖x - z‖ := by
        linarith
      _ = ‖x - z‖ + (ρ : ℝ) := by ring
  have hp_nonneg : 0 ≤ (p : ℝ) := le_trans (by norm_num) p.2
  have hpow_le :
      ‖y - z‖ ^ (p : ℝ) ≤ (‖x - z‖ + (ρ : ℝ)) ^ (p : ℝ) := by
    exact Real.rpow_le_rpow (norm_nonneg _) hdist_le hp_nonneg
  have hsum_le :
      (f z : EReal).toReal + (‖y - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))) ≤
        (f z : EReal).toReal +
          ((‖x - z‖ + (ρ : ℝ)) ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))) := by
    have hp_nonneg' : 0 ≤ (p : ℝ) := le_trans (by norm_num) p.2
    have hdiv_le :
        ‖y - z‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) ≤
          (‖x - z‖ + (ρ : ℝ)) ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) := by
      exact div_le_div_of_nonneg_right hpow_le (mul_nonneg γ.2.le hp_nonneg')
    linarith
  -- First rewrite the test-point bound as a real cast, then use the ballwise norm estimate.
  exact le_trans
    (normPowerEnvelope_le_test_point_toReal_bound f p γ y z hz)
    (EReal.coe_le_coe hsum_le)

/-- Proposition 12.9 (5): clause (v), for fixed `γ`, the `p`-power envelope is bounded above on
every open ball of `H`. -/
theorem normPowerEnvelope_boundedAbove_on_ball
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    ∀ x : H, ∀ ρ : Set.Ioi (0 : ℝ), ∃ M : ℝ,
      ∀ y ∈ Metric.ball x (ρ : ℝ), normPowerEnvelope f p γ y ≤ (M : EReal) := by
  intro x ρ
  rcases hdom with ⟨z, hz⟩
  refine ⟨(f z : EReal).toReal +
      ((‖x - z‖ + (ρ : ℝ)) ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))), ?_⟩
  intro y hy
  -- One fixed effective-domain point yields a uniform real upper bound on the whole ball.
  exact normPowerEnvelope_le_ball_test_point_bound f p γ x z y ρ hz hy

end ERealFunction
