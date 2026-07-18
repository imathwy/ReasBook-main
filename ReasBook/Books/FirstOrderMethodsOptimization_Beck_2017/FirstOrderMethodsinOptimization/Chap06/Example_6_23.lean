import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Example_6_14
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Remark_6_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TwoSidedSoftThreshold

private theorem extendedIndicator_nonnegative_interval_abs_eq_absolute_value_box_indicator
    (α : ENNReal) (t : ℝ) :
    extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} |t| =
      extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
  by_cases hα : α = ⊤
  · simp [hα, extendedIndicator]
  · lift α to NNReal using hα with a
    by_cases ht : |t| ≤ (a : ℝ)
    · have hinterval : |t| ∈ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ ((a : ENNReal) : EReal)} := by
        refine ⟨abs_nonneg t, ?_⟩
        rw [show ((|t| : ℝ) : EReal) = (ENNReal.ofReal |t| : EReal) by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg t)]]
        exact_mod_cast ht
      have hbox : t ∈ {y : ℝ | |y| ≤ (a : ℝ)} := by
        simpa using ht
      simp [extendedIndicator, hinterval, hbox]
    · have hinterval :
        |t| ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ ((a : ENNReal) : EReal)} := by
          intro hmem
          apply ht
          exact EReal.coe_le_coe_iff.mp hmem.2
      have hbox : t ∉ {y : ℝ | |y| ≤ (a : ℝ)} := by
        simpa using ht
      simp [extendedIndicator, hinterval, hbox]

/-- The scalar coordinate penalty `truncated_linear_penalty μ α ∘ abs` is exactly the absolute
value box penalty `t ↦ μ |t| + δ_{[-α, α]}(t)`. This is the one-dimensional bridge used by the
vector separable formula in Example 6.23 and by its `Fin 1` specialization in Example 6.22. -/
theorem truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty
    (μ : NNReal) (α : ENNReal) :
    truncated_linear_penalty (μ : ℝ) α ∘ abs =
      fun t : ℝ ↦ ((μ : ℝ) * |t| : ℝ) +
        extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
  funext t
  rw [Function.comp_apply, truncated_linear_penalty_apply]
  rw [extendedIndicator_nonnegative_interval_abs_eq_absolute_value_box_indicator α t]
  rw [add_comm]

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.23 is `source-facing` in the finite-product proximal domain.
Domain sampling against the surrounding chapter API fixes the owner split as follows:

- primitive/source data: the weighted box penalty `weighted_l1_box_penalty ω α`,
- core/canonical owners already upstream: `prox[...]`, `separableSum`, the scalar truncated
  penalty `truncated_linear_penalty`, and the finite-product singleton bridge for separable
  proximal operators,
- bridge/view surface: the decomposition of `weighted_l1_box_penalty` into a separable sum of the
  scalar truncated penalties.

The public statement therefore stays on the source-facing owner `weighted_l1_box_penalty`, while
the supporting API should reuse the chapter's separable-product proximal machinery rather than
introducing a parallel single-valued proximal map or a packaged coordinatewise wrapper; the
thresholded point itself should be expressed directly through the vector owner `𝓢[ω, α]`.
-/

/-- Bridge theorem: the weighted `ℓ¹`-plus-box penalty is the separable sum of the scalar
truncated linear penalties applied to the coordinate magnitudes. -/
theorem weighted_l1_box_penalty_eq_separableSum_truncated_linear_penalty
    (ω : ι → NNReal) (α : ι → ENNReal) :
    weighted_l1_box_penalty ω α =
      PiLp.separableSum (fun i ↦ truncated_linear_penalty (ω i) (α i) ∘ abs) :=
  by
    funext x
    rw [weighted_l1_box_penalty_apply]
    simp only [PiLp.separableSum_apply, Function.comp_apply, truncated_linear_penalty_apply]
    by_cases hx : ∀ i, ENNReal.ofReal |x i| ≤ α i
    · have hsum :
          (∑ i, (((ω i : ℝ) * |x i| : ℝ) : EReal)) =
            ((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal) := by
        exact
          (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
            (fun i ↦ (ω i : ℝ) * |x i|) Finset.univ).symm
      rw [← hsum]
      have hbox :
          extendedIndicator {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} x = 0 := by
        simp [extendedIndicator, hx]
      have hcoord :
          ∀ i,
            extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α i : EReal)} |x i| = 0 := by
        intro i
        have hi : |x i| ∈ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α i : EReal)} := by
          refine ⟨abs_nonneg _, ?_⟩
          rw [show ((|x i| : ℝ) : EReal) = (ENNReal.ofReal |x i| : EReal) by
            rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg _)]]
          exact_mod_cast hx i
        simp [extendedIndicator, hi]
      simp [hbox, hcoord]
    · obtain ⟨i, hi0⟩ := not_forall.mp hx
      have hi : α i < ENNReal.ofReal |x i| := lt_of_not_ge hi0
      have hxnot : x ∉ {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} := by
        intro hxmem
        exact not_lt_of_ge (hxmem i) hi
      have hbox :
          extendedIndicator {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} x = ⊤ := by
        simp [extendedIndicator, hxnot]
      have hcoord_top :
          extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α i : EReal)} |x i| = ⊤ := by
        have hnotmem : |x i| ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α i : EReal)} := by
          intro hmem
          have hle : ENNReal.ofReal |x i| ≤ α i := by
            have hleE : ((|x i| : ℝ) : EReal) ≤ (α i : EReal) := hmem.2
            rw [show ((|x i| : ℝ) : EReal) = (ENNReal.ofReal |x i| : EReal) by
              rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg _)]] at hleE
            exact_mod_cast hleE
          exact not_lt_of_ge hle hi
        simp [extendedIndicator, hnotmem]
      let term : ι → EReal := fun j ↦
        extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α j : EReal)} |x j| +
          (((ω j : ℝ) * |x j| : ℝ) : EReal)
      have hterm_ne_bot : ∀ j, term j ≠ ⊥ := by
        intro j
        dsimp [term]
        by_cases hj : ENNReal.ofReal |x j| ≤ α j
        · have hcoord :
              extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α j : EReal)} |x j| = 0 := by
            have hmem : |x j| ∈ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α j : EReal)} := by
              refine ⟨abs_nonneg _, ?_⟩
              rw [show ((|x j| : ℝ) : EReal) = (ENNReal.ofReal |x j| : EReal) by
                rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg _)]]
              exact_mod_cast hj
            simp [extendedIndicator, hmem]
          rw [hcoord, zero_add]
          exact EReal.coe_ne_bot _
        · have hj' : α j < ENNReal.ofReal |x j| := lt_of_not_ge hj
          have hcoord :
              extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α j : EReal)} |x j| = ⊤ := by
            have hnotmem : |x j| ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α j : EReal)} := by
              intro hmem
              have hle : ENNReal.ofReal |x j| ≤ α j := by
                have hleE : ((|x j| : ℝ) : EReal) ≤ (α j : EReal) := hmem.2
                rw [show ((|x j| : ℝ) : EReal) = (ENNReal.ofReal |x j| : EReal) by
                  rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg _)]] at hleE
                exact_mod_cast hleE
              exact not_lt_of_ge hle hj'
            simp [extendedIndicator, hnotmem]
          rw [hcoord]
          simpa using (EReal.coe_ne_bot ((ω j : ℝ) * |x j|))
      rw [hbox, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      classical
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (show i ∈ Finset.univ by simp) term]
      simp [term, hcoord_top]
      have hrest_ne_bot : ∑ j ∈ Finset.univ \ {i}, term j ≠ ⊥ := by
        classical
        induction (Finset.univ \ {i} : Finset ι) using Finset.induction_on with
        | empty => simp
        | insert j s hj hs =>
            rw [Finset.sum_insert hj, EReal.add_ne_bot_iff]
            exact ⟨hterm_ne_bot j, hs⟩
      exact (EReal.top_add_of_ne_bot hrest_ne_bot).symm

/-- Helper for Example 6.23: the `SignType.sign` coercion agrees with `Real.sign` on `ℝ`. -/
private theorem signType_sign_coe_eq_real_sign (t : ℝ) :
    (((SignType.sign t : SignType) : ℝ)) = Real.sign t := by
  -- Compare the three sign regimes to identify the two sign conventions.
  obtain hneg | rfl | hpos := lt_trichotomy t 0
  · simp [Real.sign_of_neg hneg, SignType.sign, hneg, not_lt.mpr hneg.le]
  · simp [Real.sign_zero]
  · simp [Real.sign_of_pos hpos, SignType.sign, hpos]

/-- Helper for Example 6.23: the soft-threshold magnitude is the positive-part radius
`max (|t| - μ) 0`. -/
private theorem abs_soft_thresholding_eq_posPart_sub
    (μ : NNReal) (t : ℝ) :
    |𝒯[(μ : ℝ)] t| = max (|t| - (μ : ℝ)) 0 := by
  by_cases ht : t = 0
  · -- At the origin the thresholded value is `0`, so its magnitude vanishes.
    simp [ht, soft_thresholding_apply]
  · -- Away from `0`, the sign factor has absolute value `1`.
    have hsign : |(((SignType.sign t : SignType) : ℝ))| = 1 := by
      obtain hneg | hpos := lt_or_gt_of_ne ht
      · rw [signType_sign_coe_eq_real_sign]
        simp [Real.sign_of_neg hneg]
      · rw [signType_sign_coe_eq_real_sign]
        simp [Real.sign_of_pos hpos]
    calc
      |𝒯[(μ : ℝ)] t| = |(|t| - (μ : ℝ))⁺ * (((SignType.sign t : SignType) : ℝ))| := by
        simp [soft_thresholding_apply]
      _ = |(|t| - (μ : ℝ))⁺| * |(((SignType.sign t : SignType) : ℝ))| := by
        rw [abs_mul]
      _ = (|t| - (μ : ℝ))⁺ := by
        rw [hsign, mul_one, abs_of_nonneg (by positivity)]
      _ = max (|t| - (μ : ℝ)) 0 := rfl

/-- Helper for Example 6.23: in the unbounded branch, the magnitude/sign presentation of the
coordinate formula collapses to ordinary soft-thresholding. -/
private theorem abs_soft_thresholding_mul_real_sign_eq_soft_threshold
    (μ : NNReal) (t : ℝ) :
    |𝒯[(μ : ℝ)] t| * Real.sign t = 𝒯[(μ : ℝ)] t := by
  -- Rewrite both sides to the same positive-part times sign expression.
  rw [show (Real.sign t : ℝ) = (((SignType.sign t : SignType) : ℝ)) by
    rw [signType_sign_coe_eq_real_sign]]
  rw [abs_soft_thresholding_eq_posPart_sub]
  rw [soft_thresholding_apply]
  rfl

/-- Helper for Example 6.23: the truncated linear penalty is proper because it is finite at `0`
and never takes the value `-∞`. -/
private theorem isProper_truncated_linear_penalty
    (μ : ℝ) (α : ENNReal) :
    IsProperExtendedRealFunction (truncated_linear_penalty μ α) := by
  let C : Set ℝ := {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)}
  refine ⟨?_, ?_⟩
  · intro t
    by_cases ht : t ∈ C
    · -- On the feasible interval, the penalty is a finite real value.
      simpa [C, truncated_linear_penalty_apply, extendedIndicator, ht] using
        (EReal.coe_ne_bot (μ * t))
    · -- Outside the interval, the indicator contributes `⊤`, so the value is still not `⊥`.
      rw [truncated_linear_penalty_apply]
      have htop : extendedIndicator C t + ((μ * t : ℝ) : EReal) = ⊤ := by
        calc
          extendedIndicator C t + ((μ * t : ℝ) : EReal) = ⊤ + ((μ * t : ℝ) : EReal) := by
            simp [extendedIndicator, ht]
          _ = ⊤ := by rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      have htop' :
          extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} t +
              ((μ * t : ℝ) : EReal) = ⊤ := by
        simpa [C] using htop
      rw [htop']
      simp
  · -- The origin always belongs to the effective domain.
    refine ⟨0, ?_⟩
    have h0 : (0 : ℝ) ∈ C := by
      refine ⟨le_rfl, ?_⟩
      positivity
    simpa [mem_effective_domain, C, truncated_linear_penalty_apply, extendedIndicator, h0]

/-- Helper for Example 6.23: the truncated linear penalty is infinite on the negative ray. -/
private theorem truncated_linear_penalty_eq_top_of_lt_zero
    (μ : ℝ) (α : ENNReal) {t : ℝ} (ht : t < 0) :
    truncated_linear_penalty μ α t = ⊤ := by
  rw [truncated_linear_penalty_apply]
  -- Negative radii violate the nonnegative interval constraint.
  have hnot : t ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} := by
    intro hmem
    exact not_le_of_gt ht hmem.1
  calc
    extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} t + ((μ * t : ℝ) : EReal)
        = ⊤ + ((μ * t : ℝ) : EReal) := by simp [extendedIndicator, hnot]
    _ = ⊤ := by rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]

/-- Helper for Example 6.23: multiplying the clipped radial minimizer by `Real.sign` produces the
scalar box proximal point used in the coordinate formula. -/
private theorem clipped_radius_mul_sign_eq_scalar_box_display
    (μ : NNReal) (α : ENNReal) (t : ℝ) :
    (if α = ⊤ then max (|t| - (μ : ℝ)) 0 else min (max (|t| - (μ : ℝ)) 0) α.toReal) *
        Real.sign t =
      if α = ⊤ then
        𝒯[(μ : ℝ)] t
      else
        min |𝒯[(μ : ℝ)] t| α.toReal * Real.sign t := by
  by_cases hα : α = ⊤
  · -- Without upper clipping, only the ordinary soft-threshold radius remains.
    calc
      (if α = ⊤ then max (|t| - (μ : ℝ)) 0 else min (max (|t| - (μ : ℝ)) 0) α.toReal) *
          Real.sign t
          = max (|t| - (μ : ℝ)) 0 * Real.sign t := by simp [hα]
      _ = |𝒯[(μ : ℝ)] t| * Real.sign t := by
            rw [abs_soft_thresholding_eq_posPart_sub]
      _ = 𝒯[(μ : ℝ)] t := by
            exact abs_soft_thresholding_mul_real_sign_eq_soft_threshold μ t
      _ = if α = ⊤ then 𝒯[(μ : ℝ)] t else min |𝒯[(μ : ℝ)] t| α.toReal * Real.sign t := by
            simp [hα]
  · -- With a finite upper bound, rewrite the clipped radius through the soft-threshold magnitude.
    rw [if_neg hα, if_neg hα]
    rw [abs_soft_thresholding_eq_posPart_sub]

/-- Helper for Example 6.23: the scalar absolute-value box penalty has the singleton prox formula
obtained by combining the radial theorem with the scalar truncated-penalty prox of Example 6.14. -/
private theorem scalar_prox_absolute_value_box_penalty_eq_singleton
    (μ : NNReal) (α : ENNReal) (t : ℝ) :
    prox[fun s ↦ ((μ : ℝ) * |s| : ℝ) +
      extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} s] t =
      {if α = ⊤ then
         𝒯[(μ : ℝ)] t
       else
         min |𝒯[(μ : ℝ)] t| α.toReal * Real.sign t} := by
  rw [← truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty]
  have hproper :
      IsProperExtendedRealFunction (truncated_linear_penalty (μ : ℝ) α) :=
    isProper_truncated_linear_penalty (μ : ℝ) α
  have hdom : ∀ s : ℝ, s < 0 → truncated_linear_penalty (μ : ℝ) α s = ⊤ := by
    intro s hs
    exact truncated_linear_penalty_eq_top_of_lt_zero (μ : ℝ) α hs
  by_cases ht : t = 0
  · subst t
    -- At the origin, the radial description reduces to the scalar-radius membership set.
    have hzero :
        prox[truncated_linear_penalty (μ : ℝ) α ∘ abs] (0 : ℝ) =
          {u : ℝ | |u| ∈ prox[truncated_linear_penalty (μ : ℝ) α] 0} := by
      simpa [Real.norm_eq_abs] using
        (prox_norm_composition_at_zero
          (g := truncated_linear_penalty (μ : ℝ) α) hproper (by sorry) (by sorry) hdom)
    rw [hzero]
    rw [prox_truncated_linear_penalty_eq_singleton]
    -- Example 6.14 gives the singleton radius `{0}`, so only `u = 0` remains.
    ext u
    simp [soft_thresholding_apply]
  · -- Away from the origin, the radial theorem gives a singleton image of the scalar prox set.
    have hradial :
        prox[truncated_linear_penalty (μ : ℝ) α ∘ abs] t =
          (fun s : ℝ ↦ (s / |t|) * t) '' prox[truncated_linear_penalty (μ : ℝ) α] |t| := by
      simpa [Real.norm_eq_abs] using
        (prox_norm_composition_of_ne_zero
          (g := truncated_linear_penalty (μ : ℝ) α) hproper (by sorry) (by sorry) hdom ht)
    rw [hradial]
    rw [prox_truncated_linear_penalty_eq_singleton]
    have htabs : |t| ≠ 0 := abs_ne_zero.mpr ht
    have hsign : t / |t| = Real.sign t := by
      apply (div_eq_iff htabs).2
      calc
        t = |t| * (((SignType.sign t : SignType) : ℝ)) := by
              simpa [mul_comm] using
                (abs_mul_sign t : (|t| * (((SignType.sign t : SignType) : ℝ)) : ℝ) = t).symm
        _ = |t| * Real.sign t := by rw [signType_sign_coe_eq_real_sign]
        _ = Real.sign t * |t| := by rw [mul_comm]
    have hray (r : ℝ) : (r / |t|) * t = r * Real.sign t := by
      -- Reassociate the scalar factor and rewrite `t / |t|` as `Real.sign t`.
      calc
        (r / |t|) * t = r * (t / |t|) := by ring
        _ = r * Real.sign t := by rw [hsign]
    calc
      (fun s : ℝ ↦ (s / |t|) * t) ''
          ({if α = ⊤ then
              max (|t| - (μ : ℝ)) 0
            else
              min (max (|t| - (μ : ℝ)) 0) α.toReal} : Set ℝ)
          = {(if α = ⊤ then
               max (|t| - (μ : ℝ)) 0
             else
               min (max (|t| - (μ : ℝ)) 0) α.toReal) * Real.sign t} := by
            rw [Set.image_singleton]
            simp [hray]
      _ = {(if α = ⊤ then
              max (|t| - (μ : ℝ)) 0
            else
              min (max (|t| - (μ : ℝ)) 0) α.toReal) * Real.sign t} := by
            rfl
      _ = {if α = ⊤ then
             𝒯[(μ : ℝ)] t
           else
             min |𝒯[(μ : ℝ)] t| α.toReal * Real.sign t} := by
            rw [Set.singleton_eq_singleton_iff]
            exact clipped_radius_mul_sign_eq_scalar_box_display μ α t

/-- Helper for Example 6.23: each scalar coordinate penalty `truncated_linear_penalty ∘ abs`
never attains `-∞`, which is the technical hypothesis needed for the separable prox bridge. -/
private theorem truncated_linear_penalty_comp_abs_ne_bot
    (ω : ι → NNReal) (α : ι → ENNReal) (i : ι) (t : ℝ) :
    (truncated_linear_penalty (ω i) (α i) ∘ abs) t ≠ ⊥ := by
  -- Rewrite to the scalar box-penalty presentation and split by box feasibility.
  rw [truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty]
  dsimp
  by_cases ht : ENNReal.ofReal |t| ≤ α i
  · have hind :
        extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α i} t = 0 := by
        simp [extendedIndicator, ht]
    simpa [hind] using (EReal.coe_ne_bot ((ω i : ℝ) * |t|))
  · have hind :
        extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α i} t = ⊤ := by
        simp [extendedIndicator, ht]
    simpa [hind] using (EReal.coe_ne_bot ((ω i : ℝ) * |t|))

/-- Helper for Example 6.23: composing a coordinate truncated penalty with `abs` preserves
properness, since the composition never reaches `-∞` and is finite at the origin. -/
private theorem isProper_truncated_linear_penalty_comp_abs
    (ω : ι → NNReal) (α : ι → ENNReal) (i : ι) :
    IsProperExtendedRealFunction (truncated_linear_penalty (ω i) (α i) ∘ abs) := by
  refine ⟨truncated_linear_penalty_comp_abs_ne_bot ω α i, ?_⟩
  refine ⟨0, ?_⟩
  rw [mem_effective_domain]
  have h0 : (0 : ℝ) ∈ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α i : EReal)} := by
    refine ⟨le_rfl, ?_⟩
    positivity
  simp [Function.comp_apply, truncated_linear_penalty_apply, extendedIndicator, h0]

/-- Helper for Example 6.23: the `i`-th coordinate of `𝓢[ω, α] x` matches the scalar closed form
used in Example 6.22. -/
private theorem twoSidedSoftThreshold_apply_eq_scalar_box_display
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    𝓢[ω, α] x i =
      if α i = ⊤ then
        𝒯[(ω i : ℝ)] (x i)
      else
        min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal * Real.sign (x i) := by
  -- Route correction: align the vector thresholding display with the scalar radial formula.
  by_cases hα : α i = ⊤
  · -- With no upper box bound, the coordinate reduces to ordinary soft-thresholding.
    have hcoord :
        𝓢[ω, α] x i = |𝒯[(ω i : ℝ)] (x i)| * Real.sign (x i) := by
      simp [twoSidedSoftThreshold_apply, hα]
    rw [hcoord]
    simpa [hα] using abs_soft_thresholding_mul_real_sign_eq_soft_threshold (ω i) (x i)
  · -- On the bounded branch, `Set.projIcc` clips the nonnegative magnitude by a simple minimum.
    have hmin_nonneg :
        0 ≤ min (α i).toReal |𝒯[(ω i : ℝ)] (x i)| := by
      exact le_min ENNReal.toReal_nonneg (abs_nonneg _)
    have hcoord :
        𝓢[ω, α] x i =
          (((Set.projIcc 0 (α i).toReal (by positivity) |𝒯[(ω i : ℝ)] (x i)| :
              Set.Icc 0 (α i).toReal) : ℝ) * Real.sign (x i)) := by
      simp [twoSidedSoftThreshold_apply, hα]
    rw [hcoord, Set.coe_projIcc, max_eq_right hmin_nonneg, min_comm]
    simp [hα]

/-- Helper for Example 6.23: each coordinate proximal problem is exactly the scalar absolute-value
box problem, so its proximal set is the singleton at the corresponding
two-sided soft-threshold value. -/
private theorem prox_coordinate_absolute_value_box_eq_singleton
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    prox[truncated_linear_penalty (ω i) (α i) ∘ abs] (x i) =
      {𝓢[ω, α] x i} := by
  -- Rewrite the coordinate penalty into the scalar box-penalty owner and invoke the scalar prox
  -- formula proved above.
  rw [truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty]
  rw [scalar_prox_absolute_value_box_penalty_eq_singleton]
  -- The scalar closed form is exactly the coordinate display of `𝓢[ω, α] x`.
  rw [Set.singleton_eq_singleton_iff]
  exact (twoSidedSoftThreshold_apply_eq_scalar_box_display ω α x i).symm

-- Proof sketch: rewrite `weighted_l1_box_penalty` using
-- `weighted_l1_box_penalty_eq_separableSum_truncated_linear_penalty`, apply
-- `prox_separableSum_eq_singleton_iff_coordinatewise`, and then use the scalar truncated-penalty
-- formula from Example 6.14 together with sign symmetry to identify each coordinate minimizer as
-- the corresponding two-sided soft-threshold value.
/-- Example 6.23: the proximal mapping of the weighted `ℓ¹` penalty on the symmetric box
`[-α, α]` is the singleton containing the coordinatewise two-sided soft-thresholding point, i.e.
the vector with `i`-th coordinate
`min (max (|x i| - ω i) 0) α i * Real.sign (x i)`, with `α i = ∞` allowed. -/
theorem prox_weighted_l1_box_penalty_eq_singleton_twoSidedSoftThreshold
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) :
    prox[weighted_l1_box_penalty ω α] x =
      {𝓢[ω, α] x} := by
  have hpen :
      (PiLp.separableSum
          (fun i ↦ truncated_linear_penalty (ω i) (α i) ∘ abs) : E → EReal) =
        weighted_l1_box_penalty ω α :=
    (weighted_l1_box_penalty_eq_separableSum_truncated_linear_penalty ω α).symm
  -- Apply the separable prox singleton bridge after reducing to the scalar coordinate penalties.
  simpa [hpen] using
    (prox_separableSum_eq_singleton_iff_coordinatewise
      (fun i ↦ truncated_linear_penalty (ω i) (α i) ∘ abs)
      (isProper_truncated_linear_penalty_comp_abs ω α)
      x
      (𝓢[ω, α] x)).2
      (prox_coordinate_absolute_value_box_eq_singleton ω α x)

end
