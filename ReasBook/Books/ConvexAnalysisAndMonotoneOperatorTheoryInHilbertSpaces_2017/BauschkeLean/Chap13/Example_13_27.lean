import Mathlib
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Example_12_2
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Example_13_8
import BauschkeLean.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Metric

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- Helper for Example 13 27: after coercion to `EReal`, the real-valued distance to a nonempty
set agrees with the indicator-plus-norm infimal convolution. -/
private theorem infDist_eq_indicator_infimalConvolution_norm
    (C : Set H) (hC_nonempty : C.Nonempty) :
    (fun x : H ↦ Metric.infDist x C).toEReal.asEReal = ι[C] □ norm.toEReal := by
  have hkernel : scaledNormKernel (H := H) (1 : NNReal) = norm.toEReal := by
    funext x
    apply Subtype.ext
    simp [scaledNormKernel_apply, Function.toEReal_apply]
  funext x
  have hdist : (Metric.infEDist x C : EReal) = ((Metric.infDist x C : ℝ) : EReal) := by
    rw [Metric.infDist]
    symm
    exact EReal.coe_ennreal_toReal (Metric.infEDist_ne_top (x := x) hC_nonempty)
  -- Rewrite Example 12.2 from `infEDist` and the scaled norm kernel to the present `infDist`
  -- formulation.
  calc
    ((Metric.infDist x C : ℝ) : EReal) = (Metric.infEDist x C : EReal) := hdist.symm
    _ = (ι[C] □ scaledNormKernel (1 : NNReal)) x := by
      simpa using congrFun (distanceToSet_eq_indicator_infimalConvolution_norm (C := C)) x
    _ = (ι[C] □ norm.toEReal) x := by
      rw [hkernel]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Example 13 27: adding two indicators gives the indicator of the intersection. -/
private theorem indicator_add_eq_indicator_inter
    (A B : Set H) :
    (ι[A]).asEReal + (ι[B]).asEReal = (ι[A ∩ B]).asEReal := by
  funext x
  by_cases hA : x ∈ A
  · by_cases hB : x ∈ B
    · simp [indicator_apply, hA, hB]
    · simp [indicator_apply, hA, hB]
  · by_cases hB : x ∈ B
    · simp [indicator_apply, hA, hB]
    · simp [indicator_apply, hA, hB]

/-- Helper for Example 13 27: on `ℝ`, the Fenchel conjugate body rewrites to the scalar supremum
`sup_x (ux - f x)`. -/
@[simp] private theorem conjugate_apply_real (f : ℝ → EReal) (u : ℝ) :
    f∗ u = sSup (Set.range fun x : ℝ ↦ ((u * x : ℝ) : EReal) - f x) := by
  -- Rewrite the indexed supremum from `conjugate_apply` as an `sSup` over its scalar range.
  rw [conjugate_apply, ← sSup_range]
  congr with x

/-- Helper for Example 13 27: an `sSup` equals `a` when every value is bounded above by `a` and
every strict lower bound of `a` is exceeded somewhere in the range. -/
private theorem supremum_eq_of_pointwise_le_and_dense_lower_bounds
    (g : ℝ → EReal) (a : EReal) (h_upper : ∀ x, g x ≤ a)
    (h_lower : ∀ z, z < a → ∃ x, z < g x) :
    sSup (Set.range g) = a := by
  -- Apply the standard `sSup` characterization directly to the range of `g`.
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact h_upper x
  · intro z hz
    rcases h_lower z hz with ⟨x, hx⟩
    exact ⟨g x, ⟨x, rfl⟩, hx⟩

/-- Helper for Example 13 27: the Young-extremizing point
`sign(u) * |u|^(Real.conjExponent p - 1)` attains the value `|u|^(Real.conjExponent p) /
Real.conjExponent p`. -/
private theorem power_conjugate_maximizer_value
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    let q := Real.conjExponent p
    let x0 := Real.sign u * |u| ^ (q - 1)
    u * x0 - |x0| ^ p / p = |u| ^ q / q := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  have hp_ne : p ≠ 0 := hpq.ne_zero
  have hq_ne : q ≠ 0 := hpq.symm.ne_zero
  have hcoeff : 1 - 1 / p = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hqp : (q - 1) * p = q := by
    calc
      (q - 1) * p = (q / p) * p := by rw [hpq.symm.div_conj_eq_sub_one]
      _ = q := by field_simp [hp_ne]
  rcases eq_or_ne u 0 with rfl | hu0
  · have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hpq.symm.sub_one_pos
    -- At the origin both the maximizer and the optimal value are zero.
    simp [q, hp_ne, hq_ne, hq_sub_ne]
  · rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
    · have hu_abs : |u| = -u := abs_of_neg hu_neg
      have hu_pos' : 0 < -u := by linarith
      have hu_nonneg' : 0 ≤ -u := hu_pos'.le
      have hu_mul_pow : u * (-((-u) ^ (q - 1))) = (-u) ^ q := by
        -- On the negative branch the maximizing point has the opposite sign.
        calc
          u * (-((-u) ^ (q - 1))) = (-u) * (-u) ^ (q - 1) := by ring
          _ = (-u) ^ (1 : ℝ) * (-u) ^ (q - 1) := by rw [Real.rpow_one]
          _ = (-u) ^ q := by
            calc
              (-u) ^ (1 : ℝ) * (-u) ^ (q - 1) = (-u) ^ ((1 : ℝ) + (q - 1)) := by
                exact (Real.rpow_add hu_pos' (1 : ℝ) (q - 1)).symm
              _ = (-u) ^ q := by congr 1; ring
      have hpow : ((-u) ^ (q - 1)) ^ p = (-u) ^ q := by
        rw [← Real.rpow_mul hu_nonneg' (q - 1) p, hqp]
      -- Substitute the negative-branch maximizer and simplify the Holder coefficient.
      calc
        u * x0 - |x0| ^ p / p = u * (-((-u) ^ (q - 1))) - ((-u) ^ (q - 1)) ^ p / p := by
          simp [x0, hu_abs, Real.sign_of_neg hu_neg,
            abs_of_nonneg (Real.rpow_nonneg hu_nonneg' _)]
        _ = (-u) ^ q - (-u) ^ q / p := by rw [hu_mul_pow, hpow]
        _ = (-u) ^ q * (1 - 1 / p) := by ring
        _ = (-u) ^ q * (1 / q) := by rw [hcoeff]
        _ = (-u) ^ q / q := by ring
        _ = |u| ^ q / q := by simp [hu_abs]
    · have hu_abs : |u| = u := abs_of_pos hu_pos
      have hu_nonneg : 0 ≤ u := hu_pos.le
      have hu_mul_pow : u * u ^ (q - 1) = u ^ q := by
        -- On the positive branch the maximizing point is the usual positive power.
        calc
          u * u ^ (q - 1) = u ^ (1 : ℝ) * u ^ (q - 1) := by rw [Real.rpow_one]
          _ = u ^ q := by
            calc
              u ^ (1 : ℝ) * u ^ (q - 1) = u ^ ((1 : ℝ) + (q - 1)) := by
                exact (Real.rpow_add hu_pos (1 : ℝ) (q - 1)).symm
              _ = u ^ q := by congr 1; ring
      have hpow : (u ^ (q - 1)) ^ p = u ^ q := by
        rw [← Real.rpow_mul hu_nonneg (q - 1) p, hqp]
      -- Substitute the positive-branch maximizer and simplify the Holder coefficient.
      calc
        u * x0 - |x0| ^ p / p = u * u ^ (q - 1) - (u ^ (q - 1)) ^ p / p := by
          simp [x0, hu_abs, Real.sign_of_pos hu_pos,
            abs_of_nonneg (Real.rpow_nonneg hu_nonneg _)]
        _ = u ^ q - u ^ q / p := by rw [hu_mul_pow, hpow]
        _ = u ^ q * (1 - 1 / p) := by ring
        _ = u ^ q * (1 / q) := by rw [hcoeff]
        _ = u ^ q / q := by ring
        _ = |u| ^ q / q := by simp [hu_abs]

/-- Helper for Example 13 27: the scalar conjugate of `x ↦ |x|^p / p` is
`u ↦ |u|^(p*) / p*`. -/
private theorem conjugate_absRpowDivided
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    ((fun x : ℝ ↦ |x| ^ p / p).toEReal.asEReal)∗ u =
      ((fun x : ℝ ↦ |x| ^ Real.conjExponent p / Real.conjExponent p).toEReal.asEReal) u := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  rw [conjugate_apply_real]
  simp only [Function.asEReal_apply, Function.toEReal_apply]
  -- Bound the scalar defect above by Young's inequality and attain the bound at the extremizer.
  refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
      (fun x : ℝ ↦ ((u * x : ℝ) : EReal) - ((|x| ^ p / p : ℝ) : EReal))
      ((|u| ^ q / q : ℝ) : EReal) ?_ ?_
  · intro x
    have hmul : u * x ≤ |x| * |u| := by
      calc
        u * x ≤ |u * x| := le_abs_self (u * x)
        _ = |u| * |x| := by rw [abs_mul]
        _ = |x| * |u| := by ring
    have hyoung :
        |x| * |u| ≤ |x| ^ p / p + |u| ^ q / q := by
      simpa [q, abs_abs] using
        Real.young_inequality_of_nonneg (abs_nonneg x) (abs_nonneg u) hpq
    have hreal : u * x - |x| ^ p / p ≤ |u| ^ q / q := by
      linarith
    have hEReal :
        ((u * x - |x| ^ p / p : ℝ) : EReal) ≤ ((|u| ^ q / q : ℝ) : EReal) :=
      EReal.coe_le_coe hreal
    simpa [sub_eq_add_neg, ← EReal.coe_sub] using hEReal
  · intro z hz
    have hvalue_real : u * x0 - |x0| ^ p / p = |u| ^ q / q := by
      simpa [q, x0] using power_conjugate_maximizer_value p hp u
    have hvalue :
        (((u * x0 : ℝ) : EReal) - ((|x0| ^ p / p : ℝ) : EReal)) =
          ((|u| ^ q / q : ℝ) : EReal) := by
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using
        congrArg (fun t : ℝ ↦ (t : EReal)) hvalue_real
    exact ⟨x0, hz.trans_eq hvalue.symm⟩

/-- Helper for Example 13 27: the support function of the singleton `{0}` is the zero function. -/
private theorem supportFunction_singleton_zero_eq_zero :
    σ[({0} : Set H)] = fun _ : H ↦ (0 : EReal) := by
  ext u
  -- The image of `{0}` under the pairing map is `{0}`, so the support supremum is zero.
  rw [supportFunction_eq_sSup_image]
  simp

/-- Helper for Example 13 27: the conjugate of `x ↦ ‖x‖^p / p` is the norm power with conjugate
exponent. -/
private theorem conjugate_normPowerDivided_eq_normPowerDivided_conjugateExponent_aux
    (p : ℝ) (hp : 1 < p) :
    (fun x : H ↦ ‖x‖ ^ p / p).toEReal.asEReal∗ =
      (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := by
  let φ : ℝ → Set.Ioi (⊥ : EReal) := (fun t : ℝ ↦ |t| ^ p / p).toEReal
  have hφ_even : Function.Even φ := by
    intro t
    apply Subtype.ext
    simp [φ, abs_neg]
  have hrewrite :
      (fun x : H ↦ ‖x‖ ^ p / p).toEReal.asEReal = (φ ∘ norm).asEReal := by
    funext x
    simp [φ, abs_of_nonneg (norm_nonneg x)]
  have hscalar :
      φ.asEReal∗ ∘ norm =
        (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := by
    funext u
    simpa [φ, abs_of_nonneg (norm_nonneg u)] using
      conjugate_absRpowDivided p hp ‖u‖
  -- Example 13.8 transports the scalar conjugacy from Example 13.2 along the norm.
  rw [hrewrite, conjugate_comp_norm_eq_comp_norm_conjugate_of_even φ hφ_even]
  exact hscalar

omit [InnerProductSpace ℝ H] in
/-- Helper for Example 13 27: the powered distance is the infimal convolution of the indicator of
`C` with the powered norm kernel. -/
private theorem infDistPowerDivided_eq_indicator_infimalConvolution_normPowerDivided
    (C : Set H) (hC_nonempty : C.Nonempty) (p : ℝ) (hp : 1 < p) :
    (fun x : H ↦ Metric.infDist x C ^ p / p).toEReal.asEReal =
      ι[C] □ (fun x : H ↦ ‖x‖ ^ p / p).toEReal := by
  funext x
  simp only [Function.asEReal_apply, Function.toEReal_apply, infimalConvolution_apply]
  have hreduced :
      (⨅ y : H, (ι[C] y : EReal) + ((‖x - y‖ ^ p / p : ℝ) : EReal)) =
        ⨅ y : C, ((‖x - (y : H)‖ ^ p / p : ℝ) : EReal) := by
    apply le_antisymm
    · refine le_iInf ?_
      intro y
      have hle :
          (⨅ z : H, (ι[C] z : EReal) + ((‖x - z‖ ^ p / p : ℝ) : EReal)) ≤
            (ι[C] (y : H) : EReal) + ((‖x - (y : H)‖ ^ p / p : ℝ) : EReal) :=
        iInf_le _ (y : H)
      simpa [indicator_apply, y.property] using hle
    · refine le_iInf ?_
      intro y
      by_cases hy : y ∈ C
      · have hle :
            (⨅ z : C, ((‖x - (z : H)‖ ^ p / p : ℝ) : EReal)) ≤
              ((‖x - ((⟨y, hy⟩ : C) : H)‖ ^ p / p : ℝ) : EReal) :=
          iInf_le _ (⟨y, hy⟩ : C)
        simpa [indicator_apply, hy] using hle
      · have hle : (⨅ z : C, ((‖x - (z : H)‖ ^ p / p : ℝ) : EReal)) ≤ ⊤ := le_top
        have hle' :
            (⨅ z : C, ((‖x - (z : H)‖ ^ p / p : ℝ) : EReal)) ≤
              (ι[C] y : EReal) + ((‖x - y‖ ^ p / p : ℝ) : EReal) := by
          convert hle using 1
          simp [indicator_apply, hy]
        exact hle'
  let _ : Nonempty C := hC_nonempty.to_subtype
  let φ : ℝ → ℝ := fun t ↦ (max t 0) ^ p / p
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hφ_cont : Continuous φ := by
    have hmax : Continuous fun t : ℝ ↦ max t 0 := continuous_id.max continuous_const
    have hrpow : Continuous fun t : ℝ ↦ (max t 0) ^ p :=
      hmax.rpow_const fun _ ↦ Or.inr hp_pos.le
    exact hrpow.div_const p
  have hφ_mono : Monotone φ := by
    intro a b hab
    have hmax : max a 0 ≤ max b 0 := max_le_max hab le_rfl
    have hrpow :
        (max a 0) ^ p ≤ (max b 0) ^ p :=
      (Real.strictMonoOn_rpow_Ici_of_exponent_pos hp_pos).monotoneOn
        (le_max_right a 0)
        (le_max_right b 0)
        hmax
    exact div_le_div_of_nonneg_right hrpow hp_pos.le
  have hbdd : BddBelow (Set.range fun y : C ↦ dist x (y : H)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact dist_nonneg
  have hmap :
      φ (⨅ y : C, dist x (y : H)) = ⨅ y : C, φ (dist x (y : H)) := by
    refine Monotone.map_ciInf_of_continuousAt hφ_cont.continuousAt hφ_mono ?_
    exact hbdd
  have hinf_nonneg : 0 ≤ ⨅ y : C, dist x (y : H) := by
    refine le_ciInf ?_
    intro y
    exact dist_nonneg
  let f : ℝ → EReal := fun t ↦ ((φ t : ℝ) : EReal)
  have hf_cont : ContinuousAt f (⨅ y : C, dist x (y : H)) := by
    -- First use continuity of the real cutoff-power map, then coerce to `EReal`.
    dsimp [f]
    exact continuous_coe_real_ereal.continuousAt.comp hφ_cont.continuousAt
  have hf_mono : Monotone f := by
    intro a b hab
    change ((φ a : ℝ) : EReal) ≤ ((φ b : ℝ) : EReal)
    exact_mod_cast hφ_mono hab
  have hpowEq :
      ((Metric.infDist x C ^ p / p : ℝ) : EReal) =
        ⨅ y : C, ((‖x - (y : H)‖ ^ p / p : ℝ) : EReal) := by
    -- Apply the cutoff-power map directly at the `EReal` level to avoid extra coercion lemmas.
    calc
      ((Metric.infDist x C ^ p / p : ℝ) : EReal) = f (⨅ y : C, dist x (y : H)) := by
        rw [Metric.infDist_eq_iInf]
        simp [f, φ, max_eq_left hinf_nonneg]
      _ = ⨅ y : C, f (dist x (y : H)) := by
        refine Monotone.map_ciInf_of_continuousAt hf_cont hf_mono ?_
        exact hbdd
      _ = ⨅ y : C, ((‖x - (y : H)‖ ^ p / p : ℝ) : EReal) := by
        refine iInf_congr fun y ↦ ?_
        simp [f, φ, dist_eq_norm]
  -- Convert the real infimum formula to `EReal` and then restore the unconstrained infimum.
  calc
    ((Metric.infDist x C ^ p / p : ℝ) : EReal) =
        ⨅ y : C, ((‖x - (y : H)‖ ^ p / p : ℝ) : EReal) := by
          exact hpowEq
    _ = (⨅ y : H, (ι[C] y : EReal) + ((‖x - y‖ ^ p / p : ℝ) : EReal)) := hreduced.symm

-- Proof sketch: rewrite `Metric.infDist` through the source-facing distance decomposition from
-- Example 12.2, then apply Proposition 13.24(i), Example 13.3(i), and Example 13.3(v). The
-- resulting support function already depends only on the underlying set `C`.
/-- Example 13 27 (1): if `C` is a nonempty subset of `H`, then the Fenchel
conjugate of the distance function `d_C` is the support function `σ[C]` plus the indicator of the
closed unit ball `B(0;1)`. -/
theorem fenchelConjugate_infDist_eq_supportFunction_add_indicator_closedUnitBall
    (C : Set H) (hC_nonempty : C.Nonempty) :
    (fun x : H ↦ Metric.infDist x C).toEReal.asEReal∗ =
      σ[C] + (ι[closedBall (0 : H) 1]).asEReal := by
  have hnorm :
      norm.toEReal.asEReal∗ = (ι[closedBall (0 : H) 1]).asEReal := by
    simpa [Function.asEReal_apply, Function.toEReal_apply] using
      (conjugate_norm_eq_indicator_closedUnitBall (H := H))
  -- Rewrite the distance function as the indicator-plus-norm infimal convolution from Example
  -- 12.2 in the `infDist` form used here.
  rw [infDist_eq_indicator_infimalConvolution_norm C hC_nonempty]
  -- Proposition 13.24(i) and Example 13.3 identify the two conjugate factors.
  rw [conjugate_infimalConvolution_eq]
  rw [conjugate_indicator_eq_supportFunction]
  rw [hnorm]

-- Proof sketch: specialize clause (1) to the underlying set of `V`, rewrite the support function
-- using Example 13.3(iii), and combine the two indicators into the indicator of the intersection
-- `Vᗮ ∩ B(0;1)`.
/-- Example 13 27 (2): if `V` is a linear subspace of `H`, then the Fenchel conjugate of
the distance function `d_V` is the indicator of `Vᗮ ∩ B(0;1)`. -/
theorem fenchelConjugate_infDist_submodule_eq_indicator_orthogonal_inter_closedUnitBall
    (V : Submodule ℝ H) :
    (fun x : H ↦ Metric.infDist x (↑V : Set H)).toEReal.asEReal∗ =
      (ι[((↑Vᗮ : Set H) ∩ closedBall (0 : H) 1)]).asEReal := by
  have hV_nonempty : (↑V : Set H).Nonempty := ⟨0, V.zero_mem⟩
  -- Specialize clause (1) to the underlying set of the submodule.
  rw [fenchelConjugate_infDist_eq_supportFunction_add_indicator_closedUnitBall
    (C := (↑V : Set H)) hV_nonempty]
  -- Rewrite the support function of `V` as the indicator of `Vᗮ`.
  rw [← conjugate_indicator_eq_supportFunction (C := (↑V : Set H))]
  rw [conjugate_indicator_submodule_eq_indicator_orthogonal]
  -- Collapse the two indicators into the indicator of the intersection.
  rw [indicator_add_eq_indicator_inter]

-- Proof sketch: combine the distance-to-set infimal-convolution identity from Example 12.2 with
-- Proposition 13.24(i), Example 13.3(i), and the scalar/radial conjugacy formulas from
-- Example 13.2(i) and Example 13.8.
/-- Example 13 27 (3): if `C` is a nonempty subset of `H` and `p ∈ ]1,+∞[`, then
the Fenchel conjugate of `x ↦ d(x,C)^p / p` is `σ[C] + ‖·‖^(p*) / p*`, where
`p* = Real.conjExponent p = p / (p - 1)`. -/
theorem fenchelConjugate_infDistPowerDivided_eq_supportFunction_add_normPowerDivided
    (C : Set H) (hC_nonempty : C.Nonempty) (p : ℝ) (hp : 1 < p) :
    (fun x : H ↦ Metric.infDist x C ^ p / p).toEReal.asEReal∗ =
      σ[C] + (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := by
  -- Rewrite the powered distance as the indicator-plus-powered-norm infimal convolution.
  rw [infDistPowerDivided_eq_indicator_infimalConvolution_normPowerDivided C hC_nonempty p hp]
  -- Proposition 13.24(i), Example 13.3(i), and the norm-power conjugacy identify the two factors.
  rw [conjugate_infimalConvolution_eq]
  rw [conjugate_indicator_eq_supportFunction]
  rw [conjugate_normPowerDivided_eq_normPowerDivided_conjugateExponent_aux p hp]

-- Proof sketch: specialize clause (3) to the singleton `{0}` and use `Metric.infDist x {0} = ‖x‖`
-- to identify the distance-to-singleton formula with the norm-power formula.
/-- Example 13 27 (4): for `p ∈ ]1,+∞[`, the Fenchel conjugate of `x ↦ ‖x‖^p / p` is
`u ↦ ‖u‖^(p*) / p*`, where `p* = Real.conjExponent p = p / (p - 1)`. -/
theorem fenchelConjugate_normPowerDivided_eq_normPowerDivided_conjugateExponent
    (p : ℝ) (hp : 1 < p) :
    (fun x : H ↦ ‖x‖ ^ p / p).toEReal.asEReal∗ =
      (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := by
  have hsingleton : ({0} : Set H).Nonempty := ⟨0, by simp⟩
  have hmain :
      (fun x : H ↦ Metric.infDist x ({0} : Set H) ^ p / p).toEReal.asEReal∗ =
        σ[({0} : Set H)] +
          (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal :=
    fenchelConjugate_infDistPowerDivided_eq_supportFunction_add_normPowerDivided
      (C := ({0} : Set H)) hsingleton p hp
  have hzero :
      (fun _ : H ↦ (0 : EReal)) +
        (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal =
          (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := by
    funext u
    simp
  -- Specialize clause (3) to `{0}` and simplify the distance and support-function terms.
  rw [supportFunction_singleton_zero_eq_zero] at hmain
  calc
    (fun x : H ↦ ‖x‖ ^ p / p).toEReal.asEReal∗ =
        (fun _ : H ↦ (0 : EReal)) +
          (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := by
            simpa [Metric.infDist_singleton, dist_eq_norm] using hmain
    _ = (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := hzero

end Conjugation

end ERealFunction
