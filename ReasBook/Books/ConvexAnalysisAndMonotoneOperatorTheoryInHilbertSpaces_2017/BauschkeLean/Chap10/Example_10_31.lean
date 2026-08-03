import BauschkeLean.Chap08.Example_8_23
import BauschkeLean.Chap10.Example_10_30

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

section StrictConvex

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [StrictConvexSpace ℝ H]

/-- Helper for Example 10.31: every element of `Set.range (norm : H → ℝ)` is nonnegative. -/
lemma normRange_nonneg (t : Set.range (norm : H → ℝ)) : 0 ≤ (t : ℝ) := by
  -- Unpack the range witness and reduce to the nonnegativity of the norm.
  rcases t.2 with ⟨x, hx⟩
  simpa [hx] using (norm_nonneg x)

/-- Helper for Example 10.31: squaring is monotone on the range of `norm`. -/
lemma normRangeSquareMonotone :
    Monotone (fun t : Set.range (norm : H → ℝ) ↦ (t : ℝ) ^ (2 : ℝ)) := by
  -- The range of the norm lives in `[0, +∞)`, where `Real.rpow` is monotone.
  intro a b hab
  exact Real.rpow_le_rpow (normRange_nonneg a) hab zero_le_two

/-- Helper for Example 10.31: `t ↦ t ^ p` is strictly increasing on the range of `norm` when
`0 < p`. -/
lemma normRangeRpowStrictMono (p : ℝ) (hp : 0 < p) :
    StrictMono (fun t : Set.range (norm : H → ℝ) ↦ (t : ℝ) ^ p) := by
  -- Positive powers are strictly increasing on nonnegative reals.
  intro a b hab
  exact Real.rpow_lt_rpow (normRange_nonneg a) hab hp

-- Proof sketch: first apply Example 10.30(2) with the monotone range map `t ↦ t ^ 2` to recover
-- strict quasiconvexity of the norm from the strict convexity of `x ↦ ‖x‖ ^ 2`.
-- Then compose with the strictly increasing range map `t ↦ t ^ p` via Example 10.30(1).
/-- Example 10.31 (1): clause (i). On a strictly convex real normed space, for `p > 0`, the
norm-power function is strictly quasiconvex. -/
theorem strictlyQuasiconvex_norm_rpow (p : ℝ) (hp : 0 < p) :
    StrictlyQuasiconvex ((fun x : H ↦ ‖x‖ ^ p).toEReal.asEReal) := by
  let square : Set.range (norm : H → ℝ) → ℝ := fun t ↦ (t : ℝ) ^ (2 : ℝ)
  -- First recover the norm case from the strictly convex square.
  have hnorm : StrictlyQuasiconvex ((norm : H → ℝ).toEReal.asEReal) := by
    simpa [square, Function.comp_def] using
      (strictlyQuasiconvex_of_strictConvexOn_comp_range
        (f := norm) (φ := square) normRangeSquareMonotone
        (by
          simpa [square, Function.comp_def] using
            (strictConvexOn_norm_rpow (H := H) (p := (2 : ℝ)) one_lt_two)))
  let power : Set.range (norm : H → ℝ) → ℝ := fun t ↦ (t : ℝ) ^ p
  -- Then transport strict quasiconvexity through the increasing power map.
  simpa [power, Function.comp_def] using
    (strictlyQuasiconvex_comp_strictMono_range
      (f := norm) (φ := power) hnorm (normRangeRpowStrictMono (H := H) p hp))

-- The norm case is the source-facing specialization `p = 1` of the norm-power statement.
/-- On a strictly convex real normed space, the norm is strictly quasiconvex. -/
theorem strictlyQuasiconvex_norm :
    StrictlyQuasiconvex ((norm : H → ℝ).toEReal.asEReal) := by
  simpa using strictlyQuasiconvex_norm_rpow (1 : ℝ) zero_lt_one

end StrictConvex

section NontrivialNormed

/-- Helper for Example 10.31: the half-ray increment of `t ↦ t ^ p` is nonnegative on
`(1 / 2, +∞)`. -/
lemma halfRayGap_nonneg (p : ℝ) (hp : 0 < p) {s : ℝ} (hs : 1 / 2 < s) :
    0 ≤ (s + 1 / 2) ^ p - s ^ p := by
  -- The positive power map is increasing on nonnegative reals.
  have hs_nonneg : 0 ≤ s := by linarith
  refine sub_nonneg.mpr ?_
  exact Real.rpow_le_rpow hs_nonneg (by linarith) hp.le

/-- Helper for Example 10.31: concavity bounds the half-ray increment by the derivative at the
left endpoint. -/
lemma halfRayGap_le_derivBound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {s : ℝ} (hs : 1 / 2 < s) :
    (s + 1 / 2) ^ p - s ^ p ≤ (p / 2) * s ^ (p - 1) := by
  let f : ℝ → ℝ := fun x ↦ x ^ p
  have hs_pos : 0 < s := by linarith
  have hs_mem : s ∈ Set.Ici (0 : ℝ) := hs_pos.le
  have hs' : s + 1 / 2 ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ s + 1 / 2
    linarith
  have hs_lt : s < s + 1 / 2 := by linarith
  have hslope :
      slope f s (s + 1 / 2) ≤ deriv f s := by
    -- Concavity makes secant slopes decrease, so the secant is controlled by the left derivative.
    exact (Real.concaveOn_rpow hp.le hp1.le).slope_le_deriv hs_mem hs' hs_lt
      (Real.differentiableAt_rpow_const_of_ne p hs_pos.ne')
  have hdelta_nonneg : 0 ≤ (s + 1 / 2) - s := by linarith
  have hmul :=
    mul_le_mul_of_nonneg_left hslope hdelta_nonneg
  -- Rewrite the scaled slope as the ray increment, then evaluate the derivative explicitly.
  calc
    (s + 1 / 2) ^ p - s ^ p = ((s + 1 / 2) - s) * slope f s (s + 1 / 2) := by
      simpa [f] using (sub_smul_slope f s (s + 1 / 2)).symm
    _ ≤ ((s + 1 / 2) - s) * deriv f s := hmul
    _ = (1 / 2 : ℝ) * (p * s ^ (p - 1)) := by
      rw [Real.deriv_rpow_const]
      ring
    _ = (p / 2) * s ^ (p - 1) := by ring

/-- Helper for Example 10.31: the half-ray increment of `t ↦ t ^ p` tends to `0` at `+∞` when
`0 < p < 1`. -/
lemma tendstoAddHalfRpowSubRpowZero (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun s : ℝ ↦ (s + 1 / 2) ^ p - s ^ p) Filter.atTop (nhds 0) := by
  have hupper :
      Filter.Tendsto (fun s : ℝ ↦ (p / 2) * s ^ (p - 1)) Filter.atTop (nhds 0) := by
    have hp_sub : 0 < 1 - p := by linarith
    have hpow : Filter.Tendsto (fun s : ℝ ↦ s ^ (p - 1)) Filter.atTop (nhds 0) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (tendsto_rpow_neg_atTop hp_sub)
    simpa using (tendsto_const_nhds.mul hpow)
  -- Squeeze the increment between `0` and the derivative bound from the previous lemma.
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [show ∀ᶠ s : ℝ in Filter.atTop, 1 / 2 < s from
      Filter.eventually_atTop.2 ⟨1, fun s hs => by linarith⟩] with s hs
    exact halfRayGap_nonneg p hp hs
  · filter_upwards [show ∀ᶠ s : ℝ in Filter.atTop, 1 / 2 < s from
      Filter.eventually_atTop.2 ⟨1, fun s hs => by linarith⟩] with s hs
    exact halfRayGap_le_derivBound p hp hp1 hs

/-- Helper for Example 10.31: uniform quasiconvexity on a unit ray gives a fixed quarter-modulus
lower bound on the half-ray increment. -/
lemma quarterMulModulusOne_le_halfRayGap
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : ℝ) (hp : 0 < p) {φ : NNReal → EReal}
    (hf : UniformlyQuasiconvex ((fun x : H ↦ ‖x‖ ^ p).toEReal.asEReal) φ)
    {z : H} (hz : ‖z‖ = 1) {s : ℝ} (hs : 1 / 2 < s) :
    (((1 / 4 : ℝ) : EReal) * φ 1) ≤ (((s + 1 / 2) ^ p - s ^ p : ℝ) : EReal) := by
  let x : H := (s - 1 / 2) • z
  let y : H := (s + 1 / 2) • z
  have hs_sub_nonneg : 0 ≤ s - 1 / 2 := by linarith
  have hs_add_nonneg : 0 ≤ s + 1 / 2 := by linarith
  have hmid : (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y = s • z := by
    -- The chosen endpoints are symmetric around the midpoint `s • z`.
    calc
      (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
        norm_num
      _ 
          = ((1 / 2 : ℝ) * (s - 1 / 2)) • z + ((1 / 2 : ℝ) * (s + 1 / 2)) • z := by
              simp [x, y, smul_smul]
      _ = (((1 / 2 : ℝ) * (s - 1 / 2) + (1 / 2 : ℝ) * (s + 1 / 2)) : ℝ) • z := by
            rw [← add_smul]
      _ = s • z := by
            congr 1
            ring
  have hdist : ‖x - y‖₊ = 1 := by
    -- Their distance is the fixed unit spacing along the ray generated by `z`.
    have : x - y = (-1 : ℝ) • z := by
      calc
        x - y = ((s - 1 / 2) - (s + 1 / 2) : ℝ) • z := by
          simp [x, y, sub_eq_add_neg, add_smul]
        _ = (-1 : ℝ) • z := by
          congr 1
          ring
    have hznn : ‖z‖₊ = 1 := by
      apply NNReal.eq
      simpa using hz
    rw [this, nnnorm_smul, hznn]
    norm_num
  have hineq := hf.ineq (x := x) (y := y)
    (by simp [ERealFunction.dom])
    (by simp [ERealFunction.dom])
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hquarter : ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))) = 1 / 4 := by
    norm_num
  have hquarterE :
      (((1 / 2 : ℝ) : EReal) * (1 - ((1 / 2 : ℝ) : EReal))) = (((1 / 4 : ℝ) : EReal)) := by
    exact_mod_cast hquarter
  have hquarterMul :
      ((((1 / 2 : ℝ) : EReal) * (1 - ((1 / 2 : ℝ) : EReal))) * φ 1) =
        (((1 / 4 : ℝ) : EReal) * φ 1) := by
    rw [hquarterE]
  have hineq' := hineq
  rw [hmid, hdist] at hineq'
  have hnorm_mid : ‖s • z‖ ^ p = s ^ p := by
    simpa [one_mul] using
      (by rw [norm_smul, hz, Real.norm_of_nonneg (by linarith : 0 ≤ s)] : ‖s • z‖ ^ p = (s * 1) ^ p)
  have hnorm_left : ‖(s - 1 / 2) • z‖ ^ p = (s - 1 / 2) ^ p := by
    simpa [one_mul] using
      (by
        rw [norm_smul, hz, Real.norm_of_nonneg hs_sub_nonneg] :
          ‖(s - 1 / 2) • z‖ ^ p = ((s - 1 / 2) * 1) ^ p)
  have hnorm_right : ‖(s + 1 / 2) • z‖ ^ p = (s + 1 / 2) ^ p := by
    simpa [one_mul] using
      (by
        rw [norm_smul, hz, Real.norm_of_nonneg hs_add_nonneg] :
          ‖(s + 1 / 2) • z‖ ^ p = ((s + 1 / 2) * 1) ^ p)
  have hor :
      (((s ^ p : ℝ) : EReal)) + (((1 / 4 : ℝ) : EReal) * φ 1) ≤
          (((s - 1 / 2) ^ p : ℝ) : EReal) ∨
        (((s ^ p : ℝ) : EReal)) + (((1 / 4 : ℝ) : EReal) * φ 1) ≤
          (((s + 1 / 2) ^ p : ℝ) : EReal) := by
    -- The normalized midpoint estimate is a comparison with one of the two endpoint values.
    rcases (by
      simpa [x, y, Function.toEReal_apply, Function.asEReal_apply] using hineq') with hleft | hright
    · exact Or.inl <| by
        rw [hnorm_mid] at hleft
        norm_num at hleft
        rw [hquarterMul] at hleft
        rw [hnorm_left] at hleft
        exact hleft
    · exact Or.inr <| by
        rw [hnorm_mid] at hright
        norm_num at hright
        rw [hquarterMul] at hright
        rw [hnorm_right] at hright
        exact hright
  have hmain :
      (((s ^ p : ℝ) : EReal)) + (((1 / 4 : ℝ) : EReal) * φ 1) ≤
        (((s + 1 / 2) ^ p : ℝ) : EReal) := by
    -- The right endpoint dominates the left endpoint along the positive ray.
    refine hor.elim ?_ ?_
    · intro hleft
      exact le_trans hleft (by
        exact_mod_cast Real.rpow_le_rpow hs_sub_nonneg (by linarith) hp.le)
    · intro hright
      exact hright
  have hsub :
      (((1 / 4 : ℝ) : EReal) * φ 1) ≤
        (((s + 1 / 2) ^ p : ℝ) : EReal) - (((s ^ p : ℝ) : EReal)) := by
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot (s ^ p)))
      (.inl (EReal.coe_ne_top (s ^ p)))]
    simpa [add_comm, add_left_comm, add_assoc] using hmain
  simpa [EReal.coe_sub] using hsub

-- Proof sketch: evaluate Jensen convexity at a nonzero vector `z` and `0` with a coefficient
-- `α ∈ (0, 1)`; the required inequality becomes `α ^ p ≤ α`, which fails for `0 < p < 1`.
/-- Example 10.31 (2): clause (ii), first part. On a nontrivial real normed space, if `0 < p <
1`, then the norm-power function is not convex on the whole space. -/
theorem not_convexOn_univ_norm_rpow_of_lt_one
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ¬ ConvexOn ℝ Set.univ (fun x : H ↦ ‖x‖ ^ p) := by
  intro hconv
  obtain ⟨z, hz⟩ := exists_norm_eq H zero_le_one
  have hmid :=
    hconv.2 (by simp : z ∈ Set.univ) (by simp : (0 : H) ∈ Set.univ)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
  have hhalf_le : (1 / 2 : ℝ) ^ p ≤ 1 / 2 := by
    -- Specializing Jensen's inequality to `z` and `0` collapses it to a scalar inequality.
    simpa [hz, norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)),
      hp.ne', Real.zero_rpow (show p ≠ 0 by linarith)] using hmid
  have hhalf_lt : (1 / 2 : ℝ) < (1 / 2 : ℝ) ^ p := by
    exact Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hp1
  exact (not_le_of_gt hhalf_lt) hhalf_le

-- Proof sketch: if a modulus `φ` made the canonical `EReal` lift of the norm-power uniformly
-- quasiconvex, then applying the defining inequality on a nonzero ray at the symmetric points
-- `(s - t) z` and `(s + t) z` would give `φ (2t) / 4 ≤ (s + t)^p - s^p`.
-- Letting `s → ∞` forces `φ (2t) = 0` for every `t > 0`, contradicting the modulus axiom.
/-- Example 10.31 (3): clause (ii), second part. On a nontrivial real normed space, if
`0 < p < 1`, then the norm-power function is not uniformly quasiconvex. -/
theorem not_uniformlyQuasiconvex_norm_rpow_of_lt_one
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ¬ ∃ φ : NNReal → EReal,
      UniformlyQuasiconvex ((fun x : H ↦ ‖x‖ ^ p).toEReal.asEReal) φ := by
  rintro ⟨φ, hφ⟩
  obtain ⟨z, hz⟩ := exists_norm_eq H zero_le_one
  let term : EReal := (((1 / 4 : ℝ) : EReal) * φ 1)
  have hφ_one_nonneg : (0 : EReal) ≤ φ 1 := by
    -- Monotonicity and the normalization `φ 0 = 0` force the modulus to be nonnegative.
    rw [← (hφ.modulus_eq_zero_iff 0).2 rfl]
    exact hφ.monotone (by norm_num : (0 : NNReal) ≤ 1)
  have hφ_one_ne_zero : φ 1 ≠ 0 := by
    intro hzero
    exact one_ne_zero ((hφ.modulus_eq_zero_iff 1).1 hzero)
  have hterm_pos : (0 : EReal) < term := by
    have hquarter_pos : (0 : EReal) < (((1 / 4 : ℝ) : EReal)) := by
      exact_mod_cast (show 0 < (1 / 4 : ℝ) by norm_num)
    have hφ_one_pos : (0 : EReal) < φ 1 :=
      lt_of_le_of_ne hφ_one_nonneg (Ne.symm hφ_one_ne_zero)
    simpa [term] using EReal.mul_pos hquarter_pos hφ_one_pos
  have hterm_bot : term ≠ ⊥ := by
    intro hbot
    simp [term, hbot] at hterm_pos
  have hterm_top : term ≠ ⊤ := by
    -- A single finite ray-gap estimate rules out `term = ⊤`.
    exact ne_of_lt <| lt_of_le_of_lt
      (quarterMulModulusOne_le_halfRayGap (H := H) p hp hφ hz (s := 1) (by norm_num))
      (EReal.coe_lt_top _)
  have hterm_toReal_pos : 0 < term.toReal := by
    have hcoe : ((term.toReal : ℝ) : EReal) = term := EReal.coe_toReal hterm_top hterm_bot
    have : (0 : EReal) < ((term.toReal : ℝ) : EReal) := by
      simpa [hcoe] using hterm_pos
    exact_mod_cast this
  have hterm_le_gap :
      ∀ᶠ s : ℝ in Filter.atTop, term.toReal ≤ (s + 1 / 2) ^ p - s ^ p := by
    filter_upwards [show ∀ᶠ s : ℝ in Filter.atTop, 1 / 2 < s from
      Filter.eventually_atTop.2 ⟨1, fun s hs => by linarith⟩] with s hs
    -- Convert the `EReal` gap estimate to a real inequality once `term` is known finite.
    exact EReal.toReal_le_toReal
      (quarterMulModulusOne_le_halfRayGap (H := H) p hp hφ hz hs)
      hterm_bot (EReal.coe_ne_top _)
  have hgap_small :
      ∀ᶠ s : ℝ in Filter.atTop, (s + 1 / 2) ^ p - s ^ p < term.toReal / 2 := by
    -- The half-ray increment tends to `0`, so eventually it is smaller than half the fixed gap.
    have hhalf_pos : 0 < term.toReal / 2 := by
      nlinarith
    exact tendstoAddHalfRpowSubRpowZero p hp hp1
      (show Set.Iio (term.toReal / 2) ∈ nhds (0 : ℝ) from Iio_mem_nhds hhalf_pos)
  rcases Filter.Eventually.exists (hterm_le_gap.and hgap_small) with ⟨s, hs_le, hs_lt⟩
  have hhalf_lt_term : term.toReal / 2 < term.toReal := by
    linarith
  exact (not_le_of_gt (lt_trans hs_lt hhalf_lt_term)) hs_le

end NontrivialNormed
