import Mathlib
import BauschkeLean.Chap09.Corollary_9_44
import BauschkeLean.Chap09.Proposition_9_5
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Proposition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/- Internal seed for Example 17.13: the scalar square map on `[0, +∞)`, extended by `+∞` on
`(-∞, 0)`. The public owner of the example remains the bivariate function below; this seed only
supports the canonical closed-perspective implementation. -/
private noncomputable def nonnegativeSquare (t : ℝ) : Set.Ioi (⊥ : EReal) :=
  if ht : 0 ≤ t then
    ⟨((t ^ 2 : ℝ) : EReal), EReal.bot_lt_coe _⟩
  else
    ⟨⊤, by simp⟩

private theorem nonnegativeSquare_effectiveDomain_nonempty :
    (effectiveDomain nonnegativeSquare).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_effectiveDomain_iff]
  simp [nonnegativeSquare]

/-- Helper for Example 17 13: on the nonnegative half-line, `nonnegativeSquare` agrees with the
ordinary square. -/
@[simp] private theorem nonnegativeSquare_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (nonnegativeSquare t : EReal) = ((t ^ 2 : ℝ) : EReal) := by
  -- Select the finite branch of the definition.
  simp [nonnegativeSquare, ht]

/-- Helper for Example 17 13: on the negative half-line, `nonnegativeSquare` takes the value
`+∞`. -/
@[simp] private theorem nonnegativeSquare_apply_of_neg {t : ℝ} (ht : t < 0) :
    (nonnegativeSquare t : EReal) = ⊤ := by
  -- Negative inputs land in the `+∞` branch of the definition.
  simp [nonnegativeSquare, not_le.mpr ht]

/-- Helper for Example 17 13: the effective domain of `nonnegativeSquare` is the closed half-line
`[0,+∞)`. -/
private theorem effectiveDomain_nonnegativeSquare_eq_Ici :
    effectiveDomain nonnegativeSquare = Set.Ici (0 : ℝ) := by
  ext t
  constructor
  · intro ht
    -- Negative inputs are excluded because the function value there is `+∞`.
    by_cases ht_neg : t < 0
    · rw [mem_effectiveDomain_iff, nonnegativeSquare_apply_of_neg ht_neg] at ht
      exact False.elim (lt_irrefl (⊤ : EReal) ht)
    · exact le_of_not_gt ht_neg
  · intro ht
    -- Every nonnegative input uses the finite quadratic branch.
    rw [mem_effectiveDomain_iff]
    rw [nonnegativeSquare_apply_of_nonneg ht]
    exact EReal.coe_lt_top (t ^ 2)

/-- Helper for Example 17 13: the scalar seed is lower semicontinuous because its finite branch is
continuous on `[0,+∞)` and the complementary branch is `+∞`. -/
private theorem nonnegativeSquare_lowerSemicontinuous :
    LowerSemicontinuous (fun t : ℝ ↦ (nonnegativeSquare t : EReal)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  by_cases ha_top : a = ⊤
  · -- At level `⊤`, the closed sublevel set is the whole line.
    subst ha_top
    simp
  · have htop_not_le : ¬ (⊤ : EReal) ≤ a := by
      intro h
      exact ha_top (le_antisymm le_top h)
    have hpreimage :
        (fun t : ℝ ↦ (nonnegativeSquare t : EReal)) ⁻¹' Set.Iic a =
          Set.Ici (0 : ℝ) ∩
            (fun t : ℝ ↦ ((t ^ 2 : ℝ) : EReal)) ⁻¹' Set.Iic a := by
      ext t
      constructor
      · intro ht
        have ht_le : (nonnegativeSquare t : EReal) ≤ a := ht
        have ht_nonneg : 0 ≤ t := by
          by_cases ht_neg : t < 0
          · exact False.elim <| htop_not_le <| by
              simpa [nonnegativeSquare_apply_of_neg ht_neg] using ht_le
          · exact le_of_not_gt ht_neg
        exact ⟨ht_nonneg, by simpa [nonnegativeSquare_apply_of_nonneg ht_nonneg] using ht_le⟩
      · rintro ⟨ht_nonneg, ht⟩
        simpa [nonnegativeSquare_apply_of_nonneg ht_nonneg] using ht
    rw [hpreimage]
    have hcont : Continuous (fun t : ℝ ↦ ((t ^ 2 : ℝ) : EReal)) := by
      -- The finite quadratic branch is continuous before and after coercion to `EReal`.
      exact continuous_coe_real_ereal.comp (continuous_id.pow 2)
    exact isClosed_Ici.inter (isClosed_Iic.preimage hcont)

/-- Helper for Example 17 13: the scalar seed is convex on its effective domain because
`t ↦ t^2` is convex on `[0,+∞)`. -/
private theorem nonnegativeSquare_convexOn_effectiveDomain :
    ConvexOn nonnegativeSquare (effectiveDomain nonnegativeSquare) := by
  refine ⟨nonnegativeSquare_effectiveDomain_nonempty, subset_rfl, ?_⟩
  intro x hx y hy α hα0 hα1
  have hx0 : x ∈ Set.Ici (0 : ℝ) := by
    simpa [effectiveDomain_nonnegativeSquare_eq_Ici] using hx
  have hy0 : y ∈ Set.Ici (0 : ℝ) := by
    simpa [effectiveDomain_nonnegativeSquare_eq_Ici] using hy
  have hsquare : _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ t ^ 2) := by
    simpa using (show Even (2 : ℕ) by decide).convexOn_pow
  have hsquare_ineq := hsquare.2
  have hcombo_nonneg : 0 ≤ α • x + (1 - α) • y := by
    have hx_nonneg : 0 ≤ x := hx0
    have hy_nonneg : 0 ≤ y := hy0
    change 0 ≤ α * x + (1 - α) * y
    nlinarith [hx_nonneg, hy_nonneg, hα0, hα1]
  have hreal :
      (α * x + (1 - α) * y) ^ 2 ≤ α * x ^ 2 + (1 - α) * y ^ 2 := by
    simpa [smul_eq_mul] using
      hsquare_ineq (x := x) (by simp) (y := y) (by simp)
        (a := α) (b := 1 - α) hα0.le (sub_nonneg.mpr hα1.le) (by ring)
  have hcast :
      ((((α * x + (1 - α) * y) ^ 2 : ℝ) : EReal)) ≤
        (((α * x ^ 2 + (1 - α) * y ^ 2 : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hsub_cast : (((1 - α : ℝ) : EReal)) = 1 - (α : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  -- Rewrite back to the subtype-valued owner after casting the real Jensen inequality.
  -- Rewrite back to the subtype-valued owner after casting the real Jensen inequality.
  calc
    (nonnegativeSquare (α • x + (1 - α) • y) : EReal)
        = ((((α * x + (1 - α) * y) ^ 2 : ℝ) : EReal)) := by
            simpa [smul_eq_mul] using nonnegativeSquare_apply_of_nonneg hcombo_nonneg
    _ ≤ (((α * x ^ 2 + (1 - α) * y ^ 2 : ℝ) : EReal)) := hcast
    _ = (α : EReal) * (nonnegativeSquare x : EReal) +
          (1 - α : EReal) * (nonnegativeSquare y : EReal) := by
          simp [hsub_cast, EReal.coe_add, EReal.coe_mul,
            nonnegativeSquare_apply_of_nonneg hx0, nonnegativeSquare_apply_of_nonneg hy0]

-- Proof sketch: `nonnegativeSquare` is the lower-semicontinuous convex extension of `t ↦ t^2`
-- from `Set.Ici (0 : ℝ)` to `ℝ`, so it is a member of `Γ₀(ℝ)`.
private theorem nonnegativeSquare_mem_gammaZero :
    nonnegativeSquare ∈ Γ₀(ℝ) := by
  -- Package the scalar seed using the defining `Γ₀` clauses.
  rw [mem_gammaZero_iff]
  exact ⟨nonnegativeSquare_lowerSemicontinuous, nonnegativeSquare_convexOn_effectiveDomain⟩

/-- Helper for Example 17 13: the recession function of `nonnegativeSquare` vanishes at `0` and is
`+∞` in every nonzero direction. -/
private theorem nonnegativeSquare_recession_eq_zero_or_top (y : ℝ) :
    (recessionFunction nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty y : EReal) =
      if y = 0 then 0 else ⊤ := by
  by_cases hy0 : y = 0
  · -- At the origin, every translated increment is identically zero.
    subst y
    simpa using recessionFunction_zero nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty
  · by_cases hy_pos : 0 < y
    · -- For positive directions, the quadratic increment grows without bound.
      rw [if_neg hy0, EReal.eq_top_iff_forall_lt]
      intro r
      let x : ℝ := |r| / y + 1
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        positivity
      have hx_dom : x ∈ effectiveDomain nonnegativeSquare := by
        simpa [effectiveDomain_nonnegativeSquare_eq_Ici] using hx_nonneg
      have hxy_nonneg : 0 ≤ x + y := by
        dsimp [x]
        positivity
      have hincrement :
          ((nonnegativeSquare (x + y) : EReal) - (nonnegativeSquare x : EReal)) =
            (((x + y) ^ 2 - x ^ 2 : ℝ) : EReal) := by
        rw [nonnegativeSquare_apply_of_nonneg hxy_nonneg]
        rw [nonnegativeSquare_apply_of_nonneg hx_nonneg]
        simp [sub_eq_add_neg]
      have hreal_gt : r < (x + y) ^ 2 - x ^ 2 := by
        dsimp [x]
        have hstep :
            (|r| / y + 1 + y) ^ 2 - (|r| / y + 1) ^ 2 = 2 * |r| + 2 * y + y ^ 2 := by
          field_simp [hy_pos.ne']
          ring
        rw [hstep]
        have hr_abs : r ≤ |r| := le_abs_self r
        nlinarith
      have hlt_increment :
          (r : EReal) <
            ((nonnegativeSquare (x + y) : EReal) - (nonnegativeSquare x : EReal)) := by
        rw [hincrement]
        exact_mod_cast hreal_gt
      have hle_sSup :
          ((nonnegativeSquare (x + y) : EReal) - (nonnegativeSquare x : EReal)) ≤
            (recessionFunction nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty y :
              EReal) := by
        rw [recessionFunction_apply]
        exact (isLUB_sSup _).1 ⟨x, hx_dom, rfl⟩
      exact lt_of_lt_of_le hlt_increment hle_sSup
    · -- For negative directions, one translated point immediately leaves the effective domain.
      have hy_nonpos : y ≤ 0 := le_of_not_gt hy_pos
      have hy_neg : y < 0 := lt_of_le_of_ne hy_nonpos fun h => hy0 h
      rw [if_neg hy0]
      have hhalf_nonneg : 0 ≤ -y / 2 := by
        nlinarith
      have hhalf_dom : -y / 2 ∈ effectiveDomain nonnegativeSquare := by
        simpa [effectiveDomain_nonnegativeSquare_eq_Ici] using hhalf_nonneg
      have hhalf_shift_neg : -y / 2 + y < 0 := by
        nlinarith
      have htop_mem :
          (⊤ : EReal) ∈
            (fun x : ℝ ↦ (nonnegativeSquare (x + y) : EReal) - (nonnegativeSquare x : EReal)) ''
              effectiveDomain nonnegativeSquare := by
        refine ⟨-y / 2, hhalf_dom, ?_⟩
        change (nonnegativeSquare (-y / 2 + y) : EReal) - (nonnegativeSquare (-y / 2) : EReal) = ⊤
        rw [nonnegativeSquare_apply_of_neg hhalf_shift_neg,
          nonnegativeSquare_apply_of_nonneg hhalf_nonneg]
        rw [EReal.top_sub (EReal.coe_ne_top ((-y / 2) ^ 2))]
      rw [recessionFunction_apply]
      exact top_le_iff.mp ((isLUB_sSup _).1 htop_mem)

/-- Helper for Example 17 13: on the positive-height branch, the perspective of the quadratic seed
reduces to the quotient term `η^2 / ξ`. -/
private theorem square_perspective_positive_branch (ξ η : ℝ) (hξ : 0 < ξ) :
    ξ * (ξ⁻¹ * η) ^ 2 = η ^ 2 / ξ := by
  -- Normalize the inverse scaling into the textbook quotient formula.
  field_simp [hξ.ne']

/-- Helper for Example 17 13: the scalar square map already belongs to `γ(ℝ)` after coercion to
`EReal`. -/
private theorem square_coe_mem_gamma :
    (fun t : ℝ ↦ ((t ^ 2 : ℝ) : EReal)) ∈ gamma ℝ := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The real square is convex on all of `ℝ`.
    intro x y a ha0 ha1
    have hsquare : _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ t ^ 2) := by
      simpa using (show Even (2 : ℕ) by decide).convexOn_pow
    have hsquare_ineq := hsquare.2
    have hineq :
        (a * x + (1 - a) * y) ^ 2 ≤ a * x ^ 2 + (1 - a) * y ^ 2 := by
      simpa [smul_eq_mul] using
        hsquare_ineq (x := x) (by simp) (y := y) (by simp)
          (a := a) (b := 1 - a) ha0 (sub_nonneg.mpr ha1) (by ring)
    have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hineq_cast :
        ((((a * x + (1 - a) * y) ^ 2 : ℝ) : EReal)) ≤
          (((a * x ^ 2 + (1 - a) * y ^ 2 : ℝ) : EReal)) := by
      exact_mod_cast hineq
    have hsum_cast :
        (((a * x ^ 2 + (1 - a) * y ^ 2 : ℝ) : EReal)) =
          (a : EReal) * ((x ^ 2 : ℝ) : EReal) +
            (1 - a : EReal) * ((y ^ 2 : ℝ) : EReal) := by
      simp [hsub_cast, EReal.coe_add, EReal.coe_mul]
    simpa [smul_eq_mul] using hineq_cast.trans_eq hsum_cast
  · -- The finite quadratic branch is continuous, hence lower semicontinuous.
    simpa using (continuous_coe_real_ereal.comp (continuous_id.pow 2)).lowerSemicontinuous

/-- Example 17 13: the counterexample function on `ℝ²` is
`f(ξ,η)=η^2+η^2/ξ` for `ξ > 0` and `η ≥ 0`, `f(0,0)=0`, and `f=+∞` otherwise. -/
noncomputable def quadraticPerspectivePlusSquare : ℝ × ℝ → Set.Ioi (⊥ : EReal) :=
  closedPerspective nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty +
    (fun p : ℝ × ℝ ↦ p.2 ^ 2).toEReal

-- Proof sketch: unfold the canonical pointwise sum. The closed perspective of
-- `nonnegativeSquare` supplies the `η^2 / ξ` branch on `ξ > 0`, the recession-value branch at
-- `ξ = 0`, and `+∞` elsewhere; the added `toEReal` quadratic contributes the extra `η^2` term.
/-- Coercing the Example 17.13 function to `EReal` recovers its explicit piecewise formula. -/
@[simp] theorem quadraticPerspectivePlusSquare_apply (p : ℝ × ℝ) :
    (quadraticPerspectivePlusSquare p : EReal) =
      if 0 < p.1 ∧ 0 ≤ p.2 then
        ((p.2 ^ 2 + p.2 ^ 2 / p.1 : ℝ) : EReal)
      else if p = ((0 : ℝ), (0 : ℝ)) then
        0
      else
        ⊤ := by
  rcases p with ⟨ξ, η⟩
  -- Evaluate the closed perspective branch first, then add the quadratic correction.
  rw [quadraticPerspectivePlusSquare, add_apply, closedPerspective_coe, Function.toEReal_apply]
  by_cases hξ_pos : 0 < ξ
  · by_cases hη_nonneg : 0 ≤ η
    · -- On the positive orthant, both pieces are finite and reduce to the textbook formula.
      rw [if_pos ⟨hξ_pos, hη_nonneg⟩]
      rw [closedPerspectiveEReal_apply_of_ne_zero
          (φ := nonnegativeSquare) (hdom := nonnegativeSquare_effectiveDomain_nonempty) hξ_pos.ne',
        perspective_apply_of_pos _ hξ_pos]
      have hscale_nonneg : 0 ≤ ξ⁻¹ * η := by
        exact mul_nonneg (inv_nonneg.mpr hξ_pos.le) hη_nonneg
      have hseed :
          (nonnegativeSquare (ξ⁻¹ • η) : EReal) = (((ξ⁻¹ * η) ^ 2 : ℝ) : EReal) := by
        simpa [smul_eq_mul] using nonnegativeSquare_apply_of_nonneg hscale_nonneg
      rw [hseed]
      have hreal :
          ξ * (ξ⁻¹ * η) ^ 2 + η ^ 2 = η ^ 2 + η ^ 2 / ξ := by
        rw [square_perspective_positive_branch ξ η hξ_pos]
        ring
      exact_mod_cast hreal
    · -- Positive height but negative second coordinate forces the quadratic seed to `+∞`.
      have hη_neg : η < 0 := lt_of_not_ge hη_nonneg
      rw [if_neg (by simp [hξ_pos, hη_nonneg])]
      rw [if_neg (by
        intro h
        exact hξ_pos.ne' (by simpa using congrArg Prod.fst h))]
      rw [closedPerspectiveEReal_apply_of_ne_zero
          (φ := nonnegativeSquare) (hdom := nonnegativeSquare_effectiveDomain_nonempty) hξ_pos.ne',
        perspective_apply_of_pos _ hξ_pos]
      have hscale_neg : ξ⁻¹ * η < 0 := by
        exact mul_neg_of_pos_of_neg (inv_pos.mpr hξ_pos) hη_neg
      have hseed : (nonnegativeSquare (ξ⁻¹ • η) : EReal) = ⊤ := by
        simpa [smul_eq_mul] using nonnegativeSquare_apply_of_neg hscale_neg
      rw [hseed]
      rw [EReal.coe_mul_top_of_pos hξ_pos, EReal.top_add_of_ne_bot (EReal.coe_ne_bot (η ^ 2))]
  · by_cases hξ_zero : ξ = 0
    · subst ξ
      by_cases hη_zero : η = 0
      · -- The origin lies on the zero-height recession slice and both summands vanish.
        subst η
        rw [if_neg (by simp), if_pos rfl]
        rw [closedPerspectiveEReal_apply_zero, nonnegativeSquare_recession_eq_zero_or_top]
        simp
      · -- At zero height away from the origin, the recession value is `+∞`.
        rw [if_neg (by simp), if_neg (by simp [hη_zero])]
        rw [closedPerspectiveEReal_apply_zero]
        rw [nonnegativeSquare_recession_eq_zero_or_top, if_neg hη_zero]
        rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot (η ^ 2))]
    · -- Nonpositive nonzero height is the ordinary perspective `+∞` branch.
      have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ_pos
      rw [if_neg (by simp [hξ_pos]), if_neg (by
        intro h
        exact hξ_zero (by simpa using congrArg Prod.fst h))]
      rw [closedPerspectiveEReal_apply_of_ne_zero
          (φ := nonnegativeSquare) (hdom := nonnegativeSquare_effectiveDomain_nonempty) hξ_zero,
        perspective_apply_of_nonpos _ hξ_nonpos]
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot (η ^ 2))]

-- Proof sketch: on the open positive orthant, the formula is the rational-polynomial map
-- `(ξ,η) ↦ η^2 + η^2 / ξ`; standard Fréchet calculus on products shows this map is twice
-- differentiable there because division by `ξ` is smooth on `ξ > 0`.
/-- The open-domain formula `h(ξ,η)=η^2+η^2/ξ` is twice Fréchet differentiable on
`ℝ_{++}^2 = ]0,+∞[ × ]0,+∞[`. -/
theorem quadraticPerspective_openFormula_contDiffOn :
    ContDiffOn ℝ 2
      (fun p : ℝ × ℝ ↦ p.2 ^ 2 + p.2 ^ 2 / p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  let s : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)
  have hsquare : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ p.2 ^ 2) s := by
    -- The second-coordinate square is polynomial on the ambient product space.
    fun_prop
  have hfst : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ p.1) s := by
    -- The first projection is smooth everywhere.
    fun_prop
  have hquotient : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ p.2 ^ 2 / p.1) s := by
    -- Division is smooth because the first coordinate stays strictly positive on `s`.
    refine hsquare.div hfst ?_
    intro p hp
    exact ne_of_gt hp.1
  simpa [s] using hsquare.add hquotient

/-- Helper for Example 17 13: the everywhere-finite second-coordinate square belongs to
`Γ₀(ℝ × ℝ)`. -/
private theorem snd_square_toEReal_mem_gammaZero :
    ((fun p : ℝ × ℝ ↦ p.2 ^ 2).toEReal) ∈ Γ₀(ℝ × ℝ) := by
  -- Pull the scalar square through the second-coordinate continuous linear map.
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  simpa [Function.comp] using
    mem_gamma_comp_continuousLinearMap
      (f := fun t : ℝ ↦ ((t ^ 2 : ℝ) : EReal))
      (L := ContinuousLinearMap.snd ℝ ℝ ℝ)
      square_coe_mem_gamma

-- Proof sketch: `nonnegativeSquare_mem_gammaZero` packages the one-sided quadratic seed in
-- `Γ₀(ℝ)`, so `closedPerspective_mem_gammaZero` puts its closed perspective in `Γ₀(ℝ × ℝ)`. The
-- everywhere-finite second-coordinate square is another `Γ₀(ℝ × ℝ)` member, and
-- `pointwiseAdd_mem_gammaZero` applies because the two effective domains intersect at `(0, 0)`.
/-- The Example 17.13 counterexample belongs to `Γ₀(ℝ × ℝ)`. -/
theorem quadraticPerspectivePlusSquare_mem_gammaZero :
    quadraticPerspectivePlusSquare ∈ Γ₀(ℝ × ℝ) := by
  have hclosed :
      closedPerspective nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty ∈
        Γ₀(ℝ × ℝ) :=
    closedPerspective_mem_gammaZero nonnegativeSquare nonnegativeSquare_mem_gammaZero
  have hdom :
      (effectiveDomain
          (closedPerspective nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty) ∩
        effectiveDomain ((fun p : ℝ × ℝ ↦ p.2 ^ 2).toEReal)).Nonempty := by
    refine ⟨(1, 0), ?_, ?_⟩
    · -- The closed perspective is finite at `(1,0)` because the scalar seed is finite at `0`.
      refine mem_effectiveDomain_closedPerspective_of_mem_smul_effectiveDomain
        nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty (by norm_num) ?_
      refine Set.mem_smul_set.mpr ?_
      refine ⟨0, ?_, by simp⟩
      simp [effectiveDomain_nonnegativeSquare_eq_Ici]
    · -- The second-coordinate square is finite everywhere.
      simp [Function.effectiveDomain_toEReal]
  -- Sum the two `Γ₀` owners along a common effective-domain point.
  exact pointwiseAdd_mem_gammaZero
    (closedPerspective nonnegativeSquare nonnegativeSquare_effectiveDomain_nonempty)
    ((fun p : ℝ × ℝ ↦ p.2 ^ 2).toEReal)
    hclosed
    snd_square_toEReal_mem_gammaZero
    hdom

-- Proof sketch: the function vanishes on the ray `{(ξ,0) | ξ ≥ 0}` inside its effective domain.
-- Evaluating the strict Jensen inequality on two distinct points of that ray gives equality
-- instead of strict inequality, so strict convexity fails.
/-- The Example 17.13 counterexample is not strictly convex. -/
theorem quadraticPerspectivePlusSquare_not_strictlyConvex :
    ¬ StrictlyConvex quadraticPerspectivePlusSquare := by
  intro hstrict
  have hx : ((0 : ℝ), (0 : ℝ)) ∈ effectiveDomain quadraticPerspectivePlusSquare := by
    rw [mem_effectiveDomain_iff, quadraticPerspectivePlusSquare_apply]
    simp
  have hy : ((1 : ℝ), (0 : ℝ)) ∈ effectiveDomain quadraticPerspectivePlusSquare := by
    rw [mem_effectiveDomain_iff, quadraticPerspectivePlusSquare_apply]
    simp
  have hineq :=
    hstrict.ineq hx hy (by simp)
      (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
  -- Route correction: test strict convexity on the zero-valued ray `{(ξ, 0) | ξ ≥ 0}`.
  have hcombo :
      (1 / 2 : ℝ) • ((0 : ℝ), (0 : ℝ)) + (1 - 1 / 2 : ℝ) • ((1 : ℝ), (0 : ℝ)) =
        ((1 / 2 : ℝ), (0 : ℝ)) := by
    ext <;> norm_num
  have hx0 : (quadraticPerspectivePlusSquare ((0 : ℝ), (0 : ℝ)) : EReal) = 0 := by
    simp [quadraticPerspectivePlusSquare_apply]
  have hy0 : (quadraticPerspectivePlusSquare ((1 : ℝ), (0 : ℝ)) : EReal) = 0 := by
    simp [quadraticPerspectivePlusSquare_apply]
  have hineq'' :
      (quadraticPerspectivePlusSquare ((1 / 2 : ℝ), (0 : ℝ)) : EReal) < 0 := by
    calc
      (quadraticPerspectivePlusSquare ((1 / 2 : ℝ), (0 : ℝ)) : EReal)
          = (quadraticPerspectivePlusSquare
              ((1 / 2 : ℝ) • ((0 : ℝ), (0 : ℝ)) +
                (1 - 1 / 2 : ℝ) • ((1 : ℝ), (0 : ℝ))) : EReal) := by
                rw [hcombo]
      _ < (1 / 2 : EReal) * (quadraticPerspectivePlusSquare ((0 : ℝ), (0 : ℝ)) : EReal) +
            (1 - (1 / 2 : ℝ) : EReal) *
              (quadraticPerspectivePlusSquare ((1 : ℝ), (0 : ℝ)) : EReal) := hineq
      _ = 0 := by simp
  have : (0 : EReal) < 0 := by
    simp at hineq''
  exact lt_irrefl _ this

end ERealFunction
