import BauschkeLean.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ERealFunction

-- Semantic search note: `lean_leansearch` surfaced `Real.artanh` and `Real.tanh`.
-- Because the source text only states a proximal-operator identity and does not assert `Γ₀`
-- membership, the owner/API choice here is the general Chapter 12 surface
-- `HasUniqueProxPoint`/`proximityOperator`, together with the canonical indicator owner `ι[C]`
-- and the finite real-valued bridge `Function.toEReal`.

/-- Helper for Example 24.44: the finite real-valued proximal objective on `(-1,1)` for the
artanh/log barrier at base point `x`. -/
private def artanhLogBarrierProxSeed (x ξ : ℝ) : ℝ :=
  ξ * Real.artanh ξ + (1 / 2 : ℝ) * Real.log (1 - ξ ^ (2 : ℕ)) - x * ξ +
    (1 / 2 : ℝ) * x ^ (2 : ℕ)

/-- The `]-∞,+∞]`-valued function equal to
`ξ * artanh ξ + (1 / 2) * (log (1 - ξ^2) - ξ^2)` on `|ξ| < 1` and to `+∞` on `|ξ| ≥ 1`. -/
def artanh_log_barrier_minus_half_sq : ℝ → Set.Ioi (⊥ : EReal) :=
  ι[Set.Ioo (-1) 1] +
    (fun ξ : ℝ ↦
      ξ * Real.artanh ξ +
        (1 / 2 : ℝ) * (Real.log (1 - ξ ^ (2 : ℕ)) - ξ ^ (2 : ℕ))).toEReal

/-- Helper for Example 24.44: on `(-1,1)`, the textbook barrier agrees with its finite branch. -/
private theorem artanh_log_barrier_minus_half_sq_apply_of_mem_Ioo {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioo (-1 : ℝ) 1) :
    (artanh_log_barrier_minus_half_sq ξ : EReal) =
      ((ξ * Real.artanh ξ +
          (1 / 2 : ℝ) * (Real.log (1 - ξ ^ (2 : ℕ)) - ξ ^ (2 : ℕ))) : ℝ) := by
  -- Interior points activate the zero-indicator branch.
  simp [artanh_log_barrier_minus_half_sq, hξ]

/-- Helper for Example 24.44: outside `(-1,1)`, the textbook barrier is `+∞`. -/
private theorem artanh_log_barrier_minus_half_sq_apply_of_not_mem_Ioo {ξ : ℝ}
    (hξ : ξ ∉ Set.Ioo (-1 : ℝ) 1) :
    (artanh_log_barrier_minus_half_sq ξ : EReal) = ⊤ := by
  -- Outside the interval, the indicator contributes `⊤` and the finite branch stays real-valued.
  simpa [artanh_log_barrier_minus_half_sq, indicator_apply, hξ] using
    (EReal.top_add_coe
      (ξ * Real.artanh ξ + (1 / 2 : ℝ) * (Real.log (1 - ξ ^ (2 : ℕ)) - ξ ^ (2 : ℕ))))

/-- Helper for Example 24.44: on `(-1,1)`, the proximal objective agrees with the seed. -/
private theorem artanhLogBarrierProxSeed_eq_proximalObjective_of_mem_Ioo (x ξ : ℝ)
    (hξ : ξ ∈ Set.Ioo (-1 : ℝ) 1) :
    (artanhLogBarrierProxSeed x ξ : EReal) =
      proximalObjective artanh_log_barrier_minus_half_sq x ξ := by
  -- Route correction: use the algebraically simplified seed so the quadratic term cancels `-ξ²/2`.
  rw [proximalObjective, artanh_log_barrier_minus_half_sq_apply_of_mem_Ioo hξ]
  rw [Real.norm_eq_abs, sq_abs]
  have hreal :
      artanhLogBarrierProxSeed x ξ =
        ξ * Real.artanh ξ +
          (1 / 2 : ℝ) * (Real.log (1 - ξ ^ (2 : ℕ)) - ξ ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * (x - ξ) ^ (2 : ℕ) := by
    -- Expand the quadratic term and cancel the `-ξ² / 2` contribution.
    dsimp [artanhLogBarrierProxSeed]
    ring
  exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal

/-- Helper for Example 24.44: `artanh` has derivative `(1 - ξ²)⁻¹` on `(-1,1)`. -/
private theorem hasDerivAt_artanh {ξ : ℝ} (hξ : ξ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh ((1 - ξ ^ (2 : ℕ))⁻¹) ξ := by
  have hξ' : ξ ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hnum_pos : 0 < 1 + ξ := by
    have hleft : -1 < ξ := hξ.1
    linarith
  have hden_pos : 0 < 1 - ξ := by
    have hright : ξ < 1 := hξ.2
    linarith
  have hpos : 0 < (1 + ξ) / (1 - ξ) := by
    exact div_pos hnum_pos hden_pos
  have hfrac :
      HasDerivAt (fun y : ℝ ↦ (1 + y) / (1 - y))
        (((1 : ℝ) * (1 - ξ) - (1 + ξ) * (-1)) / (1 - ξ) ^ (2 : ℕ)) ξ := by
    -- Differentiate the logarithm argument as a quotient.
    simpa using
      ((hasDerivAt_const ξ 1).add (hasDerivAt_id ξ)).div
        ((hasDerivAt_const ξ 1).sub (hasDerivAt_id ξ))
        (by
          have hne : 1 - ξ ≠ 0 := by
            linarith [hξ.2]
          simpa using hne)
  have hlog_raw :
      HasDerivAt
        (fun y : ℝ ↦ (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)))
        ((1 / 2 : ℝ) *
          ((((1 : ℝ) * (1 - ξ) - (1 + ξ) * (-1)) / (1 - ξ) ^ (2 : ℕ)) /
            ((1 + ξ) / (1 - ξ)))) ξ := by
    -- Compose the quotient derivative with `log`, then scale by `1 / 2`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_log hpos.ne').comp ξ hfrac).const_mul (1 / 2 : ℝ)
  have hlog :
      HasDerivAt
        (fun y : ℝ ↦ (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)))
        ((1 - ξ ^ (2 : ℕ))⁻¹) ξ := by
    -- The chain-rule derivative simplifies to the standard `1 / (1 - ξ²)` formula.
    have hcoeff :
        ((1 - ξ ^ (2 : ℕ))⁻¹ : ℝ) =
          (1 / 2 : ℝ) *
            ((((1 : ℝ) * (1 - ξ) - (1 + ξ) * (-1)) / (1 - ξ) ^ (2 : ℕ)) /
              ((1 + ξ) / (1 - ξ))) := by
      have hne1 : 1 - ξ ≠ 0 := by
        linarith [hξ.2]
      have hne2 : 1 + ξ ≠ 0 := by
        linarith [hξ.1]
      have hne : 1 - ξ ^ (2 : ℕ) ≠ 0 := by
        nlinarith [hξ.1, hξ.2]
      field_simp [pow_two, hne1, hne2, hne]
      ring
    simpa [hcoeff] using hlog_raw
  have hEq :
      Real.artanh =ᶠ[nhds ξ]
        (fun y : ℝ ↦ (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y))) := by
    have hnhds : Set.Ioo (-1 : ℝ) 1 ∈ nhds ξ := isOpen_Ioo.mem_nhds hξ
    filter_upwards [hnhds] with y hy
    rw [Real.artanh_eq_half_log ⟨le_of_lt hy.1, le_of_lt hy.2⟩]
  simpa using hlog.congr_of_eventuallyEq hEq

/-- Helper for Example 24.44: the seed derivative is `artanh ξ - x` on `(-1,1)`. -/
private theorem artanh_log_barrier_prox_seed_hasDerivAt (x ξ : ℝ)
    (hξ : ξ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (artanhLogBarrierProxSeed x) (Real.artanh ξ - x) ξ := by
  have hlog :
      HasDerivAt (fun y : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 - y ^ (2 : ℕ)))
        (-(ξ * (1 - ξ ^ (2 : ℕ))⁻¹)) ξ := by
    have hinner :
        HasDerivAt (fun y : ℝ ↦ 1 - y ^ (2 : ℕ)) (-(2 * ξ)) ξ := by
      -- Differentiate the logarithm argument `1 - y²`.
      have hpow : HasDerivAt (fun y : ℝ ↦ y ^ (2 : ℕ)) (2 * ξ) ξ := by
        simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id ξ).pow 2)
      simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using (hasDerivAt_const ξ (1 : ℝ)).sub hpow
    have hpos : 0 < 1 - ξ ^ (2 : ℕ) := by
      nlinarith [hξ.1, hξ.2]
    -- The chain rule gives the logarithmic correction.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_log (by positivity : (1 - ξ ^ (2 : ℕ)) ≠ 0)).comp ξ hinner).const_mul
        (1 / 2 : ℝ)
  have hmul :
      HasDerivAt (fun y : ℝ ↦ y * Real.artanh y)
        (Real.artanh ξ + ξ * (1 - ξ ^ (2 : ℕ))⁻¹) ξ := by
    -- Differentiate the product `y * artanh y`.
    convert ((hasDerivAt_artanh hξ).mul (hasDerivAt_id ξ)) using 1
    · ext y
      simp [mul_comm]
    · simpa [mul_comm, add_comm]
  have hlinear :
      HasDerivAt (fun y : ℝ ↦ -x * y) (-x) ξ := by
    -- The affine perturbation contributes the constant derivative `-x`.
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id ξ).const_mul (-x)
  have hconst :
      HasDerivAt (fun _ : ℝ ↦ (1 / 2 : ℝ) * x ^ (2 : ℕ)) 0 ξ := by
    simpa using hasDerivAt_const ξ ((1 / 2 : ℝ) * x ^ (2 : ℕ))
  -- The rational terms cancel, leaving exactly `artanh ξ - x`.
  convert hmul.add (hlog.add (hlinear.add hconst)) using 1
  · ext y
    simp [artanhLogBarrierProxSeed, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · field_simp [pow_two]
    ring

/-- Helper for Example 24.44: the seed value at `tanh x` is minimal on `(-1,1)`. -/
private theorem tanh_minimizes_artanh_log_barrier_prox_seed (x y : ℝ)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    artanhLogBarrierProxSeed x (Real.tanh x) ≤ artanhLogBarrierProxSeed x y := by
  let p : ℝ := Real.tanh x
  have hp : p ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  by_cases hpy : p = y
  · -- Equal endpoints make the inequality tautological.
    simpa [p, hpy]
  · by_cases hlt : p < y
    · -- Apply the mean value theorem on `[p,y]` and use that `artanh ξ - x > 0` beyond `p`.
      have hcont :
          ContinuousOn (artanhLogBarrierProxSeed x) (Set.Icc p y) := by
        intro z hz
        have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_of_lt_of_le hp.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
        exact (artanh_log_barrier_prox_seed_hasDerivAt x z hzIoo).continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo p y, HasDerivAt (artanhLogBarrierProxSeed x)
            (Real.artanh z - x) z := by
        intro z hz
        have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hp.1 hz.1, lt_trans hz.2 hy.2⟩
        exact artanh_log_barrier_prox_seed_hasDerivAt x z hzIoo
      rcases exists_hasDerivAt_eq_slope (f := artanhLogBarrierProxSeed x) (f' := fun z ↦ Real.artanh z - x)
          hlt hcont hderiv with ⟨c, hc, hcSlope⟩
      have hcIoo : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hp.1 hc.1, lt_trans hc.2 hy.2⟩
      have hcx : 0 < Real.artanh c - x := by
        have hArt : Real.artanh (Real.tanh x) < Real.artanh c :=
          (Real.artanh_lt_artanh_iff hp hcIoo).2 hc.1
        simpa [Real.artanh_tanh x, sub_pos] using hArt
      have hslope : 0 < (artanhLogBarrierProxSeed x y - artanhLogBarrierProxSeed x p) / (y - p) := by
        rw [← hcSlope]
        exact hcx
      have hypos : 0 < y - p := sub_pos.mpr hlt
      have hdiff : 0 < artanhLogBarrierProxSeed x y - artanhLogBarrierProxSeed x p := by
        rw [div_pos_iff] at hslope
        rcases hslope with hpos | hneg
        · exact hpos.1
        · linarith
      linarith [hdiff]
    · have hlt' : y < p := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpy)
      -- Reverse the interval and use that `artanh ξ - x < 0` to the left of `p`.
      have hcont :
          ContinuousOn (artanhLogBarrierProxSeed x) (Set.Icc y p) := by
        intro z hz
        have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hp.2⟩
        exact (artanh_log_barrier_prox_seed_hasDerivAt x z hzIoo).continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo y p, HasDerivAt (artanhLogBarrierProxSeed x)
            (Real.artanh z - x) z := by
        intro z hz
        have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hp.2⟩
        exact artanh_log_barrier_prox_seed_hasDerivAt x z hzIoo
      rcases exists_hasDerivAt_eq_slope (f := artanhLogBarrierProxSeed x) (f' := fun z ↦ Real.artanh z - x)
          hlt' hcont hderiv with ⟨c, hc, hcSlope⟩
      have hcIoo : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hy.1 hc.1, lt_trans hc.2 hp.2⟩
      have hcx : Real.artanh c - x < 0 := by
        have hArt : Real.artanh c < Real.artanh (Real.tanh x) :=
          (Real.artanh_lt_artanh_iff hcIoo hp).2 hc.2
        simpa [Real.artanh_tanh x, sub_neg] using hArt
      have hslope :
          (artanhLogBarrierProxSeed x p - artanhLogBarrierProxSeed x y) / (p - y) < 0 := by
        rw [← hcSlope]
        exact hcx
      have hypos : 0 < p - y := sub_pos.mpr hlt'
      have hdiff : artanhLogBarrierProxSeed x p - artanhLogBarrierProxSeed x y < 0 := by
        rw [div_neg_iff] at hslope
        rcases hslope with hneg | hneg
        · linarith
        · exact hneg.1
      linarith

/-- Helper for Example 24.44: `tanh x` is a proximal point of the artanh/log barrier at `x`. -/
private theorem tanh_isProxPoint_artanh_log_barrier_minus_half_sq (x : ℝ) :
    IsProxPoint artanh_log_barrier_minus_half_sq x (Real.tanh x) := by
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ Set.Ioo (-1 : ℝ) 1
  · -- On the effective domain, compare the real-valued seed objective.
    have hp : Real.tanh x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
    rw [← artanhLogBarrierProxSeed_eq_proximalObjective_of_mem_Ioo x (Real.tanh x) hp,
      ← artanhLogBarrierProxSeed_eq_proximalObjective_of_mem_Ioo x y hy]
    exact_mod_cast tanh_minimizes_artanh_log_barrier_prox_seed x y hy
  · -- Outside the interval, the objective is `⊤`, so the proximal inequality is immediate.
    have hp : Real.tanh x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
    rw [← artanhLogBarrierProxSeed_eq_proximalObjective_of_mem_Ioo x (Real.tanh x) hp,
      proximalObjective, artanh_log_barrier_minus_half_sq_apply_of_not_mem_Ioo hy, EReal.top_add_coe]
    exact le_top

/-- Example 24.44: if
`φ(ξ) = ξ * artanh ξ + (1 / 2) * (log (1 - ξ^2) - ξ^2)` for `|ξ| < 1` and
`φ(ξ) = +∞` for `|ξ| ≥ 1`, then any chosen proximity operator of `φ` is `tanh`. -/
theorem prox_artanh_log_barrier_minus_half_sq_eq_tanh
    (hprox : HasUniqueProxPoint artanh_log_barrier_minus_half_sq) :
    proximityOperator artanh_log_barrier_minus_half_sq hprox =
      Real.tanh := by
  funext x
  -- The candidate `tanh x` is a proximal point, so uniqueness identifies it with the chosen prox.
  exact
    (eq_proximityOperator_of_isProxPoint
      artanh_log_barrier_minus_half_sq hprox
      (tanh_isProxPoint_artanh_log_barrier_minus_half_sq x)).symm

end ERealFunction
