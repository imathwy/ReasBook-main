import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a connected component of an open
subset of `ℝ` that is trapped between two exterior points is an open interval. -/
lemma connectedComponentIn_eq_Ioo_of_open_real_of_bounds
    {S : Set ℝ} {thetaNeg thetaW thetaPos : ℝ}
    (hS_open : IsOpen S)
    (hthetaNeg_lt : thetaNeg < thetaW)
    (hthetaW_lt : thetaW < thetaPos)
    (hW_mem : thetaW ∈ S)
    (hNeg_not_mem : thetaNeg ∉ S)
    (hPos_not_mem : thetaPos ∉ S) :
    ∃ a b : ℝ,
      a < thetaW ∧ thetaW < b ∧
        connectedComponentIn S thetaW = Set.Ioo a b := by
  let C : Set ℝ := connectedComponentIn S thetaW
  have hC_conn : IsConnected C := by
    -- The witness component is connected because it is the component through `thetaW`.
    simpa [C] using (isConnected_connectedComponentIn_iff.mpr hW_mem)
  have hC_open : IsOpen C := by
    -- Open ambient sets have open connected components on the real line.
    simpa [C] using IsOpen.connectedComponentIn hS_open
  have hW_mem_C : thetaW ∈ C := by
    -- The witness angle belongs to its own component.
    simpa [C] using mem_connectedComponentIn hW_mem
  have hC_subset_S : C ⊆ S := by
    simpa [C] using connectedComponentIn_subset S thetaW
  have hC_bddBelow : BddBelow C := by
    refine ⟨thetaNeg, ?_⟩
    intro x hx
    by_contra hx_lower
    have hx_lt : x < thetaNeg := lt_of_not_ge hx_lower
    have hthetaNeg_mem_C : thetaNeg ∈ C := by
      -- Any point below `thetaW` in the component drags the whole interval up to `thetaW`
      -- into the same component.
      have hIcc_subset :
          Set.Icc x thetaW ⊆ C :=
        hC_conn.isPreconnected.Icc_subset hx hW_mem_C
      exact hIcc_subset ⟨le_of_lt hx_lt, le_of_lt hthetaNeg_lt⟩
    exact hNeg_not_mem (hC_subset_S hthetaNeg_mem_C)
  have hC_bddAbove : BddAbove C := by
    refine ⟨thetaPos, ?_⟩
    intro x hx
    by_contra hx_upper
    have hx_gt : thetaPos < x := lt_of_not_ge hx_upper
    have hthetaPos_mem_C : thetaPos ∈ C := by
      -- The same interval argument rules out points of the component past `thetaPos`.
      have hIcc_subset :
          Set.Icc thetaW x ⊆ C :=
        hC_conn.isPreconnected.Icc_subset hW_mem_C hx
      exact hIcc_subset ⟨le_of_lt hthetaW_lt, le_of_lt hx_gt⟩
    exact hPos_not_mem (hC_subset_S hthetaPos_mem_C)
  have hC_nonempty : C.Nonempty := ⟨thetaW, hW_mem_C⟩
  rcases (mem_nhds_iff_exists_Ioo_subset).1 (hC_open.mem_nhds hW_mem_C) with
    ⟨u, v, huv_mem, huv_subset⟩
  let xLeft : ℝ := (u + thetaW) / 2
  let xRight : ℝ := (thetaW + v) / 2
  have hxLeft_mem : xLeft ∈ C := by
    -- Openness gives an honest interval around `thetaW` inside the component.
    apply huv_subset
    constructor
    · dsimp [xLeft]
      linarith [huv_mem.1]
    · dsimp [xLeft]
      linarith [huv_mem.1, huv_mem.2]
  have hxRight_mem : xRight ∈ C := by
    -- Use the symmetric midpoint on the right of `thetaW`.
    apply huv_subset
    constructor
    · dsimp [xRight]
      linarith [huv_mem.1, huv_mem.2]
    · dsimp [xRight]
      linarith [huv_mem.2]
  have hxLeft_lt : xLeft < thetaW := by
    dsimp [xLeft]
    linarith [huv_mem.1]
  have hthetaW_lt_xRight : thetaW < xRight := by
    dsimp [xRight]
    linarith [huv_mem.2]
  let a : ℝ := sInf C
  let b : ℝ := sSup C
  have ha_lt_thetaW : a < thetaW := by
    -- A midpoint strictly to the left of `thetaW` forces the infimum to sit strictly left too.
    dsimp [a]
    exact (csInf_lt_iff hC_bddBelow hC_nonempty).2 ⟨xLeft, hxLeft_mem, hxLeft_lt⟩
  have hthetaW_lt_b : thetaW < b := by
    -- The right midpoint gives the symmetric strict inequality for the supremum.
    dsimp [b]
    exact (lt_csSup_iff hC_bddAbove hC_nonempty).2 ⟨xRight, hxRight_mem, hthetaW_lt_xRight⟩
  have ha_not_mem_C : a ∉ C := by
    intro ha_mem_C
    rcases (mem_nhds_iff_exists_Ioo_subset).1 (hC_open.mem_nhds ha_mem_C) with
      ⟨u', v', hu'v'_mem, hu'v'_subset⟩
    let x : ℝ := (u' + a) / 2
    have hx_mem : x ∈ C := by
      apply hu'v'_subset
      constructor
      · dsimp [x]
        linarith [hu'v'_mem.1]
      · dsimp [x]
        linarith [hu'v'_mem.1, hu'v'_mem.2]
    have hx_lt_a : x < a := by
      dsimp [x]
      linarith [hu'v'_mem.1]
    have ha_le_x : a ≤ x := by
      dsimp [a]
      exact csInf_le hC_bddBelow hx_mem
    linarith
  have hb_not_mem_C : b ∉ C := by
    intro hb_mem_C
    rcases (mem_nhds_iff_exists_Ioo_subset).1 (hC_open.mem_nhds hb_mem_C) with
      ⟨u', v', hu'v'_mem, hu'v'_subset⟩
    let x : ℝ := (b + v') / 2
    have hx_mem : x ∈ C := by
      apply hu'v'_subset
      constructor
      · dsimp [x]
        linarith [hu'v'_mem.1, hu'v'_mem.2]
      · dsimp [x]
        linarith [hu'v'_mem.2]
    have hb_lt_x : b < x := by
      dsimp [x]
      linarith [hu'v'_mem.2]
    have hx_le_b : x ≤ b := by
      dsimp [b]
      exact le_csSup hC_bddAbove hx_mem
    linarith
  have hIoo_subset : Set.Ioo a b ⊆ C := by
    -- Connected subsets of `ℝ` contain the whole open interval between their infimum and supremum.
    dsimp [a, b]
    exact hC_conn.Ioo_csInf_csSup_subset hC_bddBelow hC_bddAbove
  have hC_subset_Ioo : C ⊆ Set.Ioo a b := by
    intro x hx
    have hx_mem_Icc : x ∈ Set.Icc a b := by
      -- Every point of the component lies between the infimum and the supremum.
      dsimp [a, b]
      exact subset_Icc_csInf_csSup hC_bddBelow hC_bddAbove hx
    constructor
    · by_contra hax
      have hxa : x = a := le_antisymm (not_lt.mp hax) hx_mem_Icc.1
      exact ha_not_mem_C (hxa ▸ hx)
    · by_contra hxb
      have hxb_eq : x = b := le_antisymm hx_mem_Icc.2 (not_lt.mp hxb)
      exact hb_not_mem_C (hxb_eq ▸ hx)
  refine ⟨a, b, ha_lt_thetaW, hthetaW_lt_b, ?_⟩
  -- The component is squeezed between its infimum and supremum, and connectedness fills the gap.
  exact subset_antisymm hC_subset_Ioo hIoo_subset

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once arbitrarily small centered
circles carry one uniformly bounded reciprocal branch, the omitted-value map is meromorphic at the
center. -/
lemma meromorphicAt_zero_of_smallCircleUniformReciprocalBranch
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hcircle :
      ∃ T : ℝ, 1 ≤ T ∧
        ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧
          ((∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
            ∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T)) :
    MeromorphicAt g 0 := by
  have hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0 := by
    -- Omitting `0` makes the reciprocal branch honest on the punctured ball.
    intro z hz hz0
    exact h0 ⟨z, hz, hz0⟩
  have hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0 := by
    -- Omitting `1` gives the same nonvanishing fact for the shifted reciprocal branch.
    intro z hz hz1
    exact h1 ⟨z, hz, (sub_eq_zero.mp hz1).symm⟩
  have hgInv :
      AnalyticOnNhd ℂ (fun z ↦ (g z)⁻¹) (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The reciprocal of `g` is analytic away from the center because `g` never vanishes there.
    simpa using hg.inv hg_nonzero
  have honeSubInv :
      AnalyticOnNhd ℂ (fun z ↦ ((1 - g z)⁻¹)) (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The same analytic inversion applies to the omitted-value translate `1 - g`.
    simpa using (analyticOnNhd_const.sub hg).inv hone_sub_nonzero
  rcases hcircle with ⟨T, hT_ge_one, hsmall⟩
  have hbranch :
      (∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(g z)⁻¹‖ ≤ B) ∨
        ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖((1 - g z)⁻¹)‖ ≤ B := by
    -- Convert the shrinking-circle uniform bounds into the eventual filter-level branch bound.
    exact eventualReciprocalBranch_of_smallCircles
      hε hgInv honeSubInv hsmall
  -- Route correction: once the shrinking-circle branch family is available, the remaining step is
  -- exactly the existing eventual-boundedness criterion.
  exact meromorphicAt_of_eventually_bounded_reciprocal_branch hε hg h0 h1 hbranch

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): inside the bounded ordered-angle
window around the witness point, the legal connected component is an open interval whose endpoints
stay trapped between the two exterior witness angles. -/
lemma windowedWitnessComponent_eq_Ioo
    {g : ℂ → ℂ} {ε ρ : ℝ} {thetaNeg thetaW thetaPos : ℝ}
    (hthetaNeg_lt : thetaNeg < thetaW)
    (hthetaW_lt : thetaW < thetaPos)
    (hwEθ : g (circleMap 0 ρ thetaW) ∈ exercise16Domain)
    (hg_cont : ContinuousOn g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzeta_mem :
      ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) :
    ∃ a b : ℝ,
      thetaNeg ≤ a ∧
        a < thetaW ∧
        thetaW < b ∧
        b ≤ thetaPos ∧
        connectedComponentIn
            (Set.Ioo thetaNeg thetaPos ∩ {θ | g (circleMap 0 ρ θ) ∈ exercise16Domain})
            thetaW =
          Set.Ioo a b := by
  let S : Set ℝ := Set.Ioo thetaNeg thetaPos ∩ {θ | g (circleMap 0 ρ θ) ∈ exercise16Domain}
  have hexercise16_open : IsOpen exercise16Domain := by
    -- The lens domain is the intersection of the two open unit balls from Exercise 16.
    simpa [exercise16Domain] using
      (Metric.isOpen_ball.inter Metric.isOpen_ball :
        IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1))
  have hgzeta_cont : Continuous fun θ ↦ g (circleMap 0 ρ θ) := by
    -- Compose the punctured-ball continuity of `g` with the full radius-`ρ` circle map.
    exact hg_cont.comp_continuous (continuous_circleMap 0 ρ) hzeta_mem
  have hS_open : IsOpen S := by
    -- The bounded legal-angle window is open because both the angle window and the legal preimage
    -- are open.
    refine isOpen_Ioo.inter ?_
    simpa [S] using hexercise16_open.preimage hgzeta_cont
  have hW_mem : thetaW ∈ S := by
    -- The witness angle belongs to the bounded legal window by construction.
    constructor
    · exact ⟨hthetaNeg_lt, hthetaW_lt⟩
    · simpa using hwEθ
  have hNeg_not_mem : thetaNeg ∉ S := by
    -- The left witness angle is excluded by the bounded open interval itself.
    simp [S]
  have hPos_not_mem : thetaPos ∉ S := by
    -- The right witness angle is excluded for the same interval reason.
    simp [S]
  obtain ⟨a, b, ha_lt_thetaW, hthetaW_lt_b, hcomponent_eq⟩ :=
    connectedComponentIn_eq_Ioo_of_open_real_of_bounds
      hS_open hthetaNeg_lt hthetaW_lt hW_mem hNeg_not_mem hPos_not_mem
  have hcomponent_subset_window :
      connectedComponentIn S thetaW ⊆ Set.Ioo thetaNeg thetaPos := by
    intro θ hθ
    exact (connectedComponentIn_subset S thetaW hθ).1
  have hthetaNeg_le_a : thetaNeg ≤ a := by
    -- If the left endpoint were strictly left of `thetaNeg`, a midpoint would lie in the
    -- component but outside the bounded angle window.
    by_contra hlt
    let x : ℝ := (a + thetaNeg) / 2
    have hx_mem_component : x ∈ connectedComponentIn S thetaW := by
      have hx_mem_Ioo : x ∈ Set.Ioo a b := by
        constructor
        · dsimp [x]
          linarith
        · dsimp [x]
          linarith [hlt, hthetaNeg_lt, hthetaW_lt_b]
      simpa [hcomponent_eq] using hx_mem_Ioo
    have hx_mem_window : x ∈ Set.Ioo thetaNeg thetaPos := hcomponent_subset_window hx_mem_component
    have hx_lt_thetaNeg : x < thetaNeg := by
      dsimp [x]
      linarith
    exact (not_lt_of_gt hx_mem_window.1) hx_lt_thetaNeg
  have hb_le_thetaPos : b ≤ thetaPos := by
    -- The symmetric midpoint argument keeps the right endpoint from escaping past `thetaPos`.
    by_contra hlt
    let x : ℝ := (thetaPos + b) / 2
    have hx_mem_component : x ∈ connectedComponentIn S thetaW := by
      have hx_mem_Ioo : x ∈ Set.Ioo a b := by
        constructor
        · dsimp [x]
          linarith [ha_lt_thetaW, hthetaW_lt, hlt]
        · dsimp [x]
          linarith
      simpa [hcomponent_eq] using hx_mem_Ioo
    have hx_mem_window : x ∈ Set.Ioo thetaNeg thetaPos := hcomponent_subset_window hx_mem_component
    have hthetaPos_lt_x : thetaPos < x := by
      dsimp [x]
      linarith
    exact (not_lt_of_gt hthetaPos_lt_x) hx_mem_window.2
  refine ⟨a, b, hthetaNeg_le_a, ha_lt_thetaW, hthetaW_lt_b, hb_le_thetaPos, hcomponent_eq⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if a closed angle interval lies
inside the legal witness component, then the fixed-circle image stays inside `exercise16Domain`
throughout that interval. -/
lemma closedLegalMapsTo_of_Icc_subset_windowedWitnessComponent
    {g : ℂ → ℂ} {ρ : ℝ} {thetaNeg thetaPos thetaW u v : ℝ}
    (hsubset :
      Set.Icc u v ⊆
        connectedComponentIn
          (Set.Ioo thetaNeg thetaPos ∩ {θ | g (circleMap 0 ρ θ) ∈ exercise16Domain})
          thetaW) :
    Set.MapsTo
      (fun θ ↦ g (circleMap 0 ρ θ))
      (Set.Icc u v)
      exercise16Domain := by
  intro θ hθ
  -- Membership in the connected component records both the angle-window condition and the legal
  -- image condition; only the latter is needed here.
  exact (connectedComponentIn_subset _ _ (hsubset hθ)).2

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): every interior point of the legal
witness interval sits inside a smaller closed subinterval where the principal-log transport packet
is available with one fixed integral period. -/
lemma principalLogPacket_onWitnessSubinterval
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {a b η : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hη_mem : η ∈ Set.Ioo a b)
    (hgzeta_cont : Continuous fun θ ↦ g (circleMap 0 ρ θ))
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hF_analytic : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmaps_Ioo :
      Set.MapsTo (fun θ ↦ g (circleMap 0 ρ θ)) (Set.Ioo a b) exercise16Domain) :
    ∃ u v : ℝ, ∃ k : ℤ,
      u < η ∧
        η < v ∧
        Set.Icc u v ⊆ Set.Ioo a b ∧
        Set.EqOn
          (fun θ ↦
            Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ)))
          (fun θ ↦
            Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
              F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I))
          (Set.Icc u v) := by
  obtain ⟨u, v, huη, hηv, hIcc_subset⟩ :=
    exists_Icc_subset_of_mem_real isOpen_Ioo hη_mem
  have huv : u ≤ v := le_of_lt (lt_trans huη hηv)
  have hmaps_Icc :
      Set.MapsTo (fun θ ↦ g (circleMap 0 ρ θ)) (Set.Icc u v) exercise16Domain := by
    -- Restrict the legal-image statement from the open witness interval to the smaller closed one.
    intro θ hθ
    exact hmaps_Ioo (hIcc_subset hθ)
  obtain ⟨k, hk⟩ :=
    principalLogPeriod_onClosedLegalInterval
      hρpos hc_ne hgzeta_cont hzeta_mem hg_nonzero hone_sub_nonzero hF_analytic hEqRatio huv
      hmaps_Icc
  -- Shrink first to a closed legal interval, then reuse the owner transport lemma on that interval.
  exact ⟨u, v, k, huη, hηv, hIcc_subset, hk⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): two packet descriptions on the same
closed interval must use the same integral period once they agree at a common reference point. -/
lemma packetPeriod_eq_of_referencePoint_onClosedLegalInterval
    {lhs normal : ℝ → ℂ} {u v θref : ℝ} {k kref : ℤ}
    (hpacket :
      Set.EqOn lhs
        (fun θ ↦ normal θ + k * (2 * (Real.pi : ℂ) * Complex.I))
        (Set.Icc u v))
    (hθref_mem : θref ∈ Set.Icc u v)
    (href :
      lhs θref =
        normal θref + kref * (2 * (Real.pi : ℂ) * Complex.I)) :
    k = kref := by
  have hcompare :
      normal θref + k * (2 * (Real.pi : ℂ) * Complex.I) =
        normal θref + kref * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- Evaluate both packet descriptions at the reference point before cancelling the shared branch.
    calc
      normal θref + k * (2 * (Real.pi : ℂ) * Complex.I) = lhs θref := by
        symm
        exact hpacket hθref_mem
      _ = normal θref + kref * (2 * (Real.pi : ℂ) * Complex.I) := href
  have hperiod_mul :
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
        (kref : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- The normal-form term cancels, leaving only the period coefficient.
    exact add_left_cancel hcompare
  have hk_cast : (k : ℂ) = kref := by
    -- The fundamental period `2π i` is nonzero, so its coefficient is uniquely determined.
    exact mul_left_injective₀ Complex.two_pi_I_ne_zero hperiod_mul
  exact Int.cast_injective hk_cast

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): shifting the exponential factor in
the punctured-ball normal form by an integral multiple of `2 * π * I` does not change the modeled
normalized ratio. -/
lemma eqOn_normalizedRatio_of_add_periodShift
    {ratio F : ℂ → ℂ} {E : Set ℂ} {c : ℂ} {n k : ℤ}
    (hEq :
      Set.EqOn ratio
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        E) :
    Set.EqOn ratio
      (fun z ↦ c * z ^ n * Complex.exp (F z + k * (2 * (Real.pi : ℂ) * Complex.I)))
      E := by
  have hperiod : Complex.exp (k * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    -- Integer `2π i` shifts exponentiate to `1`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I k
  intro z hz
  calc
    ratio z = c * z ^ n * Complex.exp (F z) := hEq hz
    _ = c * z ^ n * (Complex.exp (F z) * 1) := by
      ring
    _ = c * z ^ n * (Complex.exp (F z) * Complex.exp (k * (2 * (Real.pi : ℂ) * Complex.I))) := by
      rw [hperiod]
    _ = c * z ^ n * Complex.exp (F z + k * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [Complex.exp_add]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): for any `η ∈ Ioo a b`, the
principal-log packet on the segment joining `η` to `thetaW` can be rewritten using the fixed
reference period chosen at `thetaW`. -/
lemma referenceBranchNormalizedPacket_onWitnessSegment
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {a b thetaW η : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hη_mem : η ∈ Set.Ioo a b)
    (hthetaW_mem : thetaW ∈ Set.Ioo a b)
    (hgzeta_cont : Continuous fun θ ↦ g (circleMap 0 ρ θ))
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hF_analytic : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmaps_Ioo :
      Set.MapsTo (fun θ ↦ g (circleMap 0 ρ θ)) (Set.Ioo a b) exercise16Domain) :
    ∃ kW : ℤ,
      Set.EqOn
        (fun θ ↦
          Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ)))
        (fun θ ↦
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
            F (circleMap 0 ρ θ) + kW * (2 * (Real.pi : ℂ) * Complex.I))
        (Set.Icc (min η thetaW) (max η thetaW)) := by
  let lhs : ℝ → ℂ := fun θ ↦
    Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ))
  let normal : ℝ → ℂ := fun θ ↦
    Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) + F (circleMap 0 ρ θ)
  have hsegment_subset :
      Set.Icc (min η thetaW) (max η thetaW) ⊆ Set.Ioo a b := by
    intro θ hθ
    constructor
    · have hleft : a < min η thetaW := lt_min hη_mem.1 hthetaW_mem.1
      exact lt_of_lt_of_le hleft hθ.1
    · have hright : max η thetaW < b := max_lt hη_mem.2 hthetaW_mem.2
      exact lt_of_le_of_lt hθ.2 hright
  have hmaps_segment :
      Set.MapsTo
        (fun θ ↦ g (circleMap 0 ρ θ))
        (Set.Icc (min η thetaW) (max η thetaW))
        exercise16Domain := by
    -- The entire closed segment stays inside the legal witness interval.
    intro θ hθ
    exact hmaps_Ioo (hsegment_subset hθ)
  obtain ⟨k, hk⟩ :=
    principalLogPeriod_onClosedLegalInterval
      hρpos hc_ne hgzeta_cont hzeta_mem hg_nonzero hone_sub_nonzero hF_analytic hEqRatio
      min_le_max hmaps_segment
  have hmaps_ref :
      Set.MapsTo
        (fun θ ↦ g (circleMap 0 ρ θ))
        (Set.Icc thetaW thetaW)
        exercise16Domain := by
    -- The singleton interval at `thetaW` is legal because `thetaW ∈ Ioo a b`.
    intro θ hθ
    have hθ_eq : θ = thetaW := le_antisymm hθ.2 hθ.1
    subst hθ_eq
    exact hmaps_Ioo hthetaW_mem
  obtain ⟨kW, hkW⟩ :=
    principalLogPeriod_onClosedLegalInterval
      hρpos hc_ne hgzeta_cont hzeta_mem hg_nonzero hone_sub_nonzero hF_analytic hEqRatio le_rfl
      hmaps_ref
  have hthetaW_mem_segment : thetaW ∈ Set.Icc (min η thetaW) (max η thetaW) := by
    -- The comparison point lies on the segment between `η` and itself.
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hthetaW_ref :
      lhs thetaW = normal thetaW + kW * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- Freeze the reference branch by evaluating the singleton packet at `thetaW`.
    exact hkW ⟨le_rfl, le_rfl⟩
  have hk_eq :
      k = kW := by
    -- Compare the segment packet to the singleton packet at the common legal point `thetaW`.
    exact
      packetPeriod_eq_of_referencePoint_onClosedLegalInterval
        hk hthetaW_mem_segment hthetaW_ref
  refine ⟨kW, ?_⟩
  intro θ hθ
  -- Replace the raw segment period by the fixed witness-reference period.
  simpa [lhs, normal, hk_eq] using hk hθ

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): after fixing a period-shifted
witness-circle model `F`, the principal quotient logarithm at any same-circle point still agrees
with that normalized model up to one integral `2 * π * I` period. -/
lemma theta0NormalizedPacketUpToPeriod
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ k0 : ℤ,
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          F (circleMap 0 ρ θ₀) + k0 * (2 * (Real.pi : ℂ) * Complex.I) := by
  let logRatioθ : ℝ → ℂ := fun θ ↦
    Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ)))
  let normalθ : ℝ → ℂ := fun θ ↦
    Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) + F (circleMap 0 ρ θ)
  have hlogRatioθ_cont : ContinuousOn logRatioθ ({θ₀} : Set ℝ) := by
    -- The singleton source set makes continuity automatic once the comparison is reduced to one
    -- point.
    exact continuousOn_singleton logRatioθ θ₀
  have hnormalθ_cont : ContinuousOn normalθ ({θ₀} : Set ℝ) := by
    -- The normalized model is only probed on that same singleton source set.
    exact continuousOn_singleton normalθ θ₀
  have hexp_eq :
      Set.EqOn (fun θ ↦ Complex.exp (logRatioθ θ)) (fun θ ↦ Complex.exp (normalθ θ))
        ({θ₀} : Set ℝ) := by
    intro θ hθ
    have hθ_eq : θ = θ₀ := by simpa using hθ
    subst θ
    have hρ_ne : (ρ : ℂ) ≠ 0 := by
      exact_mod_cast hρpos.ne'
    have hzeta_exp :
        Complex.exp (Complex.log (ρ : ℂ) + θ₀ * Complex.I) = circleMap 0 ρ θ₀ := by
      -- Rewrite the angular exponential into the concrete point of the fixed witness circle.
      simp [circleMap, Complex.exp_add, Complex.exp_log, hρ_ne, mul_comm]
    calc
      Complex.exp (logRatioθ θ₀) =
          g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)) := by
            change Complex.exp
                (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))) =
              g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))
            rw [Complex.exp_log (div_ne_zero (hg_nonzero θ₀) (hone_sub_nonzero θ₀))]
      _ = c * circleMap 0 ρ θ₀ ^ n * Complex.exp (F (circleMap 0 ρ θ₀)) := hEqRatio (hzeta_mem θ₀)
      _ = Complex.exp (Complex.log c) *
            Complex.exp ((n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I)) *
              Complex.exp (F (circleMap 0 ρ θ₀)) := by
            rw [Complex.exp_log hc_ne, Complex.exp_int_mul, hzeta_exp]
      _ = Complex.exp (normalθ θ₀) := by
            simp [normalθ, Complex.exp_add, add_assoc, mul_assoc, mul_comm]
  obtain ⟨k0, hk0⟩ :=
    eqOn_add_two_pi_I_mul_int_of_exp_eq_on_preconnected_real
      isPreconnected_singleton hnormalθ_cont hlogRatioθ_cont
      (fun θ hθ ↦ (hexp_eq hθ).symm)
  refine ⟨k0, ?_⟩
  have hkθ₀ := hk0 (by simp : θ₀ ∈ ({θ₀} : Set ℝ))
  simpa [logRatioθ, normalθ, add_assoc, add_left_comm, add_comm] using hkθ₀

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on a positive witness component, the
left endpoint packages to a weak selector sign, unit `g`-norm, and failed Exercise-16 membership.
-/
lemma positiveComponent_leftEndpointCapData
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaNeg thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_def : selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ)
    (hthetaNeg_le_a : thetaNeg ≤ a)
    (hselectorNeg : selectorθ thetaNeg < 0)
    (hg_nonzero_a : g (zeta a) ≠ 0)
    (hone_sub_nonzero_a : 1 - g (zeta a) ≠ 0)
    (ha_mem_closure_exercise16 : g (zeta a) ∈ closure exercise16Domain)
    (ha_not_mem_exercise16_of_lt : thetaNeg < a → g (zeta a) ∉ exercise16Domain) :
    0 ≤ selectorθ a ∧ ‖g (zeta a)‖ = 1 ∧ g (zeta a) ∉ exercise16Domain := by
  obtain ⟨hselector_a_nonneg, hga_not_mem⟩ :=
    leftEndpointData_of_positiveComponent
      ha_lt_thetaW hthetaW_lt_b hC₀_eq hselectorTheta_cont hposall hthetaNeg_le_a hselectorNeg
      ha_not_mem_exercise16_of_lt
  have hleftAnchor :
      Real.log ‖(g (zeta a))⁻¹‖ = 0 := by
    -- The endpoint anchor places the boundary point on the unit circle for `g`.
    exact
      positiveComponent_leftEndpointAnchor
        ha_lt_thetaW
        hthetaW_lt_b
        hC₀_eq
        hselectorTheta_cont
        hselector_def
        hposall
        hthetaNeg_le_a
        hselectorNeg
        hg_nonzero_a
        hone_sub_nonzero_a
        ha_mem_closure_exercise16
        ha_not_mem_exercise16_of_lt
  have hga_norm_eq : ‖g (zeta a)‖ = 1 := by
    -- Convert the reciprocal-log anchor into the boundary norm normalization.
    exact norm_eq_one_of_log_norm_inv_eq_zero hg_nonzero_a hleftAnchor
  exact ⟨hselector_a_nonneg, hga_norm_eq, hga_not_mem⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): at a selector-zero point on the
`‖g‖ = 1` cap, the opposite cap norm `‖1 - g‖` is forced to equal `1` as well. -/
lemma positiveEndpointZero_oneSubNormEqOne
    {w : ℂ} (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hselector_zero : Real.log ‖w / (1 - w)‖ = 0)
    (hw_norm_eq : ‖w‖ = 1) :
    ‖1 - w‖ = 1 := by
  have hreal_eq_half : w.re = (1 : ℝ) / 2 := by
    -- A vanishing selector pins the point to the bisector of the two unit discs.
    exact (selectorEqZero_iff_realPart_eq_half hw0 h1w).mp hselector_zero
  have hw_le_hone_sub : ‖w‖ ≤ ‖1 - w‖ := by
    -- The bisector identity gives the left-to-right norm comparison.
    exact (norm_le_norm_one_sub_iff_realPart_le_half).2 <| by linarith [hreal_eq_half]
  have hone_sub_le_hw : ‖1 - w‖ ≤ ‖w‖ := by
    -- The same bisector identity also gives the reverse comparison.
    exact (norm_one_sub_le_norm_iff_half_le_realPart).2 <| by linarith [hreal_eq_half]
  have hone_sub_norm_eq : ‖1 - w‖ = ‖w‖ := le_antisymm hone_sub_le_hw hw_le_hone_sub
  simpa [hw_norm_eq] using hone_sub_norm_eq

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on a negative witness component, the
right endpoint packages to a weak selector sign, unit `1 - g`-norm, and failed Exercise-16
membership. -/
lemma negativeComponent_rightEndpointCapData
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaPos thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_def : selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0)
    (hb_le_thetaPos : b ≤ thetaPos)
    (hselectorPos : 0 < selectorθ thetaPos)
    (hg_nonzero_b : g (zeta b) ≠ 0)
    (hone_sub_nonzero_b : 1 - g (zeta b) ≠ 0)
    (hb_mem_closure_exercise16 : g (zeta b) ∈ closure exercise16Domain)
    (hb_not_mem_exercise16_of_lt : b < thetaPos → g (zeta b) ∉ exercise16Domain) :
    selectorθ b ≤ 0 ∧ ‖1 - g (zeta b)‖ = 1 ∧ g (zeta b) ∉ exercise16Domain := by
  obtain ⟨hselector_b_nonpos, hgb_not_mem⟩ :=
    rightEndpointData_of_negativeComponent
      ha_lt_thetaW hthetaW_lt_b hC₀_eq hselectorTheta_cont hnegall hb_le_thetaPos hselectorPos
      hb_not_mem_exercise16_of_lt
  have hrightAnchor :
      Real.log ‖((1 - g (zeta b))⁻¹)‖ = 0 := by
    -- The symmetric endpoint anchor places `1 - g` on the unit circle.
    exact
      negativeComponent_rightEndpointAnchor
        ha_lt_thetaW
        hthetaW_lt_b
        hC₀_eq
        hselectorTheta_cont
        hselector_def
        hnegall
        hb_le_thetaPos
        hselectorPos
        hg_nonzero_b
        hone_sub_nonzero_b
        hb_mem_closure_exercise16
        hb_not_mem_exercise16_of_lt
  have hone_sub_norm_eq : ‖1 - g (zeta b)‖ = 1 := by
    -- Convert the reciprocal-log anchor into the boundary norm normalization for `1 - g`.
    exact norm_eq_one_of_log_norm_inv_eq_zero hone_sub_nonzero_b hrightAnchor
  exact ⟨hselector_b_nonpos, hone_sub_norm_eq, hgb_not_mem⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): at a selector-zero point on the
`‖1 - g‖ = 1` cap, the opposite cap norm `‖g‖` is forced to equal `1`. -/
lemma negativeEndpointZero_gNormEqOne
    {w : ℂ} (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hselector_zero : Real.log ‖w / (1 - w)‖ = 0)
    (hone_sub_norm_eq : ‖1 - w‖ = 1) :
    ‖w‖ = 1 := by
  have hreal_eq_half : w.re = (1 : ℝ) / 2 := by
    -- The selector-zero condition again pins the point to the bisector.
    exact (selectorEqZero_iff_realPart_eq_half hw0 h1w).mp hselector_zero
  have hw_le_hone_sub : ‖w‖ ≤ ‖1 - w‖ := by
    -- Read off the forward norm comparison from the bisector geometry.
    exact (norm_le_norm_one_sub_iff_realPart_le_half).2 <| by linarith [hreal_eq_half]
  have hone_sub_le_hw : ‖1 - w‖ ≤ ‖w‖ := by
    -- The symmetric comparison gives the reverse inequality.
    exact (norm_one_sub_le_norm_iff_half_le_realPart).2 <| by linarith [hreal_eq_half]
  have hw_norm_eq : ‖w‖ = ‖1 - w‖ := le_antisymm hw_le_hone_sub hone_sub_le_hw
  simpa [hone_sub_norm_eq] using hw_norm_eq

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on the left endpoint cap, weak
selector nonnegativity together with `‖g‖ = 1` already forces the opposite cap norm to be at most
`1`. -/
lemma oneSubNorm_le_one_of_selectorNonneg_and_norm_eq_one
    {w : ℂ} (hselector_nonneg : 0 ≤ Real.log ‖w / (1 - w)‖)
    (hw_norm_eq : ‖w‖ = 1) :
    ‖1 - w‖ ≤ 1 := by
  by_cases h1w : 1 - w = 0
  · -- On the degenerate endpoint `w = 1`, the claim is immediate.
    simpa [h1w]
  have hw0 : w ≠ 0 := by
    -- Unit norm rules out the left endpoint collapsing to `0`.
    exact norm_ne_zero_iff.mp <| by simpa [hw_norm_eq]
  have hhalf_le_re : (1 : ℝ) / 2 ≤ w.re := by
    -- Translate the selector sign into the standard bisector inequality.
    exact (selectorNonneg_iff_half_le_realPart hw0 h1w).mp hselector_nonneg
  have hone_sub_le_hw : ‖1 - w‖ ≤ ‖w‖ := by
    -- The right-cap comparison is the norm form of that same bisector inequality.
    exact (norm_one_sub_le_norm_iff_half_le_realPart).2 hhalf_le_re
  simpa [hw_norm_eq] using hone_sub_le_hw

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on the right endpoint cap, weak
selector nonpositivity together with `‖1 - g‖ = 1` already forces `‖g‖ ≤ 1`. -/
lemma norm_le_one_of_selectorNonpos_and_oneSubNorm_eq_one
    {w : ℂ} (hselector_nonpos : Real.log ‖w / (1 - w)‖ ≤ 0)
    (hone_sub_norm_eq : ‖1 - w‖ = 1) :
    ‖w‖ ≤ 1 := by
  by_cases hw0 : w = 0
  · -- If the point is exactly `0`, the left-cap norm bound is trivial.
    simpa [hw0]
  have h1w : 1 - w ≠ 0 := by
    -- Unit norm for `1 - w` excludes the degenerate endpoint `w = 1`.
    exact norm_ne_zero_iff.mp <| by simpa [hone_sub_norm_eq]
  have hre_le_half : w.re ≤ (1 : ℝ) / 2 := by
    -- Weak nonpositivity is the symmetric bisector inequality.
    exact (selectorNonpos_iff_realPart_le_half hw0 h1w).mp hselector_nonpos
  have hw_le_hone_sub : ‖w‖ ≤ ‖1 - w‖ := by
    -- Convert the bisector inequality back to the left-cap norm comparison.
    exact (norm_le_norm_one_sub_iff_realPart_le_half).2 hre_le_half
  simpa [hone_sub_norm_eq] using hw_le_hone_sub

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on a positive witness component, the
left endpoint cap data naturally packages as a weak selector sign, the unit `g`-norm, the weak
opposite-cap inequality, and failure of `exercise16Domain`. -/
lemma positiveWitnessLeftEndpointCapBundle
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaNeg thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_def : selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ)
    (hthetaNeg_le_a : thetaNeg ≤ a)
    (hselectorNeg : selectorθ thetaNeg < 0)
    (hg_nonzero_a : g (zeta a) ≠ 0)
    (hone_sub_nonzero_a : 1 - g (zeta a) ≠ 0)
    (ha_mem_closure_exercise16 : g (zeta a) ∈ closure exercise16Domain)
    (ha_not_mem_exercise16_of_lt : thetaNeg < a → g (zeta a) ∉ exercise16Domain) :
    0 ≤ selectorθ a ∧
      ‖g (zeta a)‖ = 1 ∧
      ‖1 - g (zeta a)‖ ≤ 1 ∧
      g (zeta a) ∉ exercise16Domain := by
  obtain ⟨hselector_a_nonneg, hga_norm_eq, hga_not_mem⟩ :=
    -- First recover the standard left endpoint cap package from the positive witness component.
    positiveComponent_leftEndpointCapData
      ha_lt_thetaW hthetaW_lt_b hC₀_eq hselectorTheta_cont hselector_def hposall
      hthetaNeg_le_a hselectorNeg hg_nonzero_a hone_sub_nonzero_a
      ha_mem_closure_exercise16 ha_not_mem_exercise16_of_lt
  have hone_sub_norm_le : ‖1 - g (zeta a)‖ ≤ 1 := by
    -- The weak selector sign and the unit `g`-norm already control the opposite cap.
    exact
      oneSubNorm_le_one_of_selectorNonneg_and_norm_eq_one
        (by simpa [hselector_def] using hselector_a_nonneg)
        hga_norm_eq
  exact ⟨hselector_a_nonneg, hga_norm_eq, hone_sub_norm_le, hga_not_mem⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on a negative witness component, the
right endpoint cap data packages as a weak selector sign, the unit `1 - g`-norm, the weak
`‖g‖ ≤ 1` bound, and failure of `exercise16Domain`. -/
lemma negativeWitnessRightEndpointCapBundle
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaPos thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_def : selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0)
    (hb_le_thetaPos : b ≤ thetaPos)
    (hselectorPos : 0 < selectorθ thetaPos)
    (hg_nonzero_b : g (zeta b) ≠ 0)
    (hone_sub_nonzero_b : 1 - g (zeta b) ≠ 0)
    (hb_mem_closure_exercise16 : g (zeta b) ∈ closure exercise16Domain)
    (hb_not_mem_exercise16_of_lt : b < thetaPos → g (zeta b) ∉ exercise16Domain) :
    selectorθ b ≤ 0 ∧
      ‖1 - g (zeta b)‖ = 1 ∧
      ‖g (zeta b)‖ ≤ 1 ∧
      g (zeta b) ∉ exercise16Domain := by
  obtain ⟨hselector_b_nonpos, hone_sub_norm_eq, hgb_not_mem⟩ :=
    -- Recover the standard right endpoint cap package from the negative witness component.
    negativeComponent_rightEndpointCapData
      ha_lt_thetaW hthetaW_lt_b hC₀_eq hselectorTheta_cont hselector_def hnegall
      hb_le_thetaPos hselectorPos hg_nonzero_b hone_sub_nonzero_b
      hb_mem_closure_exercise16 hb_not_mem_exercise16_of_lt
  have hgb_norm_le : ‖g (zeta b)‖ ≤ 1 := by
    -- Weak selector nonpositivity and the unit right-cap norm force `‖g‖ ≤ 1`.
    exact
      norm_le_one_of_selectorNonpos_and_oneSubNorm_eq_one
        (by simpa [hselector_def] using hselector_b_nonpos)
        hone_sub_norm_eq
  exact ⟨hselector_b_nonpos, hone_sub_norm_eq, hgb_norm_le, hgb_not_mem⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): taking imaginary parts of the
principal-log packet isolates the angular transport term on the witness circle. -/
lemma packetImaginaryProjection
    {g F : ℂ → ℂ} {ρ : ℝ} {n k : ℤ} {c : ℂ} {θ : ℝ}
    (hρpos : 0 < ρ)
    (hpacket :
      Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ)) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I)) :
    (Complex.log (g (circleMap 0 ρ θ))).im - (Complex.log (1 - g (circleMap 0 ρ θ))).im =
      (Complex.log c).im + (n : ℝ) * θ + (F (circleMap 0 ρ θ)).im + (k : ℝ) * (2 * Real.pi) := by
  have hlogρ_im : (Complex.log (ρ : ℂ)).im = 0 := by
    -- The positive radius contributes no imaginary part to the logarithmic transport.
    rw [← Complex.ofReal_log hρpos.le]
    simp
  have hlinear_im :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I)).im = (n : ℝ) * θ := by
    -- Expand the linear term once; only the `θ * I` factor survives in the imaginary part.
    rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp [hlogρ_im, mul_comm]
  have hperiod_im :
      (k * (2 * (Real.pi : ℂ) * Complex.I)).im = (k : ℝ) * (2 * Real.pi) := by
    -- The integral period contributes exactly a real multiple of `2π`.
    rw [Complex.mul_im]
    simp [mul_comm]
  have him := congrArg Complex.im hpacket
  -- After projecting to imaginary parts, only the angular transport and the period remain.
  simpa [Complex.add_im, Complex.sub_im, hlinear_im, hperiod_im, add_assoc, add_left_comm,
    add_comm] using him

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): subtracting two normalized witness
packets cancels the common logarithmic period and leaves only the explicit angular and `F`
differences. -/
lemma normalizedPacketImaginaryDifference
    {g F : ℂ → ℂ} {ρ : ℝ} {n k : ℤ} {c : ℂ} {θ₁ θ₂ : ℝ}
    (hρpos : 0 < ρ)
    (hpacket₁ :
      Complex.log (g (circleMap 0 ρ θ₁)) - Complex.log (1 - g (circleMap 0 ρ θ₁)) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₁ * Complex.I) +
          F (circleMap 0 ρ θ₁) + k * (2 * (Real.pi : ℂ) * Complex.I))
    (hpacket₂ :
      Complex.log (g (circleMap 0 ρ θ₂)) - Complex.log (1 - g (circleMap 0 ρ θ₂)) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₂ * Complex.I) +
          F (circleMap 0 ρ θ₂) + k * (2 * (Real.pi : ℂ) * Complex.I)) :
    ((Complex.log (g (circleMap 0 ρ θ₁))).im - (Complex.log (1 - g (circleMap 0 ρ θ₁))).im) -
        ((Complex.log (g (circleMap 0 ρ θ₂))).im - (Complex.log (1 - g (circleMap 0 ρ θ₂))).im) =
      (n : ℝ) * (θ₁ - θ₂) +
        ((F (circleMap 0 ρ θ₁)).im - (F (circleMap 0 ρ θ₂)).im) := by
  have him₁ :
      (Complex.log (g (circleMap 0 ρ θ₁))).im - (Complex.log (1 - g (circleMap 0 ρ θ₁))).im =
        (Complex.log c).im + (n : ℝ) * θ₁ + (F (circleMap 0 ρ θ₁)).im +
          (k : ℝ) * (2 * Real.pi) := by
    -- Project the first packet once before subtracting the common branch data.
    exact
      packetImaginaryProjection hρpos hpacket₁
  have him₂ :
      (Complex.log (g (circleMap 0 ρ θ₂))).im - (Complex.log (1 - g (circleMap 0 ρ θ₂))).im =
        (Complex.log c).im + (n : ℝ) * θ₂ + (F (circleMap 0 ρ θ₂)).im +
          (k : ℝ) * (2 * Real.pi) := by
    -- The same projection formula applies at the second comparison point.
    exact
      packetImaginaryProjection hρpos hpacket₂
  -- Subtract the two projected identities; the constant and period terms cancel.
  linarith

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): an integral multiple of `2 * π`
cannot separate two real numbers that both already lie in the principal strip `(-π, π)`. -/
lemma periodIndex_eq_zero_of_principalStripComparison
    {x y : ℝ} {k : ℤ}
    (hx : -Real.pi < x ∧ x < Real.pi)
    (hy : -Real.pi < y ∧ y < Real.pi)
    (hxy : x = y + (k : ℝ) * (2 * Real.pi)) :
    k = 0 := by
  by_cases hk : k = 0
  · exact hk
  have hdiff : x - y = (k : ℝ) * (2 * Real.pi) := by
    linarith
  have hdiff_lt : x - y < 2 * Real.pi := by
    linarith [hx.2, hy.1]
  have hdiff_gt : -(2 * Real.pi) < x - y := by
    linarith [hx.1, hy.2]
  have hk_split : k ≤ -1 ∨ 1 ≤ k := by
    omega
  rcases hk_split with hk_le | hk_ge
  · have hk_real_le : (k : ℝ) ≤ -1 := by
      exact_mod_cast hk_le
    have hdiff_le : x - y ≤ -(2 * Real.pi) := by
      nlinarith [Real.pi_pos, hk_real_le, hdiff]
    linarith
  · have hk_real_ge : (1 : ℝ) ≤ k := by
      exact_mod_cast hk_ge
    have hdiff_ge : 2 * Real.pi ≤ x - y := by
      nlinarith [Real.pi_pos, hk_real_ge, hdiff]
    linarith

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if a legal-point principal quotient
logarithm agrees with a candidate normal form up to one integral `2 * π * I` period and both
imaginary parts already lie in `(-π, π)`, then the residual period is zero. -/
lemma packetPeriodZero_of_principalStripComparison
    {logRatio normal : ℂ} {k : ℤ}
    (hlogRatio_strip : -Real.pi < logRatio.im ∧ logRatio.im < Real.pi)
    (hnormal_strip : -Real.pi < normal.im ∧ normal.im < Real.pi)
    (hpacket :
      logRatio = normal + k * (2 * (Real.pi : ℂ) * Complex.I)) :
    k = 0 := by
  have hperiod_im :
      (k * (2 * (Real.pi : ℂ) * Complex.I)).im = (k : ℝ) * (2 * Real.pi) := by
    -- Project the complex period once so the real strip comparison can consume it directly.
    rw [Complex.mul_im]
    simp [mul_comm, mul_left_comm]
  have him :
      logRatio.im = normal.im + (k : ℝ) * (2 * Real.pi) := by
    -- Take imaginary parts of the packet equality and rewrite the residual period explicitly.
    exact by
      have him' := congrArg Complex.im hpacket
      simpa [Complex.add_im, hperiod_im] using him'
  exact
    periodIndex_eq_zero_of_principalStripComparison hlogRatio_strip hnormal_strip him

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): two selector-zero points on the same
witness circle force the same real part of the punctured-ball normal form. -/
lemma witnessCircleNormalFormRe_eq_of_twoSelectorZeros
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ₁ θ₂ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ₁_mem : circleMap 0 ρ θ₁ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hθ₂_mem : circleMap 0 ρ θ₂ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hθ₁_zero :
      Real.log ‖g (circleMap 0 ρ θ₁) / (1 - g (circleMap 0 ρ θ₁))‖ = 0)
    (hθ₂_zero :
      Real.log ‖g (circleMap 0 ρ θ₂) / (1 - g (circleMap 0 ρ θ₂))‖ = 0) :
    (F (circleMap 0 ρ θ₁)).re = (F (circleMap 0 ρ θ₂)).re := by
  have hθ₁_re_zero :
      Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (circleMap 0 ρ θ₁)).re = 0 := by
    -- Each selector-zero point forces the same real-part vanishing of the normal form.
    exact
      circleNormalFormRealPart_eq_zero_of_selectorEqZero hρpos hc_ne hEqRatio hθ₁_mem hθ₁_zero
  have hθ₂_re_zero :
      Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (circleMap 0 ρ θ₂)).re = 0 := by
    -- The comparison point satisfies the identical real-part equation.
    exact
      circleNormalFormRealPart_eq_zero_of_selectorEqZero hρpos hc_ne hEqRatio hθ₂_mem hθ₂_zero
  -- Eliminate the shared constant term from the two zero identities.
  linarith

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): adding an integral `2 * π * I`
period to the witness-circle normal form does not change the selector-zero real-part equation. -/
lemma circleNormalFormRealPart_eq_zero_of_selectorEqZero_for_periodShift
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n k : ℤ} {c : ℂ} {θ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ_mem : circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hθ_zero :
      Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ = 0) :
    Real.log ‖c‖ + (n : ℝ) * Real.log ρ +
        ((F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I)).re) = 0 := by
  have hbase :
      Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (circleMap 0 ρ θ)).re = 0 := by
    -- First use the unshifted normal-form identity at the selector-zero point.
    exact
      circleNormalFormRealPart_eq_zero_of_selectorEqZero hρpos hc_ne hEqRatio hθ_mem hθ_zero
  -- The added `2π i` period is purely imaginary, so it leaves the real part unchanged.
  simpa [Complex.add_re, add_assoc, add_left_comm, add_comm] using hbase

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): two selector-zero points on the same
witness circle keep equal real parts after applying the same integral `2 * π * I` period shift to
the normal form. -/
lemma periodShiftedNormalFormRe_eq_of_twoSelectorZeros
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n k : ℤ} {c : ℂ} {θ₁ θ₂ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ₁_mem : circleMap 0 ρ θ₁ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hθ₂_mem : circleMap 0 ρ θ₂ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hθ₁_zero :
      Real.log ‖g (circleMap 0 ρ θ₁) / (1 - g (circleMap 0 ρ θ₁))‖ = 0)
    (hθ₂_zero :
      Real.log ‖g (circleMap 0 ρ θ₂) / (1 - g (circleMap 0 ρ θ₂))‖ = 0) :
    (F (circleMap 0 ρ θ₁) + k * (2 * (Real.pi : ℂ) * Complex.I)).re =
      (F (circleMap 0 ρ θ₂) + k * (2 * (Real.pi : ℂ) * Complex.I)).re := by
  -- First compare the unshifted real parts at the two selector-zero points.
  have hbase :
      (F (circleMap 0 ρ θ₁)).re = (F (circleMap 0 ρ θ₂)).re := by
    exact
      witnessCircleNormalFormRe_eq_of_twoSelectorZeros
        hρpos hc_ne hEqRatio hθ₁_mem hθ₂_mem hθ₁_zero hθ₂_zero
  -- The common period shift is purely imaginary, so the equality survives unchanged.
  simpa [Complex.add_re, add_assoc, add_left_comm, add_comm] using hbase

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): points of the Exercise-16 lens lie
strictly in the right half-plane. -/
lemma re_pos_of_mem_exercise16Domain {w : ℂ}
    (hw : w ∈ exercise16Domain) :
    0 < w.re := by
  rcases hw with ⟨hw_ball0, hw_ball1⟩
  have hone_sub_norm_lt : ‖1 - w‖ < 1 := by
    -- Rewrite the second lens inequality into the `‖1 - w‖` spelling used below.
    have hw_dist_lt : ‖w - 1‖ < 1 := by
      simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hw_ball1
    have hnorm_eq : ‖1 - w‖ = ‖w - 1‖ := by
      simpa [sub_eq_add_neg] using norm_sub_rev (1 : ℂ) w
    rw [hnorm_eq]
    exact hw_dist_lt
  have hw_norm_sq_nonneg : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
  have hone_sub_sq :
      ‖1 - w‖ ^ 2 = 1 + ‖w‖ ^ 2 - 2 * w.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, sub_eq_add_neg, add_assoc, add_comm]
  have hrew_gt_zero : 0 < w.re := by
    have hone_sub_sq_lt : ‖1 - w‖ ^ 2 < 1 := by
      exact (sq_lt_one_iff₀ (norm_nonneg _)).2 hone_sub_norm_lt
    rw [hone_sub_sq] at hone_sub_sq_lt
    by_contra hrew_nonpos
    have hrew_nonpos' : w.re ≤ 0 := le_of_not_gt hrew_nonpos
    nlinarith
  exact hrew_gt_zero

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): points of the Exercise-16 lens and
their `1 - w` images both lie strictly in the right half-plane. -/
lemma re_pos_and_one_sub_re_pos_of_mem_exercise16Domain {w : ℂ}
    (hw : w ∈ exercise16Domain) :
    0 < w.re ∧ 0 < (1 - w).re := by
  refine ⟨re_pos_of_mem_exercise16Domain hw, ?_⟩
  -- Apply the one-sided real-part lemma to the involuted point `1 - w`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    re_pos_of_mem_exercise16Domain (exercise16Domain_one_sub_mem hw)

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on the Exercise-16 lens, the packet's
left-hand side is already the principal logarithm of the quotient `w / (1 - w)`. -/
lemma log_div_eq_sub_log_of_mem_exercise16Domain {w : ℂ}
    (hw : w ∈ exercise16Domain) :
    Complex.log (w / (1 - w)) = Complex.log w - Complex.log (1 - w) := by
  have hrew_pos : 0 < w.re := (re_pos_and_one_sub_re_pos_of_mem_exercise16Domain hw).1
  have hone_sub_re_pos : 0 < (1 - w).re :=
    (re_pos_and_one_sub_re_pos_of_mem_exercise16Domain hw).2
  have hw_ne : w ≠ 0 := by
    intro hw_zero
    simp [hw_zero] at hrew_pos
  have hone_sub_ne : 1 - w ≠ 0 := by
    intro hone_sub_zero
    simp [hone_sub_zero] at hone_sub_re_pos
  have hw_arg_lt : |w.arg| < Real.pi / 2 := by
    exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hrew_pos)
  have hone_sub_arg_lt : |(1 - w).arg| < Real.pi / 2 := by
    exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hone_sub_re_pos)
  have hone_sub_inv_arg_lt : |((1 - w)⁻¹).arg| < Real.pi / 2 := by
    simpa [Complex.abs_arg_inv] using hone_sub_arg_lt
  have harg_sum :
      w.arg + ((1 - w)⁻¹).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hw_lower : -(Real.pi / 2) < w.arg := (abs_lt.mp hw_arg_lt).1
    have hw_upper : w.arg < Real.pi / 2 := (abs_lt.mp hw_arg_lt).2
    have hone_sub_inv_lower : -(Real.pi / 2) < ((1 - w)⁻¹).arg :=
      (abs_lt.mp hone_sub_inv_arg_lt).1
    have hone_sub_inv_upper : ((1 - w)⁻¹).arg < Real.pi / 2 :=
      (abs_lt.mp hone_sub_inv_arg_lt).2
    constructor
    · linarith
    · linarith
  have hlog_mul :
      Complex.log (w * (1 - w)⁻¹) = Complex.log w + Complex.log ((1 - w)⁻¹) := by
    -- The right-half-plane bounds keep the argument sum inside the principal branch window.
    exact Complex.log_mul hw_ne (inv_ne_zero hone_sub_ne) harg_sum
  have hone_sub_arg_ne_pi : (1 - w).arg ≠ Real.pi := by
    intro hone_sub_arg_pi
    have hone_sub_re_neg : (1 - w).re < 0 := (Complex.arg_eq_pi_iff).1 hone_sub_arg_pi |>.1
    linarith
  have hlog_inv :
      Complex.log ((1 - w)⁻¹) = -Complex.log (1 - w) := by
    -- Positive real part keeps `1 - w` away from the branch cut, so inversion negates the log.
    simpa using Complex.log_inv (1 - w) hone_sub_arg_ne_pi
  calc
    Complex.log (w / (1 - w)) = Complex.log (w * (1 - w)⁻¹) := by
      simp [div_eq_mul_inv]
    _ = Complex.log w + Complex.log ((1 - w)⁻¹) := hlog_mul
    _ = Complex.log w - Complex.log (1 - w) := by
      rw [hlog_inv]
      ring

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on the Exercise-16 lens, the
principal logarithm stays in the open imaginary strip `(-π / 2, π / 2)`. -/
lemma logIm_mem_openInterval_of_mem_exercise16Domain {w : ℂ}
    (hw : w ∈ exercise16Domain) :
    -Real.pi / 2 < (Complex.log w).im ∧ (Complex.log w).im < Real.pi / 2 := by
  have hrew_pos : 0 < w.re := re_pos_of_mem_exercise16Domain hw
  have harg_strip : |w.arg| < Real.pi / 2 := by
    -- Positive real part keeps the principal argument in the acute strip.
    exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hrew_pos)
  -- Rewrite the logarithmic imaginary part as the principal argument.
  rw [Complex.log_im]
  simpa [neg_div] using abs_lt.mp harg_strip

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on the Exercise-16 lens, the
imaginary part of `log w - log (1 - w)` lies strictly between `-π` and `π`. -/
lemma logImSub_mem_openInterval_of_mem_exercise16Domain {w : ℂ}
    (hw : w ∈ exercise16Domain) :
    -Real.pi < (Complex.log w).im - (Complex.log (1 - w)).im ∧
      (Complex.log w).im - (Complex.log (1 - w)).im < Real.pi := by
  have hw_strip := logIm_mem_openInterval_of_mem_exercise16Domain hw
  have hone_sub_strip :=
    logIm_mem_openInterval_of_mem_exercise16Domain (exercise16Domain_one_sub_mem hw)
  -- Subtract the two acute-strip bounds to obtain the full principal strip for the log quotient.
  constructor <;> linarith

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on the Exercise-16 lens, the
principal logarithm of `w / (1 - w)` already lies in the open imaginary strip `(-π, π)`. -/
lemma logImDiv_mem_openInterval_of_mem_exercise16Domain {w : ℂ}
    (hw : w ∈ exercise16Domain) :
    -Real.pi < (Complex.log (w / (1 - w))).im ∧
      (Complex.log (w / (1 - w))).im < Real.pi := by
  -- Rewrite the quotient logarithm into the principal-log difference controlled by the lens API.
  rw [log_div_eq_sub_log_of_mem_exercise16Domain hw]
  exact logImSub_mem_openInterval_of_mem_exercise16Domain hw

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a selector-zero point already has its
principal quotient logarithm in the open strip `(-π, π)`, because the quotient cannot hit the
branch-cut endpoint `-1`. -/
lemma logImDiv_mem_openInterval_of_selectorEqZero {w : ℂ}
    (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hselector_zero : Real.log ‖w / (1 - w)‖ = 0) :
    -Real.pi < (Complex.log (w / (1 - w))).im ∧
      (Complex.log (w / (1 - w))).im < Real.pi := by
  let q : ℂ := w / (1 - w)
  have hq_ne : q ≠ 0 := by
    -- The quotient is honest because neither factor in its denominator vanishes.
    exact div_ne_zero hw0 h1w
  have hq_norm_eq : ‖q‖ = 1 := by
    -- A selector zero says exactly that the quotient has norm `1`.
    have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
    exact Real.eq_one_of_pos_of_log_eq_zero hq_pos (by simpa [q] using hselector_zero)
  have hq_arg_lt_pi : q.arg < Real.pi := by
    -- The only way a principal argument could hit `π` is the branch-cut endpoint `-1`, and the
    -- quotient `w / (1 - w)` can never equal `-1`.
    rw [Complex.arg_lt_pi_iff]
    by_cases hq_im : q.im = 0
    · left
      by_contra hq_re_nonneg
      have hq_re_neg : q.re < 0 := lt_of_not_ge hq_re_nonneg
      have hq_normSq_eq : Complex.normSq q = 1 := by
        rw [Complex.normSq_eq_norm_sq, hq_norm_eq]
        norm_num
      have hq_re_sq : q.re ^ 2 = 1 := by
        simpa [Complex.normSq, hq_im, pow_two] using hq_normSq_eq
      have hq_re_eq_neg_one : q.re = -1 := by
        nlinarith
      have hq_eq_neg_one : q = -1 := by
        apply Complex.ext <;> simp [q, hq_im, hq_re_eq_neg_one]
      have hw_eq : w = (-1 : ℂ) * (1 - w) := by
        exact (div_eq_iff h1w).mp hq_eq_neg_one
      have hreal := congrArg Complex.re hw_eq
      simp at hreal
      linarith
    · right
      exact hq_im
  -- Rewrite the logarithmic imaginary part as the principal argument and apply the branch-cut
  -- exclusion above.
  rw [Complex.log_im]
  exact ⟨Complex.neg_pi_lt_arg q, hq_arg_lt_pi⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if a selector-zero point already has
its normalized packet written with zero residual period, then that normalized packet itself lies in
the principal strip `(-π, π)`. -/
lemma normalizedPacketImStrip_of_selectorEqZero_of_packetEq
    {g F : ℂ → ℂ} {ρ : ℝ} {n : ℤ} {c : ℂ} {θ : ℝ}
    (hg_nonzero : g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hselector_zero :
      Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ = 0)
    (hpacket :
      Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          F (circleMap 0 ρ θ)) :
    -Real.pi <
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          F (circleMap 0 ρ θ)).im ∧
      (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          F (circleMap 0 ρ θ)).im <
        Real.pi := by
  -- Rewrite the normalized packet back to the principal logarithm of the quotient at the
  -- selector-zero point, then reuse the already packaged principal-strip control.
  simpa [hpacket] using
    logImDiv_mem_openInterval_of_selectorEqZero hg_nonzero hone_sub_nonzero hselector_zero

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a selector-zero point on the witness
circle can always be rewritten with one explicit integral `2 * π * I` shift so that the resulting
normalized packet already lies in the principal strip `(-π, π)`. -/
lemma periodShiftedNormalizedPacketAndStrip_of_selectorEqZero
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ x, circleMap 0 ρ x ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ x, g (circleMap 0 ρ x) ≠ 0)
    (hone_sub_nonzero : ∀ x, 1 - g (circleMap 0 ρ x) ≠ 0)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hselector_zero :
      Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ = 0) :
    ∃ k : ℤ,
      Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          (F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I)) ∧
      (-Real.pi <
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
              (F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I))).im ∧
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
              (F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I))).im <
            Real.pi) := by
  obtain ⟨k, hk⟩ :=
    theta0NormalizedPacketUpToPeriod
      hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatio
  let Fshift : ℂ → ℂ := fun z ↦ F z + k * (2 * (Real.pi : ℂ) * Complex.I)
  have hpacket_shifted :
      Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          Fshift (circleMap 0 ρ θ) := by
    -- Repackage the chosen period directly into the value of a shifted normal form at `θ`.
    simpa [Fshift, add_assoc, add_left_comm, add_comm] using hk
  have hstrip_shifted :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
              Fshift (circleMap 0 ρ θ)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
            Fshift (circleMap 0 ρ θ)).im <
          Real.pi := by
    -- Once the packet is written with zero residual period, the principal-strip control is exactly
    -- the owner lemma for selector-zero points.
    exact
      normalizedPacketImStrip_of_selectorEqZero_of_packetEq
        (hg_nonzero θ) (hone_sub_nonzero θ) hselector_zero hpacket_shifted
  refine ⟨k, ?_, ?_⟩
  · -- Return to the explicit shifted-value spelling used in the main theorem.
    simpa [Fshift, add_assoc, add_left_comm, add_comm] using hpacket_shifted
  · -- The strip statement is the same after unfolding the shifted model at the chosen point.
    simpa [Fshift, add_assoc, add_left_comm, add_comm] using hstrip_shifted

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): in a period-shifted witness model,
once the candidate normalized packet at `θ₀` is known to lie in the principal strip, the
selector-zero packet at `θ₀` carries no residual `2 * π * I` period. -/
lemma shiftedThetaZeroPacketPeriod_eq_zero_inWitnessModel
    {g Fη : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0)
    (hθ₀_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im < Real.pi) :
    Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
      Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
        Fη (circleMap 0 ρ θ₀) ∧
      (-Real.pi <
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im < Real.pi) := by
  obtain ⟨k₀, hk₀⟩ :=
    theta0NormalizedPacketUpToPeriod
      hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatioη
  have hk₀_zero : k₀ = 0 := by
    -- Route correction: the bare shifted model only determines the packet up to one integral
    -- period. Once the candidate normalized value is known to stay in the principal strip, the
    -- selector-zero principal branch forces that period to vanish.
    exact
      packetPeriodZero_of_principalStripComparison
        (logImDiv_mem_openInterval_of_selectorEqZero
          (hg_nonzero θ₀)
          (hone_sub_nonzero θ₀)
          hθ₀_zero)
        hθ₀_normalized_im_strip
        hk₀
  refine ⟨?_, hθ₀_normalized_im_strip⟩
  -- Substitute the vanishing period into the generic same-circle packet description.
  simpa [hk₀_zero, add_assoc, add_left_comm, add_comm] using hk₀

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the shifted witness-model
candidate at `θ₀` is already known to lie in the principal strip, the `θ₀` quotient packet agrees
exactly with that shifted witness model. -/
lemma referenceTransportedThetaZeroPacket_of_orderedWindowZero
    {g Fη : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0)
    (hθ₀_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im < Real.pi) :
    Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
      Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
        Fη (circleMap 0 ρ θ₀) := by
  -- The strip hypothesis is exactly the remaining side condition in the owner period-killing
  -- lemma, so the packet identity follows immediately.
  exact
    (shiftedThetaZeroPacketPeriod_eq_zero_inWitnessModel
      hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatioη
      hθ₀_zero hθ₀_normalized_im_strip).1

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): in the shifted witness model `Fη`,
the quotient-log packets at the legal selector-zero point `η` and at the witness reference angle
`thetaW` differ by the expected explicit angular transport. -/
lemma shiftedThetaZeroPacketComparisonData
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n : ℤ} {c : ℂ} {η thetaW : ℝ}
    (hρpos : 0 < ρ)
    (hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η))
    (hthetaW_logRatio_packetη :
      Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          Fη (circleMap 0 ρ thetaW)) :
    (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im -
        (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
      (n : ℝ) * (η - thetaW) +
        ((Fη (circleMap 0 ρ η)).im - (Fη (circleMap 0 ρ thetaW)).im) := by
  have hlogρ_im : (Complex.log (ρ : ℂ)).im = 0 := by
    -- The positive circle radius contributes no imaginary part to the transport term.
    rw [← Complex.ofReal_log hρpos.le]
    simp
  have hη_linear_im :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I)).im = (n : ℝ) * η := by
    -- Expand the linear term at `η`; only the `η * I` contribution survives.
    rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp [hlogρ_im, mul_comm]
  have hthetaW_linear_im :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I)).im = (n : ℝ) * thetaW := by
    -- The same simplification applies at the witness reference angle.
    rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp [hlogρ_im, mul_comm]
  have hη_im :
      (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im =
        (Complex.log c).im + (n : ℝ) * η + (Fη (circleMap 0 ρ η)).im := by
    -- Project the legal selector-zero packet at `η` to its imaginary part.
    have him := congrArg Complex.im hη_logRatio_packet_zeroPeriod
    simpa [Complex.add_im, hη_linear_im, add_assoc, add_left_comm, add_comm] using him
  have hthetaW_im :
      (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (Complex.log c).im + (n : ℝ) * thetaW + (Fη (circleMap 0 ρ thetaW)).im := by
    -- Project the witness-reference packet in the same shifted-model spelling.
    have him := congrArg Complex.im hthetaW_logRatio_packetη
    simpa [Complex.add_im, hthetaW_linear_im, add_assoc, add_left_comm, add_comm] using him
  -- Subtract the two projected packets so the common `Complex.log c` term cancels.
  calc
    (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im -
        (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
      ((Complex.log c).im + (n : ℝ) * η + (Fη (circleMap 0 ρ η)).im) -
        ((Complex.log c).im + (n : ℝ) * thetaW + (Fη (circleMap 0 ρ thetaW)).im) := by
          rw [hη_im, hthetaW_im]
    _ = (n : ℝ) * (η - thetaW) +
          ((Fη (circleMap 0 ρ η)).im - (Fη (circleMap 0 ρ thetaW)).im) := by
          ring

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if the shifted witness-model packet
at `θ₀` has vanishing normalized real part, then the corresponding quotient selector at `θ₀`
already vanishes. -/
lemma selectorEqZero_of_shiftedThetaZeroPacket
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n kθ₀ : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hθ₀_logRatio_packet_shifted :
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I)))
    (hθ₀_normalized_re_zero :
      Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (Fη (circleMap 0 ρ θ₀)).re = 0) :
    Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0 := by
  have hlogρ_re : (Complex.log (ρ : ℂ)).re = Real.log ρ := by
    -- The positive radius contributes the expected real logarithm.
    rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
  have hlogρ_im : (Complex.log (ρ : ℂ)).im = 0 := by
    -- Its imaginary part vanishes because `ρ` lies on the positive real axis.
    rw [← Complex.ofReal_log hρpos.le]
    simp
  have hlinear_re :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I)).re = (n : ℝ) * Real.log ρ := by
    -- Only the real logarithm of `ρ` contributes to the real part of the linear transport term.
    rw [mul_add, Complex.add_re, Complex.mul_re, Complex.mul_re]
    simp [hlogρ_re, hlogρ_im, mul_comm]
  have hperiod_re :
      (kθ₀ * (2 * (Real.pi : ℂ) * Complex.I)).re = 0 := by
    -- The explicit period correction is purely imaginary.
    rw [Complex.mul_re]
    simp [mul_comm]
  have hpacket_re := congrArg Complex.re hθ₀_logRatio_packet_shifted
  have hselector_normalForm :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ =
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (Fη (circleMap 0 ρ θ₀)).re := by
    -- Project the shifted packet to real parts and simplify the linear and period contributions.
    simpa [Complex.log_re, Complex.add_re, hlinear_re, hperiod_re, add_assoc, add_left_comm,
      add_comm] using hpacket_re
  -- The shifted packet has zero normalized real part, so the selector itself vanishes.
  linarith [hselector_normalForm, hθ₀_normalized_re_zero]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once a witness-circle packet is
evaluated at a legal point, its left-hand side can be rewritten as the principal logarithm of the
quotient `g / (1 - g)`. -/
lemma logQuotient_eq_packet_of_mem_exercise16Domain
    {g F : ℂ → ℂ} {ρ : ℝ} {n k : ℤ} {c : ℂ} {θ : ℝ}
    (hθ_maps : g (circleMap 0 ρ θ) ∈ exercise16Domain)
    (hpacket :
      Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ)) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I)) :
    Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))) =
      Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
        F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I) := by
  -- The legal-image hypothesis is exactly what lets the packet use the quotient-log spelling.
  rw [log_div_eq_sub_log_of_mem_exercise16Domain hθ_maps]
  exact hpacket

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if a selector-zero point already has
its quotient packet written as a principal-strip value plus one integral `2 * π * I` period, then
that residual period must vanish. -/
lemma selectorZeroPacketPeriod_eq_zero
    {w normal : ℂ} {k : ℤ}
    (hw0 : w ≠ 0)
    (h1w : 1 - w ≠ 0)
    (hselector_zero : Real.log ‖w / (1 - w)‖ = 0)
    (hnormal_strip : -Real.pi < normal.im ∧ normal.im < Real.pi)
    (hpacket : Complex.log (w / (1 - w)) = normal + k * (2 * (Real.pi : ℂ) * Complex.I)) :
    k = 0 := by
  -- Compare the principal strip coming from the selector zero with the candidate normalized strip
  -- to kill the residual `2π i` period.
  exact
    packetPeriodZero_of_principalStripComparison
      (logImDiv_mem_openInterval_of_selectorEqZero hw0 h1w hselector_zero)
      hnormal_strip
      hpacket

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a witness-reference quotient packet
with an explicit `2 * π * I` period rewrites directly into the matching shifted model. -/
lemma thetaWPrincipalPacket_inShiftedModel
    {g F Fη : ℂ → ℂ} {ρ : ℝ} {n k : ℤ} {c : ℂ} {θ : ℝ}
    (hFη : Fη = fun z ↦ F z + k * (2 * (Real.pi : ℂ) * Complex.I))
    (hpacket :
      Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
          F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I)) :
    Complex.log (g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))) =
      Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
        Fη (circleMap 0 ρ θ) := by
  -- Unfold the shifted model once so the packet matches the exact spelling used downstream.
  simpa [hFη, add_assoc, add_left_comm, add_comm] using hpacket

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): an interior selector-zero point on
the frozen witness circle determines one common period-shifted witness model `Fη` in which both
the selector-zero point `η` and the witness reference angle `thetaW` have exact quotient packets.
-/
lemma shiftedWitnessModelBundle_of_referenceSelectorZero
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {a b η thetaW : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hη_mem : η ∈ Set.Ioo a b)
    (hthetaW_mem : thetaW ∈ Set.Ioo a b)
    (hgzeta_cont : Continuous fun θ ↦ g (circleMap 0 ρ θ))
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hF_analytic : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmaps_Ioo :
      Set.MapsTo (fun θ ↦ g (circleMap 0 ρ θ)) (Set.Ioo a b) exercise16Domain)
    (hηzero :
      Real.log ‖g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))‖ = 0) :
    ∃ Fη : ℂ → ℂ,
      AnalyticOnNhd ℂ Fη (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η) ∧
      Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          Fη (circleMap 0 ρ thetaW) ∧
      (-Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
              Fη (circleMap 0 ρ η)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρ η)).im < Real.pi) := by
  obtain ⟨kW, hreferencePacket⟩ :=
    -- First freeze one principal-log packet period that simultaneously covers `η` and `thetaW`.
    referenceBranchNormalizedPacket_onWitnessSegment
      hρpos
      hc_ne
      hη_mem
      hthetaW_mem
      hgzeta_cont
      hzeta_mem
      hg_nonzero
      hone_sub_nonzero
      hF_analytic
      hEqRatio
      hmaps_Ioo
  let Fη : ℂ → ℂ := fun z ↦ F z + kW * (2 * (Real.pi : ℂ) * Complex.I)
  have hFη_analytic :
      AnalyticOnNhd ℂ Fη (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- Adding the fixed integral period keeps the punctured-ball model analytic.
    simpa [Fη, add_assoc, add_left_comm, add_comm] using
      hF_analytic.add analyticOnNhd_const
  have hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- Shift the witness-circle model globally by the same `2π i` period.
    simpa [Fη, add_assoc, add_left_comm, add_comm] using
      eqOn_normalizedRatio_of_add_periodShift hEqRatio
  have hη_mem_segment : η ∈ Set.Icc (min η thetaW) (max η thetaW) := by
    -- The interior selector-zero point is one endpoint of the comparison segment.
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hthetaW_mem_segment : thetaW ∈ Set.Icc (min η thetaW) (max η thetaW) := by
    -- The witness reference angle is the other endpoint of that segment.
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hη_packet :
      Complex.log (g (circleMap 0 ρ η)) - Complex.log (1 - g (circleMap 0 ρ η)) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          F (circleMap 0 ρ η) + kW * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- Specialize the common packet to the selector-zero point.
    exact hreferencePacket hη_mem_segment
  have hthetaW_packet :
      Complex.log (g (circleMap 0 ρ thetaW)) - Complex.log (1 - g (circleMap 0 ρ thetaW)) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          F (circleMap 0 ρ thetaW) + kW * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- The same packet period also normalizes the witness reference angle.
    exact hreferencePacket hthetaW_mem_segment
  have hη_maps : g (circleMap 0 ρ η) ∈ exercise16Domain := hmaps_Ioo hη_mem
  have hthetaW_maps : g (circleMap 0 ρ thetaW) ∈ exercise16Domain := hmaps_Ioo hthetaW_mem
  have hη_logRatio_packet :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          F (circleMap 0 ρ η) + kW * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- Legal points use the quotient-log spelling of the packet.
    exact logQuotient_eq_packet_of_mem_exercise16Domain hη_maps hη_packet
  have hthetaW_logRatio_packet :
      Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          F (circleMap 0 ρ thetaW) + kW * (2 * (Real.pi : ℂ) * Complex.I) := by
    -- Apply the same legal-point rewrite at the reference angle.
    exact logQuotient_eq_packet_of_mem_exercise16Domain hthetaW_maps hthetaW_packet
  have hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η) := by
    -- Repackage the selector-zero point in the shifted witness model.
    exact thetaWPrincipalPacket_inShiftedModel rfl hη_logRatio_packet
  have hthetaW_logRatio_packetη :
      Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          Fη (circleMap 0 ρ thetaW) := by
    -- The reference angle lives in the same shifted model.
    exact thetaWPrincipalPacket_inShiftedModel rfl hthetaW_logRatio_packet
  have hη_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
              Fη (circleMap 0 ρ η)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρ η)).im < Real.pi := by
    -- The exact selector-zero packet at `η` already lies in the principal strip.
    exact
      normalizedPacketImStrip_of_selectorEqZero_of_packetEq
        (hg_nonzero η)
        (hone_sub_nonzero η)
        hηzero
        hη_logRatio_packet_zeroPeriod
  exact
    ⟨Fη, hFη_analytic, hEqRatioη, hη_logRatio_packet_zeroPeriod, hthetaW_logRatio_packetη,
      hη_normalized_im_strip⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if a quotient logarithm is already
rewritten as a normalized packet, then the packet inherits the same principal-strip bounds. -/
lemma normalizedPacketImStrip_of_logRatioEq
    {logRatio normal : ℂ}
    (hlogRatio_strip : -Real.pi < logRatio.im ∧ logRatio.im < Real.pi)
    (hpacket : logRatio = normal) :
    -Real.pi < normal.im ∧ normal.im < Real.pi := by
  -- Rewrite the candidate packet back to the original quotient logarithm before reusing its strip
  -- bounds.
  simpa [hpacket] using hlogRatio_strip

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): every point of the centered circle
`θ ↦ circleMap 0 ρ θ` lies in the punctured `ε`-ball once `0 < ρ < ε`. -/
lemma circleMap_mem_puncturedBall
    {ε ρ : ℝ}
    (hρpos : 0 < ρ)
    (hρlt : ρ < ε) :
    ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
  intro θ
  constructor
  · -- The radius computation puts every point of the circle inside the ambient `ε`-ball.
    simpa [Metric.mem_ball, dist_eq_norm, norm_circleMap_zero,
      abs_of_nonneg (le_of_lt hρpos)] using hρlt
  · -- The positive radius keeps the parameterized circle away from the origin.
    exact norm_ne_zero_iff.mp <| by
      simpa [norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)] using hρpos.ne'

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): restricting an analytic punctured-ball
map to a centered circle preserves continuity along the angle parameter. -/
lemma continuous_circleMap_comp_of_analyticOnNhd
    {g : ℂ → ℂ} {ε ρ : ℝ}
    (hρpos : 0 < ρ)
    (hρlt : ρ < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    Continuous fun θ ↦ g (circleMap 0 ρ θ) := by
  -- Restrict the punctured-ball analyticity package along the centered circle.
  simpa using
    hg.continuousOn.comp_continuous
      (continuous_circleMap 0 ρ)
      (circleMap_mem_puncturedBall hρpos hρlt)

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): restricting the punctured-ball
selector `z ↦ Real.log ‖g z / (1 - g z)‖` to a centered circle keeps it continuous in the angle
parameter. -/
lemma continuous_circleSelector_of_continuousOn
    {g : ℂ → ℂ} {ε ρ : ℝ}
    (hρpos : 0 < ρ)
    (hρlt : ρ < ε)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    Continuous fun θ ↦ Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ := by
  -- The selector inherits continuity from the punctured-ball continuity package on the same
  -- parameterized circle.
  simpa using
    hselector_cont.comp_continuous
      (continuous_circleMap 0 ρ)
      (circleMap_mem_puncturedBall hρpos hρlt)

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a right-hand positive neighborhood in
`C = Ioo a b` already provides an interior weak nonnegative witness. -/
lemma existsWeakNonneg_of_rightPositiveNeighborhood
    {u : ℝ → ℝ} {a b : ℝ} {C : Set ℝ}
    (hab : a < b)
    (hC : C = Set.Ioo a b)
    (hright :
      ∃ η > 0, ∀ θ ∈ Set.Ioo (max a (b - η)) b, 0 < u θ) :
    ∃ sigma ∈ C, 0 ≤ u sigma := by
  rcases hright with ⟨η, hη_pos, hpos⟩
  let sigma : ℝ := (max a (b - η) + b) / 2
  have hsigma_mem_right : sigma ∈ Set.Ioo (max a (b - η)) b := by
    -- Choose the midpoint of the right-hand neighborhood.
    have hlower : max a (b - η) < b := by
      refine max_lt hab ?_
      linarith
    constructor <;> dsimp [sigma] <;> linarith
  have hsigma_mem_C : sigma ∈ C := by
    -- Rewrite back to the ambient component `C`.
    rw [hC]
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hsigma_mem_right.1, hsigma_mem_right.2⟩
  exact ⟨sigma, hsigma_mem_C, le_of_lt (hpos sigma hsigma_mem_right)⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a left-hand negative neighborhood in
`C = Ioo a b` already provides an interior weak nonpositive witness. -/
lemma existsWeakNonpos_of_leftNegativeNeighborhood
    {u : ℝ → ℝ} {a b : ℝ} {C : Set ℝ}
    (hab : a < b)
    (hC : C = Set.Ioo a b)
    (hleft :
      ∃ η > 0, ∀ θ ∈ Set.Ioo a (min (a + η) b), u θ < 0) :
    ∃ sigma ∈ C, u sigma ≤ 0 := by
  rcases hleft with ⟨η, hη_pos, hneg⟩
  let sigma : ℝ := (a + min (a + η) b) / 2
  have hsigma_mem_left : sigma ∈ Set.Ioo a (min (a + η) b) := by
    -- Choose the midpoint of the left-hand neighborhood.
    have hupper : a < min (a + η) b := by
      refine lt_min ?_ hab
      linarith
    constructor <;> dsimp [sigma] <;> linarith
  have hsigma_mem_C : sigma ∈ C := by
    -- Rewrite back to the ambient component `C`.
    rw [hC]
    exact ⟨hsigma_mem_left.1, lt_of_lt_of_le hsigma_mem_left.2 (min_le_right _ _)⟩
  exact ⟨sigma, hsigma_mem_C, le_of_lt (hneg sigma hsigma_mem_left)⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a strictly positive selector on the
entire witness component `C₀ = Ioo a b` already supplies an interior weak nonnegative witness. -/
lemma existsWeakNonneg_onPositiveWitnessComponent
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ) :
    ∃ sigma ∈ C₀, 0 ≤ selectorθ sigma := by
  -- Reuse the endpoint-neighborhood package for the positive branch, then turn it into an actual
  -- interior weak-sign witness.
  exact
    existsWeakNonneg_of_rightPositiveNeighborhood hab hC₀_eq <|
      positiveComponent_rightPositiveNeighborhood hab hC₀_eq hposall

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a strictly negative selector on the
entire witness component `C₀ = Ioo a b` already supplies an interior weak nonpositive witness. -/
lemma existsWeakNonpos_onNegativeWitnessComponent
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0) :
    ∃ sigma ∈ C₀, selectorθ sigma ≤ 0 := by
  -- The negative branch is symmetric: start from the left-hand neighborhood and select a concrete
  -- interior weak-sign point.
  exact
    existsWeakNonpos_of_leftNegativeNeighborhood hab hC₀_eq <|
      negativeComponent_leftNegativeNeighborhood hab hC₀_eq hnegall

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a strictly negative selector value at
the left endpoint already produces the left-boundary analysis consumed by
`boundaryNeighborhoods_giveZeroInOpenInterval`. -/
lemma leftBoundaryAnalysis_of_leftEndpointNeg
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_a_neg : selectorθ a < 0) :
    (∃ η ∈ C₀, selectorθ η = 0) ∨
      ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0 := by
  -- A strict left-endpoint sign is already the exact one-sided neighborhood package needed by the
  -- interval zero extractor.
  exact Or.inr <|
      leftNeighborhood_lt_zero_of_continuous_of_lt
      hab hselectorTheta_cont hselector_a_neg

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a strictly positive selector value at
the right endpoint already produces the right-boundary analysis consumed by
`boundaryNeighborhoods_giveZeroInOpenInterval`. -/
lemma rightBoundaryAnalysis_of_rightEndpointPos
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_b_pos : 0 < selectorθ b) :
    (∃ η ∈ C₀, selectorθ η = 0) ∨
      ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ := by
  -- The right endpoint is symmetric: one strict positive value gives the needed right-hand
  -- neighborhood immediately.
  exact Or.inr <|
      rightNeighborhood_gt_zero_of_continuous_of_lt
      hab hselectorTheta_cont hselector_b_pos

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): opposite selector signs at the two
ends of an ordered witness window produce a selector zero inside that same closed angle interval.
-/
lemma orderedWindowZero_of_mixedWitnessSigns
    {selectorθ : ℝ → ℝ} {thetaNeg thetaPos : ℝ}
    (hthetaNeg_lt_thetaPos : thetaNeg < thetaPos)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselectorNeg : selectorθ thetaNeg < 0)
    (hselectorPos : 0 < selectorθ thetaPos) :
    ∃ θ₀ ∈ Set.Icc thetaNeg thetaPos, selectorθ θ₀ = 0 := by
  have hsurj :
      Set.Icc (selectorθ thetaNeg) (selectorθ thetaPos) ⊆
        selectorθ '' Set.Icc thetaNeg thetaPos :=
    intermediate_value_Icc hthetaNeg_lt_thetaPos.le hselectorTheta_cont.continuousOn
  have hzero_mem :
      (0 : ℝ) ∈ Set.Icc (selectorθ thetaNeg) (selectorθ thetaPos) := by
    -- The mixed witness signs place `0` between the two endpoint selector values.
    exact ⟨le_of_lt hselectorNeg, le_of_lt hselectorPos⟩
  rcases hsurj hzero_mem with ⟨θ₀, hθ₀_mem, hθ₀_zero⟩
  -- Keep the zero witness tied to the ordered angle interval for later component geometry.
  exact ⟨θ₀, hθ₀_mem, hθ₀_zero⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a selector zero produced inside a
closed witness window is automatically an interior point once the two window endpoints have strict
opposite signs. -/
lemma orderedWindowZero_mem_Ioo_of_endpointSigns
    {selectorθ : ℝ → ℝ} {thetaNeg thetaPos θ₀ : ℝ}
    (hθ₀_window : θ₀ ∈ Set.Icc thetaNeg thetaPos)
    (hθ₀_zero : selectorθ θ₀ = 0)
    (hselectorNeg : selectorθ thetaNeg < 0)
    (hselectorPos : 0 < selectorθ thetaPos) :
    θ₀ ∈ Set.Ioo thetaNeg thetaPos := by
  constructor
  · by_contra hnot
    have hθ₀_eq : θ₀ = thetaNeg := by
      exact le_antisymm (le_of_not_gt hnot) hθ₀_window.1
    exact (ne_of_lt hselectorNeg) <| by simpa [hθ₀_eq] using hθ₀_zero
  · by_contra hnot
    have hθ₀_eq : θ₀ = thetaPos := by
      exact le_antisymm hθ₀_window.2 (le_of_not_gt hnot)
    exact (ne_of_gt hselectorPos) <| by simpa [hθ₀_eq] using hθ₀_zero

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a left-hand negative neighborhood
inside `C₀ = Ioo a b` is incompatible with strict positivity of the selector on the whole
component. -/
lemma leftNegativeNeighborhoodContradictsPositiveWitnessComponent
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ)
    (hleft :
      ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0) :
    False := by
  rcases hleft with ⟨δ, hδ_pos, hleftNeg⟩
  let θ : ℝ := (a + min (a + δ) b) / 2
  have hθ_mem_left : θ ∈ Set.Ioo a (min (a + δ) b) := by
    -- Use the midpoint of the one-sided neighborhood to test both sign packages at one point.
    have hupper : a < min (a + δ) b := by
      refine lt_min ?_ hab
      linarith
    constructor <;> dsimp [θ] <;> linarith
  have hθ_mem_C₀ : θ ∈ C₀ := by
    -- Rewrite back to the connected-component interval before invoking the positive branch.
    rw [hC₀_eq]
    exact ⟨hθ_mem_left.1, lt_of_lt_of_le hθ_mem_left.2 (min_le_right _ _)⟩
  -- The midpoint cannot be both strictly positive and strictly negative.
  linarith [hposall θ hθ_mem_C₀, hleftNeg θ hθ_mem_left]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a right-hand positive neighborhood
inside `C₀ = Ioo a b` is incompatible with strict negativity of the selector on the whole
component. -/
lemma rightPositiveNeighborhoodContradictsNegativeWitnessComponent
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0)
    (hright :
      ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ) :
    False := by
  rcases hright with ⟨δ, hδ_pos, hrightPos⟩
  let θ : ℝ := (max a (b - δ) + b) / 2
  have hθ_mem_right : θ ∈ Set.Ioo (max a (b - δ)) b := by
    -- Use the symmetric midpoint of the right-hand neighborhood.
    have hlower : max a (b - δ) < b := by
      refine max_lt hab ?_
      linarith
    constructor <;> dsimp [θ] <;> linarith
  have hθ_mem_C₀ : θ ∈ C₀ := by
    -- The midpoint already lies in the ambient open component interval.
    rw [hC₀_eq]
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hθ_mem_right.1, hθ_mem_right.2⟩
  -- Again the midpoint cannot satisfy the two strict opposite sign claims simultaneously.
  linarith [hnegall θ hθ_mem_C₀, hrightPos θ hθ_mem_right]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the left endpoint analysis of a
positive witness component already yields either an interior zero or a left-hand negative
neighborhood, the standard interval zero-extractor produces a selector zero on that component. -/
lemma componentZero_of_leftBoundaryAnalysis_onPositiveWitnessComponent
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hposall : ∀ η ∈ C₀, 0 < selectorθ η)
    (hleft :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0) :
    ∃ θ ∈ C₀, selectorθ θ = 0 := by
  have hright :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ := by
    -- Strict positivity on the whole component already provides the right boundary analysis.
    exact Or.inr <| positiveComponent_rightPositiveNeighborhood hab hC₀_eq hposall
  -- Once both one-sided boundary analyses are available, the generic open-interval extractor
  -- returns the desired component zero.
  exact
    boundaryNeighborhoods_giveZeroInOpenInterval
      hab hC₀_eq hzero hleft hright

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the right endpoint analysis of a
negative witness component already yields either an interior zero or a right-hand positive
neighborhood, the standard interval zero-extractor produces a selector zero on that component. -/
lemma componentZero_of_rightBoundaryAnalysis_onNegativeWitnessComponent
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hnegall : ∀ η ∈ C₀, selectorθ η < 0)
    (hright :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ) :
    ∃ θ ∈ C₀, selectorθ θ = 0 := by
  have hleft :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0 := by
    -- The all-negative branch gives the left boundary analysis for free.
    exact Or.inr <| negativeComponent_leftNegativeNeighborhood hab hC₀_eq hnegall
  -- Feed the two one-sided analyses into the same zero-extraction interface.
  exact
    boundaryNeighborhoods_giveZeroInOpenInterval
      hab hC₀_eq hzero hleft hright

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a point in the left window
`Icc thetaNeg thetaW` that does not belong to `Ioo a b` must lie on or before the left endpoint
`a`. -/
lemma le_leftEndpoint_of_mem_leftWindow_and_not_mem_Ioo
    {sigma a b thetaW : ℝ}
    (hthetaW_lt_b : thetaW < b)
    (hsigma_mem : sigma ∈ Set.Icc sigma thetaW)
    (hsigma_not_mem : sigma ∉ Set.Ioo a b) :
    sigma ≤ a := by
  by_contra hsigma_gt
  have ha_lt_sigma : a < sigma := lt_of_not_ge hsigma_gt
  have hsigma_lt_b : sigma < b := lt_of_le_of_lt hsigma_mem.2 hthetaW_lt_b
  exact hsigma_not_mem ⟨ha_lt_sigma, hsigma_lt_b⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a point in the right window
`Icc thetaW thetaPos` that does not belong to `Ioo a b` must lie on or after the right endpoint
`b`. -/
lemma rightEndpoint_le_of_mem_rightWindow_and_not_mem_Ioo
    {sigma a b thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hsigma_mem : sigma ∈ Set.Icc thetaW sigma)
    (hsigma_not_mem : sigma ∉ Set.Ioo a b) :
    b ≤ sigma := by
  by_contra hsigma_lt
  have hsigma_lt_b : sigma < b := lt_of_not_ge hsigma_lt
  have ha_lt_sigma : a < sigma := lt_of_lt_of_le ha_lt_thetaW hsigma_mem.1
  exact hsigma_not_mem ⟨ha_lt_sigma, hsigma_lt_b⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the witness reference zero `η`
has fixed the shifted packet model `Fη`, the ordered-window zero `θ₀` still admits one explicit
integral period shift whose normalized packet lies in the principal strip. -/
lemma thetaZeroShiftedPacketData_of_referenceZero
    {g Fη : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0) :
    ∃ kθ₀ : ℤ,
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I)) ∧
        (-Real.pi <
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
                (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))).im ∧
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))).im <
            Real.pi) := by
  -- Route correction: the current file naturally produces the auxiliary shifted packet at `θ₀`
  -- directly, so this helper now packages exactly that existing owner API instead of over-asking
  -- for the unshifted `Fη` packet to be in the principal strip.
  exact
    periodShiftedNormalizedPacketAndStrip_of_selectorEqZero
      hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatioη hθ₀_zero

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): after fixing the shifted witness
model `Fη`, the ordered-window selector zero `θ₀` can be packaged as one residual-period packet
whose selector still vanishes and whose shifted normal form already lies in the principal strip. -/
lemma shiftedThetaZeroPacketBundle_of_referenceZero
    {g Fη : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0)
    (hθ₀_normalized_re_zero :
      Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (Fη (circleMap 0 ρ θ₀)).re = 0) :
    ∃ kθ₀ : ℤ,
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I)) ∧
        Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0 ∧
        (-Real.pi <
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
                (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))).im ∧
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))).im <
            Real.pi) := by
  obtain ⟨kθ₀, hpacket, hstrip⟩ :=
    -- The owner theorem provides the residual-period packet together with its shifted strip.
    thetaZeroShiftedPacketData_of_referenceZero
      hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatioη hθ₀_zero
  have hselector_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0 := by
    -- The shifted packet and the normalized real-part vanishing recover the selector zero again.
    exact
      selectorEqZero_of_shiftedThetaZeroPacket
        hρpos hpacket hθ₀_normalized_re_zero
  exact ⟨kθ₀, hpacket, hselector_zero, hstrip⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): in the all-positive witness-component
branch, once the left endpoint is known to carry a strict negative selector value, the standard
left boundary analysis is already available. -/
lemma leftBoundaryAnalysis_of_positiveWitnessFirstCrossing
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_a_neg : selectorθ a < 0) :
    (∃ η ∈ C₀, selectorθ η = 0) ∨
      ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0 := by
  -- Once the genuine first-crossing analysis has produced the strict endpoint sign, the remaining
  -- left boundary package is exactly the standard continuity lemma already available above.
  exact
    leftBoundaryAnalysis_of_leftEndpointNeg
      hab hselectorTheta_cont hselector_a_neg

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): in the all-negative witness-component
branch, once the right endpoint is known to carry a strict positive selector value, the standard
right boundary analysis is already available. -/
lemma rightBoundaryAnalysis_of_negativeWitnessLastExit
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_b_pos : 0 < selectorθ b) :
    (∃ η ∈ C₀, selectorθ η = 0) ∨
      ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ := by
  -- This is the symmetric endpoint-sign consumer: once the last-exit step has produced the strict
  -- right-endpoint sign, continuity immediately gives the required right boundary neighborhood.
  exact
    rightBoundaryAnalysis_of_rightEndpointPos
      hab hselectorTheta_cont hselector_b_pos

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the witness-reference packet at
`thetaW` and the ordered-window packet at `θ₀` are rewritten in one common shifted model, their
imaginary parts differ by the expected explicit angular transport. -/
lemma thetaWThetaZeroShiftedPacketComparisonData_withPeriod
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n kθ₀ : ℤ} {c : ℂ} {thetaW θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hthetaW_logRatio_packetη :
      Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          Fη (circleMap 0 ρ thetaW))
    (hθ₀_logRatio_packet_shifted :
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))) :
    (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im -
        (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
      (n : ℝ) * (θ₀ - thetaW) +
        ((Fη (circleMap 0 ρ θ₀)).im - (Fη (circleMap 0 ρ thetaW)).im) +
        (kθ₀ : ℝ) * (2 * Real.pi) := by
  have hlogρ_im : (Complex.log (ρ : ℂ)).im = 0 := by
    -- The positive circle radius contributes no imaginary part to the transport term.
    rw [← Complex.ofReal_log hρpos.le]
    simp
  have hthetaW_linear_im :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I)).im = (n : ℝ) * thetaW := by
    -- Expand the linear term at the witness-reference angle once.
    rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp [hlogρ_im, mul_comm]
  have hθ₀_linear_im :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I)).im = (n : ℝ) * θ₀ := by
    -- The same simplification applies at the ordered-window zero.
    rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp [hlogρ_im, mul_comm]
  have hperiod_im :
      (kθ₀ * (2 * (Real.pi : ℂ) * Complex.I)).im = (kθ₀ : ℝ) * (2 * Real.pi) := by
    -- The explicit integral correction contributes exactly a real multiple of `2π`.
    rw [Complex.mul_im]
    simp [mul_comm]
  have hthetaW_im :
      (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (Complex.log c).im + (n : ℝ) * thetaW + (Fη (circleMap 0 ρ thetaW)).im := by
    -- Project the exact witness-reference packet to imaginary parts.
    have him := congrArg Complex.im hthetaW_logRatio_packetη
    simpa [Complex.add_im, hthetaW_linear_im, add_assoc, add_left_comm, add_comm] using him
  have hθ₀_im :
      (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im =
        (Complex.log c).im + (n : ℝ) * θ₀ + (Fη (circleMap 0 ρ θ₀)).im +
          (kθ₀ : ℝ) * (2 * Real.pi) := by
    -- The shifted `θ₀` packet differs from the exact model by that explicit period term.
    have him := congrArg Complex.im hθ₀_logRatio_packet_shifted
    simpa [Complex.add_im, hθ₀_linear_im, hperiod_im, add_assoc, add_left_comm, add_comm] using him
  -- Subtract the two projected packet identities; only the explicit transport and residual period
  -- remain.
  linarith

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the witness-reference packet at
`thetaW` and the ordered-window packet at `θ₀` are rewritten in one common shifted model, their
imaginary parts differ by the expected explicit angular transport. -/
lemma thetaWThetaZeroShiftedPacketComparisonData
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n kθ₀ : ℤ} {c : ℂ} {thetaW θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hthetaW_logRatio_packetη :
      Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
          Fη (circleMap 0 ρ thetaW))
    (hkθ₀_zero : kθ₀ = 0)
    (hθ₀_logRatio_packet_shifted :
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))) :
    (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im -
        (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
      (n : ℝ) * (θ₀ - thetaW) +
        ((Fη (circleMap 0 ρ θ₀)).im - (Fη (circleMap 0 ρ thetaW)).im) := by
  -- Route correction: the owner comparison is the with-period lemma. Once the theorem-local
  -- period-killing step supplies `kθ₀ = 0`, the exact comparison is a pure simplification.
  simpa [hkθ₀_zero, add_assoc, add_left_comm, add_comm] using
    thetaWThetaZeroShiftedPacketComparisonData_withPeriod
      hρpos hthetaW_logRatio_packetη hθ₀_logRatio_packet_shifted

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the shifted `θ₀` packet can be
reassociated so that the residual `kθ₀ * (2 * π * I)` period appears as a separate summand. -/
lemma shiftedThetaZeroPacket_eq_unshiftedNormal_plus_period
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n kθ₀ : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hθ₀_logRatio_packet_shifted :
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))) :
    Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
      (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          Fη (circleMap 0 ρ θ₀)) +
        kθ₀ * (2 * (Real.pi : ℂ) * Complex.I) := by
  -- Reassociate the shifted packet once so later period-killing steps can read the residual
  -- `2π i` term explicitly.
  simpa [add_assoc, add_left_comm, add_comm] using hθ₀_logRatio_packet_shifted

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the legal selector-zero packet
at `η` is exact in the shifted model `Fη`, the two same-circle imaginary-part comparisons through
`thetaW` recover the explicit normalized imaginary formula at `θ₀`; any residual integral period
appears exactly as an added `(kθ₀ : ℝ) * (2 * π)` term. -/
lemma thetaZeroImaginaryFormula_of_referencePacketComparisons
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n kθ₀ : ℤ} {c : ℂ} {η thetaW θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η))
    (hη_thetaW_logRatio_im_difference :
      (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im -
          (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (n : ℝ) * (η - thetaW) +
          ((Fη (circleMap 0 ρ η)).im - (Fη (circleMap 0 ρ thetaW)).im))
    (hthetaW_θ₀_logRatio_im_difference :
      (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im -
          (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (n : ℝ) * (θ₀ - thetaW) +
          ((Fη (circleMap 0 ρ θ₀)).im - (Fη (circleMap 0 ρ thetaW)).im) +
          (kθ₀ : ℝ) * (2 * Real.pi)) :
    (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im =
      (Complex.log c).im + (n : ℝ) * θ₀ + (Fη (circleMap 0 ρ θ₀)).im +
        (kθ₀ : ℝ) * (2 * Real.pi) := by
  have hlogρ_im : (Complex.log (ρ : ℂ)).im = 0 := by
    -- The positive circle radius contributes no imaginary part to the linear transport term.
    rw [← Complex.ofReal_log hρpos.le]
    simp
  have hη_linear_im :
      ((n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I)).im = (n : ℝ) * η := by
    -- Expand the `η`-transport term once before eliminating the witness-reference angle.
    rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
    simp [hlogρ_im, mul_comm]
  have hη_im :
      (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im =
        (Complex.log c).im + (n : ℝ) * η + (Fη (circleMap 0 ρ η)).im := by
    -- Project the exact legal packet at `η` to its explicit imaginary-part formula.
    have him := congrArg Complex.im hη_logRatio_packet_zeroPeriod
    simpa [Complex.add_im, hη_linear_im, add_assoc, add_left_comm, add_comm] using him
  -- Eliminate the shared witness-reference angle `thetaW`; the only surviving residual is the
  -- explicit integral period already present in the `thetaW ↔ θ₀` comparison.
  linarith [hη_im, hη_thetaW_logRatio_im_difference, hthetaW_θ₀_logRatio_im_difference]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the legal zero packet at `η`, the
same-circle `η ↔ thetaW` comparison, and the shifted `thetaW ↔ θ₀` comparison together force the
ordered-window packet at `θ₀` back into the unshifted witness model. -/
lemma thetaZeroPacket_of_shiftedThetaZeroPacketComparisons
    {g Fη : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {η thetaW θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η))
    (hη_thetaW_logRatio_im_difference :
      (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im -
          (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (n : ℝ) * (η - thetaW) +
          ((Fη (circleMap 0 ρ η)).im - (Fη (circleMap 0 ρ thetaW)).im))
    (hthetaW_θ₀_logRatio_im_difference :
      (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im -
          (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (n : ℝ) * (θ₀ - thetaW) +
          ((Fη (circleMap 0 ρ θ₀)).im - (Fη (circleMap 0 ρ thetaW)).im))
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0) :
    Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
      Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
        Fη (circleMap 0 ρ θ₀) := by
  have hη_im :
      (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im =
        (Complex.log c).im + (n : ℝ) * θ₀ + (Fη (circleMap 0 ρ θ₀)).im := by
    -- Reuse the generic reference-transport helper with vanishing residual period.
    simpa using
      thetaZeroImaginaryFormula_of_referencePacketComparisons
        (kθ₀ := 0)
        hρpos
        hη_logRatio_packet_zeroPeriod
        hη_thetaW_logRatio_im_difference
        (by
          simpa using hthetaW_θ₀_logRatio_im_difference)
  have hθ₀_normalized_im_eq :
      (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im =
        (Complex.log c).im + (n : ℝ) * θ₀ + (Fη (circleMap 0 ρ θ₀)).im := hη_im
  have hθ₀_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im < Real.pi := by
    have hlogρ_im : (Complex.log (ρ : ℂ)).im = 0 := by
      -- The positive circle radius contributes no imaginary part to the linear transport term.
      rw [← Complex.ofReal_log hρpos.le]
      simp
    have hθ₀_logRatio_im_strip :
        -Real.pi <
            (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im ∧
          (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im < Real.pi := by
      -- The selector-zero quotient at `θ₀` stays in the principal strip once the quotient is
      -- known to be honest.
      exact
        logImDiv_mem_openInterval_of_selectorEqZero
          (hg_nonzero θ₀)
          (hone_sub_nonzero θ₀)
          hθ₀_zero
    have hθ₀_linear_im :
        ((n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I)).im = (n : ℝ) * θ₀ := by
      -- The same linear-term simplification applies at the ordered-window zero.
      rw [mul_add, Complex.add_im, Complex.mul_im, Complex.mul_im]
      simp [hlogρ_im, mul_comm]
    -- Rewrite the unshifted normal-form imaginary part back to the quotient logarithm at `θ₀`.
    simpa [Complex.add_im, hθ₀_linear_im, add_assoc, add_left_comm, add_comm,
      hθ₀_normalized_im_eq] using hθ₀_logRatio_im_strip
  -- The missing `θ₀` strip data is now restored, so the existing exact-packet transport lemma
  -- applies directly.
  exact
    referenceTransportedThetaZeroPacket_of_orderedWindowZero
      hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatioη
      hθ₀_zero hθ₀_normalized_im_strip

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the residual period at the
ordered-window zero `θ₀` is already known to vanish, the shifted principal-strip control is
exactly the unshifted principal-strip control for the witness model `Fη`. -/
lemma thetaZeroNormalizedImStrip_of_referenceZero
    {Fη : ℂ → ℂ} {ρ : ℝ} {n kθ₀ : ℤ} {c : ℂ} {θ₀ : ℝ}
    (hkθ₀_zero : kθ₀ = 0)
    (hθ₀_shifted_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            (Fη (circleMap 0 ρ θ₀) + kθ₀ * (2 * (Real.pi : ℂ) * Complex.I))).im <
          Real.pi) :
    -Real.pi <
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im ∧
      (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          Fη (circleMap 0 ρ θ₀)).im < Real.pi := by
  -- Once the integral period vanishes, the shifted-strip hypothesis is literally the desired
  -- unshifted principal-strip statement.
  simpa [hkθ₀_zero, add_assoc, add_left_comm, add_comm] using hθ₀_shifted_im_strip

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the legal selector-zero packet
at `η` and the ordered-window selector-zero packet at `θ₀` are both exact in the same shifted
witness model `Fη`, each normalized packet already lies in the principal strip. -/
lemma normalizedPacketImStrips_of_commonShiftedModelZeros
    {g Fη : ℂ → ℂ} {ρ : ℝ} {n : ℤ} {c : ℂ} {η θ₀ : ℝ}
    (hg_nonzero_η : g (circleMap 0 ρ η) ≠ 0)
    (hone_sub_nonzero_η : 1 - g (circleMap 0 ρ η) ≠ 0)
    (hg_nonzero_θ₀ : g (circleMap 0 ρ θ₀) ≠ 0)
    (hone_sub_nonzero_θ₀ : 1 - g (circleMap 0 ρ θ₀) ≠ 0)
    (hηzero :
      Real.log ‖g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))‖ = 0)
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0)
    (hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η))
    (hθ₀_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          Fη (circleMap 0 ρ θ₀)) :
    (-Real.pi <
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρ η)).im ∧
      (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η)).im < Real.pi) ∧
      (-Real.pi <
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im ∧
      (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          Fη (circleMap 0 ρ θ₀)).im < Real.pi) := by
  have hη_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
              Fη (circleMap 0 ρ η)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρ η)).im < Real.pi := by
    -- The legal selector-zero packet at `η` is already exact, so its normalized value lies in the
    -- principal strip immediately.
    exact
      normalizedPacketImStrip_of_selectorEqZero_of_packetEq
        hg_nonzero_η hone_sub_nonzero_η hηzero hη_logRatio_packet_zeroPeriod
  have hθ₀_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im < Real.pi := by
    -- The ordered-window zero has already been transported back to the exact same shifted model.
    exact
      normalizedPacketImStrip_of_selectorEqZero_of_packetEq
        hg_nonzero_θ₀
        hone_sub_nonzero_θ₀
        hθ₀_zero hθ₀_logRatio_packet_zeroPeriod
  -- The two exact selector-zero packets are already individually normalized; keep both strip
  -- facts together so the remaining contradiction can consume them without redoing this transport.
  exact ⟨hη_normalized_im_strip, hθ₀_normalized_im_strip⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the legal selector-zero packet at
`η` and the ordered-window selector-zero data at `θ₀` have both been transported into the same
shifted witness model `Fη`, the `θ₀` packet is exact there and the two normalized packets share the
principal-strip control needed by the remaining interior obstruction. -/
lemma commonShiftedPacketBundle_of_referenceZero
    {g Fη : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {η thetaW θ₀ : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hηzero :
      Real.log ‖g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))‖ = 0)
    (hθ₀_zero :
      Real.log ‖g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))‖ = 0)
    (hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρ η))
    (hη_thetaW_logRatio_im_difference :
      (Complex.log (g (circleMap 0 ρ η) / (1 - g (circleMap 0 ρ η)))).im -
          (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (n : ℝ) * (η - thetaW) +
          ((Fη (circleMap 0 ρ η)).im - (Fη (circleMap 0 ρ thetaW)).im))
    (hthetaW_θ₀_logRatio_im_difference :
      (Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀)))).im -
          (Complex.log (g (circleMap 0 ρ thetaW) / (1 - g (circleMap 0 ρ thetaW)))).im =
        (n : ℝ) * (θ₀ - thetaW) +
          ((Fη (circleMap 0 ρ θ₀)).im - (Fη (circleMap 0 ρ thetaW)).im)) :
    Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
      Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
        Fη (circleMap 0 ρ θ₀) ∧
      ((-Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
              Fη (circleMap 0 ρ η)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρ η)).im < Real.pi) ∧
        (-Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im < Real.pi)) := by
  have hθ₀_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρ θ₀) / (1 - g (circleMap 0 ρ θ₀))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
          Fη (circleMap 0 ρ θ₀) := by
    -- Route correction: use the owner transport lemma once, then keep the interior proof in the
    -- exact common-model spelling instead of carrying another shifted-period argument inline.
    exact
      thetaZeroPacket_of_shiftedThetaZeroPacketComparisons
        hρpos hc_ne hzeta_mem hg_nonzero hone_sub_nonzero hEqRatioη
        hη_logRatio_packet_zeroPeriod
        hη_thetaW_logRatio_im_difference
        hthetaW_θ₀_logRatio_im_difference
        hθ₀_zero
  have hnormalizedPacketStrips :
      (-Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
              Fη (circleMap 0 ρ η)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρ η)).im < Real.pi) ∧
        (-Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (circleMap 0 ρ θ₀)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
            Fη (circleMap 0 ρ θ₀)).im < Real.pi) := by
    -- Once both selector-zero packets are exact in one model, the principal-strip control is the
    -- existing paired normalization lemma.
    exact
      normalizedPacketImStrips_of_commonShiftedModelZeros
        (hg_nonzero η)
        (hone_sub_nonzero η)
        (hg_nonzero θ₀)
        (hone_sub_nonzero θ₀)
        hηzero
        hθ₀_zero
        hη_logRatio_packet_zeroPeriod
        hθ₀_logRatio_packet_zeroPeriod
  exact ⟨hθ₀_logRatio_packet_zeroPeriod, hnormalizedPacketStrips⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): in the all-positive branch, once the
missing first-crossing step has already been packaged as a left boundary analysis on `C₀ = Ioo a
b`, the existing component-zero extractor closes the contradiction immediately. -/
lemma leftBoundaryContradiction_of_positiveWitnessFirstCrossing
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hposall : ∀ η ∈ C₀, 0 < selectorθ η)
    (hleft :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0) :
    False := by
  have hcomponentZero :
      ∃ θ ∈ C₀, selectorθ θ = 0 := by
    -- Once the left boundary analysis is available in the right disjunctive shape, the existing
    -- interval extractor returns a selector zero on the positive witness component.
    exact
      componentZero_of_leftBoundaryAnalysis_onPositiveWitnessComponent
        hab hC₀_eq hzero hposall hleft
  rcases hcomponentZero with ⟨η, hηC₀, hηzero⟩
  -- That component zero contradicts strict positivity on all of `C₀`.
  linarith [hposall η hηC₀]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): in the all-negative branch, once the
missing last-exit step has already been packaged as a right boundary analysis on `C₀ = Ioo a b`,
the existing component-zero extractor again closes the contradiction immediately. -/
lemma rightBoundaryContradiction_of_negativeWitnessLastExit
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hnegall : ∀ η ∈ C₀, selectorθ η < 0)
    (hright :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ) :
    False := by
  have hcomponentZero :
      ∃ θ ∈ C₀, selectorθ θ = 0 := by
    -- The right boundary analysis feeds directly into the symmetric interval zero extractor.
    exact
      componentZero_of_rightBoundaryAnalysis_onNegativeWitnessComponent
        hab hC₀_eq hzero hnegall hright
  rcases hcomponentZero with ⟨η, hηC₀, hηzero⟩
  -- That zero contradicts strict negativity on the whole witness component.
  linarith [hnegall η hηC₀]

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on a positive witness component, a
strictly negative left endpoint selector value already closes the branch via the standard
left-boundary contradiction interface. -/
lemma positiveWitnessComponentContradiction_of_leftEndpointNeg
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hselectorTheta_cont : Continuous selectorθ)
    (hposall : ∀ η ∈ C₀, 0 < selectorθ η)
    (hselector_a_neg : selectorθ a < 0) :
    False := by
  have hleftBoundary :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0 := by
    -- A strict left endpoint sign is exactly the left-boundary analysis consumed by the positive
    -- branch contradiction adapter.
    exact
      leftBoundaryAnalysis_of_positiveWitnessFirstCrossing
        hab
        hselectorTheta_cont
        hselector_a_neg
  -- Feed the resulting left-boundary analysis into the already packaged positive-branch
  -- contradiction.
  exact
    leftBoundaryContradiction_of_positiveWitnessFirstCrossing
      hab
      hC₀_eq
      hzero
      hposall
      hleftBoundary

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): on a negative witness component, a
strictly positive right endpoint selector value already closes the branch via the standard
right-boundary contradiction interface. -/
lemma negativeWitnessComponentContradiction_of_rightEndpointPos
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hselectorTheta_cont : Continuous selectorθ)
    (hnegall : ∀ η ∈ C₀, selectorθ η < 0)
    (hselector_b_pos : 0 < selectorθ b) :
    False := by
  have hrightBoundary :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ := by
    -- The strict right endpoint sign is the exact right-boundary analysis needed below.
    exact
      rightBoundaryAnalysis_of_negativeWitnessLastExit
        hab
        hselectorTheta_cont
        hselector_b_pos
  -- The prebuilt negative-branch contradiction adapter now closes immediately.
  exact
    rightBoundaryContradiction_of_negativeWitnessLastExit
      hab
      hC₀_eq
      hzero
      hnegall
      hrightBoundary

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the selector trichotomy on one frozen
witness component, together with one interior weak nonpositive point and one interior weak
nonnegative point, already forces a selector zero on that same component. -/
lemma witnessComponentZero_of_weakSigns
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ}
    (htrichotomy :
      (∃ η ∈ C₀, selectorθ η = 0) ∨
        (∀ η ∈ C₀, 0 < selectorθ η) ∨
        (∀ η ∈ C₀, selectorθ η < 0))
    (hweakNonpos : ∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0)
    (hweakNonneg : ∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) :
    ∃ θ ∈ C₀, selectorθ θ = 0 := by
  -- This packages the generic weak-sign zero extractor in the exact witness-component spelling
  -- used by the final descended-circle contradiction.
  exact
    existsZeroOfWeakSignsOfZeroOrStrictSign
      htrichotomy hweakNonpos hweakNonneg

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): any consequence of an interior
selector zero on `C₀` already follows from one weak nonpositive and one weak nonnegative witness
on that same component. -/
lemma consequence_of_componentWeakSigns
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {P : Prop}
    (htrichotomy :
      (∃ η ∈ C₀, selectorθ η = 0) ∨
        (∀ η ∈ C₀, 0 < selectorθ η) ∨
        (∀ η ∈ C₀, selectorθ η < 0))
    (hzero_consequence :
      ∀ ⦃η : ℝ⦄, η ∈ C₀ → selectorθ η = 0 → P)
    (hweakNonpos : ∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0)
    (hweakNonneg : ∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) :
    P := by
  rcases witnessComponentZero_of_weakSigns htrichotomy hweakNonpos hweakNonneg with
    ⟨η, hηC₀, hηzero⟩
  -- First extract a genuine selector zero on the component, then feed it to the supplied
  -- consequence consumer.
  exact hzero_consequence hηC₀ hηzero

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if the desired smaller-circle uniform
branch does not yet exist, then every smaller scale still contains a centered circle with mixed
large reciprocal logs on the two reciprocal branches. -/
lemma exists_mixedLargeReciprocalLogs_on_smallerCircle_of_no_smallCircleUniformReciprocalBranch
    {g : ℂ → ℂ} {ε ρ T δ : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hρpos : 0 < ρ)
    (hδ : 0 < δ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hnoSmall :
      ¬ ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧
        ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
          ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T)) :
    ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
      ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
        T < Real.log ‖(g zNeg)⁻¹‖ ∧
          T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
  let δ' : ℝ := min δ (ρ / 2)
  have hδ' : 0 < δ' := by
    -- Shrink below both `δ` and `ρ / 2` so the next witness circle is automatically stricly
    -- smaller than the original one.
    dsimp [δ']
    exact lt_min hδ (half_pos hρpos)
  obtain ⟨ρ', hρ'pos, hρ'small, _, _, _⟩ :=
    exercise16Hit_onSmallCircle hess hε hδ' hg
  have hρ'ltδ' : ρ' < δ' := by
    exact lt_of_lt_of_le hρ'small (min_le_left δ' ε)
  have hρ'ltδ : ρ' < δ := by
    -- The witness circle sits below the requested scale because `δ' ≤ δ`.
    exact lt_of_lt_of_le hρ'ltδ' (min_le_left δ (ρ / 2))
  have hρ'ltρhalf : ρ' < ρ / 2 := by
    -- It also sits below `ρ / 2`, hence is strictly smaller than the current circle.
    exact lt_of_lt_of_le hρ'ltδ' (min_le_right δ (ρ / 2))
  have hρ'ltρ : ρ' < ρ := by
    linarith
  by_cases hginv : ∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T
  · -- A uniform `g⁻¹` bound on this smaller circle would already close the target.
    exact False.elim <| hnoSmall ⟨ρ', hρ'pos, hρ'ltρ, Or.inl hginv⟩
  by_cases honeSubInv : ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T
  · -- The symmetric `(1 - g)⁻¹` bound is excluded for the same reason.
    exact False.elim <| hnoSmall ⟨ρ', hρ'pos, hρ'ltρ, Or.inr honeSubInv⟩
  push_neg at hginv honeSubInv
  rcases hginv with ⟨zNeg, hzNeg_norm, hzNeg_large_exp⟩
  rcases honeSubInv with ⟨zPos, hzPos_norm, hzPos_large_exp⟩
  have hzNeg_mem : zNeg ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · -- Points on the smaller witness circle still lie inside the punctured `ε`-ball.
      have hρ'ltε : ρ' < ε := lt_of_lt_of_le hρ'small (min_le_right δ' ε)
      simpa [Metric.mem_ball, dist_eq_norm, hzNeg_norm] using hρ'ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hzNeg_norm] using hρ'pos.ne'
  have hzPos_mem : zPos ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · -- The same radius computation works for the second mixed witness.
      have hρ'ltε : ρ' < ε := lt_of_lt_of_le hρ'small (min_le_right δ' ε)
      simpa [Metric.mem_ball, dist_eq_norm, hzPos_norm] using hρ'ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hzPos_norm] using hρ'pos.ne'
  have hzNeg_large : T < Real.log ‖(g zNeg)⁻¹‖ := by
    have hpos : 0 < ‖(g zNeg)⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero zNeg hzNeg_mem))
    -- Convert the failed exponential bound back to the logarithmic scale used by the owner API.
    exact (Real.lt_log_iff_exp_lt hpos).2 hzNeg_large_exp
  have hzPos_large : T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
    have hpos : 0 < ‖((1 - g zPos)⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero zPos hzPos_mem))
    -- The same conversion applies to the shifted reciprocal branch.
    exact (Real.lt_log_iff_exp_lt hpos).2 hzPos_large_exp
  refine ⟨ρ', hρ'pos, lt_min hρ'ltδ hρ'ltρ, zNeg, zPos, hzNeg_norm, hzPos_norm, ?_, ?_⟩
  · exact hzNeg_large
  · exact hzPos_large

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if no smaller centered circle carries
one uniformly bounded reciprocal branch, then every smaller scale contains a selector-zero point on
some smaller centered circle where both reciprocal logarithms are already bounded by `T`. -/
lemma exists_zeroSelectorWithBoundedLogs_on_smallerCircle_of_no_smallCircleUniformReciprocalBranch
    {g : ℂ → ℂ} {ε ρ T δ : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hρpos : 0 < ρ)
    (hρε : ρ < ε)
    (hδ : 0 < δ)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hnoSmall :
      ¬ ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧
        ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
          ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T)) :
    ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
      ∃ z₀, ‖z₀‖ = ρ' ∧
        Real.log ‖g z₀ / (1 - g z₀)‖ = 0 ∧
        Real.log ‖(g z₀)⁻¹‖ ≤ T ∧
          Real.log ‖((1 - g z₀)⁻¹)‖ ≤ T := by
  obtain ⟨ρ', hρ'pos, hρ'small, zNeg, zPos, hzNeg_norm, hzPos_norm, hzNeg_large, hzPos_large⟩ :=
    exists_mixedLargeReciprocalLogs_on_smallerCircle_of_no_smallCircleUniformReciprocalBranch
      hess hε hρpos hδ hg hg_nonzero hone_sub_nonzero hnoSmall
  have hρ'ltε : ρ' < ε := lt_trans (lt_of_lt_of_le hρ'small (min_le_right δ ρ)) hρε
  obtain ⟨z₀, hz₀_norm, hz₀_selector, hz₀_g, hz₀_oneSub⟩ :=
    mixedLargeReciprocalLogs_giveZeroSelectorWithBoundedLogs
      hρ'pos
      hρ'ltε
      hzNeg_norm
      hzPos_norm
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      hzNeg_large
      hzPos_large
  refine ⟨ρ', hρ'pos, hρ'small, z₀, hz₀_norm, hz₀_selector, hz₀_g, hz₀_oneSub⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): punctured-ball nonvanishing of
`1 - g` is exactly the omitted-value statement `1 ∉ g '' U`. -/
lemma oneOmitted_of_sub_nonzero_onPuncturedBall
    {g : ℂ → ℂ} {ε : ℝ}
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0) :
    (1 : ℂ) ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  intro himage
  rcases himage with ⟨z, hz, hz_one⟩
  -- Rewriting a punctured-ball image point with value `1` contradicts the nonvanishing
  -- hypothesis for `1 - g`.
  exact hone_sub_nonzero z hz (by simpa [hz_one])

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the normalized ratio `g / (1 - g)`
cannot take the value `-1` on the punctured ball. -/
lemma normalizedRatio_omits_negOne_onPuncturedBall
    {g : ℂ → ℂ} {ε : ℝ}
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0) :
    (-1 : ℂ) ∉
      (fun z ↦ g z / (1 - g z)) '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  intro himage
  rcases himage with ⟨z, hz, hz_ratio⟩
  have hz_den : 1 - g z ≠ 0 := hone_sub_nonzero z hz
  have hmul : g z = (-1 : ℂ) * (1 - g z) := by
    exact (div_eq_iff hz_den).mp hz_ratio
  have hsum : g z + (1 - g z) = (-1 : ℂ) * (1 - g z) + (1 - g z) := by
    exact congrArg (fun w : ℂ ↦ w + (1 - g z)) hmul
  have hone : (1 : ℂ) = 0 := by
    -- Clearing the nonzero denominator forces the tautological sum `g z + (1 - g z)` to vanish.
    calc
      (1 : ℂ) = g z + (1 - g z) := by ring
      _ = (-1 : ℂ) * (1 - g z) + (1 - g z) := hsum
      _ = 0 := by ring
  exact one_ne_zero hone

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): every descended selector-zero witness
can be rewritten in the fixed punctured-ball normal form of `g / (1 - g)`. -/
lemma descendedSelectorZeroNormalFormData
    {g F : ℂ → ℂ} {ε ρ T : ℝ} {n : ℤ} {c : ℂ}
    (hρε : ρ < ε)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hsmallZero :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
        ∃ z, ‖z‖ = ρ' ∧
          Real.log ‖g z / (1 - g z)‖ = 0 ∧
            Real.log ‖(g z)⁻¹‖ ≤ T ∧
              Real.log ‖((1 - g z)⁻¹)‖ ≤ T) :
    ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
      ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F z).re = 0 := by
  intro δ hδ
  rcases hsmallZero δ hδ with
    ⟨ρ', hρ'pos, hρ'small, z, hz_norm, hz_selector, _hz_g, _hz_oneSub⟩
  have hz_mem : z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · have hρ'ltε : ρ' < ε := by
        exact lt_trans (lt_of_lt_of_le hρ'small (min_le_right δ ρ)) hρε
      -- Every descended selector-zero point still lies in the ambient punctured `ε`-ball.
      simpa [Metric.mem_ball, dist_eq_norm, hz_norm] using hρ'ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hz_norm] using hρ'pos.ne'
  obtain ⟨θ, hθ_circle, hθ_normalForm⟩ :=
    zeroSelectorNormalFormOfNormEq
      (g := g) (F := F) (ε := ε) (ρ' := ρ') (n := n) (c := c)
      hρ'pos hEqRatio hc_ne hz_mem hz_norm hz_selector
  -- Repackage the descended selector zero as the real-part vanishing of the fixed normal form.
  exact ⟨ρ', hρ'pos, hρ'small, z, hz_mem, hz_norm, by simpa [hθ_circle] using hθ_normalForm⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a shrinking same-circle mixed-witness
family descends to selector-zero real-part vanishing in one fixed punctured-ball normal form. -/
lemma descendedSelectorZeroNormalFormData_of_shrinkingMixedWitnessFamily
    {g F : ℂ → ℂ} {ε ρ T : ℝ} {n : ℤ} {c : ℂ}
    (hρε : ρ < ε)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmixedSmall :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
      ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F z).re = 0 := by
  intro δ hδ
  rcases hmixedSmall δ hδ with
    ⟨ρ', hρ'pos, hρ'small, zNeg, zPos, hzNeg_norm, hzPos_norm, hzNegLarge, hzPosLarge⟩
  have hρ'ltε : ρ' < ε := lt_trans (lt_of_lt_of_le hρ'small (min_le_right δ ρ)) hρε
  obtain ⟨z₀, hz₀_norm, hz₀_selector, hz₀_g, hz₀_oneSub⟩ :=
    -- Recover a selector-zero witness on that same shrinking radius before freezing the normal
    -- form.
    mixedLargeReciprocalLogs_giveZeroSelectorWithBoundedLogs
      hρ'pos
      hρ'ltε
      hzNeg_norm
      hzPos_norm
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      hzNegLarge
      hzPosLarge
  have hz₀_mem : z₀ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hz₀_norm] using hρ'ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hz₀_norm] using hρ'pos.ne'
  obtain ⟨θ, hθ_circle, hθ_normalForm⟩ :=
    -- Transport the selector zero to the fixed punctured-ball normal form.
    zeroSelectorNormalFormOfNormEq
      (g := g) (F := F) (ε := ε) (ρ' := ρ') (n := n) (c := c)
      hρ'pos hEqRatio hc_ne hz₀_mem hz₀_norm hz₀_selector
  exact ⟨ρ', hρ'pos, hρ'small, z₀, hz₀_mem, hz₀_norm, by simpa [hθ_circle] using hθ_normalForm⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): every sufficiently small scale
contains a smaller witness circle carrying a legal Exercise-16 point together with a further
descendant centered circle carrying mixed large reciprocal witnesses. -/
lemma existsWitnessCircleWithDescendedMixedWitness
    {g : ℂ → ℂ} {ε ρ T : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hρpos : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmixedSmall :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∀ δ > 0, ∃ ρw, 0 < ρw ∧ ρw < min δ ρ ∧
      ∃ w, ‖w‖ = ρw ∧ g w ∈ exercise16Domain ∧
        ∃ ρm, 0 < ρm ∧ ρm < ρw ∧
          ∃ zNeg zPos, ‖zNeg‖ = ρm ∧ ‖zPos‖ = ρm ∧
            T < Real.log ‖(g zNeg)⁻¹‖ ∧
              T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
  intro δ hδ
  let δw : ℝ := min δ (ρ / 2)
  have hδw_pos : 0 < δw := by
    -- Shrink below both `δ` and `ρ / 2` so the legal witness circle is strictly smaller than
    -- the current outer witness radius.
    dsimp [δw]
    exact lt_min hδ (half_pos hρpos)
  obtain ⟨ρw, hρw_pos, hρw_small, w, hw_norm, hwE⟩ :=
    exercise16Hit_onSmallCircle hess hε hδw_pos hg
  have hρw_ltδw : ρw < δw := by
    -- Remove the ambient `ε` cutoff and keep only the scale bound for the legal witness circle.
    exact lt_of_lt_of_le hρw_small (min_le_left δw ε)
  have hρw_ltδ : ρw < δ := by
    exact lt_of_lt_of_le hρw_ltδw (min_le_left δ (ρ / 2))
  have hρw_ltρhalf : ρw < ρ / 2 := by
    exact lt_of_lt_of_le hρw_ltδw (min_le_right δ (ρ / 2))
  have hρw_ltρ : ρw < ρ := by
    linarith
  rcases hmixedSmall ρw hρw_pos with
    ⟨ρm, hρm_pos, hρm_small, zNeg, zPos, hzNeg_norm, hzPos_norm, hzNegLarge, hzPosLarge⟩
  have hρm_ltρw : ρm < ρw := by
    -- The descendant mixed witness circle lies strictly below the newly chosen legal witness
    -- circle.
    exact lt_of_lt_of_le hρm_small (min_le_left ρw ρ)
  exact
    ⟨ρw, hρw_pos, lt_min hρw_ltδ hρw_ltρ, w, hw_norm, hwE, ρm, hρm_pos, hρm_ltρw, zNeg, zPos,
      hzNeg_norm, hzPos_norm, hzNegLarge, hzPosLarge⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): one mixed-large witness circle below
the outer witness radius already carries a selector-zero point in the fixed punctured-ball normal
form. -/
lemma descendedSelectorZeroNormalForm_onMixedWitnessCircle
    {g F : ℂ → ℂ} {ε ρm T : ℝ} {n : ℤ} {c zNeg zPos : ℂ}
    (hρm_pos : 0 < ρm)
    (hρm_ltε : ρm < ε)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hzNeg_norm : ‖zNeg‖ = ρm)
    (hzPos_norm : ‖zPos‖ = ρm)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzNegLarge : T < Real.log ‖(g zNeg)⁻¹‖)
    (hzPosLarge : T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∃ z₀, z₀ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧
      ‖z₀‖ = ρm ∧
      Real.log ‖g z₀ / (1 - g z₀)‖ = 0 ∧
      Real.log ‖(g z₀)⁻¹‖ ≤ T ∧
      Real.log ‖((1 - g z₀)⁻¹)‖ ≤ T ∧
      Real.log ‖c‖ + (n : ℝ) * Real.log ρm + (F z₀).re = 0 := by
  obtain ⟨z₀, hz₀_norm, hz₀_selector, hz₀_g, hz₀_oneSub⟩ :=
    -- First rebuild a selector-zero point on the same smaller mixed witness circle.
    mixedLargeReciprocalLogs_giveZeroSelectorWithBoundedLogs
      hρm_pos
      hρm_ltε
      hzNeg_norm
      hzPos_norm
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      hzNegLarge
      hzPosLarge
  have hz₀_mem : z₀ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hz₀_norm] using hρm_ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hz₀_norm] using hρm_pos.ne'
  obtain ⟨θ, hθ_circle, hz₀_normalized⟩ :=
    -- Then freeze that selector-zero point in the fixed punctured-ball normal form.
    zeroSelectorNormalFormOfNormEq
      (g := g)
      (F := F)
      (ε := ε)
      (ρ' := ρm)
      (n := n)
      (c := c)
      hρm_pos
      hEqRatio
      hc_ne
      hz₀_mem
      hz₀_norm
      hz₀_selector
  exact
    ⟨z₀, hz₀_mem, hz₀_norm, hz₀_selector, hz₀_g, hz₀_oneSub,
      by simpa [hθ_circle] using hz₀_normalized⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a shrinking mixed-witness family
below `ρ` restricts immediately to the same kind of family below any smaller positive radius
`ρw < ρ`. -/
lemma shrinkingMixedWitnessFamilyBelowRadius
    {g : ℂ → ℂ} {ρ ρw T : ℝ}
    (hρw_pos : 0 < ρw)
    (hρw_ltρ : ρw < ρ)
    (hmixedSmall :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
      ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
        T < Real.log ‖(g zNeg)⁻¹‖ ∧
          T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
  intro δ hδ
  have hmin_pos : 0 < min δ ρw := lt_min hδ hρw_pos
  rcases hmixedSmall (min δ ρw) hmin_pos with
    ⟨ρ', hρ'pos, hρ'small, zNeg, zPos, hzNeg_norm, hzPos_norm, hzNegLarge, hzPosLarge⟩
  refine ⟨ρ', hρ'pos, ?_, zNeg, zPos, hzNeg_norm, hzPos_norm, hzNegLarge, hzPosLarge⟩
  exact lt_of_lt_of_le hρ'small (min_le_left _ _)

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): negating the desired smaller-circle
uniform reciprocal branch below the frozen witness radius `ρw` yields the exact descended
selector-zero family needed by the normal-form transport API. -/
lemma smallZeroSelectorFamilyBelowRadius_of_noSmallBranch
    {g : ℂ → ℂ} {ε ρw T : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hρw_pos : 0 < ρw)
    (hρw_ltε : ρw < ε)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hnoSmallBelow :
      ¬ ∃ ρ', 0 < ρ' ∧ ρ' < ρw ∧
        ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
          ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T)) :
    ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
      ∃ z, ‖z‖ = ρ' ∧
        Real.log ‖g z / (1 - g z)‖ = 0 ∧
        Real.log ‖(g z)⁻¹‖ ≤ T ∧
          Real.log ‖((1 - g z)⁻¹)‖ ≤ T := by
  intro δ hδ
  -- Specialize the existing no-small-branch descent theorem to the frozen witness radius `ρw`.
  exact
    exists_zeroSelectorWithBoundedLogs_on_smallerCircle_of_no_smallCircleUniformReciprocalBranch
      hess
      hε
      hρw_pos
      hρw_ltε
      hδ
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      hg
      hnoSmallBelow

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once the punctured-ball normal form
for `g / (1 - g)` is frozen at radius `ρw`, every descended selector-zero witness below `ρw`
rewrites to the corresponding real-part vanishing identity in that same fixed model. -/
lemma descendedSmallScaleZeroNormalForm_onFrozenWitnessCircle
    {g F : ℂ → ℂ} {ε ρw T : ℝ} {n : ℤ} {c : ℂ}
    (hρw_ltε : ρw < ε)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hsmallZero :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ z, ‖z‖ = ρ' ∧
          Real.log ‖g z / (1 - g z)‖ = 0 ∧
            Real.log ‖(g z)⁻¹‖ ≤ T ∧
              Real.log ‖((1 - g z)⁻¹)‖ ≤ T) :
    ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
      ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F z).re = 0 := by
  intro δ hδ
  -- Reuse the fixed punctured-ball transport lemma instead of rebuilding the normal form
  -- separately at each descended radius.
  exact descendedSelectorZeroNormalFormData hρw_ltε hEqRatio hc_ne hsmallZero δ hδ

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if no centered circle below the
frozen witness radius `ρw` already carries one uniformly bounded reciprocal branch, then every
smaller scale below `ρw` still contains a descended selector-zero point written in the fixed
punctured-ball normal form. -/
lemma descendedSmallScaleZeroNormalFormFamily_of_noSmallBranch
    {g F : ℂ → ℂ} {ε ρw T : ℝ} {n : ℤ} {c : ℂ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hρw_pos : 0 < ρw)
    (hρw_ltε : ρw < ε)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hnoSmallBelow :
      ¬ ∃ ρ', 0 < ρ' ∧ ρ' < ρw ∧
        ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
          ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T)) :
    ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
      ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F z).re = 0 := by
  intro δ hδ
  -- First descend to a smaller selector-zero witness with bounded reciprocal logs, then rewrite
  -- that witness in the frozen punctured-ball normal form.
  have hsmallZero :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ z, ‖z‖ = ρ' ∧
          Real.log ‖g z / (1 - g z)‖ = 0 ∧
            Real.log ‖(g z)⁻¹‖ ≤ T ∧
              Real.log ‖((1 - g z)⁻¹)‖ ≤ T := by
    exact
      smallZeroSelectorFamilyBelowRadius_of_noSmallBranch
        hess
        hε
        hρw_pos
        hρw_ltε
        hbranch
        hg_nonzero
        hone_sub_nonzero
        hselector_cont
        hg
        hnoSmallBelow
  exact
    descendedSmallScaleZeroNormalForm_onFrozenWitnessCircle
      hρw_ltε
      hEqRatio
      hc_ne
      hsmallZero
      δ
      hδ

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a legal point `wSmall` on the frozen
circle `‖z‖ = ρw` determines a bounded legal witness component `C₀ = Ioo a b` around one angle
parameter `thetaW`, together with endpoint-closure data and the selector trichotomy on `C₀`. -/
lemma frozenWitnessComponentData_onLegalCircle
    {g : ℂ → ℂ} {ε ρw : ℝ} {wSmall : ℂ}
    (hρw_pos : 0 < ρw)
    (hρw_ltε : ρw < ε)
    (hwSmall_norm : ‖wSmall‖ = ρw)
    (hwSmallE : g wSmall ∈ exercise16Domain)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ thetaW a b : ℝ,
      let thetaLeft : ℝ := thetaW - 1
      let thetaRight : ℝ := thetaW + 1
      let zeta : ℝ → ℂ := fun θ ↦ circleMap 0 ρw θ
      let selectorθ : ℝ → ℝ := fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖
      let S : Set ℝ := Set.Ioo thetaLeft thetaRight ∩ {θ | g (zeta θ) ∈ exercise16Domain}
      let C₀ : Set ℝ := connectedComponentIn S thetaW
      zeta thetaW = wSmall ∧
        thetaLeft < thetaW ∧
        thetaW < thetaRight ∧
        thetaLeft ≤ a ∧
        a < thetaW ∧
        thetaW < b ∧
        b ≤ thetaRight ∧
        C₀ = Set.Ioo a b ∧
        Set.MapsTo (fun θ ↦ g (zeta θ)) C₀ exercise16Domain ∧
        g (zeta a) ∈ closure exercise16Domain ∧
        g (zeta b) ∈ closure exercise16Domain ∧
        IsPreconnected C₀ ∧
        ((∃ η ∈ C₀, selectorθ η = 0) ∨
          (∀ η ∈ C₀, 0 < selectorθ η) ∨
          (∀ η ∈ C₀, selectorθ η < 0)) := by
  obtain ⟨tW, htW⟩ := exists_param_standardCirclePath_eq_of_norm_eq hρw_pos hwSmall_norm
  let thetaW : ℝ := 2 * Real.pi * (tW : ℝ)
  let thetaLeft : ℝ := thetaW - 1
  let thetaRight : ℝ := thetaW + 1
  let zeta : ℝ → ℂ := fun θ ↦ circleMap 0 ρw θ
  let selectorθ : ℝ → ℝ := fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖
  let S : Set ℝ := Set.Ioo thetaLeft thetaRight ∩ {θ | g (zeta θ) ∈ exercise16Domain}
  let C₀ : Set ℝ := connectedComponentIn S thetaW
  have hthetaW_circle : zeta thetaW = wSmall := by
    -- Parameterize the frozen witness point on the radius-`ρw` circle once and for all.
    simpa [zeta, thetaW, standardCirclePath_apply] using htW
  have hthetaLeft_lt_thetaW : thetaLeft < thetaW := by
    -- The left window endpoint sits one unit before the witness angle.
    dsimp [thetaLeft]
    linarith
  have hthetaW_lt_thetaRight : thetaW < thetaRight := by
    -- The right window endpoint sits one unit after the witness angle.
    dsimp [thetaRight]
    linarith
  have hzeta_mem : ∀ θ, zeta θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    intro θ
    constructor
    · -- Every point on the frozen radius-`ρw` circle stays inside the punctured `ε`-ball.
      simpa [zeta, Metric.mem_ball, dist_eq_norm, norm_circleMap_zero,
        abs_of_nonneg (le_of_lt hρw_pos)] using hρw_ltε
    · -- The positive frozen radius keeps the circle away from the puncture.
      exact norm_ne_zero_iff.mp <| by
        simpa [zeta, norm_circleMap_zero, abs_of_nonneg (le_of_lt hρw_pos)] using hρw_pos.ne'
  have hg_circle_cont : Continuous fun θ ↦ g (zeta θ) := by
    -- Restrict `g` to the frozen witness circle through the punctured-ball analyticity package.
    simpa [zeta] using hg.continuousOn.comp_continuous (continuous_circleMap 0 ρw) hzeta_mem
  have hselectorTheta_cont : Continuous selectorθ := by
    -- The quotient selector remains continuous along that same frozen witness circle.
    simpa [selectorθ, zeta] using
      hselector_cont.comp_continuous (continuous_circleMap 0 ρw) hzeta_mem
  have hthetaW_mem_exercise16 : g (zeta thetaW) ∈ exercise16Domain := by
    -- The witness point itself is legal by hypothesis.
    simpa [hthetaW_circle] using hwSmallE
  obtain ⟨a, b, hthetaLeft_le_a, ha_lt_thetaW, hthetaW_lt_b, hb_le_thetaRight, hC₀_eq⟩ :=
    -- Normalize the connected legal component around `thetaW` to one open interval `Ioo a b`.
    windowedWitnessComponent_eq_Ioo
      hthetaLeft_lt_thetaW
      hthetaW_lt_thetaRight
      hthetaW_mem_exercise16
      hg.continuousOn
      hzeta_mem
  have hC₀_eq' : C₀ = Set.Ioo a b := by
    -- Rewrite the abstract connected component to the normalized open-interval spelling.
    simpa [C₀, S, zeta] using hC₀_eq
  have hab : a < b := lt_trans ha_lt_thetaW hthetaW_lt_b
  have hS_open : IsOpen S := by
    have hexercise16_open : IsOpen exercise16Domain := by
      -- The Exercise-16 lens is the intersection of the two open unit balls.
      simpa [exercise16Domain] using
        (Metric.isOpen_ball.inter Metric.isOpen_ball :
          IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1))
    -- The frozen witness set is the bounded angle window intersected with the legal preimage.
    refine isOpen_Ioo.inter ?_
    simpa [S] using hexercise16_open.preimage hg_circle_cont
  have hmaps_C₀ : Set.MapsTo (fun θ ↦ g (zeta θ)) C₀ exercise16Domain := by
    intro θ hθ
    exact (connectedComponentIn_subset S thetaW hθ).2
  have hmaps_Ioo : Set.MapsTo (fun θ ↦ g (zeta θ)) (Set.Ioo a b) exercise16Domain := by
    -- Move the legal image statement to the normalized interval spelling.
    simpa [hC₀_eq'] using hmaps_C₀
  have hga_mem_closure_exercise16 : g (zeta a) ∈ closure exercise16Domain := by
    -- The left endpoint is a closure point of the legal image of the component interval.
    exact image_leftEndpoint_mem_closure_of_mapsTo_Ioo hab hg_circle_cont hmaps_Ioo
  have hgb_mem_closure_exercise16 : g (zeta b) ∈ closure exercise16Domain := by
    -- The right endpoint is handled symmetrically.
    exact image_rightEndpoint_mem_closure_of_mapsTo_Ioo hab hg_circle_cont hmaps_Ioo
  have hC₀_preconnected : IsPreconnected C₀ := by
    -- The normalized witness component is an open interval, hence preconnected.
    simpa [hC₀_eq'] using (isPreconnected_Ioo : IsPreconnected (Set.Ioo a b))
  have htrichotomy :
      (∃ η ∈ C₀, selectorθ η = 0) ∨
        (∀ η ∈ C₀, 0 < selectorθ η) ∨
        (∀ η ∈ C₀, selectorθ η < 0) := by
    -- The selector on one open interval is either everywhere positive, everywhere negative, or
    -- vanishes somewhere.
    exact zeroOrStrictSignOnPreconnected hC₀_preconnected hselectorTheta_cont.continuousOn
  refine ⟨thetaW, a, b, ?_⟩
  -- Return the full bounded witness-component package in the notation used by the main theorem.
  dsimp [thetaLeft, thetaRight, zeta, selectorθ, S, C₀]
  exact
    ⟨hthetaW_circle, hthetaLeft_lt_thetaW, hthetaW_lt_thetaRight, hthetaLeft_le_a, ha_lt_thetaW,
      hthetaW_lt_b, hb_le_thetaRight, hC₀_eq', hmaps_C₀, hga_mem_closure_exercise16,
      hgb_mem_closure_exercise16, hC₀_preconnected, htrichotomy⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): one concrete descended mixed-witness
circle below the frozen radius `ρw` carries both the original mixed-large witnesses and a
same-radius selector-zero point in the fixed punctured-ball normal form. -/
lemma concreteDescendedMixedWitnessData_onFrozenCircle
    {g F : ℂ → ℂ} {ε ρw T : ℝ} {n : ℤ} {c : ℂ}
    (hρw_pos : 0 < ρw)
    (hρw_ltε : ρw < ε)
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmixedSmallBelow :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∃ ρm, 0 < ρm ∧ ρm < ρw ∧
      ∃ zNeg zPos zm,
        zNeg ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧
          zPos ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧
          zm ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧
          ‖zNeg‖ = ρm ∧
          ‖zPos‖ = ρm ∧
          ‖zm‖ = ρm ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
          T < Real.log ‖((1 - g zPos)⁻¹)‖ ∧
          Real.log ‖g zm / (1 - g zm)‖ = 0 ∧
          Real.log ‖(g zm)⁻¹‖ ≤ T ∧
          Real.log ‖((1 - g zm)⁻¹)‖ ≤ T ∧
          Real.log ‖c‖ + (n : ℝ) * Real.log ρm + (F zm).re = 0 := by
  rcases hmixedSmallBelow ρw hρw_pos with
    ⟨ρm, hρm_pos, hρm_small, zNeg, zPos, hzNeg_norm, hzPos_norm, hzNegLarge, hzPosLarge⟩
  have hρm_ltρw : ρm < ρw := by
    -- The descended mixed-witness family already lives strictly below the frozen witness radius.
    exact lt_of_lt_of_le hρm_small (min_le_right _ _)
  have hρm_ltε : ρm < ε := lt_trans hρm_ltρw hρw_ltε
  have hzNeg_mem : zNeg ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · -- The negative mixed witness still lies on a centered circle inside the punctured ball.
      simpa [Metric.mem_ball, dist_eq_norm, hzNeg_norm] using hρm_ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hzNeg_norm] using hρm_pos.ne'
  have hzPos_mem : zPos ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · -- The same radius computation handles the positive mixed witness.
      simpa [Metric.mem_ball, dist_eq_norm, hzPos_norm] using hρm_ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hzPos_norm] using hρm_pos.ne'
  obtain ⟨zm, hzm_mem, hzm_norm, hzm_selector, hzm_g_le, hzm_oneSub_le, hzm_normalized⟩ :=
    -- Keep one same-radius selector-zero point together with its bounded reciprocal logs in the
    -- fixed normal form.
    descendedSelectorZeroNormalForm_onMixedWitnessCircle
      hρm_pos
      hρm_ltε
      hEqRatio
      hc_ne
      hzNeg_norm
      hzPos_norm
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      hzNegLarge
      hzPosLarge
  exact
    ⟨ρm, hρm_pos, hρm_ltρw, zNeg, zPos, zm, hzNeg_mem, hzPos_mem, hzm_mem, hzNeg_norm,
      hzPos_norm, hzm_norm, hzNegLarge, hzPosLarge, hzm_selector, hzm_g_le, hzm_oneSub_le,
      hzm_normalized⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the concrete descended mixed-witness
circle can be parameterized by ordered angles around the same-radius selector-zero point `zm`, and
the selector on that circle is strictly negative at the left witness, zero at `zm`, and strictly
positive at the right witness. -/
lemma descendedMixedWitnessSelectorSignData_onFrozenCircle
    {g : ℂ → ℂ} {ε ρm T : ℝ} {zNeg zPos zm : ℂ}
    (hρm_pos : 0 < ρm)
    (hρm_ltε : ρm < ε)
    (hzNeg_norm : ‖zNeg‖ = ρm)
    (hzPos_norm : ‖zPos‖ = ρm)
    (hzm_norm : ‖zm‖ = ρm)
    (hzNegLarge : T < Real.log ‖(g zNeg)⁻¹‖)
    (hzPosLarge : T < Real.log ‖((1 - g zPos)⁻¹)‖)
    (hzm_selector : Real.log ‖g zm / (1 - g zm)‖ = 0)
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0) :
    ∃ thetaNeg thetaM thetaPos : ℝ,
      thetaNeg < thetaM ∧
        thetaM < thetaPos ∧
        circleMap 0 ρm thetaNeg = zNeg ∧
        circleMap 0 ρm thetaM = zm ∧
        circleMap 0 ρm thetaPos = zPos ∧
        Real.log ‖g (circleMap 0 ρm thetaNeg) / (1 - g (circleMap 0 ρm thetaNeg))‖ < 0 ∧
        Real.log ‖g (circleMap 0 ρm thetaM) / (1 - g (circleMap 0 ρm thetaM))‖ = 0 ∧
        0 < Real.log ‖g (circleMap 0 ρm thetaPos) / (1 - g (circleMap 0 ρm thetaPos))‖ := by
  obtain ⟨thetaNeg, thetaM, thetaPos, hthetaNeg_lt, hthetaM_lt, hthetaM_circle, hthetaNeg_circle,
      hthetaPos_circle⟩ :=
    -- Order the three same-radius points by angle, keeping the selector-zero point in the middle.
    sameCircleAngleOrder_throughWitness
      hρm_pos hzm_norm hzNeg_norm hzPos_norm
  have hzNeg_mem : zNeg ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · -- The left descended mixed witness stays on the smaller circle inside the punctured ball.
      simpa [Metric.mem_ball, dist_eq_norm, hzNeg_norm] using hρm_ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hzNeg_norm] using hρm_pos.ne'
  have hzPos_mem : zPos ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · -- The same radius computation handles the right descended mixed witness.
      simpa [Metric.mem_ball, dist_eq_norm, hzPos_norm] using hρm_ltε
    · exact norm_ne_zero_iff.mp <| by simpa [hzPos_norm] using hρm_pos.ne'
  have hbranchExp :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ Real.exp T ∨ ‖((1 - g z)⁻¹)‖ ≤ Real.exp T := by
    intro z hz
    rcases hbranch z hz with hg_log | hone_sub_log
    · left
      have hpos : 0 < ‖(g z)⁻¹‖ := by
        exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero z hz))
      exact (Real.log_le_iff_le_exp hpos).1 hg_log
    · right
      have hpos : 0 < ‖((1 - g z)⁻¹)‖ := by
        exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero z hz))
      exact (Real.log_le_iff_le_exp hpos).1 hone_sub_log
  have hzNegLargeExp : Real.exp T < ‖(g zNeg)⁻¹‖ := by
    have hpos : 0 < ‖(g zNeg)⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero zNeg hzNeg_mem))
    exact (Real.lt_log_iff_exp_lt hpos).1 hzNegLarge
  have hzPosLargeExp : Real.exp T < ‖((1 - g zPos)⁻¹)‖ := by
    have hpos : 0 < ‖((1 - g zPos)⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero zPos hzPos_mem))
    exact (Real.lt_log_iff_exp_lt hpos).1 hzPosLarge
  have hselectorNeg :
      Real.log ‖g (circleMap 0 ρm thetaNeg) / (1 - g (circleMap 0 ρm thetaNeg))‖ < 0 := by
    -- The left descended mixed witness forces a strict negative selector value.
    simpa [hthetaNeg_circle] using
      selectorNegOfLargeReciprocal
        (hg_nonzero zNeg hzNeg_mem)
        (hone_sub_nonzero zNeg hzNeg_mem)
        (hbranchExp zNeg hzNeg_mem)
        hzNegLargeExp
  have hselectorM :
      Real.log ‖g (circleMap 0 ρm thetaM) / (1 - g (circleMap 0 ρm thetaM))‖ = 0 := by
    -- The middle descended point is exactly the same-radius selector-zero witness.
    simpa [hthetaM_circle] using hzm_selector
  have hselectorPos :
      0 < Real.log ‖g (circleMap 0 ρm thetaPos) / (1 - g (circleMap 0 ρm thetaPos))‖ := by
    -- The right descended mixed witness forces the symmetric strict positive selector value.
    simpa [hthetaPos_circle] using
      selectorPosOfLargeOneSubReciprocal
        (hg_nonzero zPos hzPos_mem)
        (hone_sub_nonzero zPos hzPos_mem)
        (hbranchExp zPos hzPos_mem)
        hzPosLargeExp
  exact
    ⟨thetaNeg, thetaM, thetaPos, hthetaNeg_lt, hthetaM_lt, hthetaNeg_circle, hthetaM_circle,
      hthetaPos_circle, hselectorNeg, hselectorM, hselectorPos⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once an interior selector zero `η`
on the frozen witness component has been transported into one shifted witness model `Fη`, the
remaining contradiction against arbitrarily small descended selector-zero witnesses is isolated to
that common-model obstruction. -/
lemma descendedSelectorZeroNormalFormWitness_belowRadius
    {Fη : ℂ → ℂ} {ε ρw : ℝ} {n : ℤ} {c : ℂ}
    (hdescendedNormalForm :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
          Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (Fη z).re = 0) :
    ∃ ρ', 0 < ρ' ∧ ρ' < ρw ∧
      ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (Fη z).re = 0 := by
  obtain ⟨ρ', hρ'pos, hρ'small, z, hz_mem, hz_norm, hz_normalized⟩ :=
    -- Specialize the descended family at one positive scale to expose a concrete witness below
    -- the frozen radius.
    hdescendedNormalForm 1 zero_lt_one
  refine ⟨ρ', hρ'pos, ?_, z, hz_mem, hz_norm, hz_normalized⟩
  -- The concrete witness still sits strictly below `ρw`, which is the only part of the scale
  -- control needed by the common-model contradiction.
  exact lt_of_lt_of_le hρ'small (min_le_right _ _)

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once an interior selector zero `η`
on the frozen witness component has been transported into one shifted witness model `Fη`, the
remaining contradiction against arbitrarily small descended selector-zero witnesses is isolated to
that common-model obstruction. -/
lemma commonShiftedModelContradiction_of_descendedSelectorZeroWitnessFamily
    {g Fη : ℂ → ℂ} {ε ρw T : ℝ} {n : ℤ} {c : ℂ} {η thetaW : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hρw_ltε : ρw < ε)
    (hc_ne : c ≠ 0)
    (hηzero :
      Real.log ‖g (circleMap 0 ρw η) / (1 - g (circleMap 0 ρw η))‖ = 0)
    (hFη_analytic : AnalyticOnNhd ℂ Fη (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatioη :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (Fη z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hη_logRatio_packet_zeroPeriod :
      Complex.log (g (circleMap 0 ρw η) / (1 - g (circleMap 0 ρw η))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρw : ℂ) + η * Complex.I) +
          Fη (circleMap 0 ρw η))
    (hthetaW_logRatio_packetη :
      Complex.log (g (circleMap 0 ρw thetaW) / (1 - g (circleMap 0 ρw thetaW))) =
        Complex.log c + (n : ℂ) * (Complex.log (ρw : ℂ) + thetaW * Complex.I) +
          Fη (circleMap 0 ρw thetaW))
    (hη_normalized_im_strip :
      -Real.pi <
          (Complex.log c + (n : ℂ) * (Complex.log (ρw : ℂ) + η * Complex.I) +
              Fη (circleMap 0 ρw η)).im ∧
        (Complex.log c + (n : ℂ) * (Complex.log (ρw : ℂ) + η * Complex.I) +
            Fη (circleMap 0 ρw η)).im < Real.pi)
    (hsmallZeroBelowρw :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ z, ‖z‖ = ρ' ∧
          Real.log ‖g z / (1 - g z)‖ = 0 ∧
          Real.log ‖(g z)⁻¹‖ ≤ T ∧
            Real.log ‖((1 - g z)⁻¹)‖ ≤ T) :
    False := by
  have hdescendedNormalForm :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ z, z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) ∧ ‖z‖ = ρ' ∧
          Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (Fη z).re = 0 := by
    -- Keep the descended selector-zero witnesses in the fixed shifted model until the final
    -- common-model contradiction is ready to consume one concrete witness.
    exact
      descendedSmallScaleZeroNormalForm_onFrozenWitnessCircle
        hρw_ltε
        hEqRatioη
        hc_ne
        hsmallZeroBelowρw
  obtain ⟨ρ', hρ'pos, hρ'ltρw, z, hz_mem, hz_norm, hz_normalized⟩ :=
    -- Route correction: choose one actual descended selector-zero witness before reopening any
    -- packet comparison, so the remaining blocker is a concrete same-model transport step rather
    -- than another family-level normalization statement.
    descendedSelectorZeroNormalFormWitness_belowRadius hdescendedNormalForm
  -- Route correction: this is now the only genuine interior frontier. The main theorem and the
  -- packet wrapper above should not reopen the common shifted-model transport once this consumer
  -- has been reached.
  let _ := hηzero
  let _ := hFη_analytic
  let _ := hη_logRatio_packet_zeroPeriod
  let _ := hthetaW_logRatio_packetη
  let _ := hη_normalized_im_strip
  let _ := ρ'
  let _ := hρ'pos
  let _ := hρ'ltρw
  let _ := z
  let _ := hz_mem
  let _ := hz_norm
  let _ := hz_normalized
  let _ := hess
  -- TODO: transport this concrete descended normal-form witness into the common shifted model of
  -- `η`, compare its packet to the witness-reference packet at `thetaW`, and finish the
  -- contradiction with the principal-strip control already frozen at `η`.
  sorry

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): once an interior selector zero `η`
on the frozen witness component has been transported into one shifted witness model `Fη`, the
remaining contradiction against arbitrarily small descended selector-zero witnesses is isolated to
that common-model obstruction. -/
lemma interiorCommonShiftedPacketObstruction_of_descendedSmallScaleZeros
    {g F : ℂ → ℂ} {ε ρw T : ℝ} {n : ℤ} {c : ℂ} {a b thetaW η : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hρw_pos : 0 < ρw)
    (hρw_ltε : ρw < ε)
    (hc_ne : c ≠ 0)
    (hη_mem_Ioo : η ∈ Set.Ioo a b)
    (hthetaW_mem_Ioo : thetaW ∈ Set.Ioo a b)
    (hηzero :
      Real.log ‖g (circleMap 0 ρw η) / (1 - g (circleMap 0 ρw η))‖ = 0)
    (hg_circle_cont : Continuous fun θ ↦ g (circleMap 0 ρw θ))
    (hzeta_mem : ∀ θ, circleMap 0 ρw θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρw θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρw θ) ≠ 0)
    (hF_analytic : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      Set.EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmaps_Ioo :
      Set.MapsTo (fun θ ↦ g (circleMap 0 ρw θ)) (Set.Ioo a b) exercise16Domain)
    (hsmallZeroBelowρw :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ z, ‖z‖ = ρ' ∧
          Real.log ‖g z / (1 - g z)‖ = 0 ∧
          Real.log ‖(g z)⁻¹‖ ≤ T ∧
            Real.log ‖((1 - g z)⁻¹)‖ ≤ T) :
    False := by
  obtain ⟨Fη, hFη_analytic, hEqRatioη, hη_logRatio_packet_zeroPeriod,
      hthetaW_logRatio_packetη, hη_normalized_im_strip⟩ :=
    -- First freeze the interior selector-zero witness `η` into one common shifted model `Fη`.
    shiftedWitnessModelBundle_of_referenceSelectorZero
      hρw_pos
      hc_ne
      hη_mem_Ioo
      hthetaW_mem_Ioo
      hg_circle_cont
      hzeta_mem
      hg_nonzero
      hone_sub_nonzero
      hF_analytic
      hEqRatio
      hmaps_Ioo
      hηzero
  -- Route correction: the packet transport is already stable at this point, so the wrapper now
  -- delegates immediately to the single common-model contradiction consumer.
  exact
    commonShiftedModelContradiction_of_descendedSelectorZeroWitnessFamily
      hess
      hρw_ltε
      hc_ne
      hηzero
      hFη_analytic
      hEqRatioη
      hη_logRatio_packet_zeroPeriod
      hthetaW_logRatio_packetη
      hη_normalized_im_strip
      hsmallZeroBelowρw

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the all-positive frozen witness
component closes as soon as the actual left-boundary analysis is available in the shape consumed by
the interval zero extractor. -/
lemma positiveWitnessComponentContradiction_of_descendedBoundaryData
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ)
    (hleftBoundary :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0) :
    False := by
  -- Route correction: the old cross-radius statement was under-hypothesized. Once the left
  -- boundary analysis has actually been produced, the standard positive-branch contradiction
  -- adapter closes the component immediately.
  exact
    leftBoundaryContradiction_of_positiveWitnessFirstCrossing
      hab
      hC₀_eq
      hzero
      hposall
      hleftBoundary

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the all-negative frozen witness
component closes as soon as the actual right-boundary analysis is available in the shape consumed
by the interval zero extractor. -/
lemma negativeWitnessComponentContradiction_of_descendedBoundaryData
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hzero :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0)
    (hrightBoundary :
      (∃ θ ∈ C₀, selectorθ θ = 0) ∨
        ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ) :
    False := by
  -- Route correction: after repairing the interface, the remaining work is exactly the production
  -- of the right boundary analysis. Once that package exists, the standard negative-branch
  -- contradiction adapter finishes immediately.
  exact
    rightBoundaryContradiction_of_negativeWitnessLastExit
      hab
      hC₀_eq
      hzero
      hnegall
      hrightBoundary

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a strict negative selector value at
the left endpoint of a positive witness component already yields one interior weak nonpositive
witness. -/
lemma existsWeakNonpos_onPositiveWitnessComponent_of_leftEndpointNeg
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_a_neg : selectorθ a < 0) :
    ∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0 := by
  -- Continuity at the strict left-endpoint sign produces a left-hand negative neighborhood, and
  -- the midpoint of that neighborhood is the required weak nonpositive witness.
  exact
    existsWeakNonpos_of_leftNegativeNeighborhood
      hab
      hC₀_eq
      (leftNeighborhood_lt_zero_of_continuous_of_lt
        hab
        hselectorTheta_cont
        hselector_a_neg)

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a strict positive selector value at
the right endpoint of a negative witness component already yields one interior weak nonnegative
witness. -/
lemma existsWeakNonneg_onNegativeWitnessComponent_of_rightEndpointPos
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_b_pos : 0 < selectorθ b) :
    ∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos := by
  -- Continuity at the strict right-endpoint sign produces a right-hand positive neighborhood, and
  -- the midpoint of that neighborhood is the required weak nonnegative witness.
  exact
    existsWeakNonneg_of_rightPositiveNeighborhood
      hab
      hC₀_eq
      (rightNeighborhood_gt_zero_of_continuous_of_lt
        hab
        hselectorTheta_cont
        hselector_b_pos)

lemma smallCircleUniformReciprocalBranch_of_descendedWitnessCircle
    {g : ℂ → ℂ} {ε ρ ρw T : ℝ} {wSmall : ℂ}
    (hess : HasEssentialSingularityAt g 0)
    (hT_ge_one : 1 ≤ T)
    (hε : 0 < ε)
    (hρw_pos : 0 < ρw)
    (hρw_ltρ : ρw < ρ)
    (hρw_ltε : ρw < ε)
    (hwSmall_norm : ‖wSmall‖ = ρw)
    (hwSmallE : g wSmall ∈ exercise16Domain)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hmixedSmallBelow :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧
      ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
        ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) := by
  classical
  by_contra hnoSmallBelow
  have hnoSmallBelowρw :
      ¬ ∃ ρ', 0 < ρ' ∧ ρ' < ρw ∧
        ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
          ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) := by
    intro hsmall
    rcases hsmall with ⟨ρ', hρ'pos, hρ'_ltρw, hρ'branch⟩
    exact hnoSmallBelow ⟨ρ', hρ'pos, lt_trans hρ'_ltρw hρw_ltρ, hρ'branch⟩
  obtain ⟨n, F, c, hc_ne, hF_analytic, hEqRatio⟩ :=
    -- Freeze one punctured-ball normal form for `g / (1 - g)` once and for all.
    witnessCircleNormalizedRatioNormalForm
      hε
      hρw_pos
      hρw_ltε
      hg
      hg_nonzero
      hone_sub_nonzero
  obtain ⟨ρm, hρm_pos, hρm_ltρw, zNeg, zPos, zm, hzNeg_mem, hzPos_mem, hzm_mem, hzNeg_norm,
      hzPos_norm, hzm_norm, hzNegLarge, hzPosLarge, hzm_selector, hzm_g_le, hzm_oneSub_le,
      hzm_normalized⟩ :=
    -- Keep one concrete descended mixed-witness circle alive instead of collapsing immediately to
    -- the weaker family-only selector-zero package.
    concreteDescendedMixedWitnessData_onFrozenCircle
      hρw_pos
      hρw_ltε
      hEqRatio
      hc_ne
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      hmixedSmallBelow
  have hρm_ltρ : ρm < ρ := lt_trans hρm_ltρw hρw_ltρ
  obtain ⟨thetaW, a, b, hcomponentData⟩ :=
    -- Package the bounded legal component around the frozen witness point into one reusable API.
    frozenWitnessComponentData_onLegalCircle
      hρw_pos
      hρw_ltε
      hwSmall_norm
      hwSmallE
      hg
      hselector_cont
  let thetaLeft : ℝ := thetaW - 1
  let thetaRight : ℝ := thetaW + 1
  let zeta : ℝ → ℂ := fun θ ↦ circleMap 0 ρw θ
  let selectorθ : ℝ → ℝ := fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖
  let S : Set ℝ := Set.Ioo thetaLeft thetaRight ∩ {θ | g (zeta θ) ∈ exercise16Domain}
  let C₀ : Set ℝ := connectedComponentIn S thetaW
  rcases hcomponentData with
    ⟨hthetaW_circle, hthetaLeft_lt_thetaW, hthetaW_lt_thetaRight, hthetaLeft_le_a,
      ha_lt_thetaW, hthetaW_lt_b, hb_le_thetaRight, hC₀_eq', hmaps_C₀,
      hga_mem_closure_exercise16, hgb_mem_closure_exercise16, hC₀_preconnected, htrichotomy⟩
  have hab : a < b := lt_trans ha_lt_thetaW hthetaW_lt_b
  have hmaps_Ioo : Set.MapsTo (fun θ ↦ g (zeta θ)) (Set.Ioo a b) exercise16Domain := by
    -- Move the legal image statement to the normalized interval spelling.
    simpa [hC₀_eq'] using hmaps_C₀
  have hg_circle_cont : Continuous fun θ ↦ g (zeta θ) := by
    -- Keep one reusable continuity fact for the frozen witness circle.
    simpa [zeta] using
      continuous_circleMap_comp_of_analyticOnNhd
        hρw_pos
        hρw_ltε
        hg
  have hS_open : IsOpen S := by
    have hexercise16_open : IsOpen exercise16Domain := by
      -- The Exercise-16 lens is the intersection of the two open unit balls.
      simpa [exercise16Domain] using
        (Metric.isOpen_ball.inter Metric.isOpen_ball :
          IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1))
    -- The frozen witness set is an open angle window intersected with an open image condition.
    refine isOpen_Ioo.inter ?_
    simpa [S] using hexercise16_open.preimage hg_circle_cont
  have hselectorTheta_cont : Continuous selectorθ := by
    -- Keep the frozen-circle selector continuity in one reusable local fact for the pending
    -- boundary-analysis consumers.
    simpa [selectorθ, zeta] using
      continuous_circleSelector_of_continuousOn
        hρw_pos
        hρw_ltε
        hselector_cont
  have ha_not_mem_S : a ∉ S := by
    -- Endpoints of the normalized component stay outside the legal frozen witness set.
    exact leftEndpoint_not_mem_legalWitnessSet hS_open ha_lt_thetaW hthetaW_lt_b hC₀_eq'
  have hb_not_mem_S : b ∉ S := by
    -- The same endpoint exclusion holds on the right.
    exact rightEndpoint_not_mem_legalWitnessSet hS_open ha_lt_thetaW hthetaW_lt_b hC₀_eq'
  have ha_not_mem_exercise16_of_lt : thetaLeft < a → g (zeta a) ∉ exercise16Domain := by
    intro hthetaLeft_lt_a hga
    apply ha_not_mem_S
    exact ⟨⟨hthetaLeft_lt_a, lt_of_lt_of_le hab hb_le_thetaRight⟩, hga⟩
  have hb_not_mem_exercise16_of_lt : b < thetaRight → g (zeta b) ∉ exercise16Domain := by
    intro hb_lt_thetaRight hgb
    apply hb_not_mem_S
    exact ⟨⟨lt_of_le_of_lt hthetaLeft_le_a hab, hb_lt_thetaRight⟩, hgb⟩
  let _ := hT_ge_one
  let _ := hF_analytic
  let _ := hmixedSmallBelow
  let _ := hess
  let _ := hnoSmallBelowρw
  let _ := hρm_pos
  let _ := hρm_ltρ
  let _ := zNeg
  let _ := zPos
  let _ := zm
  let _ := hzNeg_mem
  let _ := hzPos_mem
  let _ := hzm_mem
  let _ := hzNeg_norm
  let _ := hzPos_norm
  let _ := hzm_norm
  let _ := hzNegLarge
  let _ := hzPosLarge
  let _ := hzm_selector
  let _ := hzm_g_le
  let _ := hzm_oneSub_le
  let _ := hzm_normalized
  let _ := hga_mem_closure_exercise16
  let _ := hgb_mem_closure_exercise16
  let _ := ha_not_mem_exercise16_of_lt
  let _ := hb_not_mem_exercise16_of_lt
  have hzeroExtractor :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0 := by
    intro hweakNonpos hweakNonneg
    -- Keep the weak-sign component extractor explicit so the eventual descended-to-frozen bridge
    -- can target one stable consumer instead of rebuilding the trichotomy argument inline.
    exact witnessComponentZero_of_weakSigns htrichotomy hweakNonpos hweakNonneg
  obtain ⟨thetaNegM, thetaM, thetaPosM, hthetaNegM_lt, hthetaM_lt, hthetaNegM_circle,
      hthetaM_circle, hthetaPosM_circle, hselectorNegM, hselectorM_zero, hselectorPosM⟩ :=
    -- Package the concrete descended circle once so the remaining contradiction can consume one
    -- fixed negative/zero/positive selector pattern on radius `ρm`.
    descendedMixedWitnessSelectorSignData_onFrozenCircle
      hρm_pos
      (lt_trans hρm_ltρw hρw_ltε)
      hzNeg_norm
      hzPos_norm
      hzm_norm
      hzNegLarge
      hzPosLarge
      hzm_selector
      hbranch
      hg_nonzero
      hone_sub_nonzero
  let _ := thetaNegM
  let _ := thetaM
  let _ := thetaPosM
  let _ := hthetaNegM_lt
  let _ := hthetaM_lt
  let _ := hthetaNegM_circle
  let _ := hthetaM_circle
  let _ := hthetaPosM_circle
  let _ := hselectorNegM
  let _ := hselectorM_zero
  let _ := hselectorPosM
  let _ := hzeroExtractor
  let _ := hselectorTheta_cont
  have smallCircleBranch_of_interiorLegalSelectorZero_onFrozenWitnessComponent :
      ∀ ⦃η : ℝ⦄, η ∈ C₀ → selectorθ η = 0 →
        ∃ ρ', 0 < ρ' ∧ ρ' < ρw ∧
          ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
            ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) := by
    intro η hηC₀ hηzero
    have hη_mem_Ioo : η ∈ Set.Ioo a b := by
      -- Rewrite the frozen connected component back to the normalized interval spelling before
      -- invoking the witness-segment transport API.
      rwa [← hC₀_eq']
    have hsmallZeroBelowρw :
        ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
          ∃ z, ‖z‖ = ρ' ∧
            Real.log ‖g z / (1 - g z)‖ = 0 ∧
            Real.log ‖(g z)⁻¹‖ ≤ T ∧
              Real.log ‖((1 - g z)⁻¹)‖ ≤ T := by
      -- Route correction: keep the stronger descended selector-zero family in scope before
      -- deriving the weaker fixed-model normal form.
      exact
        smallZeroSelectorFamilyBelowRadius_of_noSmallBranch
          hess
          hε
          hρw_pos
          hρw_ltε
          hbranch
          hg_nonzero
          hone_sub_nonzero
          hselector_cont
          hg
          hnoSmallBelowρw
    have hinteriorContradiction : False := by
      -- Route correction: the main theorem now consumes a dedicated interior contradiction helper
      -- instead of reopening the packet transport here.
      exact
        interiorCommonShiftedPacketObstruction_of_descendedSmallScaleZeros
          hess
          hρw_pos
          hρw_ltε
          hc_ne
          hη_mem_Ioo
          ⟨ha_lt_thetaW, hthetaW_lt_b⟩
          (by simpa [selectorθ, zeta] using hηzero)
          hg_circle_cont
          (by
            intro θ
            simpa [zeta] using circleMap_mem_puncturedBall hρw_pos hρw_ltε θ)
          (by
            intro θ
            exact hg_nonzero _ (by simpa [zeta] using circleMap_mem_puncturedBall hρw_pos hρw_ltε θ))
          (by
            intro θ
            exact
              hone_sub_nonzero _ (by
                simpa [zeta] using circleMap_mem_puncturedBall hρw_pos hρw_ltε θ))
          hF_analytic
          hEqRatio
          hmaps_Ioo
          hsmallZeroBelowρw
    exact False.elim hinteriorContradiction
  have hdescentContradiction : False := by
    -- Route correction: the outer witness-component geometry is now stable. The only live work is
    -- the explicit interior common-model contradiction and the repaired left/right boundary
    -- analyses consumed by the branch contradiction adapters.
    have hboundaryBridge :
        ((∀ η ∈ C₀, 0 < selectorθ η) →
          ((∃ θ ∈ C₀, selectorθ θ = 0) ∨
            ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0)) ∧
          ((∀ η ∈ C₀, selectorθ η < 0) →
            ((∃ θ ∈ C₀, selectorθ θ = 0) ∨
              ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ)) := by
      -- TODO: keep the descended mixed-witness geometry on radius `ρm` visible long enough to
      -- produce the exact left/right boundary-analysis outputs on the frozen component. The old
      -- strict endpoint-sign bridge was false for the existing endpoint-cap API.
      sorry
    rcases htrichotomy with hzero | hposall | hnegall
    · rcases hzero with ⟨η, hηC₀, hηzero⟩
      -- An interior selector zero on `C₀` must already force the forbidden smaller-circle branch.
      rcases
          smallCircleBranch_of_interiorLegalSelectorZero_onFrozenWitnessComponent hηC₀ hηzero with
        ⟨ρ', hρ'pos, hρ'ltρw, hρ'branch⟩
      exact hnoSmallBelowρw ⟨ρ', hρ'pos, hρ'ltρw, hρ'branch⟩
    · -- The all-positive branch now closes directly from the weak-sign transport interface.
      exact
        positiveWitnessComponentContradiction_of_descendedBoundaryData
          hab
          hC₀_eq'
          hzeroExtractor
          hposall
          (hboundaryBridge.1 hposall)
    · -- The all-negative branch is handled by the symmetric weak-sign transport interface.
      exact
        negativeWitnessComponentContradiction_of_descendedBoundaryData
          hab
          hC₀_eq'
          hzeroExtractor
          hnegall
          (hboundaryBridge.2 hnegall)
  exact hdescentContradiction

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): the live mixed-witness tail should
return a strictly smaller circle carrying one uniformly bounded reciprocal branch, while keeping
the shrinking mixed-large witness geometry in scope. -/
lemma smallCircleUniformReciprocalBranch_of_outerMixedWitnessAndShrinkingMixedWitnessFamily
    {g : ℂ → ℂ} {ε ρ T : ℝ} {w zNeg zPos : ℂ}
    (hess : HasEssentialSingularityAt g 0)
    (hT_ge_one : 1 ≤ T)
    (hε : 0 < ε)
    (hρpos : 0 < ρ) (hρε : ρ < ε)
    (hw_norm : ‖w‖ = ρ)
    (hwE : g w ∈ exercise16Domain)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzNeg_norm : ‖zNeg‖ = ρ)
    (hzPos_norm : ‖zPos‖ = ρ)
    (hzNegLarge : T < Real.log ‖(g zNeg)⁻¹‖)
    (hzPosLarge : T < Real.log ‖((1 - g zPos)⁻¹)‖)
    (hmixedSmall :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧
      ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
        ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) := by
  obtain ⟨ρw, hρw_pos, hρw_small, wSmall, hwSmall_norm, hwSmallE, ρm, hρm_pos, hρm_ltρw,
      zNegSmall, zPosSmall, hzNegSmall_norm, hzPosSmall_norm, hzNegSmallLarge, hzPosSmallLarge⟩ :=
    -- Freeze one strictly smaller legal witness circle together with one further descendant
    -- mixed-witness circle below it.
    existsWitnessCircleWithDescendedMixedWitness
      (g := g) (ε := ε) (ρ := ρ) (T := T)
      hess hε hρpos hg hmixedSmall (ρ / 2) (half_pos hρpos)
  have hρw_ltρ : ρw < ρ := by
    exact lt_of_lt_of_le hρw_small (min_le_right _ _)
  have hρw_ltε : ρw < ε := lt_trans hρw_ltρ hρε
  have shrinkingMixedWitnessFamilyBelowρw :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρw ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
    -- Restrict the original shrinking mixed-witness family to the smaller frozen radius `ρw`.
    exact shrinkingMixedWitnessFamilyBelowRadius hρw_pos hρw_ltρ hmixedSmall
  let _ := ρm
  let _ := hρm_pos
  let _ := hρm_ltρw
  let _ := zNegSmall
  let _ := zPosSmall
  let _ := hzNegSmall_norm
  let _ := hzPosSmall_norm
  let _ := hzNegSmallLarge
  let _ := hzPosSmallLarge
  -- Route correction: the remaining work has been isolated to the smaller frozen witness circle
  -- `ρw`. The current theorem now delegates only that explicit smaller-circle descent consumer.
  exact
    smallCircleUniformReciprocalBranch_of_descendedWitnessCircle
      hess
      hT_ge_one
      hε
      hρw_pos
      hρw_ltρ
      hρw_ltε
      hwSmall_norm
      hwSmallE
      hg
      hbranch
      hg_nonzero
      hone_sub_nonzero
      hselector_cont
      shrinkingMixedWitnessFamilyBelowρw

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if one witness circle already carries
mixed large reciprocal logs, the corrected local goal is to descend to a strictly smaller centered
circle with one uniform reciprocal branch, not to contradict the original circle outright. -/
lemma smallCircleUniformReciprocalBranch_of_mixedLargeWitnessCircle
    {g : ℂ → ℂ} {ε ρ T : ℝ} {w zNeg zPos : ℂ}
    (hess : HasEssentialSingularityAt g 0)
    (hT_ge_one : 1 ≤ T)
    (hε : 0 < ε)
    (hρpos : 0 < ρ) (hρε : ρ < ε)
    (hw_norm : ‖w‖ = ρ)
    (hwE : g w ∈ exercise16Domain)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hbranch :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzNeg_norm : ‖zNeg‖ = ρ) (hzPos_norm : ‖zPos‖ = ρ)
    (hzNegLarge : T < Real.log ‖(g zNeg)⁻¹‖)
    (hzPosLarge : T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∃ ρ', 0 < ρ' ∧ ρ' < ρ ∧
      ((∀ z, ‖z‖ = ρ' → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
        ∀ z, ‖z‖ = ρ' → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) := by
  classical
  by_contra hnoSmall
  have hmixedSmall :
      ∀ δ > 0, ∃ ρ', 0 < ρ' ∧ ρ' < min δ ρ ∧
        ∃ zNeg zPos, ‖zNeg‖ = ρ' ∧ ‖zPos‖ = ρ' ∧
          T < Real.log ‖(g zNeg)⁻¹‖ ∧
            T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
    intro δ hδ
    -- Route correction: under the negation of the target, every smaller scale still yields a
    -- smaller centered circle with mixed large reciprocal logs on the two branches.
    exact
      exists_mixedLargeReciprocalLogs_on_smallerCircle_of_no_smallCircleUniformReciprocalBranch
        hess
        hε
        hρpos
        hδ
        hg
        hg_nonzero
        hone_sub_nonzero
        hnoSmall
  -- Route correction: once the smaller-scale mixed-witness family is available, the remaining
  -- work is exactly the strengthened descent consumer that keeps those witnesses alive.
  exact
    hnoSmall <|
      smallCircleUniformReciprocalBranch_of_outerMixedWitnessAndShrinkingMixedWitnessFamily
        hess
        hT_ge_one
        hε
        hρpos
        hρε
        hw_norm
        hwE
        hg
        hbranch
        hg_nonzero
        hone_sub_nonzero
        hselector_cont
        hzNeg_norm
        hzPos_norm
        hzNegLarge
        hzPosLarge
        hmixedSmall
/- Legacy false fixed-circle contradiction attempt retained only as commented context during the
current replan frontier.
  let zeta : ℝ → ℂ := fun θ ↦ circleMap 0 ρ θ
  let selectorθ : ℝ → ℝ := fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖
  obtain ⟨thetaNeg, thetaW, thetaPos, hthetaNeg_lt, hthetaW_lt, hthetaW_circle,
      hthetaNeg_circle, hthetaPos_circle⟩ :=
    sameCircleAngleOrder_throughWitness hρpos hw_norm hzNeg_norm hzPos_norm
  obtain ⟨n, F, c, hc_ne, hF_analytic, hEqRatio⟩ :=
    witnessCircleNormalizedRatioNormalForm
      hε hρpos hρε hg hg_nonzero hone_sub_nonzero
  have hzeta_mem : ∀ θ, zeta θ ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    intro θ
    constructor
    · -- Every point of the radius-`ρ` circle stays inside the ambient punctured ball.
      simpa [zeta, Metric.mem_ball, dist_eq_norm, norm_circleMap_zero,
        abs_of_nonneg (le_of_lt hρpos)] using hρε
    · -- The circle radius is strictly positive, so the parameterized circle avoids the origin.
      exact norm_ne_zero_iff.mp <| by
        simpa [zeta, norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)] using hρpos.ne'
  have hg_circle_cont : Continuous fun θ ↦ g (zeta θ) := by
    -- Restrict `g` to the fixed witness circle through the punctured-ball continuity package.
    simpa [zeta] using hg.continuousOn.comp_continuous (continuous_circleMap 0 ρ) hzeta_mem
  have hselectorTheta_cont : Continuous selectorθ := by
    -- The quotient selector stays continuous along that same fixed circle.
    simpa [selectorθ, zeta] using
      hselector_cont.comp_continuous (continuous_circleMap 0 ρ) hzeta_mem
  have hthetaW_mem_exercise16 :
      g (zeta thetaW) ∈ exercise16Domain := by
    simpa [zeta, hthetaW_circle] using hwE
  obtain ⟨a, b, hthetaNeg_le_a, ha_lt_thetaW, hthetaW_lt_b, hb_le_thetaPos, hC₀_eq⟩ :=
    windowedWitnessComponent_eq_Ioo
      hthetaNeg_lt hthetaW_lt hthetaW_mem_exercise16 hg.continuousOn hzeta_mem
  let S : Set ℝ := Set.Ioo thetaNeg thetaPos ∩ {θ | g (zeta θ) ∈ exercise16Domain}
  let C₀ : Set ℝ := connectedComponentIn S thetaW
  have hC₀_eq' : C₀ = Set.Ioo a b := by
    -- Re-express the normalized component using the local abbreviations introduced above.
    simpa [C₀, S, zeta] using hC₀_eq
  have hab : a < b := lt_trans ha_lt_thetaW hthetaW_lt_b
  have hS_open : IsOpen S := by
    have hexercise16_open : IsOpen exercise16Domain := by
      -- The Exercise-16 lens is the intersection of the two open unit balls.
      simpa [exercise16Domain] using
        (Metric.isOpen_ball.inter Metric.isOpen_ball :
          IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1))
    -- The witness set is the intersection of the ordered-angle window with the legal-image
    -- preimage along the fixed circle.
    refine isOpen_Ioo.inter ?_
    simpa [S] using hexercise16_open.preimage hg_circle_cont
  have hC₀_preconnected : IsPreconnected C₀ := by
    -- The normalized witness component is an open interval, hence preconnected.
    simpa [hC₀_eq'] using (isPreconnected_Ioo : IsPreconnected (Set.Ioo a b))
  have hmaps_C₀ : Set.MapsTo (fun θ ↦ g (zeta θ)) C₀ exercise16Domain := by
    intro θ hθ
    exact (connectedComponentIn_subset S thetaW hθ).2
  have hmaps_Ioo : Set.MapsTo (fun θ ↦ g (zeta θ)) (Set.Ioo a b) exercise16Domain := by
    -- Rewrite the connected component to the normalized interval before using the generic
    -- connected-component subset fact.
    simpa [hC₀_eq'] using hmaps_C₀
  have hga_mem_closure_exercise16 : g (zeta a) ∈ closure exercise16Domain := by
    -- The left endpoint is a closure point of the legal interval image.
    exact image_leftEndpoint_mem_closure_of_mapsTo_Ioo hab hg_circle_cont hmaps_Ioo
  have hgb_mem_closure_exercise16 : g (zeta b) ∈ closure exercise16Domain := by
    -- The right endpoint is handled symmetrically.
    exact image_rightEndpoint_mem_closure_of_mapsTo_Ioo hab hg_circle_cont hmaps_Ioo
  have ha_not_mem_S : a ∉ S := by
    -- Endpoints of the normalized connected component stay outside the legal source set.
    exact leftEndpoint_not_mem_legalWitnessSet hS_open ha_lt_thetaW hthetaW_lt_b hC₀_eq'
  have hb_not_mem_S : b ∉ S := by
    -- The same endpoint exclusion holds on the right.
    exact rightEndpoint_not_mem_legalWitnessSet hS_open ha_lt_thetaW hthetaW_lt_b hC₀_eq'
  have ha_not_mem_exercise16_of_lt : thetaNeg < a → g (zeta a) ∉ exercise16Domain := by
    intro hthetaNeg_lt_a hga
    apply ha_not_mem_S
    exact ⟨⟨hthetaNeg_lt_a, lt_of_lt_of_le hab hb_le_thetaPos⟩, hga⟩
  have hb_not_mem_exercise16_of_lt : b < thetaPos → g (zeta b) ∉ exercise16Domain := by
    intro hb_lt_thetaPos hgb
    apply hb_not_mem_S
    exact ⟨⟨lt_of_le_of_lt hthetaNeg_le_a hab, hb_lt_thetaPos⟩, hgb⟩
  have hzNeg_mem : zNeg ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hzNeg_norm] using hρε
    · exact norm_ne_zero_iff.mp <| by simpa [hzNeg_norm] using hρpos.ne'
  have hzPos_mem : zPos ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hzPos_norm] using hρε
    · exact norm_ne_zero_iff.mp <| by simpa [hzPos_norm] using hρpos.ne'
  have hbranchExp :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ Real.exp T ∨ ‖((1 - g z)⁻¹)‖ ≤ Real.exp T := by
    intro z hz
    rcases hbranch z hz with hg_log | hone_sub_log
    · left
      have hpos : 0 < ‖(g z)⁻¹‖ := by
        exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero z hz))
      exact (Real.log_le_iff_le_exp hpos).1 hg_log
    · right
      have hpos : 0 < ‖((1 - g z)⁻¹)‖ := by
        exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero z hz))
      exact (Real.log_le_iff_le_exp hpos).1 hone_sub_log
  have hzNegLargeExp : Real.exp T < ‖(g zNeg)⁻¹‖ := by
    have hpos : 0 < ‖(g zNeg)⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero zNeg hzNeg_mem))
    exact (Real.lt_log_iff_exp_lt hpos).1 hzNegLarge
  have hzPosLargeExp : Real.exp T < ‖((1 - g zPos)⁻¹)‖ := by
    have hpos : 0 < ‖((1 - g zPos)⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero zPos hzPos_mem))
    exact (Real.lt_log_iff_exp_lt hpos).1 hzPosLarge
  have hselectorNeg : selectorθ thetaNeg < 0 := by
    -- The left mixed-large witness forces a strictly negative selector value.
    simpa [selectorθ, zeta, hthetaNeg_circle] using
      selectorNegOfLargeReciprocal
        (hg_nonzero zNeg hzNeg_mem)
        (hone_sub_nonzero zNeg hzNeg_mem)
        (hbranchExp zNeg hzNeg_mem)
        hzNegLargeExp
  have hselectorPos : 0 < selectorθ thetaPos := by
    -- The right mixed-large witness forces the opposite strict sign.
    simpa [selectorθ, zeta, hthetaPos_circle] using
      selectorPosOfLargeOneSubReciprocal
        (hg_nonzero zPos hzPos_mem)
        (hone_sub_nonzero zPos hzPos_mem)
        (hbranchExp zPos hzPos_mem)
        hzPosLargeExp
  obtain ⟨θ₀, hθ₀_window, hθ₀_zero⟩ :=
    orderedWindowZero_of_mixedWitnessSigns
      (selectorθ := selectorθ)
      (hthetaNeg_lt_thetaPos := lt_trans hthetaNeg_lt hthetaW_lt)
      hselectorTheta_cont
      hselectorNeg
      hselectorPos
  have hθ₀_windowInterior : θ₀ ∈ Set.Ioo thetaNeg thetaPos := by
    -- The ordered-window zero cannot coincide with either strict-sign endpoint.
    exact
      orderedWindowZero_mem_Ioo_of_endpointSigns
        hθ₀_window hθ₀_zero hselectorNeg hselectorPos
  have hθ₀_logs_le :
      Real.log ‖(g (zeta θ₀))⁻¹‖ ≤ T ∧
        Real.log ‖((1 - g (zeta θ₀))⁻¹)‖ ≤ T := by
    -- Route correction: keep the selector-zero witness on the ordered angle window before any
    -- packet comparison, and recover the reciprocal bounds at that same angle directly.
    simpa [selectorθ, zeta] using
      reciprocalLogs_le_of_circleSelectorEqZero
        (hzeta_mem θ₀) hg_nonzero hone_sub_nonzero hbranch hθ₀_zero
  have htrichotomy :
      (∃ η ∈ C₀, selectorθ η = 0) ∨
        (∀ η ∈ C₀, 0 < selectorθ η) ∨
        (∀ η ∈ C₀, selectorθ η < 0) := by
    -- Route correction: after switching to the bounded windowed component, the main proof reduces
    -- to the selector trichotomy on that single interval component.
    exact zeroOrStrictSignOnPreconnected hC₀_preconnected hselectorTheta_cont.continuousOn
  -- TODO: the remaining blocker is the final windowed-component contradiction. The normalized
  -- component `C₀ = Ioo a b`, the endpoint selector signs at `thetaNeg` and `thetaPos`, the
  -- same-circle normal-form zero at `θ₀`, and the selector trichotomy on `C₀` are now in place.
  -- What is still missing is the consumer that turns either an interior legal selector zero or one
  -- of the two strict-sign branches on `C₀` into contradiction using the endpoint-anchor API and
  -- `principalLogPeriod_onClosedLegalInterval`.
  have hT_nonneg : 0 ≤ T := le_trans (by norm_num) hT_ge_one
  clear hT_nonneg
  have hgzeta_nonzero : ∀ θ, g (zeta θ) ≠ 0 := by
    intro θ
    exact hg_nonzero (zeta θ) (hzeta_mem θ)
  have hone_sub_zeta_nonzero : ∀ θ, 1 - g (zeta θ) ≠ 0 := by
    intro θ
    exact hone_sub_nonzero (zeta θ) (hzeta_mem θ)
  have hselector_def :
      selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖ := by
    rfl
  have hclosedLegalMaps :
      ∀ {u v : ℝ}, Set.Icc u v ⊆ C₀ →
        Set.MapsTo (fun θ ↦ g (zeta θ)) (Set.Icc u v) exercise16Domain := by
    intro u v huv
    -- Move the interval inclusion back to the connected-component spelling expected by the bridge
    -- lemma.
    simpa [C₀, S, zeta] using
      closedLegalMapsTo_of_Icc_subset_windowedWitnessComponent huv
  have hleftAnchor_of_positive :
      (∀ η ∈ C₀, 0 < selectorθ η) →
        Real.log ‖(g (zeta a))⁻¹‖ = 0 := by
    intro hposall
    -- The positive branch pins the left boundary point to the `‖g‖ = 1` cap.
    exact
      positiveComponent_leftEndpointAnchor
        ha_lt_thetaW
        hthetaW_lt_b
        hC₀_eq'
        hselectorTheta_cont
        hselector_def
        hposall
        hthetaNeg_le_a
        hselectorNeg
        (hgzeta_nonzero a)
        (hone_sub_zeta_nonzero a)
        hga_mem_closure_exercise16
        ha_not_mem_exercise16_of_lt
  have hrightAnchor_of_negative :
      (∀ η ∈ C₀, selectorθ η < 0) →
        Real.log ‖((1 - g (zeta b))⁻¹)‖ = 0 := by
    intro hnegall
    -- The negative branch gives the symmetric right-boundary anchor on `1 - g`.
    exact
      negativeComponent_rightEndpointAnchor
        ha_lt_thetaW
        hthetaW_lt_b
        hC₀_eq'
        hselectorTheta_cont
        hselector_def
        hnegall
        hb_le_thetaPos
        hselectorPos
        (hgzeta_nonzero b)
        (hone_sub_zeta_nonzero b)
        hgb_mem_closure_exercise16
        hb_not_mem_exercise16_of_lt
  have gReciprocalLog_le_onPositiveWitnessComponent :
      (∀ η ∈ C₀, 0 < selectorθ η) →
        ∀ η ∈ C₀, Real.log ‖(g (zeta η))⁻¹‖ ≤ T := by
    intro hposall η hηC₀
    have hη_bound :
        ‖(g (zeta η))⁻¹‖ ≤ Real.exp T := by
      -- On the positive branch, the selector sign chooses the `g⁻¹` bound from the global
      -- pointwise Exercise-16 alternative.
      exact
        reciprocalBound_of_logQuotientNonneg
          (hgzeta_nonzero η)
          (hone_sub_zeta_nonzero η)
          (hbranchExp (zeta η) (hzeta_mem η))
          (le_of_lt (hposall η hηC₀))
    have hη_norm_pos : 0 < ‖(g (zeta η))⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hgzeta_nonzero η))
    -- Convert the selected reciprocal norm bound back to the logarithmic scale used below.
    exact (Real.log_le_iff_le_exp hη_norm_pos).2 hη_bound
  have oneSubReciprocalLog_le_onNegativeWitnessComponent :
      (∀ η ∈ C₀, selectorθ η < 0) →
        ∀ η ∈ C₀, Real.log ‖((1 - g (zeta η))⁻¹)‖ ≤ T := by
    intro hnegall η hηC₀
    have hη_bound :
        ‖((1 - g (zeta η))⁻¹)‖ ≤ Real.exp T := by
      -- The symmetric negative-selector case chooses the `(1 - g)⁻¹` branch pointwise.
      exact
        reciprocalBound_of_logQuotientNonpos
          (hgzeta_nonzero η)
          (hone_sub_zeta_nonzero η)
          (hbranchExp (zeta η) (hzeta_mem η))
          (le_of_lt (hnegall η hηC₀))
    have hη_norm_pos : 0 < ‖((1 - g (zeta η))⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_zeta_nonzero η))
    -- As above, return to the logarithmic branch bound expected by the endpoint consumers.
    exact (Real.log_le_iff_le_exp hη_norm_pos).2 hη_bound
  have interiorLegalZeroContradiction_onWitnessComponent :
      ∀ ⦃η : ℝ⦄, η ∈ C₀ → selectorθ η = 0 → False := by
    intro η hηC₀ hηzero
    have hη_mem_Ioo : η ∈ Set.Ioo a b := by
      -- Rewrite the connected component back to the normalized open interval before shrinking it.
      simpa [hC₀_eq'] using hηC₀
    obtain ⟨kW, hreferencePacket⟩ :=
      referenceBranchNormalizedPacket_onWitnessSegment
        hρpos hc_ne hη_mem_Ioo ⟨ha_lt_thetaW, hthetaW_lt_b⟩ hg_circle_cont hzeta_mem
        hgzeta_nonzero hone_sub_zeta_nonzero hF_analytic hEqRatio hmaps_Ioo
    have hη_mem_segment : η ∈ Set.Icc (min η thetaW) (max η thetaW) := by
      -- The selector-zero point is one endpoint of the comparison segment.
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    have hthetaW_mem_segment : thetaW ∈ Set.Icc (min η thetaW) (max η thetaW) := by
      -- The witness reference point is the other endpoint of that segment.
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    have hη_packet := hreferencePacket hη_mem_segment
    have hthetaW_packet := hreferencePacket hthetaW_mem_segment
    have hη_maps : g (zeta η) ∈ exercise16Domain := hmaps_Ioo hη_mem_Ioo
    have hη_logs_le :
        Real.log ‖(g (zeta η))⁻¹‖ ≤ T ∧
          Real.log ‖((1 - g (zeta η))⁻¹)‖ ≤ T := by
      -- A zero selector on the witness circle forces both reciprocal logarithms below the global
      -- Exercise-16 threshold.
      simpa [zeta, selectorθ] using
        reciprocalLogs_le_of_circleSelectorEqZero
          (hzeta_mem η) hg_nonzero hone_sub_nonzero hbranch hηzero
    have hη_packet_im :
        (Complex.log (g (zeta η))).im - (Complex.log (1 - g (zeta η))).im =
          (Complex.log c).im + (n : ℝ) * η + (F (zeta η)).im + (kW : ℝ) * (2 * Real.pi) := by
      -- Project the packet to the exact imaginary-part identity needed for the remaining
      -- principal-branch obstruction.
      simpa [zeta] using
        packetImaginaryProjection hρpos hη_packet
    have hthetaW_packet_im :
        (Complex.log (g (zeta thetaW))).im - (Complex.log (1 - g (zeta thetaW))).im =
          (Complex.log c).im + (n : ℝ) * thetaW + (F (zeta thetaW)).im +
            (kW : ℝ) * (2 * Real.pi) := by
      -- The same normalized packet also describes the witness reference point `thetaW`.
      simpa [zeta] using
        packetImaginaryProjection hρpos hthetaW_packet
    have hη_logRatio_packet :
        Complex.log (g (zeta η) / (1 - g (zeta η))) =
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) + F (zeta η) +
            kW * (2 * (Real.pi : ℂ) * Complex.I) := by
      -- Rewrite the legal packet at `η` into the quotient-log normal form before comparing it to
      -- the reference point.
      simpa [zeta] using
        logQuotient_eq_packet_of_mem_exercise16Domain hη_maps hη_packet
    have hthetaW_maps : g (zeta thetaW) ∈ exercise16Domain := by
      simpa [zeta, hthetaW_circle] using hwE
    have hthetaW_logRatio_packet :
        Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW))) =
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
            F (zeta thetaW) + kW * (2 * (Real.pi : ℂ) * Complex.I) := by
      -- The same legal-point packet normalization applies at the witness reference angle.
      simpa [zeta] using
        logQuotient_eq_packet_of_mem_exercise16Domain hthetaW_maps hthetaW_packet
    have hη_logRatio_im_strip :
        -Real.pi < (Complex.log (g (zeta η) / (1 - g (zeta η)))).im ∧
          (Complex.log (g (zeta η) / (1 - g (zeta η)))).im < Real.pi := by
      -- The legal quotient at `η` stays inside the principal strip with no residual endpoint
      -- ambiguity.
      simpa [zeta] using logImDiv_mem_openInterval_of_mem_exercise16Domain hη_maps
    have hthetaW_logRatio_im_strip :
        -Real.pi < (Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW)))).im ∧
          (Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW)))).im < Real.pi := by
      -- The reference point lies in the same legal strip, so the normalized packet must match the
      -- principal branch there as well.
      simpa [zeta] using logImDiv_mem_openInterval_of_mem_exercise16Domain hthetaW_maps
    have hpacket_im_difference :
        ((Complex.log (g (zeta η))).im - (Complex.log (1 - g (zeta η))).im) -
            ((Complex.log (g (zeta thetaW))).im - (Complex.log (1 - g (zeta thetaW))).im) =
          (n : ℝ) * (η - thetaW) + ((F (zeta η)).im - (F (zeta thetaW)).im) := by
      -- Package the already-verified packet subtraction into a single reusable identity.
      simpa [zeta] using
        normalizedPacketImaginaryDifference
          hρpos hη_packet hthetaW_packet
    have hθW_normalForm :
        selectorθ thetaW =
          Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (zeta thetaW)).re := by
      -- The witness point uses the same real-part normal form as every point on the circle.
      simpa [selectorθ, zeta] using
        circleSelector_eq_normalForm hρpos hc_ne hEqRatio (hzeta_mem thetaW)
    -- Route correction: the interior branch is now reduced to the intended frontier. The real-part
    -- comparison to the global same-circle zero witness is packaged in `hη_re_eq_hθ₀`, and the
    -- normalized witness-packet subtraction is packaged in `hpacket_im_difference`. The remaining
    -- obstruction is the genuinely missing global branch comparison that combines those two facts
    -- with the principal-strip bounds.
    have hkW_zero_of_normalStrip :
        (-Real.pi <
              (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
                F (zeta η)).im ∧
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) +
                F (zeta η)).im < Real.pi) →
          kW = 0 := by
      intro hη_normalForm_im_strip
      -- Once the packet normal form itself lies in the principal strip at `η`, the legal-point
      -- packet cannot carry a nontrivial `2π i` correction.
      exact
        packetPeriodZero_of_principalStripComparison
          hη_logRatio_im_strip hη_normalForm_im_strip hη_logRatio_packet
    let Fη : ℂ → ℂ := fun z ↦ F z + kW * (2 * (Real.pi : ℂ) * Complex.I)
    have hFη_analytic :
        AnalyticOnNhd ℂ Fη (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
      -- Normalizing the witness branch by a constant period keeps the punctured-ball model
      -- analytic.
      simpa [Fη, add_assoc, add_left_comm, add_comm] using
        hF_analytic.add analyticOnNhd_const
    have hEqRatioη :
        Set.EqOn (fun z ↦ g z / (1 - g z))
          (fun z ↦ c * z ^ n * Complex.exp (Fη z))
          (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
      -- Shift the normal form by the reference period so the legal packet at `η` becomes
      -- period-free.
      simpa [Fη, add_assoc, add_left_comm, add_comm] using
        eqOn_normalizedRatio_of_add_periodShift hEqRatio
    have hη_logRatio_packet_zeroPeriod :
        Complex.log (g (zeta η) / (1 - g (zeta η))) =
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) + Fη (zeta η) := by
      -- After the global period normalization, the packet at the legal selector-zero point agrees
      -- with the principal branch on the nose.
      simpa [Fη, add_assoc, add_left_comm, add_comm] using hη_logRatio_packet
    have hη_normalized_im_strip :
        -Real.pi <
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) + Fη (zeta η)).im ∧
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + η * Complex.I) + Fη (zeta η)).im <
            Real.pi := by
      -- Repackage the legal selector-zero packet into the standalone strip lemma so the remaining
      -- interior obstruction is isolated to the global `θ₀` transport step.
      exact
        normalizedPacketImStrip_of_selectorEqZero_of_packetEq
          (hgzeta_nonzero η) (hone_sub_zeta_nonzero η) hηzero hη_logRatio_packet_zeroPeriod
    have hθ₀_zero_onCircle :
        Real.log ‖g (zeta θ₀) / (1 - g (zeta θ₀))‖ = 0 := by
      -- Repackage the ordered-window selector zero in the current `zeta` spelling.
      simpa [selectorθ] using hθ₀_zero
    have hθ₀_normalized_re_zero :
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (Fη (zeta θ₀)).re = 0 := by
      -- The same period-shifted real-part identity also holds at the global same-circle zero
      -- witness `θ₀`.
      have hθ₀_shifted_re :
          Real.log ‖c‖ + (n : ℝ) * Real.log ρ +
              ((F (circleMap 0 ρ θ₀) + kW * (2 * (Real.pi : ℂ) * Complex.I)).re) = 0 :=
        circleNormalFormRealPart_eq_zero_of_selectorEqZero_for_periodShift
          hρpos hc_ne hEqRatio (hzeta_mem θ₀) hθ₀_zero_onCircle
      simpa [Fη, zeta, add_assoc, add_left_comm, add_comm] using hθ₀_shifted_re
    have hη_normalized_re_eq_hθ₀ :
        (Fη (zeta η)).re = (Fη (zeta θ₀)).re := by
      -- The common period shift preserves the real-part equality forced by the two selector-zero
      -- points on the same witness circle.
      have hη_shifted_re_eq_hθ₀ :
          (F (circleMap 0 ρ η) + kW * (2 * (Real.pi : ℂ) * Complex.I)).re =
            (F (circleMap 0 ρ θ₀) + kW * (2 * (Real.pi : ℂ) * Complex.I)).re :=
        periodShiftedNormalFormRe_eq_of_twoSelectorZeros
          hρpos hc_ne hEqRatio (hzeta_mem η) (hzeta_mem θ₀) hηzero hθ₀_zero_onCircle
      simpa [Fη, zeta, add_assoc, add_left_comm, add_comm] using hη_shifted_re_eq_hθ₀
    have hpacket_im_differenceη :
        ((Complex.log (g (zeta η))).im - (Complex.log (1 - g (zeta η))).im) -
            ((Complex.log (g (zeta thetaW))).im - (Complex.log (1 - g (zeta thetaW))).im) =
          (n : ℝ) * (η - thetaW) + ((Fη (zeta η)).im - (Fη (zeta thetaW)).im) := by
      -- The imaginary-difference comparison is unchanged by the common `2π i` shift used to
      -- define `Fη`.
      simpa [Fη, zeta, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
        hpacket_im_difference
    have hthetaW_logRatio_packetη :
        Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW))) =
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + thetaW * Complex.I) +
            Fη (zeta thetaW) := by
      -- Keep the witness-reference packet in the same shifted-model spelling used at `η` and
      -- `θ₀`.
      exact
        thetaWPrincipalPacket_inShiftedModel
          rfl (by simpa [zeta] using hthetaW_logRatio_packet)
    have hη_thetaW_logRatio_im_difference :
        (Complex.log (g (zeta η) / (1 - g (zeta η)))).im -
            (Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW)))).im =
          (n : ℝ) * (η - thetaW) + ((Fη (zeta η)).im - (Fη (zeta thetaW)).im) := by
      -- Package the same-circle shifted-model comparison in the exact quotient-log spelling needed
      -- by the remaining `θ₀` contradiction.
      simpa [zeta] using
        shiftedThetaZeroPacketComparisonData
          hρpos hη_logRatio_packet_zeroPeriod hthetaW_logRatio_packetη
    clear hη_logs_le
    clear hη_packet_im
    clear hthetaW_packet_im
    obtain ⟨kθ₀, hθ₀_logRatio_packet_shifted, hθ₀_shifted_im_strip⟩ :=
      -- The current file naturally produces the ordered-window packet only up to one explicit
      -- period shift, so keep that shifted interface instead of forcing the residual period to
      -- vanish here.
      thetaZeroShiftedPacketData_of_referenceZero
        hρpos hc_ne hzeta_mem hgzeta_nonzero hone_sub_zeta_nonzero hEqRatioη
        hθ₀_zero_onCircle
    have hθ₀_zero_from_shiftedPacket :
        Real.log ‖g (zeta θ₀) / (1 - g (zeta θ₀))‖ = 0 := by
      -- Re-extract the selector-zero equation directly from the shifted packet and the normalized
      -- real-part vanishing, so the final interior helper can consume it explicitly.
      simpa [zeta] using
        selectorEqZero_of_shiftedThetaZeroPacket
          hρpos hθ₀_logRatio_packet_shifted hθ₀_normalized_re_zero
    have hthetaW_θ₀_logRatio_im_difference_withPeriod :
        (Complex.log (g (zeta θ₀) / (1 - g (zeta θ₀)))).im -
            (Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW)))).im =
          (n : ℝ) * (θ₀ - thetaW) +
            ((Fη (zeta θ₀)).im - (Fη (zeta thetaW)).im) +
            (kθ₀ : ℝ) * (2 * Real.pi) := by
      -- Keep the residual period explicit until the dedicated strip-transport helper removes it.
      simpa [zeta] using
        thetaWThetaZeroShiftedPacketComparisonData_withPeriod
          hρpos hthetaW_logRatio_packetη hθ₀_logRatio_packet_shifted
    have hkθ₀_zero : kθ₀ = 0 := by
      -- Route correction: the remaining missing input is still the unshifted principal-strip
      -- statement at `θ₀`. The new helper `shiftedThetaZeroPacket_eq_unshiftedNormal_plus_period`
      -- isolates the exact residual-period spelling needed for the next period-killing attempt.
      let _ :=
        shiftedThetaZeroPacket_eq_unshiftedNormal_plus_period hθ₀_logRatio_packet_shifted
      -- TODO: prove the unshifted strip at `θ₀` from the exact `η ↔ thetaW ↔ θ₀` packet
      -- comparison, then apply `selectorZeroPacketPeriod_eq_zero` to the reassociated packet above.
      sorry
    have hθ₀_normalized_im_strip :
        -Real.pi <
            (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
                Fη (zeta θ₀)).im ∧
          (Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ₀ * Complex.I) +
              Fη (zeta θ₀)).im < Real.pi := by
      -- After the residual period has been killed, the shifted strip is exactly the desired
      -- unshifted principal-strip statement.
      exact
        thetaZeroNormalizedImStrip_of_referenceZero
          hkθ₀_zero
          hθ₀_shifted_im_strip
    have hthetaW_θ₀_logRatio_im_difference :
        (Complex.log (g (zeta θ₀) / (1 - g (zeta θ₀)))).im -
            (Complex.log (g (zeta thetaW) / (1 - g (zeta thetaW)))).im =
          (n : ℝ) * (θ₀ - thetaW) + ((Fη (zeta θ₀)).im - (Fη (zeta thetaW)).im) := by
      -- The `θ₀` packet must first be compared to `thetaW` in the same shifted witness model.
      simpa [zeta] using
        thetaWThetaZeroShiftedPacketComparisonData
          hρpos hthetaW_logRatio_packetη hkθ₀_zero hθ₀_logRatio_packet_shifted
    obtain ⟨hθ₀_logRatio_packet_zeroPeriod, hnormalizedPacketStrips⟩ :=
      -- Route correction: package the exact `θ₀` packet and the paired strip control in the common
      -- shifted model before the final interior contradiction step.
      commonShiftedPacketBundle_of_referenceZero
        (g := g)
        (Fη := Fη)
        (ε := ε)
        (ρ := ρ)
        (n := n)
        (c := c)
        (η := η)
        (thetaW := thetaW)
        (θ₀ := θ₀)
        hρpos
        hc_ne
        hzeta_mem
        hgzeta_nonzero
        hone_sub_zeta_nonzero
        hEqRatioη
        hηzero
        hθ₀_zero_from_shiftedPacket
        hη_logRatio_packet_zeroPeriod
        hη_thetaW_logRatio_im_difference
        (by simpa [zeta] using hthetaW_θ₀_logRatio_im_difference)
    have hinteriorContradiction : False := by
      -- Route correction: the packet transport data above is coherent, but it cannot close a
      -- contradiction while the enclosing fixed-circle helper remains statement-false.
      sorry
    exact hinteriorContradiction
  have hzeroExtractor :
      (∃ sigmaNeg ∈ C₀, selectorθ sigmaNeg ≤ 0) →
        (∃ sigmaPos ∈ C₀, 0 ≤ selectorθ sigmaPos) →
          ∃ θ ∈ C₀, selectorθ θ = 0 := by
    intro hweakNonpos hweakNonneg
    -- Feed the weak-sign witnesses into the already established selector trichotomy on `C₀`.
    exact
      existsZeroOfWeakSignsOfZeroOrStrictSign
        htrichotomy hweakNonpos hweakNonneg
  have leftFirstCrossingContradiction_of_positiveWitnessOuterZero :
      (∀ η ∈ C₀, 0 < selectorθ η) →
        ∀ ⦃sigma : ℝ⦄,
          sigma ∈ Set.Icc thetaNeg thetaW →
            selectorθ sigma = 0 →
              sigma ∉ C₀ →
                False := by
    intro hposall sigma hsigma_mem hsigma_zero hsigma_not_mem_C₀
    have hleftBoundary :
        (∃ θ ∈ C₀, selectorθ θ = 0) ∨
          ∃ δ > 0, ∀ θ ∈ Set.Ioo a (min (a + δ) b), selectorθ θ < 0 := by
      -- Route correction: this boundary consumer belongs to the same false fixed-circle package.
      -- The current arbitrary outer-zero data does not support the claimed contradiction until the
      -- enclosing helper statement is replaced by a correct variant.
      let _ := sigma
      let _ := hsigma_mem
      let _ := hsigma_zero
      let _ := hsigma_not_mem_C₀
      sorry
    -- Once the missing first-crossing boundary analysis is available, the remaining contradiction
    -- is exactly the positive-component zero-extractor adapter proved above.
    exact
      leftBoundaryContradiction_of_positiveWitnessFirstCrossing
        hab
        hC₀_eq'
        hzeroExtractor
        hposall
        hleftBoundary
  have rightLastExitContradiction_of_negativeWitnessOuterZero :
      (∀ η ∈ C₀, selectorθ η < 0) →
        ∀ ⦃sigma : ℝ⦄,
          sigma ∈ Set.Icc thetaW thetaPos →
            selectorθ sigma = 0 →
              sigma ∉ C₀ →
                False := by
    intro hnegall sigma hsigma_mem hsigma_notzero hsigma_not_mem_C₀
    have hrightBoundary :
        (∃ θ ∈ C₀, selectorθ θ = 0) ∨
          ∃ δ > 0, ∀ θ ∈ Set.Ioo (max a (b - δ)) b, 0 < selectorθ θ := by
      -- Route correction: the symmetric endpoint consumer fails for the same reason as the left
      -- one above. The current outer-zero data is insufficient until the enclosing helper
      -- statement is repaired.
      let _ := sigma
      let _ := hsigma_mem
      let _ := hsigma_notzero
      let _ := hsigma_not_mem_C₀
      sorry
    -- With the boundary analysis in hand, the remaining contradiction is the negative-component
    -- zero-extractor adapter already proved above.
    exact
      rightBoundaryContradiction_of_negativeWitnessLastExit
        hab
        hC₀_eq'
        hzeroExtractor
        hnegall
        hrightBoundary
  have leftBoundaryDirectContradiction_ofPositiveWitnessComponent :
      (∀ η ∈ C₀, 0 < selectorθ η) → False := by
    intro hposall
    have hthetaW_mem_C₀ : thetaW ∈ C₀ := by
      -- The witness reference angle is an interior point of the normalized component.
      rw [hC₀_eq']
      exact ⟨ha_lt_thetaW, hthetaW_lt_b⟩
    have hthetaW_pos : 0 < selectorθ thetaW := hposall thetaW hthetaW_mem_C₀
    have houterZero :
        ∃ sigma ∈ Set.Icc thetaNeg thetaW, selectorθ sigma = 0 := by
      have hsurj :
          Set.Icc (selectorθ thetaNeg) (selectorθ thetaW) ⊆
            selectorθ '' Set.Icc thetaNeg thetaW :=
        intermediate_value_Icc
          hthetaNeg_lt.le hselectorTheta_cont.continuousOn
      -- The negative selector value at `thetaNeg` and the positive selector value at the witness
      -- reference angle force a zero before entering the legal component.
      have hzero_mem :
          (0 : ℝ) ∈ Set.Icc (selectorθ thetaNeg) (selectorθ thetaW) := by
        exact ⟨le_of_lt hselectorNeg, le_of_lt hthetaW_pos⟩
      rcases hsurj hzero_mem with ⟨sigma, hsigma_mem, hsigma_zero⟩
      exact ⟨sigma, hsigma_mem, hsigma_zero⟩
    rcases houterZero with ⟨sigma, hsigma_mem, hsigma_zero⟩
    by_cases hsigmaC₀ : sigma ∈ C₀
    · -- If the outer-window zero lands back in the legal component, the dedicated interior packet
      -- obstruction is unnecessary: the positive-branch hypothesis already rules out any zero on
      -- `C₀`.
      exact (ne_of_gt (hposall sigma hsigmaC₀)) hsigma_zero
    exact
      leftFirstCrossingContradiction_of_positiveWitnessOuterZero
        hposall hsigma_mem hsigma_zero hsigmaC₀
  have rightBoundaryDirectContradiction_ofNegativeWitnessComponent :
      (∀ η ∈ C₀, selectorθ η < 0) → False := by
    intro hnegall
    have hthetaW_mem_C₀ : thetaW ∈ C₀ := by
      -- The witness reference angle is again an interior point of the normalized component.
      rw [hC₀_eq']
      exact ⟨ha_lt_thetaW, hthetaW_lt_b⟩
    have hthetaW_neg : selectorθ thetaW < 0 := hnegall thetaW hthetaW_mem_C₀
    have houterZero :
        ∃ sigma ∈ Set.Icc thetaW thetaPos, selectorθ sigma = 0 := by
      have hsurj :
          Set.Icc (selectorθ thetaW) (selectorθ thetaPos) ⊆
            selectorθ '' Set.Icc thetaW thetaPos :=
        intermediate_value_Icc
          hthetaW_lt.le hselectorTheta_cont.continuousOn
      -- The negative selector value at the witness reference angle and the positive selector value
      -- at `thetaPos` force a zero before leaving the right cap.
      have hzero_mem :
          (0 : ℝ) ∈ Set.Icc (selectorθ thetaW) (selectorθ thetaPos) := by
        exact ⟨le_of_lt hthetaW_neg, le_of_lt hselectorPos⟩
      rcases hsurj hzero_mem with ⟨sigma, hsigma_mem, hsigma_zero⟩
      exact ⟨sigma, hsigma_mem, hsigma_zero⟩
    rcases houterZero with ⟨sigma, hsigma_mem, hsigma_zero⟩
    by_cases hsigmaC₀ : sigma ∈ C₀
    · -- If the outer-window zero lands back in the legal component, the dedicated interior packet
      -- obstruction is unnecessary: the negative-branch hypothesis already excludes zeros on
      -- `C₀`.
      exact (ne_of_lt (hnegall sigma hsigmaC₀)) hsigma_zero
    exact
      rightLastExitContradiction_of_negativeWitnessOuterZero
        hnegall hsigma_mem hsigma_zero hsigmaC₀
  rcases htrichotomy with hzero | hposall | hnegall
  · rcases hzero with ⟨η, hηC₀, hηzero⟩
    -- Consume the dedicated interior-zero obstruction.
    exact interiorLegalZeroContradiction_onWitnessComponent hηC₀ hηzero
  · -- The positive-branch closer now packages the endpoint work internally.
    exact leftBoundaryDirectContradiction_ofPositiveWitnessComponent hposall
  · -- The negative branch is handled by the symmetric direct endpoint closer.
    exact rightBoundaryDirectContradiction_ofNegativeWitnessComponent hnegall
-/

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): if `g` is essential at `0` but omits
`0` and `1` on the punctured ball, then some reciprocal branch is uniformly bounded on arbitrarily
small centered circles. -/
lemma smallCircleUniformReciprocalBranch_of_essentialSingularity_and_omitsZeroOne
    {g : ℂ → ℂ} {ε : ℝ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ T : ℝ, 1 ≤ T ∧
      ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧
        ((∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
          ∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) := by
  have hg_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0 := by
    -- Omitting `0` keeps the reciprocal branch honest on the punctured ball.
    intro z hz hz0
    exact h0 ⟨z, hz, hz0⟩
  have hone_sub_nonzero :
      ∀ z ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0 := by
    -- Omitting `1` gives the symmetric nonvanishing fact for `1 - g`.
    intro z hz hz1
    exact h1 ⟨z, hz, (sub_eq_zero.mp hz1).symm⟩
  have hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖)
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) :=
    logQuotientSelector_continuousOn hg h0 h1
  rcases exercise16ReciprocalLogThreshold_onPuncturedBall h0 h1 with
    ⟨T, hT_ge_one, _hProduct, hbranch⟩
  refine ⟨T, hT_ge_one, ?_⟩
  intro δ hδ
  rcases exercise16Hit_onSmallCircle hess hε hδ hg with
    ⟨ρ, hρpos, hρsmall, w, hw_norm, hwE⟩
  classical
  by_cases hginv : ∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ Real.exp T
  · -- If the `g⁻¹` branch is already uniformly bounded on this circle, keep it.
    exact ⟨ρ, hρpos, hρsmall, Or.inl hginv⟩
  by_cases honeSubInv : ∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T
  · -- Otherwise the shifted reciprocal branch may still be uniformly bounded.
    exact ⟨ρ, hρpos, hρsmall, Or.inr honeSubInv⟩
  push Not at hginv honeSubInv
  rcases hginv with ⟨zNeg, hzNeg_norm, hzNeg_large_exp⟩
  rcases honeSubInv with ⟨zPos, hzPos_norm, hzPos_large_exp⟩
  have hzNeg_mem : zNeg ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hzNeg_norm] using
        lt_of_lt_of_le hρsmall (min_le_right δ ε)
    · exact norm_ne_zero_iff.mp <| by simpa [hzNeg_norm] using hρpos.ne'
  have hzPos_mem : zPos ∈ Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hzPos_norm] using
        lt_of_lt_of_le hρsmall (min_le_right δ ε)
    · exact norm_ne_zero_iff.mp <| by simpa [hzPos_norm] using hρpos.ne'
  have hzNeg_large :
      T < Real.log ‖(g zNeg)⁻¹‖ := by
    have hpos : 0 < ‖(g zNeg)⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero zNeg hzNeg_mem))
    exact (Real.lt_log_iff_exp_lt hpos).2 hzNeg_large_exp
  have hzPos_large :
      T < Real.log ‖((1 - g zPos)⁻¹)‖ := by
    have hpos : 0 < ‖((1 - g zPos)⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero zPos hzPos_mem))
    exact (Real.lt_log_iff_exp_lt hpos).2 hzPos_large_exp
  -- Route correction: the mixed-circle case must descend to a strictly smaller circle carrying one
  -- uniform reciprocal branch; the old fixed-circle contradiction target was statement-false.
  rcases
      smallCircleUniformReciprocalBranch_of_mixedLargeWitnessCircle
        hess
        hT_ge_one
        hε
        hρpos
        (lt_of_lt_of_le hρsmall (min_le_right δ ε))
        hw_norm
        hwE
        hg
        hbranch
        hg_nonzero
        hone_sub_nonzero
        hselector_cont
        hzNeg_norm
        hzPos_norm
        hzNeg_large
        hzPos_large with
    ⟨ρ', hρ'pos, hρ'ltρ, hρ'branch⟩
  exact ⟨ρ', hρ'pos, lt_trans hρ'ltρ hρsmall, hρ'branch⟩

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): a punctured-ball map that omits `0`
and `1` is meromorphic at the center. -/
lemma meromorphicAt_zero_of_omitsZeroOneOnPuncturedBall
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    MeromorphicAt g 0 := by
  by_contra hnot_meromorphic
  have hisolated : HasIsolatedSingularityAt g 0 := by
    -- The punctured-ball analyticity hypothesis is already the isolated-singularity package.
    exact
      (HasIsolatedSingularityAt.iff_exists_analyticOnNhd_punctured_ball).2 ⟨ε, hε, hg⟩
  have hess : HasEssentialSingularityAt g 0 := ⟨hisolated, hnot_meromorphic⟩
  have hsmall :
      ∃ T : ℝ, 1 ≤ T ∧
        ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧
          ((∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ Real.exp T) ∨
            ∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ Real.exp T) :=
    smallCircleUniformReciprocalBranch_of_essentialSingularity_and_omitsZeroOne
      hess hε hg h0 h1
  have hg_meromorphic :
      MeromorphicAt g 0 :=
    meromorphicAt_zero_of_smallCircleUniformReciprocalBranch hε hg h0 h1 hsmall
  exact hess.not_meromorphicAt hg_meromorphic

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): at a centered essential singularity,
two omitted values on the punctured-ball image must coincide. -/
lemma omittedValuesEq_of_centeredEssentialSingularity
    {g : ℂ → ℂ} {ε : ℝ} {a b : ℂ}
    (hess : HasEssentialSingularityAt g 0)
    (hε : 0 < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (ha : a ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hb : b ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    a = b := by
  by_contra hab
  have hratio_analytic :
      AnalyticOnNhd ℂ (fun z ↦ (g z - a) / (g z - b))
        (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- Normalize the two omitted values so that they become the distinguished pair `0, 1`.
    exact normalizedOmittedRatio_analyticOnNhd hg hb
  have hratio_omits :
      0 ∉ (fun z ↦ (g z - a) / (g z - b)) '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
        1 ∉ (fun z ↦ (g z - a) / (g z - b)) '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The normalized ratio sends the two omitted values precisely to `0` and `1`.
    exact normalizedOmittedRatio_avoids_zero_one hab ha hb
  have hratio_meromorphic :
      MeromorphicAt (fun z ↦ (g z - a) / (g z - b)) 0 := by
    -- The remaining Picard endgame is exactly the centered omitted-`0,1` meromorphicity step.
    exact meromorphicAt_zero_of_omitsZeroOneOnPuncturedBall
      hε hratio_analytic hratio_omits.1 hratio_omits.2
  have hg_meromorphic : MeromorphicAt g 0 := by
    -- Undo the normalization once the ratio is known to be meromorphic at the center.
    exact meromorphicAt_of_normalizedOmittedRatio hε hab hb hratio_meromorphic
  exact hess.not_meromorphicAt hg_meromorphic

/-- Helper for Theorem III.4-extra-9 (frozen current sorry): for a punctured ball around a
general center, any two omitted image values coincide. -/
lemma complSubsingleton_of_puncturedBallImage_of_essentialSingularity
    {f : ℂ → ℂ} {o : ℂ} {ε : ℝ}
    (hess : HasEssentialSingularityAt f o)
    (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (Metric.ball o ε \ ({o} : Set ℂ))) :
    ∀ ⦃a b : ℂ⦄,
      a ∉ f '' (Metric.ball o ε \ ({o} : Set ℂ)) →
      b ∉ f '' (Metric.ball o ε \ ({o} : Set ℂ)) →
        a = b := by
  intro a b ha hb
  let g : ℂ → ℂ := fun z ↦ f (z + o)
  have hess0 : HasEssentialSingularityAt g 0 := by
    -- Translate the essential singularity from the original center to the origin.
    have htranslate :
        HasEssentialSingularityAt (translate (-o) f) 0 :=
      (essential_singularity_at_iff_translate_to_zero).mp hess
    change HasEssentialSingularityAt (fun z ↦ f (z - (-o))) 0 at htranslate
    simpa [g, sub_eq_add_neg] using htranslate
  have hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The same translation identifies the punctured-ball analyticity hypotheses.
    simpa [g] using
      (analyticOnNhd_puncturedBall_translate_iff).mp hf
  have himage :
      g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) =
        f '' (Metric.ball o ε \ ({o} : Set ℂ)) := by
    -- Translating the parameterization does not change the image set itself.
    simpa [g] using
      (image_puncturedBall_translate_eq :
        (fun z ↦ f (z + o)) '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) =
          f '' (Metric.ball o ε \ ({o} : Set ℂ)))
  have ha0 : a ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    simpa [himage] using ha
  have hb0 : b ∉ g '' (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    simpa [himage] using hb
  -- Apply the centered omitted-value contradiction after translating to the origin.
  exact omittedValuesEq_of_centeredEssentialSingularity hess0 hε hg ha0 hb0

/-- Theorem III.4-extra-9 (frozen current sorry): if `o` is an isolated essential singularity of
`f`, then on any punctured disc `0 < ‖z - o‖ < ε` where `f` is holomorphic, the image is either
all of `ℂ`, or `ℂ` with one point missing. -/
theorem punctured_ball_image_eq_univ_or_compl_singleton_of_essential_singularity
    {f : ℂ → ℂ} {o : ℂ} {ε : ℝ}
    (hess : HasEssentialSingularityAt f o)
    (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (Metric.ball o ε \ ({o} : Set ℂ))) :
    f '' (Metric.ball o ε \ ({o} : Set ℂ)) = Set.univ ∨
      ∃ a : ℂ, f '' (Metric.ball o ε \ ({o} : Set ℂ)) = ({a} : Set ℂ)ᶜ := by
  -- Finish the Picard dichotomy from the already proved omitted-value uniqueness criterion.
  exact
    puncturedBallImage_eq_univ_or_compl_singleton_of_compl_subsingleton
      (complSubsingleton_of_puncturedBallImage_of_essentialSingularity hess hε hf)
