import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».StripBoundaryLimits
import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».SchwarzReflection

open Set
open scoped UpperHalfPlane ComplexOrder

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: away from the positive vertices `1` and `1 / k`,
the remaining source work is the positive-side ambient boundary-limit package. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_pos_offVertices
    (k : Exercise8Modulus) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1)
    (hxk : x ≠ 1 / (k : ℝ)) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k x)) := by
  let f : ℂ → ℂ := fun w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
  by_cases hxlt1 : x < 1
  · let innerStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hx0, hxlt1.le⟩
    have hstrip :
        Filter.Tendsto f (nhdsWithin (x : ℂ) innerStrip)
          (nhds (exercise8_boundary_trace k x)) := by
      -- Inside `(0, 1)`, the boundary trace is the bottom-edge branch owner.
      have hEq :
          exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x := by
        simpa [exercise8_boundary_inner_branch] using
          exercise8_boundary_value_eq_inner (k := k) hxIcc
      simpa [f, hEq] using exercise8_abel_integral_tendsto_inner_strip k hxIcc
    have hlocal : innerStrip ∈ nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet := by
      let r : ℝ := min (x / 2) ((1 - x) / 2)
      have hr_pos : 0 < r := by
        dsimp [r]
        refine lt_min ?_ ?_
        · linarith
        · linarith
      refine Filter.mem_of_superset
        (inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hr_pos)) ?_
      intro w hw
      rcases hw with ⟨hwU, hwball⟩
      have hwim : 0 < w.im := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using hwU
      have hrew :
          |w.re - x| < r := by
        have hre_le : |w.re - x| ≤ dist w (x : ℂ) := by
          simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (Complex.abs_re_le_norm (w - x))
        exact lt_of_le_of_lt hre_le hwball
      have hr_left : r ≤ x / 2 := by
        dsimp [r]
        exact min_le_left _ _
      have hr_right : r ≤ (1 - x) / 2 := by
        dsimp [r]
        exact min_le_right _ _
      have hnonneg : 0 ≤ w.re := by
        have hlt : x - r < w.re := by
          linarith [abs_lt.mp hrew |>.1]
        linarith
      have hleone : w.re ≤ 1 := by
        have hlt : w.re < x + r := by
          linarith [abs_lt.mp hrew |>.2]
        linarith
      exact ⟨hwim, hnonneg, hleone⟩
    have hle :
        nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet ≤ nhdsWithin (x : ℂ) innerStrip := by
      rw [nhdsWithin, nhdsWithin]
      refine le_inf inf_le_left ?_
      exact Filter.le_principal_iff.mpr hlocal
    exact hstrip.mono_left hle
  · by_cases hxtop : 1 / (k : ℝ) ≤ x
    · let topStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}
      have hstrip :
          Filter.Tendsto f (nhdsWithin (x : ℂ) topStrip)
            (nhds (exercise8_boundary_trace k x)) := by
        -- On the top branch, the boundary trace is the reciprocal-substitution owner.
        have hEq :
            exercise8_boundary_trace k x = exercise8_boundary_top_branch k x := by
          simpa [exercise8_boundary_top_branch] using
            exercise8_boundary_value_eq_top (k := k) hxtop
        simpa [f, hEq, topStrip] using exercise8_abel_integral_tendsto_top_strip k hxtop
      have hlocal : topStrip ∈ nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet := by
        let r : ℝ := (x - 1 / (k : ℝ)) / 2
        have hr_pos : 0 < r := by
          dsimp [r]
          have hxgt : 1 / (k : ℝ) < x := lt_of_le_of_ne hxtop (Ne.symm hxk)
          linarith
        refine Filter.mem_of_superset
          (inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hr_pos)) ?_
        intro w hw
        rcases hw with ⟨hwU, hwball⟩
        have hwim : 0 < w.im := by
          simpa [UpperHalfPlane.upperHalfPlaneSet] using hwU
        have hrew :
            |w.re - x| < r := by
          have hre_le : |w.re - x| ≤ dist w (x : ℂ) := by
            simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (Complex.abs_re_le_norm (w - x))
          exact lt_of_le_of_lt hre_le hwball
        have hlow : 1 / (k : ℝ) ≤ w.re := by
          have hlt : x - r < w.re := by
            linarith [abs_lt.mp hrew |>.1]
          dsimp [r] at hlt
          linarith
        exact ⟨hwim, hlow⟩
      have hle :
          nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet ≤ nhdsWithin (x : ℂ) topStrip := by
        rw [nhdsWithin, nhdsWithin]
        refine le_inf inf_le_left ?_
        exact Filter.le_principal_iff.mpr hlocal
      exact hstrip.mono_left hle
    · let rightStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}
      have hxge1 : 1 ≤ x := not_lt.mp hxlt1
      have hxgt1 : 1 < x := lt_of_le_of_ne hxge1 (Ne.symm hx1)
      have hxltinv : x < 1 / (k : ℝ) := not_le.mp hxtop
      have hxIcc : x ∈ Icc (1 : ℝ) (1 / (k : ℝ)) := ⟨hxge1, hxltinv.le⟩
      have hstrip :
          Filter.Tendsto f (nhdsWithin (x : ℂ) rightStrip)
            (nhds (exercise8_boundary_trace k x)) := by
        -- Between `1` and `1 / k`, the boundary trace is the right-edge owner.
        have hEq :
            exercise8_boundary_trace k x = exercise8_boundary_right_branch k x := by
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) hxge1 hxltinv.le
        simpa [f, hEq, rightStrip] using exercise8_abel_integral_tendsto_right_strip k hxIcc
      have hlocal : rightStrip ∈ nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet := by
        let r : ℝ := min ((x - 1) / 2) (((1 / (k : ℝ)) - x) / 2)
        have hr_pos : 0 < r := by
          dsimp [r]
          refine lt_min ?_ ?_
          · linarith
          · linarith
        refine Filter.mem_of_superset
          (inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hr_pos)) ?_
        intro w hw
        rcases hw with ⟨hwU, hwball⟩
        have hwim : 0 < w.im := by
          simpa [UpperHalfPlane.upperHalfPlaneSet] using hwU
        have hrew :
            |w.re - x| < r := by
          have hre_le : |w.re - x| ≤ dist w (x : ℂ) := by
            simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (Complex.abs_re_le_norm (w - x))
          exact lt_of_le_of_lt hre_le hwball
        have hr_left : r ≤ (x - 1) / 2 := by
          dsimp [r]
          exact min_le_left _ _
        have hr_right : r ≤ ((1 / (k : ℝ)) - x) / 2 := by
          dsimp [r]
          exact min_le_right _ _
        have hone : 1 ≤ w.re := by
          have hlt : x - r < w.re := by
            linarith [abs_lt.mp hrew |>.1]
          linarith
        have hleinv : w.re ≤ 1 / (k : ℝ) := by
          have hlt : w.re < x + r := by
            linarith [abs_lt.mp hrew |>.2]
          linarith
        exact ⟨hwim, hone, hleinv⟩
      have hle :
          nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet ≤ nhdsWithin (x : ℂ) rightStrip := by
        rw [nhdsWithin, nhdsWithin]
        refine le_inf inf_le_left ?_
        exact Filter.le_principal_iff.mpr hlocal
      exact hstrip.mono_left hle

/-- Helper for Cartan section26 0018_Exercise_8: the positive vertex `1` needs its own endpoint
vertical-limit argument because the nonvertex boundedness package does not apply there. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_one
    (k : Exercise8Modulus) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin ((1 : ℝ) : ℂ) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k 1)) := by
  let f : ℂ → ℂ := fun w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
  let innerStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
  let rightStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using
      (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hleft :
      Filter.Tendsto f (nhdsWithin ((1 : ℝ) : ℂ) innerStrip)
        (nhds (exercise8_boundary_trace k 1)) := by
    -- The left branch hits the common vertex value `K`.
    have hEq :
        exercise8_boundary_trace k 1 = exercise8_boundary_inner_branch k 1 := by
      simpa [exercise8_boundary_inner_branch] using
        exercise8_boundary_value_eq_inner (k := k) (x := 1) ⟨by norm_num, by norm_num⟩
    simpa [f, hEq] using
      exercise8_abel_integral_tendsto_inner_strip k (x := 1) ⟨by norm_num, by norm_num⟩
  have hright :
      Filter.Tendsto f (nhdsWithin ((1 : ℝ) : ℂ) rightStrip)
        (nhds (exercise8_boundary_trace k 1)) := by
    -- The right branch reaches the same vertex value at `x = 1`.
    have hEq :
        exercise8_boundary_trace k 1 = exercise8_boundary_right_branch k 1 := by
      simpa [exercise8_boundary_right_branch] using
        exercise8_boundary_value_eq_right (k := k) (x := 1) (by norm_num) hk_inv_gt_one.le
    simpa [f, hEq, rightStrip] using
      exercise8_abel_integral_tendsto_right_strip k (x := 1) ⟨by norm_num, hk_inv_gt_one.le⟩
  rw [Metric.tendsto_nhdsWithin_nhds] at hleft hright ⊢
  intro ε hε
  rcases hleft ε hε with ⟨δl, hδl, hleftε⟩
  rcases hright ε hε with ⟨δr, hδr, hrightε⟩
  let δ : ℝ := min δl (min δr (min (1 / 2 : ℝ) (((1 / (k : ℝ)) - 1) / 2)))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min hδl ?_
    refine lt_min hδr ?_
    refine lt_min (by norm_num) ?_
    linarith
  refine ⟨δ, hδ_pos, ?_⟩
  intro w hwU hdist
  have hwim : 0 < w.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hwU
  have hrew :
      |w.re - 1| < δ := by
    have hre_le : |w.re - 1| ≤ dist w (((1 : ℝ) : ℂ)) := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (Complex.abs_re_le_norm (w - 1))
    exact lt_of_le_of_lt hre_le hdist
  by_cases hre : w.re ≤ 1
  · have hnonneg : 0 ≤ w.re := by
      have hlt : 1 - δ < w.re := by
        linarith [abs_lt.mp hrew |>.1]
      have hδhalf : δ ≤ (1 / 2 : ℝ) := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    have hδl' : dist w (((1 : ℝ) : ℂ)) < δl := by
      exact lt_of_lt_of_le hdist (by
        dsimp [δ]
        exact min_le_left _ _)
    exact hleftε (x := w) (show w ∈ innerStrip from ⟨hwim, hnonneg, hre⟩) hδl'
  · have hone : 1 ≤ w.re := (lt_of_not_ge hre).le
    have hrightSide : 1 < w.re := lt_of_not_ge hre
    have hleinv : w.re ≤ 1 / (k : ℝ) := by
      have hlt : w.re < 1 + δ := by
        linarith [abs_lt.mp hrew |>.2]
      have hδtop : δ ≤ ((1 / (k : ℝ)) - 1) / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
    have hδr' : dist w (((1 : ℝ) : ℂ)) < δr := by
      exact lt_of_lt_of_le hdist (by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _))
    exact hrightε (x := w) (show w ∈ rightStrip from ⟨hwim, hrightSide.le, hleinv⟩) hδr'

/-- Helper for Cartan section26 0018_Exercise_8: the positive top vertex `1 / k` is a separate
endpoint limit for the Abel integral. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_inv_k
    (k : Exercise8Modulus) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (((1 / (k : ℝ)) : ℝ) : ℂ) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k (1 / (k : ℝ)))) := by
  let f : ℂ → ℂ := fun w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
  let rightStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)}
  let topStrip : Set ℂ := {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re}
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using
      (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hright :
      Filter.Tendsto f (nhdsWithin (((1 / (k : ℝ)) : ℝ) : ℂ) rightStrip)
        (nhds (exercise8_boundary_trace k (1 / (k : ℝ)))) := by
    -- The right-edge owner reaches the same vertex `K + i K'` at `1 / k`.
    have hEq :
        exercise8_boundary_trace k (1 / (k : ℝ)) =
          exercise8_boundary_right_branch k (1 / (k : ℝ)) := by
      simpa [exercise8_boundary_right_branch] using
        exercise8_boundary_value_eq_right (k := k) (x := 1 / (k : ℝ))
          hk_inv_gt_one.le le_rfl
    have h := exercise8_abel_integral_tendsto_right_strip k (x := 1 / (k : ℝ))
      ⟨hk_inv_gt_one.le, le_rfl⟩
    rw [hEq]
    simpa [f, rightStrip] using h
  have htop :
      Filter.Tendsto f (nhdsWithin (((1 / (k : ℝ)) : ℝ) : ℂ) topStrip)
        (nhds (exercise8_boundary_trace k (1 / (k : ℝ)))) := by
    -- The top-edge owner has the same common endpoint value.
    have hEq :
        exercise8_boundary_trace k (1 / (k : ℝ)) =
          exercise8_boundary_top_branch k (1 / (k : ℝ)) := by
      simpa [exercise8_boundary_top_branch] using
        exercise8_boundary_value_eq_top (k := k) (x := 1 / (k : ℝ)) le_rfl
    have h := exercise8_abel_integral_tendsto_top_strip k (x := 1 / (k : ℝ)) le_rfl
    rw [hEq]
    simpa [f, topStrip] using h
  rw [Metric.tendsto_nhdsWithin_nhds] at hright htop ⊢
  intro ε hε
  rcases hright ε hε with ⟨δr, hδr, hrightε⟩
  rcases htop ε hε with ⟨δt, hδt, htopε⟩
  let δ : ℝ := min δr (min δt (((1 / (k : ℝ)) - 1) / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min hδr ?_
    refine lt_min hδt ?_
    linarith [hk_inv_gt_one]
  refine ⟨δ, hδ_pos, ?_⟩
  intro w hwU hdist
  have hwim : 0 < w.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hwU
  have hrew :
      |w.re - 1 / (k : ℝ)| < δ := by
    have hre_le : |w.re - 1 / (k : ℝ)| ≤ dist w ((((1 / (k : ℝ)) : ℝ) : ℂ)) := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (Complex.abs_re_le_norm (w - (1 / (k : ℝ))))
    exact lt_of_le_of_lt hre_le hdist
  by_cases hre : w.re ≤ 1 / (k : ℝ)
  · have hone : 1 ≤ w.re := by
      have hlt : (1 / (k : ℝ)) - δ < w.re := by
        linarith [abs_lt.mp hrew |>.1]
      have hδbound : δ ≤ ((1 / (k : ℝ)) - 1) / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    have hδr' : dist w ((((1 / (k : ℝ)) : ℝ) : ℂ)) < δr := by
      exact lt_of_lt_of_le hdist (by
        dsimp [δ]
        exact min_le_left _ _)
    exact hrightε (x := w) (show w ∈ rightStrip from ⟨hwim, hone, hre⟩) hδr'
  · have htopRe : 1 / (k : ℝ) ≤ w.re := (lt_of_not_ge hre).le
    have hδt' : dist w ((((1 / (k : ℝ)) : ℝ) : ℂ)) < δt := by
      exact lt_of_lt_of_le hdist (by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _))
    exact htopε (x := w) (show w ∈ topStrip from ⟨hwim, htopRe⟩) hδt'

/-- Helper for Cartan section26 0018_Exercise_8: once the positive-side theorem is isolated, the
negative nonvertex limit should be recovered by one Schwarz-reflection argument. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_neg_offVertices
    (k : Exercise8Modulus) {x : ℝ} (hx : x < 0) (hx1 : x ≠ -1)
    (hxk : x ≠ -(1 / (k : ℝ))) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k x)) := by
  let y : ℝ := -x
  have hy : 0 < y := by
    -- Reflecting a negative real point lands on the positive side where the branch theorem is
    -- already available.
    dsimp [y]
    linarith
  have hy1 : y ≠ 1 := by
    -- The reflected point avoids the positive vertex `1` because `x ≠ -1`.
    intro hy1
    apply hx1
    dsimp [y] at hy1
    linarith
  have hyk : y ≠ 1 / (k : ℝ) := by
    -- The reflected point also avoids the positive vertex `1 / k`.
    intro hyk
    apply hxk
    dsimp [y] at hyk
    linarith
  -- Route correction: transport the positive nonvertex limit through the single reflection bridge.
  simpa [y] using
    exercise8_abel_integral_tendsto_boundary_trace_reflected k y
      (exercise8_abel_integral_tendsto_boundary_trace_pos_offVertices k hy hy1 hyk)

/-- Helper for Cartan section26 0018_Exercise_8: the left vertex `-1` is the reflected endpoint
counterpart of the positive bottom vertex. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_neg_one
    (k : Exercise8Modulus) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (((-1 : ℝ) : ℂ)) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k (-1))) := by
  -- Route correction: the left endpoint is just the Schwarz reflection of the solved positive
  -- endpoint `1`.
  simpa using
    exercise8_abel_integral_tendsto_boundary_trace_reflected k 1
      (exercise8_abel_integral_tendsto_boundary_trace_one k)

/-- Helper for Cartan section26 0018_Exercise_8: the left-top vertex `-1 / k` is the reflected
counterpart of the top positive vertex. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_neg_inv_k
    (k : Exercise8Modulus) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (((-(1 / (k : ℝ)) : ℝ) : ℂ)) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k (-(1 / (k : ℝ))))) := by
  -- Route correction: the left-top endpoint is the reflected image of the solved positive
  -- endpoint `1 / k`.
  simpa using
    exercise8_abel_integral_tendsto_boundary_trace_reflected k (1 / (k : ℝ))
      (exercise8_abel_integral_tendsto_boundary_trace_inv_k k)

/-- Helper for Cartan section26 0018_Exercise_8: after isolating the positive branches and the
reflected endpoint cases, the remaining ambient nonzero real limit is only a sign/vertex split. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_nonzero_real
    (k : Exercise8Modulus) {x : ℝ} (hx : x ≠ 0) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (x : ℂ) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k x)) := by
  by_cases hxpos : 0 < x
  · by_cases hx1 : x = 1
    · -- The positive bottom vertex is isolated as its own endpoint theorem.
      subst hx1
      simpa using exercise8_abel_integral_tendsto_boundary_trace_one k
    · by_cases hxk : x = 1 / (k : ℝ)
      · -- The positive top vertex is the second exceptional endpoint.
        subst hxk
        simpa using exercise8_abel_integral_tendsto_boundary_trace_inv_k k
      · -- Away from the positive vertices, the remaining source work is the positive branch
        -- package isolated above.
        exact exercise8_abel_integral_tendsto_boundary_trace_pos_offVertices k hxpos hx1 hxk
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    by_cases hx1 : x = -1
    · -- The negative bottom vertex is handled by its reflected endpoint theorem.
      subst hx1
      simpa using exercise8_abel_integral_tendsto_boundary_trace_neg_one k
    · by_cases hxk : x = -(1 / (k : ℝ))
      · -- The negative top vertex is the reflected counterpart of `1 / k`.
        subst hxk
        simpa using exercise8_abel_integral_tendsto_boundary_trace_neg_inv_k k
      · -- The remaining negative case should come from the positive theorem by Schwarz
        -- reflection.
        exact exercise8_abel_integral_tendsto_boundary_trace_neg_offVertices k hxneg hx1 hxk

/-- Helper for Cartan section26 0018_Exercise_8: once the ambient nonzero real limit is known, the
canonical closed-half-plane owner inherits the same from-above limit on the strict upper slice. -/
lemma exercise8_closed_extension_tendsto_boundary_trace_from_above_nonzero
    (k : Exercise8Modulus) (z : ClosedUpperHalfPlane) (hz : ((z : ℂ)).im = 0)
    (hzre : ((z : ℂ)).re ≠ 0) :
    Filter.Tendsto (exercise8_closed_extension k)
      (nhdsWithin z {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im})
      (nhds (exercise8_boundary_trace k ((z : ℂ).re))) := by
  let zre : ClosedUpperHalfPlane := ⟨((((z : ℂ)).re : ℝ) : ℂ), by simp⟩
  have hz_eq : z = zre := by
    -- A closed-upper-half-plane boundary point is determined by its real part.
    ext
    apply Complex.ext <;> simp [zre, hz]
  -- The ambient nonzero theorem already has the correct value; only the upper-slice transport
  -- remains.
  rw [hz_eq]
  simpa using
    exercise8_closed_extension_tendsto_from_ambient_upper_slice k zre
      (exercise8_abel_integral_tendsto_boundary_trace_nonzero_real
        k (x := ((zre : ℂ)).re) hzre)

/-- Helper for Cartan section26 0018_Exercise_8: the remaining boundary input is the from-above
limit of the canonical owner to the repaired boundary trace. -/
lemma exercise8_closed_extension_tendsto_boundary_trace_from_above
    (k : Exercise8Modulus) (z : ClosedUpperHalfPlane) (hz : ((z : ℂ)).im = 0) :
    Filter.Tendsto (exercise8_closed_extension k)
      (nhdsWithin z {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im})
      (nhds (exercise8_boundary_trace k ((z : ℂ).re))) := by
  by_cases hzre : ((z : ℂ)).re = 0
  · have hz0 : z = (⟨(0 : ℂ), by simp⟩ : ClosedUpperHalfPlane) := by
      -- A boundary point with both real and imaginary parts equal to `0` is exactly the origin.
      ext
      apply Complex.ext <;> simp [hz, hzre]
    -- The origin case is already solved by the dedicated near-zero Abel-integral estimate.
    simpa [hz0, hzre] using exercise8_closed_extension_tendsto_boundary_trace_from_above_zero k
  · -- Route correction: after isolating the origin, the boundary theorem is now pure transport of
    -- the remaining ambient nonzero real limit.
    exact exercise8_closed_extension_tendsto_boundary_trace_from_above_nonzero k z hz hzre

/-- Helper for Cartan section26 0018_Exercise_8: continuity of the Abel integral on the strict
upper half-plane is the remaining analytic input for the interior extension proof. -/
lemma exercise8_abel_integral_continuousAt
    (k : Exercise8Modulus) (z : UpperHalfPlane) :
    ContinuousAt (exercise8_abel_integral k) z := by
  let F : UpperHalfPlane → ℝ → ℂ :=
    fun w t ↦ exercise8_integrand k ((t : ℂ) * (w : ℂ)) * (w : ℂ)
  have hformula :
      exercise8_abel_integral k =
        fun w : UpperHalfPlane ↦ ∫ t in (0 : ℝ)..1, F w t := by
    -- Rewrite the segment integral in the source ray coordinates `t ↦ t z`.
    funext w
    rw [exercise8_abel_integral_def, curveIntegral_segment]
    simp [F, AffineMap.lineMap_apply, mul_comm]
  rcases exercise8_integrand_bounded_near_zero k with ⟨R, hR_pos, hR_bound⟩
  let δ : ℝ := min 1 (((z : ℂ).im) / 2)
  let B : ℝ := ‖(z : ℂ)‖ + 1
  let r : ℝ := min (1 / 2 : ℝ) (R / (2 * B))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_half_im : δ ≤ ((z : ℂ).im) / 2 := by
    dsimp [δ]
    exact min_le_right _ _
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hr_pos : 0 < r := by
    dsimp [r]
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hr_le_one : r ≤ 1 := by
    calc
      r ≤ (1 / 2 : ℝ) := by
        dsimp [r]
        exact min_le_left _ _
      _ ≤ 1 := by norm_num
  have hrB_lt_R : r * B < R := by
    have hr_le : r ≤ R / (2 * B) := by
      dsimp [r]
      exact min_le_right _ _
    have hmul :
        r * B ≤ (R / (2 * B)) * B := by
      exact mul_le_mul_of_nonneg_right hr_le hB_pos.le
    have hcalc : (R / (2 * B)) * B = R / 2 := by
      field_simp [hB_pos.ne']
    calc
      r * B ≤ (R / (2 * B)) * B := hmul
      _ = R / 2 := hcalc
      _ < R := by linarith
  have hclosedBall_im_pos :
      ∀ {u : ℂ}, u ∈ Metric.closedBall (z : ℂ) δ → 0 < u.im := by
    intro u hu
    have hu_dist : dist u (z : ℂ) ≤ δ := by
      simpa [Metric.mem_closedBall] using hu
    have him_le : |u.im - (z : ℂ).im| ≤ dist u (z : ℂ) := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (Complex.abs_im_le_norm (u - (z : ℂ)))
    have hclose : |u.im - (z : ℂ).im| ≤ (z : ℂ).im / 2 := by
      exact le_trans him_le (le_trans hu_dist hδ_le_half_im)
    have hsplit := abs_le.mp hclose
    linarith [z.im_pos]
  let tailSet : Set (ℝ × ℂ) := Set.Icc r 1 ×ˢ Metric.closedBall (z : ℂ) δ
  let tailMap : ℝ × ℂ → ℂ :=
    fun p ↦ exercise8_integrand k (((p.1 : ℂ) * p.2)) * p.2
  have htailSet_compact : IsCompact tailSet := by
    -- Away from `t = 0`, the parameter rectangle is compact in `ℝ × ℂ`.
    refine isCompact_Icc.prod (isCompact_closedBall _ _)
  have htailMap_cont : ContinuousOn tailMap tailSet := by
    have hmul : Continuous fun p : ℝ × ℂ ↦ ((p.1 : ℂ) * p.2) := by
      exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
    have hcomp :
        ContinuousOn (fun p : ℝ × ℂ ↦ exercise8_integrand k (((p.1 : ℂ) * p.2))) tailSet := by
      refine (exercise8_integrand_continuousOn_upper k).comp hmul.continuousOn ?_
      intro p hp
      rcases hp with ⟨hp_t, hp_u⟩
      have hp_im : 0 < p.2.im := hclosedBall_im_pos hp_u
      have hp_t_pos : 0 < p.1 := lt_of_lt_of_le hr_pos hp_t.1
      simpa [Complex.mul_im, mul_comm] using mul_pos hp_t_pos hp_im
    simpa [tailMap] using hcomp.mul continuous_snd.continuousOn
  obtain ⟨Ctail, hCtail⟩ := htailSet_compact.exists_bound_of_continuousOn htailMap_cont
  have hintegrand_upper_cont :
      Continuous (fun u : UpperHalfPlane ↦ exercise8_integrand k (u : ℂ)) := by
    -- Restrict the ambient upper-half-plane continuity to the subtype owner once and for all.
    exact (exercise8_integrand_continuousOn_upper k).comp_continuous
      UpperHalfPlane.continuous_coe fun u ↦ u.2
  have hF_meas :
      ∀ᶠ w in nhds z, MeasureTheory.AEStronglyMeasurable (F w)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    -- For each upper-half-plane point, the ray integrand is continuous on `(0,1]`.
    refine Filter.Eventually.of_forall ?_
    intro w
    have hcont :
        ContinuousOn (F w) (Set.Ioc (0 : ℝ) 1) := by
      have hmul : Continuous fun t : ℝ ↦ ((t : ℂ) * (w : ℂ)) := by
        exact Complex.continuous_ofReal.mul continuous_const
      have hcomp :
          ContinuousOn (fun t : ℝ ↦ exercise8_integrand k (((t : ℂ) * (w : ℂ)))) (Set.Ioc (0 : ℝ) 1) := by
        refine (exercise8_integrand_continuousOn_upper k).comp hmul.continuousOn ?_
        intro t ht
        exact exercise8_im_pos_mul_of_upper (z := w) ht.1
      simpa [F] using hcomp.mul continuous_const.continuousOn
    simpa [Set.uIoc_of_le zero_le_one] using
      hcont.aestronglyMeasurable measurableSet_Ioc
  have h_bound :
      ∀ᶠ w in nhds z, ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 → ‖F w t‖ ≤ max (2 * B) Ctail := by
    -- Use the near-zero bound on `(0,r)` and the compact tail bound on `[r,1]`.
    have hEuclidNhds :
        {w : UpperHalfPlane | dist (w : ℂ) (z : ℂ) < δ} ∈ nhds z := by
      exact UpperHalfPlane.continuous_coe.continuousAt.preimage_mem_nhds <|
        by simpa [Metric.mem_ball] using (Metric.ball_mem_nhds (z : ℂ) hδ_pos)
    refine Filter.mem_of_superset hEuclidNhds ?_
    intro w hw
    have hw_dist : dist (w : ℂ) (z : ℂ) < δ := by
      exact hw
    have hw_closedBall : (w : ℂ) ∈ Metric.closedBall (z : ℂ) δ := by
      simpa [Metric.mem_closedBall] using le_of_lt hw_dist
    have hw_im : 0 < (w : ℂ).im := hclosedBall_im_pos hw_closedBall
    have hw_norm : ‖(w : ℂ)‖ < B := by
      calc
        ‖(w : ℂ)‖ = ‖((w : ℂ) - (z : ℂ)) + (z : ℂ)‖ := by ring_nf
        _ ≤ ‖(w : ℂ) - (z : ℂ)‖ + ‖(z : ℂ)‖ := norm_add_le _ _
        _ < δ + ‖(z : ℂ)‖ := by
          gcongr
          simpa [dist_eq_norm] using hw_dist
        _ ≤ 1 + ‖(z : ℂ)‖ := by gcongr
        _ = B := by
          dsimp [B]
          ring
    show ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (0 : ℝ) 1 → ‖F w t‖ ≤ max (2 * B) Ctail
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rcases (Set.mem_uIoc.mp ht) with htu | htu
    · by_cases htr : t < r
      · have ht_nonneg : 0 ≤ t := le_of_lt htu.1
        have htw_norm : ‖((t : ℂ) * (w : ℂ))‖ < R := by
          calc
            ‖((t : ℂ) * (w : ℂ))‖ = |t| * ‖(w : ℂ)‖ := by simp
            _ = t * ‖(w : ℂ)‖ := by rw [abs_of_nonneg ht_nonneg]
            _ ≤ t * B := by nlinarith [hw_norm]
            _ ≤ r * B := by nlinarith [htr, hB_pos]
            _ < R := hrB_lt_R
        have htw_im : 0 < (((t : ℂ) * (w : ℂ)).im) := by
          simpa [Complex.mul_im, mul_comm] using mul_pos htu.1 hw_im
        have hsmall := hR_bound (((t : ℂ) * (w : ℂ))) htw_norm htw_im
        calc
          ‖F w t‖ = ‖exercise8_integrand k (((t : ℂ) * (w : ℂ)))‖ * ‖(w : ℂ)‖ := by
            simp [F]
          _ ≤ 2 * ‖(w : ℂ)‖ := by
            gcongr
          _ ≤ 2 * B := by
            gcongr
          _ ≤ max (2 * B) Ctail := le_max_left _ _
      · have ht_mem : t ∈ Set.Icc r 1 := ⟨le_of_not_gt htr, htu.2⟩
        have hp : (t, (w : ℂ)) ∈ tailSet := by
          exact ⟨ht_mem, hw_closedBall⟩
        calc
          ‖F w t‖ = ‖tailMap (t, (w : ℂ))‖ := by rfl
          _ ≤ Ctail := hCtail _ hp
          _ ≤ max (2 * B) Ctail := le_max_right _ _
    · exfalso
      linarith
  have h_cont :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 → ContinuousAt (fun w : UpperHalfPlane ↦ F w t) z := by
    -- For every `t > 0`, scaling by `t` stays inside `Im z > 0`, where the integrand is
    -- continuous.
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rcases (Set.mem_uIoc.mp ht) with htu | htu
    · have hscaled_im : 0 < (((t : ℂ) * (z : ℂ)).im) := by
        simpa [Complex.mul_im, mul_comm] using mul_pos htu.1 z.im_pos
      let scaleBase : UpperHalfPlane → ℂ := fun w ↦ ((t : ℂ) * (w : ℂ))
      let scalePos : ∀ w : UpperHalfPlane, 0 < (scaleBase w).im :=
        fun w ↦ by
          simpa [scaleBase] using exercise8_im_pos_mul_of_upper (z := w) htu.1
      have hscaleBase : Continuous scaleBase := by
        simpa [scaleBase] using (continuous_const.mul UpperHalfPlane.continuous_coe)
      have hofScale :
          (fun w : UpperHalfPlane ↦
            (((UpperHalfPlane.ofComplex (scaleBase w) : UpperHalfPlane) : ℂ))) = scaleBase := by
        funext w
        simpa [scaleBase, scalePos] using
          congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
            (UpperHalfPlane.ofComplex_apply (⟨scaleBase w, scalePos w⟩ : UpperHalfPlane))
      have hmulAt : ContinuousAt (fun w : UpperHalfPlane ↦ ((t : ℂ) * (w : ℂ))) z := by
        simpa using (continuousAt_const.mul UpperHalfPlane.continuous_coe.continuousAt)
      have hofComplexAt :
          ContinuousAt (fun u : ℂ ↦ UpperHalfPlane.ofComplex u) (scaleBase z) := by
        simpa [scaleBase] using
          (UpperHalfPlane.contMDiffAt_ofComplex (n := (0 : WithTop ℕ∞)) hscaled_im).continuousAt
      have hscaleUHP :
          ContinuousAt (fun w : UpperHalfPlane ↦ UpperHalfPlane.ofComplex (scaleBase w)) z := by
        exact hofComplexAt.comp hmulAt
      have hcomp :
          ContinuousAt
            (fun w : UpperHalfPlane ↦
              exercise8_integrand k
                (((UpperHalfPlane.ofComplex (scaleBase w) : UpperHalfPlane) : ℂ))) z := by
        exact hintegrand_upper_cont.continuousAt.comp hscaleUHP
      have hfunEq :
          (fun w : UpperHalfPlane ↦
            exercise8_integrand k
              (((UpperHalfPlane.ofComplex (scaleBase w) : UpperHalfPlane) : ℂ))) =
            fun w : UpperHalfPlane ↦ exercise8_integrand k (scaleBase w) := by
        funext w
        rw [show (((UpperHalfPlane.ofComplex (scaleBase w) : UpperHalfPlane) : ℂ)) = scaleBase w by
          simpa [scaleBase, scalePos] using
            congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
              (UpperHalfPlane.ofComplex_apply (⟨scaleBase w, scalePos w⟩ : UpperHalfPlane))]
      have hcomp' : ContinuousAt (fun w : UpperHalfPlane ↦ exercise8_integrand k (scaleBase w)) z := by
        simpa [hfunEq] using hcomp
      simpa [F, scaleBase] using hcomp'.mul UpperHalfPlane.continuous_coe.continuousAt
    · exfalso
      linarith
  have hdom :
      ContinuousAt (fun w : UpperHalfPlane ↦ ∫ t in (0 : ℝ)..1, F w t) z := by
    -- Dominated convergence handles the varying ray integrand on the fixed interval `(0,1]`.
    refine intervalIntegral.continuousAt_of_dominated_interval hF_meas h_bound ?_ h_cont
    simpa using
      (intervalIntegrable_const (a := (0 : ℝ)) (b := (1 : ℝ)) (c := max (2 * B) Ctail))
  simpa [hformula] using hdom

/-- Helper for Cartan section26 0018_Exercise_8: once the Abel integral is continuous in the
interior, the canonical closed-half-plane owner inherits continuity away from the boundary. -/
lemma exercise8_closed_extension_continuousAt_interior_of_abel_integral_continuousAt
    (k : Exercise8Modulus) {z : ClosedUpperHalfPlane} (hz : ((z : ℂ)).im ≠ 0)
    (hcont : ContinuousAt (exercise8_abel_integral k)
      ⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩) :
    ContinuousAt (exercise8_closed_extension k) z := by
  let g : ClosedUpperHalfPlane → ℂ :=
    fun w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex (w : ℂ))
  have hzpos : 0 < ((z : ℂ)).im := exercise8_im_pos_of_closed_nonreal hz
  have hz_ofComplex :
      ((UpperHalfPlane.ofComplex (z : ℂ) : UpperHalfPlane)) =
        ⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩ := by
    -- On points with positive imaginary part, `ofComplex` recovers the canonical upper-half-plane
    -- point with the same underlying complex number.
    simpa using (UpperHalfPlane.ofComplex_apply
      (⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩ : UpperHalfPlane))
  have hcont' : ContinuousAt (exercise8_abel_integral k) (UpperHalfPlane.ofComplex (z : ℂ)) := by
    simpa [hz_ofComplex] using hcont
  have hcomp :
      ContinuousAt (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        (z : ℂ) := by
    -- The ambient map `w ↦ ofComplex w` is continuous at interior points of the upper half-plane.
    exact hcont'.comp (UpperHalfPlane.contMDiffAt_ofComplex
      (n := (0 : WithTop ℕ∞)) hzpos).continuousAt
  have hg : ContinuousAt g z := by
    -- Restrict the ambient continuity statement to the closed-half-plane subtype.
    dsimp [g]
    exact hcomp.comp continuous_subtype_val.continuousAt
  have hEventuallyPos : {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im} ∈ nhds z := by
    -- Positivity of the imaginary part is an open condition, so it persists near `z`.
    exact
      (Complex.continuous_im.comp continuous_subtype_val).continuousAt.preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_Ioi hzpos)
  have heq : g =ᶠ[nhds z] exercise8_closed_extension k := by
    filter_upwards [hEventuallyPos] with w hw
    have hwne : ((w : ℂ)).im ≠ 0 := ne_of_gt hw
    have h_ofComplex :
        ((UpperHalfPlane.ofComplex (w : ℂ) : UpperHalfPlane)) =
          ⟨(w : ℂ), exercise8_im_pos_of_closed_nonreal hwne⟩ := by
      -- The same identification holds for nearby interior points.
      simpa using (UpperHalfPlane.ofComplex_apply
        (⟨(w : ℂ), exercise8_im_pos_of_closed_nonreal hwne⟩ : UpperHalfPlane))
    -- Off the real axis, the canonical owner is the Abel integral branch.
    dsimp [g]
    rw [exercise8_closed_extension_eq_abel_integral_of_im_ne_zero (k := k) hwne, h_ofComplex]
  -- Replace the canonical owner locally by the continuous ambient Abel-integral model.
  exact hg.congr heq

/-- Helper for Cartan section26 0018_Exercise_8: at a real-axis point, continuity of the canonical
closed-half-plane owner is exactly the source boundary-limit bridge from the Abel integral to the
repaired boundary trace. -/
lemma exercise8_closed_extension_continuousAt_boundary
    (k : Exercise8Modulus) (z : ClosedUpperHalfPlane) (hz : ((z : ℂ)).im = 0) :
    ContinuousAt (exercise8_closed_extension k) z := by
  -- Route correction: the topological glue is now isolated. It remains only to supply the
  -- from-above limit of the canonical owner along the strict upper slice.
  exact exercise8_closed_extension_continuousAt_boundary_of_tendsto k hz
    (exercise8_closed_extension_tendsto_boundary_trace_from_above k z hz)

/-- Helper for Cartan section26 0018_Exercise_8: away from the real axis, the canonical
closed-half-plane owner is continuous because it locally agrees with the interior Abel integral. -/
lemma exercise8_closed_extension_continuousAt_interior
    (k : Exercise8Modulus) (z : ClosedUpperHalfPlane) (hz : ((z : ℂ)).im ≠ 0) :
    ContinuousAt (exercise8_closed_extension k) z := by
  -- Route correction: the transport from the Abel integral to the closed-half-plane owner is now
  -- separated from the analytic continuity proof for the Abel integral itself.
  exact exercise8_closed_extension_continuousAt_interior_of_abel_integral_continuousAt k hz
    (exercise8_abel_integral_continuousAt k
      ⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩)

/-- Helper for Exercise 8: once the interior Abel integral is matched to the repaired boundary
trace on the real axis, the canonical owner is continuous on the closed half-plane. -/
lemma exercise8_closed_extension_continuous (k : Exercise8Modulus) :
    Continuous (exercise8_closed_extension k) := by
  -- Route correction: isolate the topological glue first. The only remaining analytic inputs are
  -- interior continuity of `exercise8_abel_integral` and the from-above boundary limit to
  -- `exercise8_boundary_trace`.
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : ((z : ℂ)).im = 0
  · -- The boundary case is isolated as the source-faithful from-above continuity bridge.
    exact exercise8_closed_extension_continuousAt_boundary k z hz
  · -- Off the boundary, the canonical owner is locally just the Abel-integral branch.
    exact exercise8_closed_extension_continuousAt_interior k z hz

/-- Helper for Exercise 8: the canonical owner built from the reflected boundary trace is the
source-faithful closed-half-plane extension. -/
lemma exercise8_closed_extension_spec (k : Exercise8Modulus) :
    IsExercise8Extension k (exercise8_closed_extension k) := by
  constructor
  · -- The continuity proof is isolated in the canonical closed-half-plane owner above.
    exact exercise8_closed_extension_continuous k
  · -- The interior branch of the definition is literally the Abel integral.
    intro z
    simpa using exercise8_closed_extension_of_upper k z

