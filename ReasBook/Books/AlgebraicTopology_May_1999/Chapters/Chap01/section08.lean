import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_1_8_1 (from Chap01) -/
noncomputable section

open scoped ContinuousMap CircleDegree

/-- Helper for Problem 1.8.1: the normalized boundary map of a product polynomial is the pointwise
product of the normalized boundary maps of the two factors. -/
-- Proof sketch: evaluate both sides on `S¹`, rewrite polynomial evaluation of a product, and use
-- multiplicativity of `complexDivNormCircle`.
theorem polynomialNormalizedBoundaryMap_mul
    (f g : Polynomial ℂ)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0)
    (hg : ∀ z : Circle, Polynomial.eval (z : ℂ) g ≠ 0) :
    polynomialNormalizedBoundaryMap (f * g)
      (fun z ↦ by
        rw [Polynomial.eval_mul]
        exact mul_ne_zero (hf z) (hg z)) =
      polynomialNormalizedBoundaryMap f hf * polynomialNormalizedBoundaryMap g hg := by
  ext z
  -- Compare the two circle-valued maps pointwise on the boundary.
  rw [polynomialNormalizedBoundaryMap_apply, ContinuousMap.mul_apply,
    polynomialNormalizedBoundaryMap_apply, polynomialNormalizedBoundaryMap_apply]
  simpa [Polynomial.eval_mul] using congrArg (fun w : Circle ↦ (w : ℂ))
    (complexDivNormCircle_mul (Polynomial.eval (z : ℂ) f) (Polynomial.eval (z : ℂ) g) (hf z) (hg z))

/-- Helper for Problem 1.8.1: equal polynomials with boundary nonvanishing define the same
normalized boundary map. -/
-- Proof sketch: compare the two continuous maps pointwise and use proof-irrelevance through
-- `complexDivNormCircle_congr`.
theorem polynomialNormalizedBoundaryMap_congr {f g : Polynomial ℂ}
    (hfg : f = g)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0)
    (hg : ∀ z : Circle, Polynomial.eval (z : ℂ) g ≠ 0) :
    polynomialNormalizedBoundaryMap f hf = polynomialNormalizedBoundaryMap g hg := by
  subst hfg
  ext z
  simp [polynomialNormalizedBoundaryMap_apply]

/-- Helper for Problem 1.8.1: the normalized boundary map of a nonzero constant polynomial is the
corresponding constant circle-valued map. -/
-- Proof sketch: evaluation of `C a` is constantly `a`, so normalization on the boundary is also
-- constant.
theorem polynomialNormalizedBoundaryMap_C (a : ℂ) (ha : a ≠ 0) :
    polynomialNormalizedBoundaryMap (Polynomial.C a)
      (fun z ↦ by simpa [Polynomial.eval_C] using ha) =
      ContinuousMap.const Circle (complexDivNormCircle a ha) := by
  ext z
  simp [polynomialNormalizedBoundaryMap_apply, Polynomial.eval_C]

/-- Helper for Problem 1.8.1: pointwise multiplication preserves homotopy between circle-valued
continuous maps. -/
-- Proof sketch: choose explicit homotopies for the two factors and multiply their values
-- pointwise in `Circle`.
theorem homotopic_mul {f₀ f₁ g₀ g₁ : C(Circle, Circle)}
    (hf : f₀.Homotopic f₁) (hg : g₀.Homotopic g₁) :
    (f₀ * g₀).Homotopic (f₁ * g₁) := by
  rcases hf with ⟨F⟩
  rcases hg with ⟨G⟩
  refine ⟨{
    toFun := fun x ↦ F x * G x
    continuous_toFun := F.continuous.mul G.continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    -- At time `0`, the product homotopy evaluates to the product of the two initial maps.
    simp
  · intro z
    -- At time `1`, the product homotopy evaluates to the product of the two terminal maps.
    simp

/-- Problem 1.8.1: if a complex polynomial has no root on `S¹`, then the number of its roots in
the open unit disk, counted with multiplicity, equals the degree of the normalized boundary map
`z ↦ p(z) / |p(z)|`. -/
-- Proof sketch: factor `p` according to whether its roots lie inside or outside the open unit
-- disk. The factors coming from roots inside the disk contribute one unit of degree each, using
-- the monic outside-zero computation for normalized boundary maps, while the factors with all
-- roots outside contribute degree `0` by the closed-disk homotopy argument. Additivity of degree
-- under multiplication then gives the desired count.
theorem circleDegree_polynomialNormalizedBoundaryMap_eq_card_roots_inside_open_unit_disk
    (p : Polynomial ℂ)
    (hp : ∀ z : Circle, p.eval (z : ℂ) ≠ 0) :
    deg(polynomialNormalizedBoundaryMap p hp) =
      ((p.roots.filter fun z ↦ ‖z‖ < 1).card : ℤ) := by
  let sIn : Multiset ℂ := p.roots.filter fun z ↦ ‖z‖ < 1
  let sOut : Multiset ℂ := p.roots.filter fun z ↦ ¬ ‖z‖ < 1
  let pin : Polynomial ℂ := (sIn.map fun a ↦ Polynomial.X - Polynomial.C a).prod
  let pout : Polynomial ℂ := (sOut.map fun a ↦ Polynomial.X - Polynomial.C a).prod
  let q : Polynomial ℂ := pin * pout
  have hp_eval_one : Polynomial.eval (1 : ℂ) p ≠ 0 := by
    -- Evaluating on the circle at `1` rules out the zero polynomial.
    simpa using hp 1
  have hpnz : p ≠ 0 := by
    intro hpz
    simp [hpz] at hp_eval_one
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpnz
  have hsplitRoots : sIn + sOut = p.roots := by
    -- The root multiset partitions into roots inside the open disk and its complement.
    simpa [sIn, sOut] using
      (Multiset.filter_add_not (p := fun z : ℂ ↦ ‖z‖ < 1) p.roots)
  have hroots : p.roots.card = p.natDegree := by
    -- Over `ℂ`, every polynomial splits, so the root multiset has full cardinality.
    simpa using (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hpinMonic : pin.Monic := by
    -- Each factor `X - a` is monic, so their multiset product is monic.
    dsimp [pin]
    exact Polynomial.monic_multiset_prod_of_monic _ _ fun a _ ↦ Polynomial.monic_X_sub_C a
  have hpoutMonic : pout.Monic := by
    -- The complementary root factor is also monic for the same reason.
    dsimp [pout]
    exact Polynomial.monic_multiset_prod_of_monic _ _ fun a _ ↦ Polynomial.monic_X_sub_C a
  have hpinnz : pin ≠ 0 := hpinMonic.ne_zero
  have hpoutnz : pout ≠ 0 := hpoutMonic.ne_zero
  have hpinOutside : ∀ z : ℂ, 1 ≤ ‖z‖ → Polynomial.eval z pin ≠ 0 := by
    intro z hzNorm hzEval
    have hz_mem_pin : z ∈ pin.roots := by
      rwa [Polynomial.mem_roots hpinnz]
    have hz_mem_in : z ∈ sIn := by
      simpa [pin] using (Polynomial.roots_multiset_prod_X_sub_C sIn ▸ hz_mem_pin)
    have hz_lt : ‖z‖ < 1 := by
      have hz_filter : z ∈ p.roots.filter (fun w : ℂ ↦ ‖w‖ < 1) := by
        simpa [sIn] using hz_mem_in
      exact (Multiset.mem_filter.1 hz_filter).2
    exact (not_lt_of_ge hzNorm) hz_lt
  have hpoutClosed : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 → Polynomial.eval z pout ≠ 0 := by
    intro z hzBall hzEval
    have hz_mem_pout : z ∈ pout.roots := by
      exact (Polynomial.mem_roots hpoutnz).2 (by simpa [Polynomial.IsRoot] using hzEval)
    have hz_mem_out : z ∈ sOut := by
      simpa [pout] using (Polynomial.roots_multiset_prod_X_sub_C sOut ▸ hz_mem_pout)
    have hz_not_lt : ¬ ‖z‖ < 1 := by
      have hz_filter : z ∈ p.roots.filter (fun w : ℂ ↦ ¬ ‖w‖ < 1) := by
        simpa [sOut] using hz_mem_out
      exact (Multiset.mem_filter.1 hz_filter).2
    have hz_le : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzBall
    have hz_norm : ‖z‖ = 1 := le_antisymm hz_le (not_lt.mp hz_not_lt)
    let w : Circle := ⟨z, mem_sphere_zero_iff_norm.2 hz_norm⟩
    have hz_mem_p : z ∈ p.roots := by
      have hz_filter : z ∈ p.roots.filter (fun w : ℂ ↦ ¬ ‖w‖ < 1) := by
        simpa [sOut] using hz_mem_out
      exact (Multiset.mem_filter.1 hz_filter).1
    have hpz : Polynomial.eval z p = 0 := by
      exact (Polynomial.mem_roots hpnz).1 hz_mem_p
    have hpw : Polynomial.eval (w : ℂ) p ≠ 0 := hp w
    exact hpw (by simpa [w] using hpz)
  have hpinCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) pin ≠ 0 :=
    polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk pin hpinOutside
  have hpoutCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) pout ≠ 0 :=
    polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk pout hpoutClosed
  have hfactor : Polynomial.C p.leadingCoeff * q = p := by
    -- Rewrite `p` as its leading coefficient times the product over the inside/outside root split.
    have hrootProd :
        (p.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod = q := by
      calc
        (p.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod =
            (((sIn + sOut).map fun a ↦ Polynomial.X - Polynomial.C a).prod) := by
              rw [← hsplitRoots]
        _ = (sIn.map fun a ↦ Polynomial.X - Polynomial.C a).prod *
              (sOut.map fun a ↦ Polynomial.X - Polynomial.C a).prod := by
              rw [Multiset.map_add, Multiset.prod_add]
        _ = q := by
              rfl
    calc
      Polynomial.C p.leadingCoeff * q =
          Polynomial.C p.leadingCoeff * (p.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod := by
            rw [hrootProd]
      _ = p := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) hroots
  have hqCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) q ≠ 0 := by
    intro z
    -- The product factor is nonzero on `S¹` because both subfactors are.
    dsimp [q]
    rw [Polynomial.eval_mul]
    exact mul_ne_zero (hpinCircle z) (hpoutCircle z)
  have hq_mul_C : q * Polynomial.C p.leadingCoeff = p := by
    -- Move the constant leading-coefficient factor to the right for the boundary-map lemma.
    calc
      q * Polynomial.C p.leadingCoeff = Polynomial.C p.leadingCoeff * q := by
        rw [mul_comm]
      _ = p := hfactor
  have hconstCompare :
      (polynomialNormalizedBoundaryMap p hp).Homotopic
        (polynomialNormalizedBoundaryMap q hqCircle) := by
    have hqCircleMul : ∀ z : Circle, Polynomial.eval (z : ℂ) (q * Polynomial.C p.leadingCoeff) ≠ 0 := by
      intro z
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      exact mul_ne_zero (hqCircle z) hlead
    have hp_eq :
        polynomialNormalizedBoundaryMap p hp =
          polynomialNormalizedBoundaryMap (q * Polynomial.C p.leadingCoeff) hqCircleMul := by
      symm
      exact polynomialNormalizedBoundaryMap_congr hq_mul_C hqCircleMul hp
    have hleadConst :
        (ContinuousMap.const Circle (complexDivNormCircle p.leadingCoeff hlead)).Homotopic
          (1 : C(Circle, Circle)) := by
      -- The leading coefficient contributes only a constant phase on the boundary.
      rw [show (1 : C(Circle, Circle)) = ContinuousMap.const Circle (1 : Circle) by rfl]
      simpa using
        (ContinuousMap.homotopic_const_iff).2
          (PathConnectedSpace.joined (complexDivNormCircle p.leadingCoeff hlead) 1)
    -- Route correction: instead of proving degree additivity directly, first strip the nonzero
    -- constant factor by splitting off the constant polynomial `C(p.leadingCoeff)`.
    rw [hp_eq]
    rw [polynomialNormalizedBoundaryMap_mul q (Polynomial.C p.leadingCoeff) hqCircle
      (fun z ↦ by simpa [Polynomial.eval_C] using hlead)]
    rw [polynomialNormalizedBoundaryMap_C]
    simpa using
      homotopic_mul
        (ContinuousMap.Homotopic.refl (polynomialNormalizedBoundaryMap q hqCircle))
        hleadConst
  have hpinHom :
      (polynomialNormalizedBoundaryMap pin hpinCircle).Homotopic
        ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) := by
    -- The inside-root factor contributes one degree for each root inside the open disk.
    simpa [pin] using
      polynomialNormalizedBoundaryMap_homotopic_id_zpow_of_monic_of_no_root_outside_open_unit_disk
        pin hpinOutside hpinMonic
  let cOut : Circle :=
    complexDivNormCircle (Polynomial.eval (0 : ℂ) pout)
      (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk pout hpoutClosed)
  have hpoutHom :
      (polynomialNormalizedBoundaryMap pout hpoutCircle).Homotopic
        (ContinuousMap.const Circle cOut) := by
    -- The complementary factor has no zeros on the closed disk, so its boundary map contracts to
    -- a constant.
    simpa [cOut, hpoutCircle] using
      polynomialNormalizedBoundaryMap_homotopic_const_of_no_root_closed_unit_disk pout hpoutClosed
  have hconstOut :
      (ContinuousMap.const Circle cOut).Homotopic (1 : C(Circle, Circle)) := by
    -- Any constant map on `S¹` is homotopic to the constant map at `1`.
    rw [show (1 : C(Circle, Circle)) = ContinuousMap.const Circle (1 : Circle) by rfl]
    simpa using (ContinuousMap.homotopic_const_iff).2 (PathConnectedSpace.joined cOut 1)
  have hqHom :
      (polynomialNormalizedBoundaryMap q hqCircle).Homotopic
        ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) := by
    have hmul :
        (polynomialNormalizedBoundaryMap q hqCircle).Homotopic
          (((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) * ContinuousMap.const Circle cOut) := by
      -- Factor the boundary map of `q = pin * pout` and combine the two imported homotopies.
      dsimp [q]
      rw [polynomialNormalizedBoundaryMap_mul pin pout hpinCircle hpoutCircle]
      exact homotopic_mul hpinHom hpoutHom
    refine ContinuousMap.Homotopic.trans hmul ?_
    -- Finally remove the constant factor on the right.
    simpa [mul_one] using
      homotopic_mul
        (ContinuousMap.Homotopic.refl ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)))
        hconstOut
  have hfinal :
      (polynomialNormalizedBoundaryMap p hp).Homotopic
        ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) := by
    -- Concatenate the leading-coefficient reduction with the inside/outside factor homotopy.
    exact ContinuousMap.Homotopic.trans hconstCompare hqHom
  calc
    deg(polynomialNormalizedBoundaryMap p hp) =
        deg((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) :=
      circleDegree_eq_of_homotopic _ _ hfinal
    _ = (sIn.card : ℤ) := circleDegree_id_zpow _
    _ = ((p.roots.filter fun z ↦ ‖z‖ < 1).card : ℤ) := by
      simp [sIn]

/-! ### Problem_1_8_2 (from Chap01) -/
noncomputable section

open scoped ContinuousMap CircleDegree unitInterval
open FundamentalGroup

/-- Helper for Problem 1.8.2: a lift of `f ∘ Real.fourierChar` records the degree of `f` through
the displacement of its endpoint over one turn. -/
lemma circleDegree_eq_fourierChar_lift_displacement
    (f : C(Circle, Circle)) {c : ℝ} (hc : Real.fourierChar c = f 1)
    (F : C(ℝ, ℝ)) (hF0 : F 0 = c)
    (hF : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩) :
    F 1 - c = (deg(f) : ℝ) := by
  let a : Path (f 1) 1 :=
    (((Path.segment (0 : ℝ) c).map Real.continuous_fourierChar).cast
      (by simp) hc.symm).symm
  let mappedLoop : Path (f 1) (f 1) := (standardLoop 1).map f.continuous
  let loop : Path (1 : Circle) 1 := (a.symm.trans mappedLoop).trans a
  have hF1 : Real.fourierChar (F 1) = f 1 := by
    have hraw : Real.fourierChar (F 1) = f (Real.fourierChar (1 : ℝ)) := congrFun hF (1 : ℝ)
    have hchar1 : Real.fourierChar (1 : ℝ) = (1 : Circle) := by
      rw [Real.fourierChar_apply']
      simpa [mul_comm, mul_left_comm, mul_assoc] using Circle.exp_two_pi
    simpa [hchar1] using hraw
  have hclass :
      circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦loop⟧) = deg(f) := by
    -- Rewrite the degree-specification loop using the chosen basepoint-change path `a`.
    have hdeg := congrArg circleFundamentalGroupLiftIndex (circleDegree_spec f a)
    rw [show γ[a] (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) =
        FundamentalGroup.fromPath ⟦loop⟧ by
          rw [show FundamentalGroup.map f (1 : Circle) (standardLoopClass 1) =
              FundamentalGroup.fromPath ⟦mappedLoop⟧ by
                rfl]
          rw [fundamentalGroupMulEquivOfPath_apply_fromPath]] at hdeg
    rw [circleFundamentalGroupLiftIndex_standardLoop] at hdeg
    exact hdeg
  have hfirstLift :
      real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero a.symm) =
        (Path.segment (0 : ℝ) c).toContinuousMap := by
    -- The chosen return path is literally the Fourier character of the segment from `0` to `c`.
    change real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero a.symm) =
          (Path.segment (0 : ℝ) c).toContinuousMap
    refine ((real_fourierChar_isCoveringMap.eq_liftPath_iff'
      (circle_path_start_eq_fourierChar_zero a.symm)).2 ?_).symm
    refine ⟨?_, by simp⟩
    ext s
    simp [a]
  have hmidLift :
      real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap c
        (by simpa [mappedLoop] using hc.symm) =
        F.comp ⟨fun s : I ↦ (s : ℝ), continuous_subtype_val⟩ := by
    -- Restrict the global lift `F` to the unit interval to lift the mapped standard loop.
    refine ((real_fourierChar_isCoveringMap.eq_liftPath_iff'
      (by simpa [mappedLoop] using hc.symm)).2 ?_).symm
    refine ⟨?_, by simp [hF0]⟩
    ext s
    simpa [Function.comp_apply, mappedLoop, standardLoop_eq_fourierChar_mul] using
      congrFun hF (s : ℝ)
  have hlastStart : a.toContinuousMap 0 = Real.fourierChar (F 1) := by
    -- At the end of the middle segment, the lift lands over the basepoint `f 1`.
    simpa [a] using hF1.symm
  have hlastLift :
      real_fourierChar_isCoveringMap.liftPath a.toContinuousMap (F 1) hlastStart =
        (Path.segment (F 1) (F 1 - c)).toContinuousMap := by
    -- The final return path subtracts the original lift value `c`.
    refine ((real_fourierChar_isCoveringMap.eq_liftPath_iff' hlastStart).2 ?_).symm
    refine ⟨?_, by simp⟩
    ext s
    exact congrArg Subtype.val <| by
      have hperiod : Real.fourierChar (F 1 - c) = (1 : Circle) := by
        have hmul : (2 * Real.pi) * (F 1 - c) = (2 * Real.pi) * F 1 - (2 * Real.pi) * c := by
          ring
        rw [Real.fourierChar_apply', hmul, Circle.exp_sub]
        simpa [Real.fourierChar_apply'] using (div_eq_one.2 (hF1.trans hc.symm))
      have hsegment :
          Real.fourierChar ((Path.segment (0 : ℝ) c) (σ s)) =
            Real.fourierChar ((1 - (s : ℝ)) * c) := by
        change Real.fourierChar ((Path.segment (0 : ℝ) c) (σ s)) = _
        rw [Path.segment_apply]
        simp [AffineMap.lineMap_apply_module]
      calc
        Real.fourierChar ((Path.segment (F 1) (F 1 - c)) s) =
            Real.fourierChar (((1 - (s : ℝ)) * c) + (F 1 - c)) := by
              rw [Path.segment_apply]
              have hline :
                  (AffineMap.lineMap (F 1) (F 1 - c)) (s : ℝ) = -(s : ℝ) * c + F 1 := by
                rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
                ring
              rw [hline]
              congr 1
              ring
        _ = Real.fourierChar ((1 - (s : ℝ)) * c) * Real.fourierChar (F 1 - c) := by
              simpa using Real.fourierChar.map_add_eq_mul' ((1 - (s : ℝ)) * c) (F 1 - c)
        _ = Real.fourierChar ((1 - (s : ℝ)) * c) := by
                simp [hperiod]
        _ = a s := by
                simpa [a] using hsegment.symm
  have hprefix :
      real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop)) 1 = F 1 := by
    -- Concatenate the first segment lift with the restricted lift of the mapped loop.
    have hfirstEnd :
        (real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero a.symm)) 1 = c := by
      simpa using DFunLike.congr_fun hfirstLift 1
    have hmidEnd :
        (real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap c
          (by simpa [mappedLoop] using hc.symm)) 1 = F 1 := by
      simpa using DFunLike.congr_fun hmidLift 1
    have hmidEnd' :
        (real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap
          ((real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero a.symm)) 1)
          (by
            simpa [mappedLoop] using
              (congr_fun
                (real_fourierChar_isCoveringMap.liftPath_lifts a.symm.toContinuousMap 0
                  (circle_path_start_eq_fourierChar_zero a.symm)) 1).symm)) 1 = F 1 := by
      simpa [hfirstEnd] using hmidEnd
    have htrans := DFunLike.congr_fun
      (real_fourierChar_isCoveringMap.liftPath_trans
        (by rw [fourierChar_zero_eq_one]) a.symm mappedLoop) 1
    have htrans' :
        (real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1 =
          (real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap
            ((real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
              (circle_path_start_eq_fourierChar_zero a.symm)) 1)
            (by
              simpa [mappedLoop] using
                (congr_fun
                  (real_fourierChar_isCoveringMap.liftPath_lifts a.symm.toContinuousMap 0
                    (circle_path_start_eq_fourierChar_zero a.symm)) 1).symm)) 1 := by
      simpa using htrans
    exact htrans'.trans hmidEnd'
  have hlastLift' :
      real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
        (real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop)) 1)
        (by simpa [hprefix] using hlastStart) =
          (Path.segment (F 1) (F 1 - c)).toContinuousMap := by
    simpa [hprefix] using hlastLift
  have hloopLift :
      real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero loop) 1 = F 1 - c := by
    -- A second application of lift concatenation computes the endpoint of the transported loop.
    have hlastEnd :
        (real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
          (real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop)) 1)
          (by simpa [hprefix] using hlastStart)) 1 = F 1 - c := by
      simpa using DFunLike.congr_fun hlastLift' 1
    have hlastEnd' :
        (real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
          ((real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1)
          (by
            simpa using
              (congr_fun
                (real_fourierChar_isCoveringMap.liftPath_lifts
                  (a.symm.trans mappedLoop).toContinuousMap 0
                  (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1).symm)) 1 =
          F 1 - c := by
      simpa using hlastEnd
    have htrans := DFunLike.congr_fun
      (real_fourierChar_isCoveringMap.liftPath_trans
        (by rw [fourierChar_zero_eq_one])
        (a.symm.trans mappedLoop) a) 1
    have htrans' :
        (real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero loop)) 1 =
          (real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
            ((real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
              (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1)
            (by
              simpa using
                (congr_fun
                  (real_fourierChar_isCoveringMap.liftPath_lifts
                    (a.symm.trans mappedLoop).toContinuousMap 0
                    (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1).symm)) 1 := by
      simpa [loop] using htrans
    exact htrans'.trans hlastEnd'
  have hloopIndex :
      ((deg(f) : ℤ) : ℝ) =
        real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero loop) 1 := by
    -- The loop class from `circleDegree_spec` has lift index exactly `deg(f)`.
    calc
      ((deg(f) : ℤ) : ℝ) =
          ((circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦loop⟧) : ℤ) : ℝ) := by
            exact congrArg (fun n : ℤ ↦ (n : ℝ)) hclass.symm
      _ = real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero loop) 1 := by
              simpa using circleFundamentalGroupLiftIndex_spec loop
  exact hloopLift.symm.trans hloopIndex.symm

/-- Helper for Problem 1.8.2: subtracting the parameter from a lift of `f ∘ Real.fourierChar`
produces the quotient map `z ↦ f z / z`. -/
lemma fourierChar_lift_difference_eq_quotient
    (f : C(Circle, Circle)) (F : C(ℝ, ℝ))
    (hF : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩)
    (t : ℝ) :
    Real.fourierChar (F t - t) = f (Real.fourierChar t) / Real.fourierChar t := by
  -- Rewrite the Fourier character of the difference as a quotient in the circle group.
  calc
    Real.fourierChar (F t - t) = Real.fourierChar (F t) / Real.fourierChar t := by
      have hmul : (2 * Real.pi) * (F t - t) = (2 * Real.pi) * F t - (2 * Real.pi) * t := by
        ring
      rw [Real.fourierChar_apply', hmul, Circle.exp_sub, Real.fourierChar_apply',
        Real.fourierChar_apply']
    _ = f (Real.fourierChar t) / Real.fourierChar t := by
      simpa [Function.comp_apply] using congrFun hF t

/-- Helper for Problem 1.8.2: if `f` has no fixed points, then the lift difference `F t - t`
never hits an integer. -/
lemma fourierChar_lift_difference_ne_int_of_no_fixed_points
    (f : C(Circle, Circle)) (hno : ∀ z : Circle, f z ≠ z)
    (F : C(ℝ, ℝ))
    (hF : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩)
    (t : ℝ) (n : ℤ) :
    F t - t ≠ n := by
  -- An integer value would make the quotient map equal `1`, forcing a fixed point.
  intro hnt
  have hquot :
      f (Real.fourierChar t) / Real.fourierChar t = (1 : Circle) := by
    rw [← fourierChar_lift_difference_eq_quotient f F hF t, hnt]
    exact fourierChar_int_eq_one n
  have hfix : f (Real.fourierChar t) = Real.fourierChar t := div_eq_one.1 hquot
  exact hno (Real.fourierChar t) hfix

/-- Helper for Problem 1.8.2: a continuous real function that avoids all integers cannot change by
a nonzero integer over the interval `[0, 1]`. -/
lemma integer_avoiding_continuous_step_eq_zero
    {d : ℝ → ℝ} (hd : Continuous d)
    (havoid : ∀ t : ℝ, ∀ n : ℤ, d t ≠ n) {k : ℤ}
    (hk : d 1 - d 0 = (k : ℝ)) :
    k = 0 := by
  -- Any nonzero integer jump would force the image of `[0, 1]` to cross an integer by IVT.
  by_contra hk0
  rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
  · let n : ℤ := Int.floor (d 0)
    have hd10 : d 1 ≤ d 0 := by
      have hk_real : (k : ℝ) < 0 := by exact_mod_cast hkneg
      linarith [hk, hk_real]
    have hn_mem : ((n : ℤ) : ℝ) ∈ Set.uIcc (d 0) (d 1) := by
      rw [Set.uIcc_of_ge hd10]
      refine ⟨?_, ?_⟩
      · have hk_int : k ≤ -1 := by omega
        have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast hk_int
        have hlt : d 0 - 1 < (n : ℝ) := by
          simpa [n] using (Int.sub_one_lt_floor (d 0))
        linarith [hk, hk_le, hlt]
      · simpa [n] using (Int.floor_le (d 0))
    obtain ⟨t, _, htd⟩ := (intermediate_value_uIcc hd.continuousOn) hn_mem
    exact (havoid t n) (by simpa [n] using htd)
  · let n : ℤ := Int.floor (d 0) + 1
    have hd01 : d 0 ≤ d 1 := by
      have hk_real : (0 : ℝ) < k := by exact_mod_cast hkpos
      linarith [hk, hk_real]
    have hn_mem : ((n : ℤ) : ℝ) ∈ Set.uIcc (d 0) (d 1) := by
      rw [Set.uIcc_of_le hd01]
      refine ⟨?_, ?_⟩
      · have hlt : d 0 < (n : ℝ) := by
          simpa [n] using (lt_floor_add_one (d 0))
        exact hlt.le
      · have hk_int : (1 : ℤ) ≤ k := by omega
        have hk_ge : (1 : ℝ) ≤ k := by exact_mod_cast hk_int
        have hfloor : ((Int.floor (d 0) : ℤ) : ℝ) ≤ d 0 := Int.floor_le (d 0)
        calc
          (n : ℝ) = ((Int.floor (d 0) : ℤ) : ℝ) + 1 := by simp [n]
          _ ≤ d 0 + 1 := by linarith
          _ ≤ d 0 + k := by linarith
          _ = d 1 := by linarith [hk]
    obtain ⟨t, _, htd⟩ := (intermediate_value_uIcc hd.continuousOn) hn_mem
    exact (havoid t n) (by simpa [n] using htd)

/-- Problem 1.8.2: any continuous self-map of `S¹` whose degree is not `1` has a fixed point. -/
-- Proof sketch: argue contrapositively. If `f` has no fixed point, then the quotient map
-- `z ↦ f z / z` is a well-defined continuous self-map of `S¹`. Its degree is `deg(f) - 1`, and
-- the absence of fixed points lets one show this quotient is null-homotopic, hence has degree
-- `0`. Therefore `deg(f) = 1`, contradicting the hypothesis.
theorem circle_exists_fixed_point_of_degree_ne_one
    (f : C(Circle, Circle)) (hf : deg(f) ≠ 1) :
    ∃ z : Circle, Function.IsFixedPt f z := by
  classical
  by_contra hnofix
  push Not at hnofix
  have hno : ∀ z : Circle, f z ≠ z := by
    intro z
    simpa [Function.IsFixedPt] using hnofix z
  let c : ℝ := Complex.arg (f 1) / (2 * Real.pi)
  have hc : Real.fourierChar c = f 1 := by
    -- Choose a concrete lift of the basepoint `f 1` using the argument.
    dsimp [c]
    rw [Real.fourierChar_apply']
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
      positivity
    field_simp [h2pi]
    simpa using Circle.exp_arg (f 1)
  let g : C(ℝ, Circle) := f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  obtain ⟨F, hF, -⟩ := real_fourierChar_isCoveringMap.existsUnique_continuousMap_lifts g 0 c
    (by simpa [g, Function.comp_apply] using hc)
  have hF0 : F 0 = c := hF.1
  have hFcomp : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩ := by
    simpa [g] using hF.2
  have hdeg :
      F 1 - c = (deg(f) : ℝ) :=
    circleDegree_eq_fourierChar_lift_displacement f hc F hF0 hFcomp
  let d : ℝ → ℝ := fun t ↦ F t - t
  have hd : Continuous d := F.continuous.sub continuous_id
  have havoid : ∀ t : ℝ, ∀ n : ℤ, d t ≠ n := by
    intro t n
    exact fourierChar_lift_difference_ne_int_of_no_fixed_points f hno F hFcomp t n
  have hstep : d 1 - d 0 = ((deg(f) - 1 : ℤ) : ℝ) := by
    -- The displacement changes by `deg(f) - 1` over a unit turn.
    dsimp [d]
    calc
      (F 1 - 1) - (F 0 - 0) = (F 1 - F 0) - 1 := by ring
      _ = ((deg(f) : ℤ) : ℝ) - 1 := by simpa [hF0] using congrArg (fun x : ℝ ↦ x - c) hdeg
      _ = ((deg(f) - 1 : ℤ) : ℝ) := by norm_num
  have hzero : deg(f) - 1 = 0 :=
    integer_avoiding_continuous_step_eq_zero hd havoid hstep
  exact hf (sub_eq_zero.mp hzero)

/-! ### Problem_1_8_3 (from Chap01) -/
noncomputable section

universe u

open Path.Homotopic.Quotient
open scoped unitInterval

section HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Helper for Problem 1.8.3: pointwise loop multiplication on homotopy classes induced by the
ambient `HSpace` structure. -/
def loop_hmul_class
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    Path.Homotopic.Quotient (HSpace.e : X) HSpace.e :=
  ((Path.Homotopic.prod p q).map HSpace.hmul).cast
    HSpace.hmul_e_e.symm
    HSpace.hmul_e_e.symm

/-- Helper for Problem 1.8.3: the left-unit homotopy coming from `HSpace.eHmul`. -/
lemma loop_hmul_refl_left_homotopic (γ : Path (HSpace.e : X) HSpace.e) :
    ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).Homotopic γ := by
  -- Track the homotopy `(t, s) ↦ e ⋀ γ s` directly on the square.
  refine ⟨{
    toFun := fun p => HSpace.eHmul (p.1, γ p.2)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro s
      simp [Path.cast]
    map_one_left := by
      intro s
      simp
    prop' := by
      intro t s hs
      rcases hs with rfl | rfl
      · calc
          ({ toFun := fun x ↦ HSpace.eHmul ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 0 = HSpace.eHmul (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.eHmul (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.eHmul.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 0 := by
              simp [Path.cast, HSpace.hmul_e_e]
      · calc
          ({ toFun := fun x ↦ HSpace.eHmul ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 1 = HSpace.eHmul (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.eHmul (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.eHmul.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 1 := by
              simp [Path.cast, HSpace.hmul_e_e] }⟩

/-- Helper for Problem 1.8.3: the right-unit homotopy coming from `HSpace.hmulE`. -/
lemma loop_hmul_refl_right_homotopic (γ : Path (HSpace.e : X) HSpace.e) :
    (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).Homotopic γ := by
  -- Track the homotopy `(t, s) ↦ γ s ⋀ e` directly on the square.
  refine ⟨{
    toFun := fun p => HSpace.hmulE (p.1, γ p.2)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro s
      simp [Path.cast]
    map_one_left := by
      intro s
      simp
    prop' := by
      intro t s hs
      rcases hs with rfl | rfl
      · calc
          ({ toFun := fun x ↦ HSpace.hmulE ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 0 = HSpace.hmulE (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.hmulE (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.hmulE.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 0 := by
              simp [Path.cast, HSpace.hmul_e_e]
      · calc
          ({ toFun := fun x ↦ HSpace.hmulE ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 1 = HSpace.hmulE (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.hmulE (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.hmulE.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 1 := by
              simp [Path.cast, HSpace.hmul_e_e] }⟩

/-- Helper for Problem 1.8.3: path composition commutes with endpoint casts on loop classes. -/
lemma loop_class_cast_trans {a₂ b₂ c₂ a₁ b₁ c₁ : X}
    (p : Path.Homotopic.Quotient a₂ b₂) (q : Path.Homotopic.Quotient b₂ c₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (p.cast ha hb).trans (q.cast hb hc) = (p.trans q).cast ha hc := by
  induction p using Quotient.ind
  rename_i p
  induction q using Quotient.ind
  rename_i q
  rfl

/-- Helper for Problem 1.8.3: loop multiplication by `HSpace.hmul` has the constant loop as a left
unit on homotopy classes. -/
lemma loop_hmul_class_refl_left (q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (X := X) (Path.Homotopic.Quotient.refl HSpace.e) q = q := by
  induction q using Quotient.ind
  rename_i γ
  -- Reduce to the explicit left-unit homotopy on representatives.
  change Path.Homotopic.Quotient.mk
      ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) = Path.Homotopic.Quotient.mk γ
  rw [Path.Homotopic.Quotient.eq]
  exact loop_hmul_refl_left_homotopic (X := X) γ

/-- Helper for Problem 1.8.3: loop multiplication by `HSpace.hmul` has the constant loop as a right
unit on homotopy classes. -/
lemma loop_hmul_class_refl_right (q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (X := X) q (Path.Homotopic.Quotient.refl HSpace.e) = q := by
  induction q using Quotient.ind
  rename_i γ
  -- Reduce to the explicit right-unit homotopy on representatives.
  change Path.Homotopic.Quotient.mk
      (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) = Path.Homotopic.Quotient.mk γ
  rw [Path.Homotopic.Quotient.eq]
  exact loop_hmul_refl_right_homotopic (X := X) γ

/-- Helper for Problem 1.8.3: pointwise loop multiplication distributes over path composition on
homotopy classes. -/
lemma loop_hmul_class_interchange
    (p₁ q₁ p₂ q₂ : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    (loop_hmul_class (X := X) p₁ q₁).trans (loop_hmul_class (X := X) p₂ q₂) =
      loop_hmul_class (X := X) (p₁.trans p₂) (q₁.trans q₂) := by
  induction p₁, q₁ using Path.Homotopic.Quotient.ind₂
  rename_i a c
  induction p₂, q₂ using Path.Homotopic.Quotient.ind₂
  rename_i b d
  -- On representatives this is the interchange between product paths and composition.
  change Path.Homotopic.Quotient.mk
      ((((a.prod c).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).trans
        (((b.prod d).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)) =
    Path.Homotopic.Quotient.mk
      ((((a.trans b).prod (c.trans d)).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)
  congr 1
  calc
    ((((a.prod c).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).trans
        (((b.prod d).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)) =
        ((((a.prod c).map HSpace.hmul.continuous).trans ((b.prod d).map HSpace.hmul.continuous)).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) := by
            simpa using (Path.cast_trans
              ((a.prod c).map HSpace.hmul.continuous)
              ((b.prod d).map HSpace.hmul.continuous)
              HSpace.hmul_e_e.symm
              HSpace.hmul_e_e.symm
              HSpace.hmul_e_e.symm).symm
    _ = ((((a.prod c).trans (b.prod d)).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) := by
            rw [← Path.map_trans]
    _ = ((((a.trans b).prod (c.trans d)).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) := by
            simp [Path.trans_prod_eq_prod_trans]

/-- Helper for Problem 1.8.3: the `HSpace` loop product agrees with path composition on homotopy
classes. -/
lemma loop_hmul_class_eq_trans
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (X := X) p q = p.trans q := by
  let htrans :
      EckmannHilton.IsUnital
        (Path.Homotopic.Quotient.trans :
          Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
            Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
              Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
        (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := Path.Homotopic.Quotient.refl_trans
      right_id := Path.Homotopic.Quotient.trans_refl }
  let hhmul :
      EckmannHilton.IsUnital (loop_hmul_class (X := X)) (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := loop_hmul_class_refl_left (X := X)
      right_id := loop_hmul_class_refl_right (X := X) }
  -- Apply the abstract Eckmann-Hilton argument to the two loop operations.
  exact
    (congr_fun₂ (EckmannHilton.mul htrans hhmul (loop_hmul_class_interchange (X := X))) p q).symm

/-- Helper for Problem 1.8.3: path composition is commutative on loop classes at the `HSpace`
unit. -/
lemma loop_trans_comm
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    p.trans q = q.trans p := by
  let htrans :
      EckmannHilton.IsUnital
        (Path.Homotopic.Quotient.trans :
          Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
            Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
              Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
        (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := Path.Homotopic.Quotient.refl_trans
      right_id := Path.Homotopic.Quotient.trans_refl }
  let hhmul :
      EckmannHilton.IsUnital (loop_hmul_class (X := X)) (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := loop_hmul_class_refl_left (X := X)
      right_id := loop_hmul_class_refl_right (X := X) }
  -- Compare path composition to the `HSpace` loop product, then use its commutativity.
  calc
    p.trans q = loop_hmul_class (X := X) p q := (loop_hmul_class_eq_trans (X := X) p q).symm
    _ = loop_hmul_class (X := X) q p :=
      (EckmannHilton.mul_comm htrans hhmul (loop_hmul_class_interchange (X := X))).comm p q
    _ = q.trans p := loop_hmul_class_eq_trans (X := X) q p

/-- Problem 1.8.3: multiplication on the fundamental group at the unit of an `HSpace` is
commutative. In particular, the fundamental group at the identity of a topological group is
commutative via `IsTopologicalGroup.hSpace`. -/
-- Proof sketch: use the `HSpace` multiplication on loops based at `HSpace.e`, compare it with path
-- composition at the level of homotopy classes, and conclude by the Eckmann-Hilton argument.
theorem fundamentalGroup_mul_comm (a b : FundamentalGroup X HSpace.e) :
    a * b = b * a := by
  -- Translate the group law into path composition of loop classes and use commutativity there.
  change (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e).trans
      (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) =
    (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e).trans
      (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
  exact
    loop_trans_comm (X := X)
      (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
      (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)

/-- The fundamental group at the unit of an `HSpace` is abelian. In particular, the fundamental
group of a topological group at the identity is abelian via `IsTopologicalGroup.hSpace`. -/
instance fundamentalGroup_commGroup : CommGroup (FundamentalGroup X HSpace.e) :=
  { (inferInstance : Group (FundamentalGroup X HSpace.e)) with
      mul_comm := fundamentalGroup_mul_comm }

end HSpace

section ContinuousMul

variable {G : Type u} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Problem 1.8.3: for loops based at the unit of a topological space with continuous
multiplication, pointwise multiplication is homotopic to path composition. In particular, this
applies to topological groups via `IsTopologicalGroup.hSpace`. -/
-- Proof sketch: consider the square `(s, t) ↦ γ s * δ t`; its diagonal recovers the identity-loop
-- specialization of `Path.mul`, while its boundary yields a reparametrization of `γ.trans δ`.
theorem loop_pointwise_mul_homotopic_trans (γ δ : Path (1 : G) 1) :
    ((γ.mul δ).cast (one_mul (1 : G)).symm (one_mul (1 : G)).symm).Homotopic (γ.trans δ) := by
  letI : HSpace G := IsTopologicalGroup.toHSpace G
  -- Route correction: specialize the abstract `HSpace` comparison instead of building a second
  -- square homotopy directly in the concrete multiplication case.
  rw [← Path.Homotopic.Quotient.eq]
  simpa [loop_hmul_class, Path.mul, IsTopologicalGroup.toHSpace,
    Path.Homotopic.Quotient.mk''_eq_mk, Path.Homotopic.prod_lift,
    Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.mk_cast] using
    loop_hmul_class_eq_trans (X := G) ⟦γ⟧ ⟦δ⟧

/-- Specialization of `fundamentalGroup_mul_comm` to a topological space with continuous
multiplication and unit, using the canonical `HSpace` structure `IsTopologicalGroup.toHSpace`. -/
theorem fundamentalGroup_mul_comm_of_continuousMul (a b : FundamentalGroup G (1 : G)) :
    a * b = b * a := by
  letI : HSpace G := IsTopologicalGroup.toHSpace G
  simpa using fundamentalGroup_mul_comm a b

end ContinuousMul
