import BauschkeLean.Chap20.Example_20_9
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory intervalIntegral
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u

namespace SetValuedOperator

attribute [local instance] Measure.Subtype.measureSpace

-- Source/core/bridge triage:
-- - `source-facing`: Proposition 21.4 asserts maximal monotonicity for the initial-value branch of
--   the time-derivative operator from Example 20.9.
-- - `core/canonical`: Chapter 21 packages maximality via `Maximal IsMonotone A`.
-- - `bridge/view`: the Minty range condition for `Id + A` is the reusable bridge to that
--   canonical owner.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
variable (T : Set.Ioi (0 : ℝ)) (x0 : H)

local notation "IccT" => Set.Icc (0 : ℝ) (T : ℝ)
local notation "L2T" => MeasureTheory.Lp H 2 (volume : Measure IccT)
local notation "W12T" => SobolevW12 H T

local instance : IsFiniteMeasure (volume : Measure IccT) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

/-- Helper for Proposition 21.4: Minty's surjectivity condition for `Id + A` forces maximal
monotonicity. -/
lemma maximal_of_range_id_add_eq_univ
    (A : SetValuedOperator L2T L2T) (hA : A.IsMonotone)
    (hrange : ((id : L2T → L2T).toSetValuedOperator + A).range = Set.univ) :
    Maximal IsMonotone A := by
  rw [maximal_iff_mem_iff]
  intro x u
  constructor
  · intro hxu y v hv
    exact (isMonotone_iff A).1 hA hxu hv
  · intro hMinty
    have hxu_range : x + u ∈ (((id : L2T → L2T).toSetValuedOperator + A).range) := by
      simpa [hrange]
    rcases
        (SetValuedOperator.mem_range_iff (((id : L2T → L2T).toSetValuedOperator + A)) (x + u)).1
          hxu_range with
      ⟨y, hy⟩
    change x + u ∈ ((id : L2T → L2T).toSetValuedOperator y + A y) at hy
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hy
    rcases hy with ⟨z, hz, v, hv, hzv⟩
    have hz' : z = y := by
      simpa using hz
    subst z
    have hzv' : y + v = x + u := by
      simpa [hz'] using hzv
    have hrel : 0 ≤ ⟪x - y, u - v⟫_ℝ := hMinty hv
    have hresid : u - v = y - x := by
      have hzero : u - v + (x - y) = 0 := by
        have : x + u - (y + v) = 0 := by
          rw [hzv']
          abel_nf
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hzero' : (u - v) - (y - x) = 0 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
      exact sub_eq_zero.mp hzero'
    have hsq_nonpos : ‖x - y‖ ^ (2 : ℕ) ≤ 0 := by
      have hnonneg : 0 ≤ -‖x - y‖ ^ (2 : ℕ) := by
        calc
          0 ≤ ⟪x - y, u - v⟫_ℝ := hrel
          _ = ⟪x - y, y - x⟫_ℝ := by
            rw [hresid]
          _ = -⟪x - y, x - y⟫_ℝ := by
            have hyx : y - x = -(x - y) := by
              abel_nf
            rw [hyx, inner_neg_right]
          _ = -‖x - y‖ ^ (2 : ℕ) := by
            rw [real_inner_self_eq_norm_sq]
      linarith
    have hsq_zero : ‖x - y‖ ^ (2 : ℕ) = 0 := by
      exact le_antisymm hsq_nonpos (sq_nonneg ‖x - y‖)
    have hxy : x = y := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero))
    have huv : u = v := by
      calc
        u = x + u - x := by
          abel_nf
        _ = y + v - x := by
          rw [← hzv']
        _ = v := by
          rw [hxy]
          abel_nf
    subst y
    simpa [huv] using hv

/-- Helper for Proposition 21.4: membership in the range of
`(id : L²([0,T]; H) → L²([0,T]; H)).toSetValuedOperator + timeDerivativeOperator T (.initial x0)`
is exactly the existence of a Sobolev representative with prescribed left endpoint solving
`u = f.toLp + f.deriv`. -/
lemma mem_range_id_add_timeDerivativeOperator_initial_iff (u : L2T) :
    u ∈ (((id : L2T → L2T).toSetValuedOperator + timeDerivativeOperator T (.initial x0)).range) ↔
      ∃ f : W12T, f.toContinuousMap (leftEndpoint T) = x0 ∧ u = f.toLp + f.deriv := by
  constructor
  · intro hu
    -- Rewrite Minty's range condition into a single Sobolev graph witness.
    rcases (SetValuedOperator.mem_range_iff
      (((id : L2T → L2T).toSetValuedOperator + timeDerivativeOperator T (.initial x0))) u).1 hu with
      ⟨x, hx⟩
    change u ∈ ((id : L2T → L2T).toSetValuedOperator x + timeDerivativeOperator T (.initial x0) x)
      at hx
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hx
    rcases hx with ⟨y, hy, x', hx', hyx'⟩
    have hy' : y = x := by
      simpa using hy
    subst y
    rcases (mem_timeDerivativeOperator_initial_iff (T := T) x0 x x').1 hx' with
      ⟨f, hfLp, hf0, hfDeriv⟩
    subst x x'
    refine ⟨f, hf0, ?_⟩
    simpa using hyx'.symm
  · rintro ⟨f, hf0, hu⟩
    -- Package the Sobolev witness back into Minty's range relation.
    refine (SetValuedOperator.mem_range_iff
      (((id : L2T → L2T).toSetValuedOperator + timeDerivativeOperator T (.initial x0))) u).2 ?_
    refine ⟨f.toLp, ?_⟩
    change u ∈ ((id : L2T → L2T).toSetValuedOperator f.toLp +
      timeDerivativeOperator T (.initial x0) f.toLp)
    rw [Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨f.toLp, by simp, f.deriv, ?_, ?_⟩
    · exact (mem_timeDerivativeOperator_initial_iff (T := T) x0 f.toLp f.deriv).2
        ⟨f, rfl, hf0, rfl⟩
    · simpa [hu]

/-- Helper for Proposition 21.4: scalarizing the explicit integrating-factor formula against a
fixed vector `z` turns the Bochner interval integral into the corresponding real-valued integral.
-/
lemma integratingFactorPath_innerFormula
    (u : L2T) (Fc : C(IccT, H))
    (hFc :
      ∀ t : IccT,
        Fc t =
          Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ),
                Real.exp s •
                  Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r) s))
    (z : H) (t : IccT) :
    ⟪Fc t, z⟫_ℝ =
      Real.exp (-(t : ℝ)) *
        (⟪x0, z⟫_ℝ +
          ∫ s in 0..(t : ℝ),
            Real.exp s *
              ⟪Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r) s, z⟫_ℝ) := by
  let extendedInput : ℝ → H :=
    Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r)
  let weightedInput : ℝ → H := fun s ↦ Real.exp s • extendedInput s
  have hExtended_int :
      IntervalIntegrable extendedInput volume 0 (t : ℝ) :=
    intervalIntegrable_IccExtend_of_memLp_witness (T := T)
      (h := fun r : IccT ↦ (u : IccT → H) r) (Lp.memLp u) t
  have hWeighted_int : IntervalIntegrable weightedInput volume 0 (t : ℝ) := by
    -- The exponential weight is continuous on `[0,t]`, so it preserves interval integrability.
    refine hExtended_int.continuousOn_smul ?_
    simpa [Set.uIcc_of_le t.2.1] using Real.continuous_exp.continuousOn
  have hInnerIntegral :
      ⟪∫ s in 0..(t : ℝ), weightedInput s, z⟫_ℝ =
        ∫ s in 0..(t : ℝ), ⟪weightedInput s, z⟫_ℝ := by
    -- Commute the scalar-valued continuous linear functional with the interval integral once.
    calc
      ⟪∫ s in 0..(t : ℝ), weightedInput s, z⟫_ℝ =
          ⟪z, ∫ s in 0..(t : ℝ), weightedInput s⟫_ℝ := by
        rw [real_inner_comm]
      _ = ∫ s in 0..(t : ℝ), ⟪z, weightedInput s⟫_ℝ := by
        simpa using
          (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ z) hWeighted_int).symm
      _ = ∫ s in 0..(t : ℝ), ⟪weightedInput s, z⟫_ℝ := by
        apply intervalIntegral.integral_congr
        intro s hs
        simp [real_inner_comm]
  -- Apply the fixed inner-product functional to the explicit path formula.
  calc
    ⟪Fc t, z⟫_ℝ =
        ⟪Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ), weightedInput s), z⟫_ℝ := by
          -- Replace `Fc` by its explicit integrating-factor formula.
          exact congrArg (fun v : H ↦ ⟪v, z⟫_ℝ) (hFc t)
    _ = Real.exp (-(t : ℝ)) *
          (⟪x0, z⟫_ℝ + ⟪∫ s in 0..(t : ℝ), weightedInput s, z⟫_ℝ) := by
          -- Pull the scalar factor through the inner product and split the sum.
          rw [real_inner_smul_left, inner_add_left, mul_add]
    _ = Real.exp (-(t : ℝ)) *
          (⟪x0, z⟫_ℝ +
            ∫ s in 0..(t : ℝ), ⟪weightedInput s, z⟫_ℝ) := by
          -- Rewrite the Bochner integral coordinatewise.
          rw [hInnerIntegral]
    _ = Real.exp (-(t : ℝ)) *
          (⟪x0, z⟫_ℝ +
            ∫ s in 0..(t : ℝ),
              Real.exp s *
                ⟪Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r) s, z⟫_ℝ) := by
          -- Unfold the weighted input inside the scalar integral.
          simp [weightedInput, extendedInput, real_inner_smul_left]

/-- Helper for Proposition 21.4: composing an interval-integrable Hilbert-valued function with the
right-inner-product functional yields an interval-integrable real-valued coordinate. -/
lemma intervalIntegrable_inner_right
    {a b : ℝ} {f : ℝ → H} (hf : IntervalIntegrable f volume a b) (z : H) :
    IntervalIntegrable (fun s ↦ ⟪f s, z⟫_ℝ) volume a b := by
  -- Rewrite interval integrability on `uIoc` and compose with the continuous linear functional
  -- `x ↦ ⟪x, z⟫`.
  rw [intervalIntegrable_iff] at hf ⊢
  simpa [Function.comp, real_inner_comm] using
    ContinuousLinearMap.integrableOn_comp (innerSL ℝ z) hf

/-- Helper for Proposition 21.4: the right-inner-product functional commutes with the interval
integral of an interval-integrable Hilbert-valued path. -/
lemma inner_intervalIntegral_right
    {a b : ℝ} {f : ℝ → H} (hf : IntervalIntegrable f volume a b) (z : H) :
    ⟪∫ s in a..b, f s, z⟫_ℝ = ∫ s in a..b, ⟪f s, z⟫_ℝ := by
  -- Commute the continuous linear functional `x ↦ ⟪x, z⟫` with the interval integral once.
  calc
    ⟪∫ s in a..b, f s, z⟫_ℝ = ⟪z, ∫ s in a..b, f s⟫_ℝ := by
      rw [real_inner_comm]
    _ = ∫ s in a..b, ⟪z, f s⟫_ℝ := by
      simpa using
        (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ z) hf).symm
    _ = ∫ s in a..b, ⟪f s, z⟫_ℝ := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp [real_inner_comm]

/-- Helper for Proposition 21.4: the scalar integrating-factor identity on `[0,t]` rewrites the
explicit formula into the Volterra integral criterion. -/
lemma scalarIntegratingFactorIntervalCriterion
    (a t : ℝ) (g : ℝ → ℝ) (ht : 0 ≤ t)
    (hg : IntervalIntegrable (fun s ↦ Real.exp s * g s) volume 0 t) :
    Real.exp (-t) * (a + ∫ s in 0..t, Real.exp s * g s) =
      a +
        ∫ s in 0..t,
          (g s - Real.exp (-s) * (a + ∫ r in 0..s, Real.exp r * g r)) := by
  -- Route correction: use interval primitives for both factors so the integration-by-parts step
  -- stays in the absolutely-continuous API and only rewrites back to `Real.exp (-·)` afterward.
  let G : ℝ → ℝ := fun s ↦ a + ∫ r in 0..s, Real.exp r * g r
  let E : ℝ → ℝ := fun s ↦ Real.exp (-s)
  have hZero_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 t := by
    simpa [Set.uIcc_of_le ht]
  have hExpInt : IntervalIntegrable (fun s ↦ Real.exp (-s)) volume 0 t := by
    -- We will also need the unsigned exponential factor for the final `integral_sub` step.
    exact ((Real.continuous_exp.comp continuous_id.neg).continuousOn.intervalIntegrable)
  have hConstAC (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) 0 t := by
    -- Constant functions are Lipschitz, hence absolutely continuous on every interval.
    have hLip : LipschitzOnWith 0 (fun _ : ℝ ↦ c) (Set.uIcc 0 t) :=
      (LipschitzWith.const' (α := ℝ) (β := ℝ) c).lipschitzOnWith
    simpa using hLip.absolutelyContinuousOnInterval (a := 0) (b := t)
  have hGac : AbsolutelyContinuousOnInterval G 0 t := by
    -- The weighted primitive is absolutely continuous, and adding the initial datum preserves it.
    change AbsolutelyContinuousOnInterval
      (fun s ↦ a + ∫ r in 0..s, Real.exp r * g r) 0 t
    simpa using (hConstAC a).add (hg.absolutelyContinuousOnInterval_intervalIntegral hZero_mem_uIcc)
  have hEac : AbsolutelyContinuousOnInterval E 0 t := by
    -- On `[0,t]` the derivative `-Real.exp (-x)` has norm at most `1`, so the exponential factor
    -- is `1`-Lipschitz and hence absolutely continuous.
    have hLip : LipschitzOnWith 1 E (Set.uIcc 0 t) := by
      refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (s := Set.uIcc 0 t) (C := 1) ?_ ?_
        (convex_uIcc 0 t)
      · intro x hx
        simpa [E] using Real.differentiableAt_exp.comp x differentiableAt_id.neg
      · intro x hx
        have hx_Icc : x ∈ Set.Icc 0 t := by
          simpa [Set.uIcc_of_le ht] using hx
        have hderiv : deriv E x = -Real.exp (-x) := by
          simpa [E] using ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).deriv
        rw [hderiv, nnnorm_neg]
        have hExpLe : Real.exp (-x) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          linarith [hx_Icc.1]
        have hExpNormLe : ‖Real.exp (-x)‖ ≤ (1 : ℝ) := by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]
          exact hExpLe
        exact_mod_cast hExpNormLe
    simpa using hLip.absolutelyContinuousOnInterval (a := 0) (b := t)
  have hGderiv :
      ∀ᵐ s, s ∈ Set.uIcc 0 t → HasDerivAt G (Real.exp s * g s) s := by
    -- Differentiate the weighted primitive almost everywhere and keep the constant term explicit.
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hs_mem
    simpa [G] using ((hs hs_mem 0 hZero_mem_uIcc).const_add a)
  have hEderiv :
      ∀ᵐ s, s ∈ Set.uIcc 0 t → HasDerivAt E (-Real.exp (-s)) s := by
    -- The exponential factor is differentiable everywhere with the expected derivative.
    filter_upwards with s hs_mem
    simpa [E] using (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
  have hE_eq_expNeg : ∀ s ∈ Set.Icc 0 t, E s = Real.exp (-s) := by
    intro s hs
    simp [E]
  have hExpWeightCancel (s : ℝ) :
      Real.exp (-s) * (Real.exp s * g s) = g s := by
    calc
      Real.exp (-s) * (Real.exp s * g s) = (Real.exp (-s) * Real.exp s) * g s := by
        ring_nf
      _ = g s := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hgInt : IntervalIntegrable g volume 0 t := by
    -- Cancel the exponential weights once to recover interval integrability of `g`.
    have hWeightedToPlain :
        (fun s ↦ Real.exp (-s) * (Real.exp s * g s)) = g := by
      funext s
      exact hExpWeightCancel s
    simpa [hWeightedToPlain] using
      hg.continuousOn_mul ((Real.continuous_exp.comp continuous_id.neg).continuousOn)
  have hCriterionInt :
      IntervalIntegrable (fun s ↦ Real.exp (-s) * G s) volume 0 t := by
    -- The residual coefficient is the product of an integrable exponential and a continuous primitive.
    simpa [G] using hExpInt.mul_continuousOn hGac.continuousOn
  have hLeft :
      ∫ s in 0..t, E s * deriv G s = ∫ s in 0..t, g s := by
    -- Rewrite the left derivative term from integration by parts into the unweighted input.
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hGderiv] with s hs hs_mem
    have hs_Ioc : s ∈ Set.Ioc 0 t := by
      simpa [Set.uIoc_of_le ht] using hs_mem
    have hs_Icc : s ∈ Set.Icc 0 t := Set.Ioc_subset_Icc_self hs_Ioc
    have hs_uIcc : s ∈ Set.uIcc 0 t := Set.uIoc_subset_uIcc hs_mem
    rw [(hs hs_uIcc).deriv, hE_eq_expNeg s hs_Icc, hExpWeightCancel s]
  have hRight :
      ∫ s in 0..t, deriv E s * G s = ∫ s in 0..t, (-Real.exp (-s)) * G s := by
    -- Rewrite the right derivative term into the explicit exponential coefficient.
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hEderiv] with s hs hs_mem
    have hs_uIcc : s ∈ Set.uIcc 0 t := Set.uIoc_subset_uIcc hs_mem
    rw [(hs hs_uIcc).deriv]
  have hIntegrationByParts :
      ∫ s in 0..t, g s =
        Real.exp (-t) * G t - a + ∫ s in 0..t, Real.exp (-s) * G s := by
    -- Apply integration by parts to the two primitives, then normalize boundary and derivative
    -- terms back to the integrating-factor expression.
    calc
      ∫ s in 0..t, g s = ∫ s in 0..t, E s * deriv G s := by
        symm
        exact hLeft
      _ = E t * G t - E 0 * G 0 - ∫ s in 0..t, deriv E s * G s := by
        simpa using hEac.integral_mul_deriv_eq_deriv_mul hGac
      _ = Real.exp (-t) * G t - E 0 * G 0 - ∫ s in 0..t, (-Real.exp (-s)) * G s := by
        rw [hE_eq_expNeg t ⟨ht, le_rfl⟩, hRight]
      _ = Real.exp (-t) * G t - a + ∫ s in 0..t, Real.exp (-s) * G s := by
        simp [E, G]
  have hRearranged :
      Real.exp (-t) * G t =
        a + ((∫ s in 0..t, g s) - ∫ s in 0..t, Real.exp (-s) * G s) := by
    -- Move the integral term to the right-hand side to match the Volterra criterion.
    let boundary : ℝ := Real.exp (-t) * G t
    let sourceInt : ℝ := ∫ s in 0..t, g s
    let residualInt : ℝ := ∫ s in 0..t, Real.exp (-s) * G s
    have hLinear : sourceInt = boundary - a + residualInt := by
      simpa [boundary, sourceInt, residualInt] using hIntegrationByParts
    have hSolve : boundary = a + sourceInt - residualInt := by
      linarith
    calc
      Real.exp (-t) * G t = (a + ∫ s in 0..t, g s) - ∫ s in 0..t, Real.exp (-s) * G s := by
        simpa [boundary, sourceInt, residualInt] using hSolve
      _ = a + ((∫ s in 0..t, g s) - ∫ s in 0..t, Real.exp (-s) * G s) := by
        abel_nf
  calc
    Real.exp (-t) * (a + ∫ s in 0..t, Real.exp s * g s) = Real.exp (-t) * G t := by
      simp [G]
    _ = a + ((∫ s in 0..t, g s) - ∫ s in 0..t, Real.exp (-s) * G s) := by
      exact hRearranged
    _ = a + ∫ s in 0..t, (g s - Real.exp (-s) * G s) := by
      exact congrArg (fun x : ℝ => a + x) (intervalIntegral.integral_sub hgInt hCriterionInt).symm
    _ =
        a +
          ∫ s in 0..t,
            (g s - Real.exp (-s) * (a + ∫ r in 0..s, Real.exp r * g r)) := by
      simp [G]

/-- Helper for Proposition 21.4: each scalar coordinate of the integrating-factor path satisfies
the interval-integral criterion for the residual witness `u - Fc`. -/
lemma integratingFactorPath_innerIntegralCriterion
    (u : L2T) (Fc : C(IccT, H))
    (hFc :
      ∀ t : IccT,
        Fc t =
          Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ),
                Real.exp s •
                  Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r) s))
    (z : H) (t : IccT) :
    ⟪Fc t, z⟫_ℝ =
      ⟪x0 +
        ∫ s in 0..(t : ℝ),
          Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r - Fc r) s, z⟫_ℝ := by
  let extendedInput : ℝ → H :=
    Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r)
  let weightedInput : ℝ → H := fun s ↦ Real.exp s • extendedInput s
  let residualInput : ℝ → H :=
    Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r - Fc r)
  let extendedPath : ℝ → H := Set.IccExtend (le_of_lt T.2) Fc
  have hExtended_int :
      IntervalIntegrable extendedInput volume 0 (t : ℝ) :=
    intervalIntegrable_IccExtend_of_memLp_witness (T := T)
      (h := fun r : IccT ↦ (u : IccT → H) r) (Lp.memLp u) t
  have hWeighted_int : IntervalIntegrable weightedInput volume 0 (t : ℝ) := by
    -- The exponential weight is continuous on `[0,t]`, so it preserves interval integrability.
    refine hExtended_int.continuousOn_smul ?_
    simpa [Set.uIcc_of_le t.2.1] using Real.continuous_exp.continuousOn
  have hScalarWeighted_int :
      IntervalIntegrable
        (fun s ↦ Real.exp s * ⟪extendedInput s, z⟫_ℝ) volume 0 (t : ℝ) := by
    -- Reduce the weighted scalar coordinate to the right-inner-product image of the weighted path.
    simpa [weightedInput, extendedInput, real_inner_smul_left] using
      intervalIntegrable_inner_right (H := H) hWeighted_int z
  have hExtendedPath_int : IntervalIntegrable extendedPath volume 0 (t : ℝ) := by
    -- The continuous path `Fc` stays interval integrable after ambient interval extension.
    exact (Fc.continuous.Icc_extend' (h := le_of_lt T.2)).intervalIntegrable _ _
  have hResidualEq : residualInput = fun s ↦ extendedInput s - extendedPath s := by
    -- All three interval extensions use the same interval projection, so subtraction commutes.
    funext s
    rfl
  have hResidual_int : IntervalIntegrable residualInput volume 0 (t : ℝ) := by
    -- Package the residual as the difference between the extended source input and the extended
    -- continuous path.
    rw [hResidualEq]
    exact hExtended_int.sub hExtendedPath_int
  -- Instantiate the scalar integrating-factor identity with the coordinate function
  -- `s ↦ ⟪extendedInput s, z⟫`.
  calc
    ⟪Fc t, z⟫_ℝ =
        Real.exp (-((t : IccT) : ℝ)) *
          (⟪x0, z⟫_ℝ +
            ∫ s in 0..(t : ℝ), Real.exp s * ⟪extendedInput s, z⟫_ℝ) := by
      simpa [extendedInput] using
        integratingFactorPath_innerFormula (T := T) (x0 := x0) u Fc hFc z t
    _ =
        ⟪x0, z⟫_ℝ +
          ∫ s in 0..(t : ℝ),
            (⟪extendedInput s, z⟫_ℝ -
              Real.exp (-s) *
                (⟪x0, z⟫_ℝ +
                  ∫ r in 0..s, Real.exp r * ⟪extendedInput r, z⟫_ℝ)) := by
      -- Route correction: use the scalar integrating-factor identity directly instead of the
      -- earlier uniqueness-of-AC-solutions detour.
      simpa [extendedInput] using
        scalarIntegratingFactorIntervalCriterion (a := ⟪x0, z⟫_ℝ) (t := (t : ℝ))
          (g := fun s ↦ ⟪extendedInput s, z⟫_ℝ) t.2.1 hScalarWeighted_int
    _ =
        ⟪x0, z⟫_ℝ +
          ∫ s in 0..(t : ℝ), ⟪residualInput s, z⟫_ℝ := by
      -- Rewrite the scalar residual by evaluating the explicit integrating-factor formula for
      -- `Fc` at the running time `s`.
      apply congrArg
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := by
        simpa [Set.uIcc_of_le t.2.1] using (Set.uIoc_subset_uIcc hs)
      have hsIccT : s ∈ IccT := ⟨hsIcc.1, le_trans hsIcc.2 t.2.2⟩
      let st : IccT := ⟨s, hsIccT⟩
      have hFcst :
          Real.exp (-s) *
              (⟪x0, z⟫_ℝ +
                ∫ r in 0..s, Real.exp r * ⟪extendedInput r, z⟫_ℝ) =
            ⟪Fc st, z⟫_ℝ := by
        simpa [extendedInput, st] using
          (integratingFactorPath_innerFormula (T := T) (x0 := x0) u Fc hFc z st).symm
      calc
        ⟪extendedInput s, z⟫_ℝ -
            Real.exp (-s) *
              (⟪x0, z⟫_ℝ +
                ∫ r in 0..s, Real.exp r * ⟪extendedInput r, z⟫_ℝ) =
            ⟪extendedInput s, z⟫_ℝ - ⟪Fc st, z⟫_ℝ := by
          rw [hFcst]
        _ = ⟪extendedInput s - Fc st, z⟫_ℝ := by
          rw [inner_sub_left]
        _ = ⟪residualInput s, z⟫_ℝ := by
          rw [hResidualEq]
          simp [extendedPath, st, Set.IccExtend_of_mem (h := le_of_lt T.2) (f := Fc) hsIccT]
    _ = ⟪x0 + ∫ s in 0..(t : ℝ), residualInput s, z⟫_ℝ := by
      -- Reassemble the coordinatewise identity back into the right-inner-product of the residual
      -- interval integral.
      symm
      rw [inner_add_left, inner_intervalIntegral_right (H := H) hResidual_int z]

/-- Helper for Proposition 21.4: the explicit integrating-factor path
`t ↦ exp (-t) • (x0 + ∫ s in 0..t, exp s • u(s))` satisfies the Sobolev integral criterion with
residual witness `u - F`. -/
lemma integratingFactorPath_integralCriterion
    (u : L2T) (Fc : C(IccT, H))
    (hFc :
      ∀ t : IccT,
        Fc t =
          Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ),
                Real.exp s •
                  Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r) s)) :
    ∀ t : IccT,
      Fc t =
        x0 +
          ∫ s in 0..(t : ℝ),
            Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r - Fc r) s := by
  intro t
  -- Reduce the vector identity to equality on every inner-product coordinate.
  apply ext_inner_right ℝ
  intro z
  simpa using integratingFactorPath_innerIntegralCriterion (T := T) (x0 := x0) u Fc hFc z t

lemma initialTimeDerivativeSolution_exists (u : L2T) :
    ∃ f : W12T, f.toContinuousMap (leftEndpoint T) = x0 ∧ u = f.toLp + f.deriv := by
  -- Route correction: the weighted-input construction only gives an a.e. derivative, so the
  -- proof must be expressed through the integral criterion defining `SobolevW12`.
  let extendedInput : ℝ → H :=
    Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r)
  let weightedInput : ℝ → H := fun s ↦ Real.exp s • extendedInput s
  have h0T : (0 : ℝ) ≤ (T : ℝ) := le_of_lt T.2
  have hExtendedInput_int : IntervalIntegrable extendedInput volume 0 (T : ℝ) :=
    intervalIntegrable_IccExtend_full_of_memLp_witness (T := T)
      (h := fun r : IccT ↦ (u : IccT → H) r) (Lp.memLp u)
  have hWeightedInput_int : IntervalIntegrable weightedInput volume 0 (T : ℝ) := by
    -- The scalar weight `exp` is continuous on `[0,T]`, so it preserves interval integrability.
    refine hExtendedInput_int.continuousOn_smul ?_
    simpa [Set.uIcc_of_le h0T] using Real.continuous_exp.continuousOn
  have hPrimitive_contOn :
      ContinuousOn (fun t : ℝ => ∫ s in 0..t, weightedInput s) (Set.uIcc (0 : ℝ) (T : ℝ)) := by
    -- The weighted primitive is continuous on the ambient source interval.
    exact intervalIntegral.continuousOn_primitive_interval' hWeightedInput_int
      (by simpa [Set.uIcc_of_le h0T] using h0T)
  have hPrimitive_cont : Continuous fun t : IccT => ∫ s in 0..((t : IccT) : ℝ), weightedInput s :=
    by
    -- Restrict the ambient primitive to the subtype interval `[0,T]`.
    refine hPrimitive_contOn.comp_continuous continuous_subtype_val ?_
    intro t
    simpa [Set.uIcc_of_le h0T] using t.2
  let primitive : C(IccT, H) := ContinuousMap.mk
    (fun t : IccT => ∫ s in 0..(t : ℝ), weightedInput s) hPrimitive_cont
  have hPath_cont :
      Continuous fun t : IccT => Real.exp (-((t : IccT) : ℝ)) • (x0 + primitive t) := by
    -- The integrating-factor formula is continuous because both the exponential weight and the
    -- primitive are continuous on the compact source interval.
    refine (Real.continuous_exp.comp ?_).smul ((continuous_const).add primitive.continuous)
    exact continuous_subtype_val.neg
  let Fc : C(IccT, H) := ContinuousMap.mk
    (fun t : IccT => Real.exp (-(t : ℝ)) • (x0 + primitive t)) hPath_cont
  have hFc :
      ∀ t : IccT,
        Fc t =
          Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ),
                Real.exp s •
                  Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (u : IccT → H) r) s) := by
    -- Unfold the path definition back to the source integrating-factor formula.
    intro t
    rfl
  let FcLp : L2T := Fc.toLp 2 (volume : Measure IccT) ℝ
  have hResidual_ae :
      (fun r : IccT ↦ (u : IccT → H) r - Fc r) =ᵐ[volume]
        fun r : IccT ↦ (((u - FcLp : L2T) r) : H) := by
    -- The explicit residual path agrees a.e. with the coercion of the `L²` residual class.
    symm
    exact (Lp.coeFn_sub u FcLp).trans
      ((Filter.EventuallyEq.rfl.sub
        (ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure IccT)) (𝕜 := ℝ) Fc)))
  have hResidual_mem :
      MemLp (fun r : IccT ↦ (u : IccT → H) r - Fc r) 2 (volume : Measure IccT) := by
    -- Transfer the `L²` residual class back to the explicit pointwise residual witness.
    refine (Lp.memLp (u - FcLp)).congr_norm ?_ ?_
    · exact (Lp.aestronglyMeasurable u).sub Fc.continuous.aestronglyMeasurable
    · filter_upwards [hResidual_ae] with r hr
      simpa [hr]
  have hResidual_toLp :
      hResidual_mem.toLp (fun r : IccT ↦ (u : IccT → H) r - Fc r) = u - FcLp := by
    -- The explicit residual witness represents exactly the residual `L²` class.
    calc
      hResidual_mem.toLp (fun r : IccT ↦ (u : IccT → H) r - Fc r) =
          (Lp.memLp (u - FcLp)).toLp (fun r : IccT ↦ (((u - FcLp : L2T) r) : H)) := by
        exact MeasureTheory.MemLp.toLp_congr hResidual_mem (Lp.memLp (u - FcLp)) hResidual_ae
      _ = u - FcLp := by
        exact MeasureTheory.Lp.toLp_coeFn (u - FcLp) (Lp.memLp (u - FcLp))
  have hFc0 : Fc (leftEndpoint T) = x0 := by
    -- Evaluating the integrating-factor formula at `t = 0` collapses the interval integral.
    simpa [leftEndpoint] using hFc (leftEndpoint T)
  let f : W12T :=
    { toContinuousMap := Fc
      deriv := u - FcLp
      hasL2DerivativeOnIcc := by
        refine ⟨fun r : IccT ↦ (u : IccT → H) r - Fc r, hResidual_mem, hResidual_toLp, ?_⟩
        -- The remaining Sobolev witness is exactly the Volterra identity for the integrating path.
        intro t
        calc
          Fc t = x0 + ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2)
              (fun r : IccT ↦ (u : IccT → H) r - Fc r) s := by
            exact integratingFactorPath_integralCriterion (T := T) (x0 := x0) u Fc hFc t
          _ = Fc (leftEndpoint T) +
              ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2)
                (fun r : IccT ↦ (u : IccT → H) r - Fc r) s := by
            rw [← hFc0]
          _ = Fc ⟨0, ⟨le_rfl, le_of_lt T.2⟩⟩ +
              ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2)
                (fun r : IccT ↦ (u : IccT → H) r - Fc r) s := by
            rfl }
  have hu : u = FcLp + (u - FcLp) := by
    -- Rearrange the residual identity back to the Minty range normal form.
    abel_nf
  refine ⟨f, hFc0, ?_⟩
  simpa [f, FcLp] using hu

/-- Helper for Proposition 21.4: the Minty range of
`Id + timeDerivativeOperator T (.initial x0)` is all of `L²([0,T]; H)`. -/
lemma range_id_add_timeDerivativeOperator_initial_eq_univ :
    (((id : L2T → L2T).toSetValuedOperator + timeDerivativeOperator T (.initial x0)).range) =
      Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    -- Solve the range goal using the explicit Sobolev witness from the previous lemma.
    rcases initialTimeDerivativeSolution_exists (T := T) (x0 := x0) u with ⟨f, hf0, hu⟩
    exact (mem_range_id_add_timeDerivativeOperator_initial_iff (T := T) (x0 := x0) u).2
      ⟨f, hf0, hu⟩

/-- Proposition 21.4: if `H` is a separable real Hilbert space, `x₀ : H`, and `T > 0`, then the
time-derivative operator on `L²([0,T]; H)` with boundary condition `x(0) = x₀`, formalized as
`timeDerivativeOperator T (.initial x0)`, is maximally monotone. -/
theorem timeDerivativeOperator_initial_isMaximallyMonotone
    (T : Set.Ioi (0 : ℝ)) (x0 : H) :
    Maximal IsMonotone (timeDerivativeOperator T (.initial x0)) := by
  -- Apply Minty's characterization and discharge surjectivity through the dedicated range lemma.
  exact maximal_of_range_id_add_eq_univ (T := T)
    (A := timeDerivativeOperator T (.initial x0))
    (timeDerivativeOperator_isMonotone T (.initial x0))
    (range_id_add_timeDerivativeOperator_initial_eq_univ (T := T) (x0 := x0))

end SetValuedOperator
