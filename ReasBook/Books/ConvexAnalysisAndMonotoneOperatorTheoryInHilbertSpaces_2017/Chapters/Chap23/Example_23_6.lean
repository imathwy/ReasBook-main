import BauschkeLean.Chap20.Example_20_9
import BauschkeLean.Chap21.Proposition_21_4
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2

open MeasureTheory intervalIntegral
open ERealFunction
open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

attribute [local instance] Measure.Subtype.measureSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
variable (T : Set.Ioi (0 : ℝ)) (x0 : E)

local notation "IccT" => Set.Icc (0 : ℝ) (T : ℝ)
local notation "L2T" => MeasureTheory.Lp E 2 (volume : Measure IccT)
local notation "W12T" => SobolevW12 E T

local instance : IsFiniteMeasure (volume : Measure IccT) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

/- This file uses the Chapter 20 source-facing owner `timeDerivativeOperator T (.initial x0)`
together with the Chapter 23 resolvent owner `J[...]`. -/

/-- The Volterra formula for the resolvent path of the initial-value time-derivative operator at
`x`. -/
noncomputable def initialTimeDerivativeResolventPathFun (x : L2T) : IccT → E :=
  fun t ↦
    Real.exp (-(t : ℝ)) • x0 +
      ∫ s in 0..(t : ℝ),
        Real.exp (s - (t : ℝ)) •
          Set.IccExtend (le_of_lt T.2) (fun u : IccT ↦ x u) s

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
/-- Helper for Example 23.6: the displayed Volterra formula is the Chapter 21 integrating-factor
path written in source-facing form. -/
lemma initialTimeDerivativeResolventPathFun_eq_integratingFactor (x : L2T) (t : IccT) :
    initialTimeDerivativeResolventPathFun T x0 x t =
      Real.exp (-(t : ℝ)) •
        (x0 +
          ∫ s in 0..(t : ℝ),
            Real.exp s • Set.IccExtend (le_of_lt T.2) (fun u : IccT ↦ x u) s) := by
  -- Factor the common exponential weight out of the Volterra integral once and for all.
  rw [initialTimeDerivativeResolventPathFun, smul_add, ← intervalIntegral.integral_smul]
  apply congrArg₂ (· + ·) rfl
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with s
  simp [sub_eq_add_neg, Real.exp_add, smul_smul, mul_comm]

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
/-- Helper for Example 23.6: the explicit Volterra path starts at the prescribed initial value
`x0`. -/
lemma initialTimeDerivativeResolventPathFun_leftEndpoint (x : L2T) :
    initialTimeDerivativeResolventPathFun T x0 x (leftEndpoint T) = x0 := by
  -- At the left endpoint, the interval integral vanishes and the exponential factor is `1`.
  simp [initialTimeDerivativeResolventPathFun, leftEndpoint]

/-- Helper for Example 23.6: the Volterra formula defines a Sobolev path whose residual class is
`x - f.toLp`. -/
lemma exists_initialTimeDerivativeResolventPath (x : L2T) :
    ∃ f : W12T,
      (∀ t : IccT,
        f.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t) ∧
        f.deriv = x - f.toLp := by
  -- Route correction: reuse the Chapter 21 integrating-factor construction, but package the
  -- resulting Sobolev path against the Chapter 23 Volterra formula.
  let extendedInput : ℝ → E :=
    Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (x : IccT → E) r)
  let weightedInput : ℝ → E := fun s ↦ Real.exp s • extendedInput s
  have h0T : (0 : ℝ) ≤ (T : ℝ) := le_of_lt T.2
  have hExtendedInput_int : IntervalIntegrable extendedInput volume 0 (T : ℝ) :=
    intervalIntegrable_IccExtend_full_of_memLp_witness (T := T)
      (h := fun r : IccT ↦ (x : IccT → E) r) (Lp.memLp x)
  have hWeightedInput_int : IntervalIntegrable weightedInput volume 0 (T : ℝ) := by
    -- The continuous exponential weight preserves interval integrability.
    refine hExtendedInput_int.continuousOn_smul ?_
    simpa [Set.uIcc_of_le h0T] using Real.continuous_exp.continuousOn
  have hPrimitive_contOn :
      ContinuousOn (fun t : ℝ => ∫ s in 0..t, weightedInput s) (Set.uIcc (0 : ℝ) (T : ℝ)) := by
    -- The weighted primitive is continuous on the ambient interval.
    exact intervalIntegral.continuousOn_primitive_interval' hWeightedInput_int
      (by simpa [Set.uIcc_of_le h0T] using h0T)
  have hPrimitive_cont :
      Continuous fun t : IccT => ∫ s in 0..((t : IccT) : ℝ), weightedInput s := by
    -- Restrict the ambient primitive back to `[0,T]`.
    refine hPrimitive_contOn.comp_continuous continuous_subtype_val ?_
    intro t
    rw [Set.uIcc_of_le h0T]
    exact t.2
  let primitive : C(IccT, E) := ContinuousMap.mk
    (fun t : IccT => ∫ s in 0..(t : ℝ), weightedInput s) hPrimitive_cont
  have hPath_cont :
      Continuous fun t : IccT => Real.exp (-((t : IccT) : ℝ)) • (x0 + primitive t) := by
    -- The integrating-factor path is continuous because both ingredients are continuous.
    refine (Real.continuous_exp.comp continuous_subtype_val.neg).smul
      ((continuous_const).add primitive.continuous)
  let Fc : C(IccT, E) := ContinuousMap.mk
    (fun t : IccT => Real.exp (-(t : ℝ)) • (x0 + primitive t)) hPath_cont
  have hFc :
      ∀ t : IccT,
        Fc t =
          Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ),
                Real.exp s • Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (x : IccT → E) r) s) := by
    -- Unfold the path definition back to the integrating-factor normal form.
    intro t
    rfl
  let FcLp : L2T := Fc.toLp 2 (volume : Measure IccT) ℝ
  have hResidual_ae :
      (fun r : IccT ↦ (x : IccT → E) r - Fc r) =ᵐ[volume]
        fun r : IccT ↦ (((x - FcLp : L2T) r) : E) := by
    -- The pointwise residual agrees a.e. with the residual `L²` class.
    symm
    exact (Lp.coeFn_sub x FcLp).trans
      ((Filter.EventuallyEq.rfl.sub
        (ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure IccT)) (𝕜 := ℝ) Fc)))
  have hResidual_mem :
      MemLp (fun r : IccT ↦ (x : IccT → E) r - Fc r) 2 (volume : Measure IccT) := by
    -- Transfer the residual `L²` class back to the explicit pointwise witness.
    refine (Lp.memLp (x - FcLp)).congr_norm ?_ ?_
    · exact (Lp.aestronglyMeasurable x).sub Fc.continuous.aestronglyMeasurable
    · filter_upwards [hResidual_ae] with r hr
      rw [hr]
  have hResidual_toLp :
      hResidual_mem.toLp (fun r : IccT ↦ (x : IccT → E) r - Fc r) = x - FcLp := by
    -- The explicit residual function represents exactly the residual `L²` class.
    calc
      hResidual_mem.toLp (fun r : IccT ↦ (x : IccT → E) r - Fc r) =
          (Lp.memLp (x - FcLp)).toLp (fun r : IccT ↦ (((x - FcLp : L2T) r) : E)) := by
        exact MeasureTheory.MemLp.toLp_congr hResidual_mem (Lp.memLp (x - FcLp)) hResidual_ae
      _ = x - FcLp := by
        exact MeasureTheory.Lp.toLp_coeFn (x - FcLp) (Lp.memLp (x - FcLp))
  have hFc0 : Fc (leftEndpoint T) = x0 := by
    -- Evaluating the integrating-factor formula at `t = 0` collapses the interval integral.
    simpa [leftEndpoint] using hFc (leftEndpoint T)
  let f : W12T :=
    { toContinuousMap := Fc
      deriv := x - FcLp
      hasL2DerivativeOnIcc := by
        refine ⟨fun r : IccT ↦ (x : IccT → E) r - Fc r, hResidual_mem, hResidual_toLp, ?_⟩
        -- The Chapter 21 integrating-factor lemma gives the Sobolev integral criterion directly.
        intro t
        calc
          Fc t = x0 + ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2)
              (fun r : IccT ↦ (x : IccT → E) r - Fc r) s := by
            exact integratingFactorPath_integralCriterion (T := T) (x0 := x0) x Fc hFc t
          _ = Fc (leftEndpoint T) +
              ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2)
                (fun r : IccT ↦ (x : IccT → E) r - Fc r) s := by
            rw [← hFc0]
          _ = Fc ⟨0, ⟨le_rfl, le_of_lt T.2⟩⟩ +
              ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2)
                (fun r : IccT ↦ (x : IccT → E) r - Fc r) s := by
            rfl }
  have hFormula :
      ∀ t : IccT,
        f.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t := by
    -- Translate the normal form back to the source-facing Volterra display.
    intro t
    calc
      f.toContinuousMap t =
          Real.exp (-(t : ℝ)) •
            (x0 +
              ∫ s in 0..(t : ℝ),
                Real.exp s • Set.IccExtend (le_of_lt T.2) (fun r : IccT ↦ (x : IccT → E) r) s) := by
        exact hFc t
      _ = initialTimeDerivativeResolventPathFun T x0 x t := by
        exact (initialTimeDerivativeResolventPathFun_eq_integratingFactor
          (T := T) (x0 := x0) x t).symm
  have hResidual :
      f.deriv = x - f.toLp := by
    -- The derivative field was chosen to be the residual of the continuous representative.
    rfl
  exact ⟨f, hFormula, hResidual⟩

/-- Helper for Example 23.6: the displayed Volterra formula determines the canonical `L²` class of
any Sobolev representative. -/
lemma toLp_eq_of_formula {x : L2T} {f g : W12T}
    (hf :
      ∀ t : IccT,
        f.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t)
    (hg :
      ∀ t : IccT,
        g.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t) :
    f.toLp = g.toLp := by
  -- The common pointwise formula identifies the continuous representatives.
  have hcont : f.toContinuousMap = g.toContinuousMap := by
    ext t
    rw [hf t, hg t]
  -- Passing to the canonical `L²` classes preserves that equality.
  simpa [SobolevW12.toLp] using
    congrArg (fun F : C(IccT, E) ↦ F.toLp 2 (volume : Measure IccT) ℝ) hcont

/-- Helper for Example 23.6: the Volterra formula together with the residual identity determines
the Sobolev path uniquely. -/
lemma eq_of_formula_and_residual {x : L2T} {f g : W12T}
    (hf :
      ∀ t : IccT,
        f.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t)
    (hfResidual : f.deriv = x - f.toLp)
    (hg :
      ∀ t : IccT,
        g.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t)
    (hgResidual : g.deriv = x - g.toLp) :
    f = g := by
  -- The shared formula first identifies the continuous representatives and hence their `L²`
  -- classes.
  have hcont : f.toContinuousMap = g.toContinuousMap := by
    ext t
    rw [hf t, hg t]
  have hLp : f.toLp = g.toLp := by
    simpa [SobolevW12.toLp] using
      congrArg (fun F : C(IccT, E) ↦ F.toLp 2 (volume : Measure IccT) ℝ) hcont
  -- Then the residual equations force the derivative classes to agree.
  have hderiv : f.deriv = g.deriv := by
    rw [hfResidual, hgResidual, hLp]
  -- Structure equality now reduces to the two data fields, since the proof field is propositional.
  cases f
  cases g
  cases hcont
  cases hderiv
  rfl

/-- There is a unique Sobolev path whose continuous representative is the Volterra formula and
whose derivative class is the resolvent residual `x - f.toLp`. -/
theorem existsUnique_initialTimeDerivativeResolventPath (x : L2T) :
    ∃! f : W12T,
      (∀ t : IccT,
        f.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t) ∧
        f.deriv = x - f.toLp := by
  -- Build the explicit Sobolev witness from the Volterra path and then prove uniqueness from the
  -- displayed formula plus the residual equation.
  rcases exists_initialTimeDerivativeResolventPath (T := T) (x0 := x0) x with
    ⟨f, hfFormula, hfResidual⟩
  refine ⟨f, ⟨hfFormula, hfResidual⟩, ?_⟩
  intro g hg
  exact eq_of_formula_and_residual (T := T) (x0 := x0) hg.1 hg.2 hfFormula hfResidual

/-- For Example 23.6, the initial-value time-derivative operator on `L²([0,T]; E)` has
resolvent is everywhere defined, i.e.
`(J[timeDerivativeOperator T (.initial x0)]).dom = Set.univ`.
-/
theorem dom_resolvent_timeDerivativeOperator_initial_eq_univ :
    (J[(timeDerivativeOperator T (.initial x0))]).dom = Set.univ :=
  by
    ext x
    constructor
    · intro _
      simp
    · intro _
      -- Use the explicit Volterra witness to realize one resolvent point at every `x`.
      rw [SetValuedOperator.mem_dom_iff]
      rcases exists_initialTimeDerivativeResolventPath (T := T) (x0 := x0) x with
        ⟨f, hfFormula, hfResidual⟩
      have hf0 : f.toContinuousMap (leftEndpoint T) = x0 := by
        -- Evaluating the formula at `t = 0` recovers the prescribed boundary condition.
        rw [hfFormula (leftEndpoint T)]
        exact initialTimeDerivativeResolventPathFun_leftEndpoint (T := T) (x0 := x0) x
      have hA :
          x - f.toLp ∈ timeDerivativeOperator T (.initial x0) f.toLp := by
        -- The witness satisfies the graph relation of the initial-value time-derivative operator.
        refine (mem_timeDerivativeOperator_initial_iff (T := T) x0 f.toLp (x - f.toLp)).2 ?_
        exact ⟨f, rfl, hf0, hfResidual⟩
      have hJ :
          f.toLp ∈ J[((1 : ℝ) • timeDerivativeOperator T (.initial x0))] x := by
        -- Convert the graph relation into resolvent membership at the unscaled parameter `γ = 1`.
        exact (mem_resolvent_smul_iff_sub_mem_smul
          (A := timeDerivativeOperator T (.initial x0)) (γ := (1 : ERealFunction.PosReal))
          (x := x) (p := f.toLp)).2 (by simpa using hA)
      exact ⟨f.toLp, by simpa using hJ⟩

/-- Example 23.6 (2): for every `x ∈ L²([0,T]; E)`, the resolvent value
`J[timeDerivativeOperator T (.initial x0)] x` is exactly the set of `L²` classes carried by
Sobolev paths whose continuous representative is the explicit Volterra formula
`t ↦ exp (-t) • x0 + ∫ s in 0..t, exp (s - t) • x(s)`. -/
theorem resolvent_timeDerivativeOperator_initial_eq_singleton (x : L2T) :
    J[(timeDerivativeOperator T (.initial x0))] x =
      {y | ∃ f : W12T,
        f.toLp = y ∧
          ∀ t : IccT, f.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t} := by
  -- Use the explicit Volterra witness as the common singleton realizer for both sides.
  rcases exists_initialTimeDerivativeResolventPath (T := T) (x0 := x0) x with
    ⟨f, hfFormula, hfResidual⟩
  have hf0 : f.toContinuousMap (leftEndpoint T) = x0 := by
    -- The explicit formula satisfies the initial condition at `t = 0`.
    rw [hfFormula (leftEndpoint T)]
    exact initialTimeDerivativeResolventPathFun_leftEndpoint (T := T) (x0 := x0) x
  have hA :
      x - f.toLp ∈ timeDerivativeOperator T (.initial x0) f.toLp := by
    -- The explicit witness lies in the graph of the time-derivative operator.
    refine (mem_timeDerivativeOperator_initial_iff (T := T) x0 f.toLp (x - f.toLp)).2 ?_
    exact ⟨f, rfl, hf0, hfResidual⟩
  have hfRes :
      f.toLp ∈ J[(timeDerivativeOperator T (.initial x0))] x := by
    -- Convert the graph relation into resolvent membership.
    have hJ :
        f.toLp ∈ J[((1 : ℝ) • timeDerivativeOperator T (.initial x0))] x := by
      exact (mem_resolvent_smul_iff_sub_mem_smul
        (A := timeDerivativeOperator T (.initial x0)) (γ := (1 : ERealFunction.PosReal))
        (x := x) (p := f.toLp)).2 (by simpa using hA)
    simpa using hJ
  have hResolventSingleton :
      J[(timeDerivativeOperator T (.initial x0))] x = ({f.toLp} : Set L2T) := by
    -- Monotonicity collapses any second resolvent point onto the explicit one.
    ext y
    constructor
    · intro hy
      have hyA : x - y ∈ timeDerivativeOperator T (.initial x0) y := by
        have hy' :
            y ∈ J[((1 : ℝ) • timeDerivativeOperator T (.initial x0))] x := by
          simpa using hy
        simpa using
          (mem_resolvent_smul_iff_sub_mem_smul
            (A := timeDerivativeOperator T (.initial x0)) (γ := (1 : ERealFunction.PosReal))
            (x := x) (p := y)).1 hy'
      have hmono :
          0 ≤ inner ℝ (f.toLp - y) ((x - f.toLp) - (x - y)) := by
        exact (isMonotone_iff (timeDerivativeOperator T (.initial x0))).1
          (timeDerivativeOperator_isMonotone T (.initial x0)) hA hyA
      have hmono' : 0 ≤ -(‖f.toLp - y‖ ^ (2 : ℕ)) := by
        have hdiff : (x - f.toLp) - (x - y) = -(f.toLp - y) := by
          abel_nf
        calc
          0 ≤ inner ℝ (f.toLp - y) ((x - f.toLp) - (x - y)) := hmono
          _ = inner ℝ (f.toLp - y) (-(f.toLp - y)) := by rw [hdiff]
          _ = -(‖f.toLp - y‖ ^ (2 : ℕ)) := by
            rw [inner_neg_right, real_inner_self_eq_norm_sq]
      have hnorm : ‖f.toLp - y‖ = 0 := by
        by_contra hne
        have hsq_pos : 0 < ‖f.toLp - y‖ ^ (2 : ℕ) := sq_pos_iff.mpr hne
        linarith
      rw [Set.mem_singleton_iff]
      exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      simpa using hfRes
  have hFormulaSingleton :
      {y | ∃ g : W12T,
        g.toLp = y ∧
          ∀ t : IccT, g.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t} =
        ({f.toLp} : Set L2T) := by
    -- The displayed formula determines the continuous representative and hence its `L²` class.
    ext y
    constructor
    · rintro ⟨g, rfl, hgFormula⟩
      rw [Set.mem_singleton_iff]
      exact toLp_eq_of_formula (T := T) (x0 := x0) hgFormula hfFormula
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨f, rfl, hfFormula⟩
  calc
    J[(timeDerivativeOperator T (.initial x0))] x = ({f.toLp} : Set L2T) :=
      hResolventSingleton
    _ =
        {y | ∃ g : W12T,
          g.toLp = y ∧
            ∀ t : IccT, g.toContinuousMap t = initialTimeDerivativeResolventPathFun T x0 x t} := by
      exact hFormulaSingleton.symm

end SetValuedOperator
