import Mathlib
import BauschkeLean.Chap02.Example_2_10
import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory InnerProductSpace

noncomputable section

universe u

namespace SetValuedOperator

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (T : Set.Ioi (0 : ℝ))

local notation "IccT" => Set.Icc (0 : ℝ) (T : ℝ)
local notation "L2T" => MeasureTheory.Lp H 2 (volume : Measure IccT)
local notation "W12T" => SobolevW12 H T

/-- The left endpoint `0` of the interval `[0,T]` as a point of `Set.Icc (0 : ℝ) T`. -/
def leftEndpoint : IccT :=
  ⟨0, Set.left_mem_Icc.2 (le_of_lt T.2)⟩

/-- The right endpoint `T` of the interval `[0,T]` as a point of `Set.Icc (0 : ℝ) T`. -/
def rightEndpoint : IccT :=
  ⟨(T : ℝ), Set.right_mem_Icc.2 (le_of_lt T.2)⟩

local instance : IsFiniteMeasure (volume : Measure IccT) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

/-- Boundary conditions from Example 20.9 for the time-derivative operator on `L²([0,T]; H)`. -/
inductive TimeDerivativeBoundaryCondition (H : Type u) where
  /-- The Sobolev representative has prescribed initial value `x0`. -/
  | initial (x0 : H)
  /-- The Sobolev representative is periodic on `[0,T]`. -/
  | periodic

namespace TimeDerivativeBoundaryCondition

variable {T : Set.Ioi (0 : ℝ)}

/-- The boundary condition from Example 20.9 imposed on a Sobolev representative on `[0,T]`. -/
def Holds (bc : TimeDerivativeBoundaryCondition H) (f : SobolevW12 H T) : Prop :=
  match bc with
  | .initial x0 => f.toContinuousMap (leftEndpoint T) = x0
  | .periodic => f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T)

@[simp] theorem holds_initial_iff (x0 : H) (f : SobolevW12 H T) :
    (.initial x0 : TimeDerivativeBoundaryCondition H).Holds f ↔
      f.toContinuousMap (leftEndpoint T) = x0 :=
  Iff.rfl

@[simp] theorem holds_periodic_iff (f : SobolevW12 H T) :
    (TimeDerivativeBoundaryCondition.periodic : TimeDerivativeBoundaryCondition H).Holds f ↔
      f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T) :=
  Iff.rfl

end TimeDerivativeBoundaryCondition

/-- The source domain `D` from Example 20.9: the `L²([0,T]; H)` classes that admit a
`W^{1,2}` representative satisfying the chosen boundary condition. -/
def timeDerivativeDomain (bc : TimeDerivativeBoundaryCondition H) : Set L2T :=
  {x | ∃ f : W12T, f.toLp = x ∧ bc.Holds f}

@[simp] theorem mem_timeDerivativeDomain_iff
    (bc : TimeDerivativeBoundaryCondition H) (x : L2T) :
    x ∈ timeDerivativeDomain T bc ↔ ∃ f : W12T, f.toLp = x ∧ bc.Holds f :=
  Iff.rfl

/-- Helper for Example 20.9: equal `L²` classes on `[0,T]` determine the same continuous Sobolev
representative. -/
lemma toContinuousMap_eq_of_toLp_eq {f g : W12T} (hfg : f.toLp = g.toLp) :
    f.toContinuousMap = g.toContinuousMap := by
  let F : ℝ → H := Set.IccExtend (le_of_lt T.2) f.toContinuousMap
  let G : ℝ → H := Set.IccExtend (le_of_lt T.2) g.toContinuousMap
  -- First rewrite the equality of `L²` classes as almost-everywhere equality on the subtype.
  have hsub :
      f.toContinuousMap =ᵐ[(volume : Measure IccT)] g.toContinuousMap := by
    have hf :
        ((f.toLp : L2T) : IccT → H) =ᵐ[volume] f.toContinuousMap :=
      ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure IccT)) (𝕜 := ℝ)
        f.toContinuousMap
    have hg :
        ((g.toLp : L2T) : IccT → H) =ᵐ[volume] g.toContinuousMap :=
      ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure IccT)) (𝕜 := ℝ)
        g.toContinuousMap
    exact hf.symm.trans (hfg ▸ hg)
  -- Then move to the ambient interval and use the standard a.e.-equality principle on `Icc`.
  have hrest : F =ᵐ[volume.restrict IccT] G := by
    rw [Filter.EventuallyEq, ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [hsub] with t ht
    simpa [F, G] using ht
  have hEq :
      Set.EqOn F G IccT :=
    Measure.eqOn_Icc_of_ae_eq (μ := volume) (a := (0 : ℝ)) (b := (T : ℝ))
      (show (0 : ℝ) ≠ (T : ℝ) from ne_of_lt T.2) hrest
      (by
        simpa [F] using
          ((f.toContinuousMap.continuous.Icc_extend' (h := le_of_lt T.2))).continuousOn)
      (by
        simpa [G] using
          ((g.toContinuousMap.continuous.Icc_extend' (h := le_of_lt T.2))).continuousOn)
  ext t
  -- Finally restrict the ambient equality back to the subtype interval.
  simpa [F, G] using hEq t.2

/-- Example 20.9: the time-derivative operator is the Sobolev graph relation consisting of all
derivative classes `x'` realized by representatives of `x` satisfying the chosen boundary
condition. -/
def timeDerivativeOperator (bc : TimeDerivativeBoundaryCondition H) : SetValuedOperator L2T L2T :=
  fun x ↦ {x' | ∃ f : W12T, f.toLp = x ∧ bc.Holds f ∧ f.deriv = x'}

/-- The source domain `D` is exactly the domain of the time-derivative operator from
Example 20.9. -/
@[simp] theorem mem_dom_timeDerivativeOperator_iff
    (bc : TimeDerivativeBoundaryCondition H) (x : L2T) :
    x ∈ (timeDerivativeOperator T bc).dom ↔ x ∈ timeDerivativeDomain T bc := by
  constructor
  · rintro ⟨x', f, rfl, hbc, rfl⟩
    exact ⟨f, rfl, hbc⟩
  · rintro ⟨f, rfl, hbc⟩
    exact ⟨f.deriv, f, rfl, hbc, rfl⟩

-- Proof sketch: this is just the graph formulation of the operator definition.
/-- Bridge lemma: membership in the time-derivative operator is exactly the existential graph
description in terms of Sobolev representatives satisfying the chosen boundary condition. -/
@[simp] theorem mem_timeDerivativeOperator_iff
    (bc : TimeDerivativeBoundaryCondition H) (x x' : L2T) :
    x' ∈ timeDerivativeOperator T bc x ↔
      ∃ f : W12T, f.toLp = x ∧ bc.Holds f ∧ f.deriv = x' :=
  Iff.rfl

-- Proof sketch: unfold `timeDerivativeOperator`; in the initial-value branch the value set is
-- exactly the derivatives of Sobolev representatives with left endpoint `x0`.
/-- Membership in the initial-value time-derivative operator means being the derivative class of a
Sobolev representative with the prescribed left endpoint. -/
theorem mem_timeDerivativeOperator_initial_iff (x0 : H) (x x' : L2T) :
    x' ∈ timeDerivativeOperator T (.initial x0) x ↔
      ∃ f : W12T,
        f.toLp = x ∧ f.toContinuousMap (leftEndpoint T) = x0 ∧ f.deriv = x' :=
  by
    rw [mem_timeDerivativeOperator_iff]
    simp

-- Proof sketch: unfold `timeDerivativeOperator`; in the periodic branch the value set is exactly
-- the derivatives of Sobolev representatives whose two endpoint values agree.
/-- Membership in the periodic time-derivative operator means being the derivative class of a
Sobolev representative whose endpoint values on `[0,T]` coincide. -/
theorem mem_timeDerivativeOperator_periodic_iff (x x' : L2T) :
    x' ∈ timeDerivativeOperator T .periodic x ↔
      ∃ f : W12T,
        f.toLp = x ∧ f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T) ∧
          f.deriv = x' := by
  rw [mem_timeDerivativeOperator_iff]
  simp

-- Proof sketch: pick Sobolev representatives witnessing `x' ∈ A x` and `y' ∈ A y`, rewrite the
-- monotonicity pairing in `L²([0,T]; H)` as the integral of `⟪f - g, f' - g'⟫`, and use the
-- integration-by-parts identity from the textbook. The boundary term vanishes in the fixed-initial
-- case and is nonnegative in the periodic case because the endpoint differences agree.
section Monotonicity

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 20.9: rewriting the `L²([0,T];H)` graph pairing as the integral of the
pointwise Sobolev pairing. -/
lemma sobolev_pairing_eq_integral (f g : W12T) :
    ⟪f.toLp - g.toLp, f.deriv - g.deriv⟫_ℝ =
      ∫ t : IccT, ⟪f.toContinuousMap t - g.toContinuousMap t,
        (((f.deriv - g.deriv : L2T) t) : H)⟫_ℝ := by
  -- First rewrite the `L²` pairing as the integral of the pointwise inner product.
  rw [MeasureTheory.L2.inner_def]
  -- Then replace the `L²` representatives of the continuous parts by the actual continuous maps.
  have hcont :
      ((f.toLp - g.toLp : L2T) : IccT → H) =ᵐ[volume]
        fun t ↦ f.toContinuousMap t - g.toContinuousMap t := by
    exact (Lp.coeFn_sub f.toLp g.toLp).trans
      ((ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure IccT)) (𝕜 := ℝ)
          f.toContinuousMap).sub
        (ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure IccT)) (𝕜 := ℝ)
          g.toContinuousMap))
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hcont] with t ht
  simpa using congrArg
    (fun z : H => ⟪z, (((f.deriv - g.deriv : L2T) t) : H)⟫_ℝ) ht

/-- Helper for Example 20.9: subtracting the two Sobolev endpoint formulas isolates the single
remaining interval-integral merge step for the difference path. -/
lemma difference_path_eq_leftEndpoint_add_sub_intervalIntegral (f g : W12T) :
    ∃ h₁ : IccT → H, ∃ h₂ : IccT → H,
      ∃ hh₁ : MemLp h₁ 2 (volume : Measure IccT),
      ∃ hh₂ : MemLp h₂ 2 (volume : Measure IccT),
        hh₁.toLp h₁ = f.deriv ∧
          hh₂.toLp h₂ = g.deriv ∧
          ∀ t : IccT,
            f.toContinuousMap t - g.toContinuousMap t =
              (f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T)) +
                ((∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h₁ s) -
                  ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h₂ s) := by
  rcases SobolevW12.exists_eq_leftEndpoint_add_intervalIntegral (T := T) f with
    ⟨h₁, hh₁, hh₁_toLp, hpath₁⟩
  rcases SobolevW12.exists_eq_leftEndpoint_add_intervalIntegral (T := T) g with
    ⟨h₂, hh₂, hh₂_toLp, hpath₂⟩
  refine ⟨h₁, h₂, hh₁, hh₂, hh₁_toLp, hh₂_toLp, ?_⟩
  intro t
  -- Rewrite both source endpoint formulas, then collect the endpoint and integral terms.
  rw [hpath₁ t, hpath₂ t]
  simp [leftEndpoint, sub_eq_add_neg]
  ac_rfl

/-- Helper for Example 20.9: an `L²` witness on `[0,T]` yields interval integrability for its
`Set.IccExtend` representative on every source subinterval `[0,t]`. -/
lemma intervalIntegrable_IccExtend_of_memLp_witness
    {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT)) (t : IccT) :
    IntervalIntegrable (Set.IccExtend (le_of_lt T.2) h) volume 0 (t : ℝ) := by
  -- First view the extended witness as an integrable function on the whole source interval
  -- `[0,T]`, where it agrees with the original subtype function.
  have hIccT : IntegrableOn (Set.IccExtend (le_of_lt T.2) h) IccT volume := by
    rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
    convert (hh.integrable (by norm_num : 1 ≤ (2 : ENNReal))) using 1
    ext x
    simp [Function.comp]
  -- Then restrict that integrable-on-set fact from `[0,T]` down to `[0,t]`.
  have hiff :
      IntervalIntegrable (Set.IccExtend (le_of_lt T.2) h) volume 0 (t : ℝ) ↔
        IntegrableOn (Set.IccExtend (le_of_lt T.2) h) (Set.Icc 0 (t : ℝ)) volume :=
    intervalIntegrable_iff_integrableOn_Icc_of_le (f := Set.IccExtend (le_of_lt T.2) h)
      (μ := volume) (a := 0) (b := (t : ℝ)) t.2.1
  exact hiff.mpr <| IntegrableOn.mono_set hIccT (Set.Icc_subset_Icc le_rfl t.2.2)

/-- Helper for Example 20.9: the same `L²` witness is interval integrable on the full source
interval `[0,T]`. -/
lemma intervalIntegrable_IccExtend_full_of_memLp_witness
    {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT)) :
    IntervalIntegrable (Set.IccExtend (le_of_lt T.2) h) volume 0 (T : ℝ) :=
  intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh (rightEndpoint T)

/-- Helper for Example 20.9: after interval integrability is available, the two interval integrals
from the subtraction witness merge into the interval integral of the difference witness. -/
lemma intervalIntegral_IccExtend_sub_of_memLp_witnesses
    {h₁ h₂ : IccT → H} (hh₁ : MemLp h₁ 2 (volume : Measure IccT))
    (hh₂ : MemLp h₂ 2 (volume : Measure IccT)) (t : IccT) :
    (∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h₁ s) -
      (∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h₂ s) =
        ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) (h₁ - h₂) s := by
  -- Rewrite the left-hand side as one interval integral of the pointwise difference.
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh₁ t)
    (intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh₂ t)]
  -- The two `Set.IccExtend` terms use the same projection, so the pointwise difference is just
  -- the extension of the difference witness.
  have hsub :
      (fun s ↦ Set.IccExtend (le_of_lt T.2) h₁ s - Set.IccExtend (le_of_lt T.2) h₂ s) =
        Set.IccExtend (le_of_lt T.2) (h₁ - h₂) := by
    funext s
    rfl
  rw [hsub]

/-- Helper for Example 20.9: the textbook energy identity for the difference of two Sobolev
representatives on `[0,T]`. -/
lemma difference_path_eq_leftEndpoint_add_intervalIntegral (f g : W12T) :
    ∃ h : IccT → H, ∃ hh : MemLp h 2 (volume : Measure IccT),
      hh.toLp h = f.deriv - g.deriv ∧
        ∀ t : IccT,
          f.toContinuousMap t - g.toContinuousMap t =
            (f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T)) +
              ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s := by
  rcases difference_path_eq_leftEndpoint_add_sub_intervalIntegral (T := T) f g with
    ⟨h₁, h₂, hh₁, hh₂, hh₁_toLp, hh₂_toLp, hpath⟩
  refine ⟨h₁ - h₂, hh₁.sub hh₂, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The `L²` derivative witness for the difference path is the difference of the two witnesses.
    simpa [hh₁_toLp, hh₂_toLp] using MemLp.toLp_sub hh₁ hh₂
  · intro t
    -- Route correction: instead of reopening the coercion-heavy interval-integrability goals
    -- locally, use the dedicated merge lemma proved once for all witnesses.
    rw [hpath t]
    rw [intervalIntegral_IccExtend_sub_of_memLp_witnesses (T := T) hh₁ hh₂ t]

/-- Helper for Example 20.9: the interval-integral witness controls each forward increment of the
path by the integral of the derivative norm. -/
lemma norm_sub_le_intervalIntegral_norm_of_intervalIntegral_witness
    {z : C(IccT, H)} {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT))
    (hz :
      ∀ t : IccT,
        z t =
          z (leftEndpoint T) +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s)
    {a b : IccT} (hab : (a : ℝ) ≤ (b : ℝ)) :
    ‖z b - z a‖ ≤ ∫ s in (a : ℝ)..(b : ℝ), ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
  -- Rewrite the path increment as the interval integral of the witness on `[a,b]`.
  have hsub :
      z b - z a = ∫ s in (a : ℝ)..(b : ℝ), Set.IccExtend (le_of_lt T.2) h s := by
    rw [hz b, hz a, add_sub_add_left_eq_sub]
    simpa using
      intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh b)
        (intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh a)
  -- Then bound the norm of that interval integral by the interval integral of the norm.
  rw [hsub]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- Helper for Example 20.9: the same interval-integral witness gives the textbook increment bound
for the squared norm along the path. -/
lemma abs_norm_sq_sub_le_mul_intervalIntegral_norm_of_intervalIntegral_witness
    {z : C(IccT, H)} {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT))
    (hz :
      ∀ t : IccT,
        z t =
          z (leftEndpoint T) +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s)
    {a b : IccT} (hab : (a : ℝ) ≤ (b : ℝ)) :
    |‖z b‖ ^ (2 : ℕ) - ‖z a‖ ^ (2 : ℕ)| ≤
      (‖z a‖ + ‖z b‖) * ∫ s in (a : ℝ)..(b : ℝ), ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
  -- First rewrite the squared-norm difference as a product of the norm gap and the norm sum.
  have hfactor :
      |‖z b‖ ^ (2 : ℕ) - ‖z a‖ ^ (2 : ℕ)| =
        |‖z b‖ - ‖z a‖| * (‖z a‖ + ‖z b‖) := by
    have hsq :
        ‖z b‖ ^ (2 : ℕ) - ‖z a‖ ^ (2 : ℕ) =
          (‖z b‖ - ‖z a‖) * (‖z b‖ + ‖z a‖) := by
      ring
    have habs :
        |‖z b‖ + ‖z a‖| = ‖z a‖ + ‖z b‖ := by
      rw [abs_of_nonneg (by positivity), add_comm]
    calc
      |‖z b‖ ^ (2 : ℕ) - ‖z a‖ ^ (2 : ℕ)| =
          |(‖z b‖ - ‖z a‖) * (‖z b‖ + ‖z a‖)| := by rw [hsq]
      _ = |‖z b‖ - ‖z a‖| * |‖z b‖ + ‖z a‖| := by rw [abs_mul]
      _ = |‖z b‖ - ‖z a‖| * (‖z a‖ + ‖z b‖) := by rw [habs]
  -- Then combine the reverse triangle inequality with the interval-integral increment bound.
  have hsum_nonneg : 0 ≤ ‖z a‖ + ‖z b‖ := by
    positivity
  calc
    |‖z b‖ ^ (2 : ℕ) - ‖z a‖ ^ (2 : ℕ)| =
        (‖z a‖ + ‖z b‖) * |‖z b‖ - ‖z a‖| := by
      rw [hfactor, mul_comm]
    _ ≤ (‖z a‖ + ‖z b‖) * ‖z b - z a‖ := by
      exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le (z b) (z a)) hsum_nonneg
    _ ≤ (‖z a‖ + ‖z b‖) *
          ∫ s in (a : ℝ)..(b : ℝ), ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_sub_le_intervalIntegral_norm_of_intervalIntegral_witness (T := T) hh hz hab)
        hsum_nonneg

/-- Helper for Example 20.9: the real primitive of the derivative norm is absolutely continuous on
`[0,T]`. -/
lemma norm_intervalIntegral_absolutelyContinuous_of_memLp_witness
    {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT)) :
    AbsolutelyContinuousOnInterval
      (fun u : ℝ => ∫ s in 0..u, ‖Set.IccExtend (le_of_lt T.2) h s‖) 0 (T : ℝ) := by
  -- First make the norm of the witness interval integrable on the full source interval.
  have hnorm :
      IntervalIntegrable (fun s ↦ ‖Set.IccExtend (le_of_lt T.2) h s‖) volume 0 (T : ℝ) := by
    exact (intervalIntegrable_IccExtend_full_of_memLp_witness (T := T) hh).norm
  -- Then apply the standard scalar interval-integral absolute-continuity theorem at basepoint `0`.
  simpa using hnorm.absolutelyContinuousOnInterval_intervalIntegral
    (c := (0 : ℝ)) (by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ (T : ℝ) from le_of_lt T.2)] using
        (Set.left_mem_Icc.2 (show (0 : ℝ) ≤ (T : ℝ) from le_of_lt T.2)))

/-- Helper for Example 20.9: the extended continuous path is uniformly bounded on the compact
interval `[0,T]`. -/
lemma exists_norm_bound_IccExtend_path (z : C(IccT, H)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ Set.uIcc (0 : ℝ) (T : ℝ), ‖Set.IccExtend (le_of_lt T.2) z u‖ ≤ C := by
  -- Extend the continuous path to the ambient interval and take the norm.
  have hcont : Continuous fun u : ℝ => ‖Set.IccExtend (le_of_lt T.2) z u‖ := by
    simpa using (z.continuous.Icc_extend' (h := le_of_lt T.2)).norm
  -- Compactness of `[0,T]` supplies a uniform bound for that real-valued continuous map.
  rcases isCompact_uIcc.exists_bound_of_continuousOn hcont.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu
  exact le_trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC u hu)
    (le_max_left _ _)

/-- Helper for Example 20.9: the ambient `Set.IccExtend` path agrees with the interval-integral
representation on every point of `[0,T]`. -/
lemma iccExtendPath_eq_leftEndpoint_add_intervalIntegral
    {z : C(IccT, H)} {h : IccT → H}
    (hz :
      ∀ t : IccT,
        z t =
          z (leftEndpoint T) +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s)
    {u : ℝ} (hu : u ∈ Set.uIcc (0 : ℝ) (T : ℝ)) :
    Set.IccExtend (le_of_lt T.2) z u =
      z (leftEndpoint T) + ∫ s in 0..u, Set.IccExtend (le_of_lt T.2) h s := by
  -- Restrict the ambient point back to the subtype interval and reuse the witness formula.
  have huIcc : u ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ (T : ℝ) from le_of_lt T.2)] using hu
  simpa [Set.IccExtend_of_mem (h := le_of_lt T.2) z huIcc] using hz ⟨u, huIcc⟩

/-- Helper for Example 20.9: a uniform bound on the path converts the textbook increment estimate
for `‖z‖²` into domination by the scalar primitive of `‖h‖`. -/
lemma normSq_dist_le_two_mul_bound_mul_primitiveDist
    {z : C(IccT, H)} {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT))
    (hz :
      ∀ t : IccT,
        z t =
          z (leftEndpoint T) +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s)
    {C : ℝ} (_hC_nonneg : 0 ≤ C)
    (hC : ∀ u ∈ Set.uIcc (0 : ℝ) (T : ℝ), ‖Set.IccExtend (le_of_lt T.2) z u‖ ≤ C)
    {x y : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) (T : ℝ)) (hy : y ∈ Set.uIcc (0 : ℝ) (T : ℝ)) :
    dist (‖Set.IccExtend (le_of_lt T.2) z x‖ ^ (2 : ℕ))
        (‖Set.IccExtend (le_of_lt T.2) z y‖ ^ (2 : ℕ)) ≤
      (2 * C) *
        dist (∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖)
          (∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖) := by
  have h0T : (0 : ℝ) ≤ (T : ℝ) := le_of_lt T.2
  have hxIcc : x ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
    simpa [Set.uIcc_of_le h0T] using hx
  have hyIcc : y ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
    simpa [Set.uIcc_of_le h0T] using hy
  let x' : IccT := ⟨x, hxIcc⟩
  let y' : IccT := ⟨y, hyIcc⟩
  by_cases hxy : x ≤ y
  · have hnorm_nonneg :
        0 ≤ ∫ s in x..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      exact intervalIntegral.integral_nonneg_of_forall hxy (fun _ ↦ norm_nonneg _)
    have hsub :
        (∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖) -
            ∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ =
          ∫ s in x..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      simpa using
        intervalIntegral.integral_interval_sub_left
          ((intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh y').norm)
          ((intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh x').norm)
    have hprimitive :
        dist (∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖)
            (∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖) =
          ∫ s in x..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      rw [Real.dist_eq, abs_sub_comm, hsub, abs_of_nonneg hnorm_nonneg]
    have hsq :
        dist (‖Set.IccExtend (le_of_lt T.2) z x‖ ^ (2 : ℕ))
            (‖Set.IccExtend (le_of_lt T.2) z y‖ ^ (2 : ℕ)) ≤
            (‖Set.IccExtend (le_of_lt T.2) z x‖ + ‖Set.IccExtend (le_of_lt T.2) z y‖) *
            ∫ s in x..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      rw [Real.dist_eq, abs_sub_comm]
      simpa [x', y', hxIcc, hyIcc, Set.IccExtend_of_mem]
        using
          abs_norm_sq_sub_le_mul_intervalIntegral_norm_of_intervalIntegral_witness
            (T := T) (z := z) (h := h) hh hz (a := x') (b := y') hxy
    have hbound :
        ‖Set.IccExtend (le_of_lt T.2) z x‖ + ‖Set.IccExtend (le_of_lt T.2) z y‖ ≤ 2 * C := by
      have hxC := hC x hx
      have hyC := hC y hy
      linarith
    calc
      dist (‖Set.IccExtend (le_of_lt T.2) z x‖ ^ (2 : ℕ))
          (‖Set.IccExtend (le_of_lt T.2) z y‖ ^ (2 : ℕ)) ≤
          (‖Set.IccExtend (le_of_lt T.2) z x‖ + ‖Set.IccExtend (le_of_lt T.2) z y‖) *
            ∫ s in x..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ := hsq
      _ ≤ (2 * C) * ∫ s in x..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
        exact mul_le_mul_of_nonneg_right hbound hnorm_nonneg
      _ = (2 * C) *
            dist (∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖)
              (∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖) := by
        rw [hprimitive]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hnorm_nonneg :
        0 ≤ ∫ s in y..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      exact intervalIntegral.integral_nonneg_of_forall hyx (fun _ ↦ norm_nonneg _)
    have hsub :
        (∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖) -
            ∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖ =
          ∫ s in y..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      simpa using
        intervalIntegral.integral_interval_sub_left
          ((intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh x').norm)
          ((intervalIntegrable_IccExtend_of_memLp_witness (T := T) hh y').norm)
    have hprimitive :
        dist (∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖)
            (∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖) =
          ∫ s in y..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      rw [Real.dist_eq, hsub, abs_of_nonneg hnorm_nonneg]
    have hsq :
        dist (‖Set.IccExtend (le_of_lt T.2) z x‖ ^ (2 : ℕ))
            (‖Set.IccExtend (le_of_lt T.2) z y‖ ^ (2 : ℕ)) ≤
            (‖Set.IccExtend (le_of_lt T.2) z y‖ + ‖Set.IccExtend (le_of_lt T.2) z x‖) *
            ∫ s in y..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
      rw [Real.dist_eq]
      simpa [x', y', hxIcc, hyIcc, Set.IccExtend_of_mem]
        using
          abs_norm_sq_sub_le_mul_intervalIntegral_norm_of_intervalIntegral_witness
            (T := T) (z := z) (h := h) hh hz (a := y') (b := x') hyx
    have hbound :
        ‖Set.IccExtend (le_of_lt T.2) z y‖ + ‖Set.IccExtend (le_of_lt T.2) z x‖ ≤ 2 * C := by
      have hxC := hC x hx
      have hyC := hC y hy
      linarith
    calc
      dist (‖Set.IccExtend (le_of_lt T.2) z x‖ ^ (2 : ℕ))
          (‖Set.IccExtend (le_of_lt T.2) z y‖ ^ (2 : ℕ)) ≤
          (‖Set.IccExtend (le_of_lt T.2) z y‖ + ‖Set.IccExtend (le_of_lt T.2) z x‖) *
            ∫ s in y..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ := hsq
      _ ≤ (2 * C) * ∫ s in y..x, ‖Set.IccExtend (le_of_lt T.2) h s‖ := by
        exact mul_le_mul_of_nonneg_right hbound hnorm_nonneg
      _ = (2 * C) *
            dist (∫ s in 0..x, ‖Set.IccExtend (le_of_lt T.2) h s‖)
              (∫ s in 0..y, ‖Set.IccExtend (le_of_lt T.2) h s‖) := by
        rw [hprimitive]

/-- Helper for Example 20.9: the scalar path `u ↦ ‖Set.IccExtend z u‖²` is absolutely continuous on
`[0,T]` once the path is represented by an interval integral. -/
lemma normSq_absolutelyContinuous_of_intervalIntegral_witness
    {z : C(IccT, H)} {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT))
    (hz :
      ∀ t : IccT,
        z t =
          z (leftEndpoint T) +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s) :
    AbsolutelyContinuousOnInterval
      (fun u : ℝ => ‖Set.IccExtend (le_of_lt T.2) z u‖ ^ (2 : ℕ)) 0 (T : ℝ) := by
  obtain ⟨C, hC_nonneg, hC⟩ := exists_norm_bound_IccExtend_path (T := T) z
  have hprimitive :
      AbsolutelyContinuousOnInterval
        (fun u : ℝ => ∫ s in 0..u, ‖Set.IccExtend (le_of_lt T.2) h s‖) 0 (T : ℝ) :=
    norm_intervalIntegral_absolutelyContinuous_of_memLp_witness (T := T) hh
  unfold AbsolutelyContinuousOnInterval at hprimitive ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using hprimitive.const_mul (2 * C))
  · exact Filter.Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  · rw [Filter.eventually_inf_principal]
    filter_upwards with (n, I) hI
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ by
      have hIi₁ : (I i).1 ∈ Set.uIcc (0 : ℝ) (T : ℝ) := (hI.1 i hi).1
      have hIi₂ : (I i).2 ∈ Set.uIcc (0 : ℝ) (T : ℝ) := (hI.1 i hi).2
      have hscale :
          (2 * C) *
              dist (∫ s in 0..(I i).1, ‖Set.IccExtend (le_of_lt T.2) h s‖)
                (∫ s in 0..(I i).2, ‖Set.IccExtend (le_of_lt T.2) h s‖) =
            dist ((2 * C) * (∫ s in 0..(I i).1, ‖Set.IccExtend (le_of_lt T.2) h s‖))
              ((2 * C) * (∫ s in 0..(I i).2, ‖Set.IccExtend (le_of_lt T.2) h s‖)) := by
        symm
        simpa [Real.norm_eq_abs, abs_of_nonneg hC_nonneg] using
          dist_smul₀ (2 * C)
            (∫ s in 0..(I i).1, ‖Set.IccExtend (le_of_lt T.2) h s‖)
            (∫ s in 0..(I i).2, ‖Set.IccExtend (le_of_lt T.2) h s‖)
      simpa [hscale] using
        normSq_dist_le_two_mul_bound_mul_primitiveDist
          (T := T) (z := z) (h := h) hh hz hC_nonneg hC hIi₁ hIi₂

/-- Helper for Example 20.9: a locally integrable vector-valued interval primitive has derivative
equal to its integrand almost everywhere. -/
lemma ae_hasDerivAt_intervalIntegral_vector_of_locallyIntegrable
    {f : ℝ → H} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc
  have LDT := (IsUnifLocDoublingMeasure.vitaliFamily (μ := volume) 1).ae_tendsto_average hf
  have hIocIcc {a b : ℝ} : ∫ t in Set.Ioc a b, f t = ∫ t in Set.Icc a b, f t :=
    (integral_Icc_eq_integral_Ioc (x := a) (y := b) (f := f)).symm
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := by grind
    by_cases hxy : y = x
    · simp [slope, average, hxy]
    · simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, hIocIcc]
      -- Route correction: rewrite the right reciprocal to the same `-(y - x)⁻¹` normal form
      -- instead of hiding the scalar normalization inside `congrArg`.
      rw [show x - y = -(y - x) by ring, inv_neg, neg_smul]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := by grind
    by_cases hxy : x = y
    · simp [slope, average, hxy]
    · simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, hIocIcc]

/-- Helper for Example 20.9: an interval-integrable vector-valued function has the expected
derivative for its interval primitive at almost every point of the source interval. -/
lemma ae_hasDerivAt_intervalIntegral_vector_of_intervalIntegrable
    {f : ℝ → H} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x, x ∈ Set.uIcc a b → ∀ c ∈ Set.uIcc a b,
      HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact Set.uIcc_comm b a ▸ @this H _ _ _ _ f b a hf.symm (le_of_not_ge hab)
  rw [Set.uIcc_of_le hab]
  have h₁ : ∀ᵐ x, x ≠ a := by
    simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by
    simp [ae_iff, measure_singleton]
  let g : ℝ → H := fun x ↦ if x ∈ Set.Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
    integrableOn_congr_fun (by grind [Set.EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards
      [ae_hasDerivAt_intervalIntegral_vector_of_locallyIntegrable (H := H) (f := g) hg, h₁, h₂]
      with x hx hxa hxb
  intro hxIcc c hc
  -- Work on the open interval first, where the truncation defining `g` disappears.
  refine HasDerivWithinAt.hasDerivAt (s := Set.Ioo a b) ?_ <|
    Ioo_mem_nhds (by grind) (by grind)
  -- On `Ioo a b`, the primitive for `g` agrees with the original primitive for `f`.
  rw [show f x = g x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals
    apply intervalIntegral.integral_congr_ae'
    all_goals
      filter_upwards
      intro y hyIoc
      grind

/-- Helper for Example 20.9: in the inner-product-derived normed-space structure, the squared
norm has derivative `2 ⟪f, f'⟫`. -/
lemma hasDerivAt_normSq_of_hasDerivAt
    {f : ℝ → H} {f' : H} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => ‖f t‖ ^ (2 : ℕ)) (2 * ⟪f x, f'⟫_ℝ) x := by
  -- Route correction: differentiate the inner-product form directly to avoid the two competing
  -- `NormedSpace` instances coming from the ambient section and the inner-product structure.
  simpa [inner_self_eq_norm_sq_to_K, two_mul, real_inner_comm] using
    (HasDerivAt.inner (𝕜 := ℝ) hf hf)

/-- Helper for Example 20.9: away from the endpoints, the squared norm of the extended path has the
expected derivative `2 ⟪z, h⟫`. -/
lemma ae_hasDerivAt_normSq_of_intervalIntegral_witness
    {z : C(IccT, H)} {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT))
    (hz :
      ∀ t : IccT,
        z t =
          z (leftEndpoint T) +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s) :
    ∀ᵐ u, u ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
      HasDerivAt (fun u : ℝ => ‖Set.IccExtend (le_of_lt T.2) z u‖ ^ (2 : ℕ))
        (2 * ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ) u := by
  have hTpos : (0 : ℝ) < (T : ℝ) := T.2
  have hfull :
      IntervalIntegrable (Set.IccExtend (le_of_lt T.2) h) volume 0 (T : ℝ) :=
    intervalIntegrable_IccExtend_full_of_memLp_witness (T := T) (h := h) hh
  have hderiv :
      ∀ᵐ u, u ∈ Set.Ioo (0 : ℝ) (T : ℝ) →
        HasDerivAt (fun u => ∫ s in 0..u, Set.IccExtend (le_of_lt T.2) h s)
          (Set.IccExtend (le_of_lt T.2) h u) u := by
    filter_upwards
      [ae_hasDerivAt_intervalIntegral_vector_of_intervalIntegrable
        (H := H) (f := Set.IccExtend (le_of_lt T.2) h) (a := 0) (b := (T : ℝ)) hfull] with u hu
    intro huIoo
    have huIcc : u ∈ Set.uIcc (0 : ℝ) (T : ℝ) := by
      simpa [Set.uIcc_of_le hTpos.le] using (show u ∈ Set.Icc (0 : ℝ) (T : ℝ) from
        ⟨huIoo.1.le, huIoo.2.le⟩)
    have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) (T : ℝ) := by
      simp [Set.uIcc_of_le hTpos.le, hTpos.le]
    exact hu huIcc 0 hzero
  filter_upwards [hderiv] with u hu
  intro huIoo
  have hEqNear :
      (Set.IccExtend (le_of_lt T.2) z) =ᶠ[nhds u]
        fun v : ℝ => z (leftEndpoint T) + ∫ s in 0..v, Set.IccExtend (le_of_lt T.2) h s := by
    have hmem : Set.Icc (0 : ℝ) (T : ℝ) ∈ nhds u :=
      Icc_mem_nhds huIoo.1 huIoo.2
    filter_upwards [hmem] with v hv
    have hvIcc : v ∈ Set.uIcc (0 : ℝ) (T : ℝ) := by
      simpa [Set.uIcc_of_le hTpos.le] using hv
    simpa using
      iccExtendPath_eq_leftEndpoint_add_intervalIntegral (T := T) (z := z) (h := h) hz hvIcc
  have hpath :
      HasDerivAt (Set.IccExtend (le_of_lt T.2) z)
        (Set.IccExtend (le_of_lt T.2) h u) u := by
    have hu' := hu huIoo
    have hprim :
        HasDerivAt
          (fun v : ℝ => z (leftEndpoint T) + ∫ s in 0..v, Set.IccExtend (le_of_lt T.2) h s)
          (Set.IccExtend (le_of_lt T.2) h u) u := by
      simpa using HasDerivAt.const_add (z (leftEndpoint T)) hu'
    exact (hEqNear.hasDerivAt_iff).2 hprim
  have htarget :
      HasDerivAt (fun v : ℝ => ‖Set.IccExtend (le_of_lt T.2) z v‖ ^ (2 : ℕ))
        (2 * ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ) u :=
    hasDerivAt_normSq_of_hasDerivAt (H := H) hpath
  simpa using htarget

/-- Helper for Example 20.9: the ambient interval integral of `⟪z, h⟫` is the same as the subtype
integral appearing in the `L²([0,T];H)` pairing. -/
lemma intervalIntegral_inner_eq_subtypeIntegral_of_memLp_witness
    {z : C(IccT, H)} {h : IccT → H} (hh : MemLp h 2 (volume : Measure IccT)) :
    ∫ u in 0..(T : ℝ), ⟪Set.IccExtend (le_of_lt T.2) z u,
      Set.IccExtend (le_of_lt T.2) h u⟫_ℝ =
      ∫ t : IccT, ⟪z t, (((hh.toLp h : L2T) t) : H)⟫_ℝ := by
  -- First normalize the interval integral to the ambient set integral on `[0,T]`.
  rw [intervalIntegral.integral_of_le (le_of_lt T.2), ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Then move from the ambient interval back to the subtype integral and rewrite the witness.
  rw [← MeasureTheory.integral_subtype measurableSet_Icc
    (fun u : ℝ =>
      ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with t ht
  simpa [Set.IccExtend_val] using congrArg (fun v : H => ⟪z t, v⟫_ℝ) ht.symm

/-- Helper for Example 20.9: the one-path norm-square endpoint identity produced from an
interval-integral witness. -/
lemma norm_sq_endpoint_identity_of_intervalIntegral_witness
    {z : C(IccT, H)} {z' : L2T}
    (hz :
      ∃ h : IccT → H, ∃ hh : MemLp h 2 (volume : Measure IccT),
        hh.toLp h = z' ∧
          ∀ t : IccT,
            z t =
              z (leftEndpoint T) +
                ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) h s) :
    ∫ t : IccT, ⟪z t, ((z' t : H))⟫_ℝ =
      (1 / 2 : ℝ) *
        (‖z (rightEndpoint T)‖ ^ (2 : ℕ) - ‖z (leftEndpoint T)‖ ^ (2 : ℕ)) := by
  rcases hz with ⟨h, hh, rfl, hz⟩
  let w : ℝ → ℝ := fun u ↦ ‖Set.IccExtend (le_of_lt T.2) z u‖ ^ (2 : ℕ)
  have hw_ac : AbsolutelyContinuousOnInterval w 0 (T : ℝ) :=
    normSq_absolutelyContinuous_of_intervalIntegral_witness (T := T) (z := z) (h := h) hh hz
  have hderiv_restrict :
      deriv w =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))]
        fun u ↦ 2 * ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ := by
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [@ae_hasDerivAt_normSq_of_intervalIntegral_witness
      H _ _ T _ _ z h hh hz] with u hu
    intro huIoo
    simpa [w] using (hu huIoo).deriv
  have hderiv_int :
      ∫ u in 0..(T : ℝ), deriv w u =
        ∫ u in 0..(T : ℝ),
          2 * ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ := by
    apply intervalIntegral.integral_congr_ae_restrict
    simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ (T : ℝ) from le_of_lt T.2)] using hderiv_restrict
  have hinner :
      ∫ u in 0..(T : ℝ),
          2 * ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ =
        2 * ∫ t : IccT, ⟪z t, (((hh.toLp h : L2T) t) : H)⟫_ℝ := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral_inner_eq_subtypeIntegral_of_memLp_witness (T := T) (z := z) (h := h) hh]
  have hw_end :
      w (T : ℝ) - w 0 =
        ‖z (rightEndpoint T)‖ ^ (2 : ℕ) - ‖z (leftEndpoint T)‖ ^ (2 : ℕ) := by
    simp [w, leftEndpoint, rightEndpoint]
  -- Apply FTC to the absolutely continuous scalar path `w`, then transport the integral back to
  -- the subtype pairing from the statement.
  have henergy :
      2 * ∫ t : IccT, ⟪z t, (((hh.toLp h : L2T) t) : H)⟫_ℝ =
        ‖z (rightEndpoint T)‖ ^ (2 : ℕ) - ‖z (leftEndpoint T)‖ ^ (2 : ℕ) := by
    calc
      2 * ∫ t : IccT, ⟪z t, (((hh.toLp h : L2T) t) : H)⟫_ℝ =
          ∫ u in 0..(T : ℝ),
            2 * ⟪Set.IccExtend (le_of_lt T.2) z u, Set.IccExtend (le_of_lt T.2) h u⟫_ℝ := by
        symm
        exact hinner
      _ = ∫ u in 0..(T : ℝ), deriv w u := by
        symm
        exact hderiv_int
      _ = w (T : ℝ) - w 0 := by
        simpa using hw_ac.integral_deriv_eq_sub
      _ = ‖z (rightEndpoint T)‖ ^ (2 : ℕ) - ‖z (leftEndpoint T)‖ ^ (2 : ℕ) := hw_end
  nlinarith

lemma sobolev_energy_identity (f g : W12T) :
    ∫ t : IccT, ⟪f.toContinuousMap t - g.toContinuousMap t,
      (((f.deriv - g.deriv : L2T) t) : H)⟫_ℝ =
        (1 / 2 : ℝ) *
          (‖f.toContinuousMap (rightEndpoint T) - g.toContinuousMap (rightEndpoint T)‖ ^
              (2 : ℕ) -
            ‖f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T)‖ ^
              (2 : ℕ)) :=
by
  -- Reduce the pairwise identity to the generic one-path endpoint identity for the difference
  -- path constructed above.
  exact
    norm_sq_endpoint_identity_of_intervalIntegral_witness (T := T)
      (z := f.toContinuousMap - g.toContinuousMap) (z' := f.deriv - g.deriv)
      (difference_path_eq_leftEndpoint_add_intervalIntegral (T := T) f g)

/-- Helper for Example 20.9: the endpoint energy gap is nonnegative under either admissible
boundary condition. -/
lemma endpoint_gap_nonneg_of_boundary
    {bc : TimeDerivativeBoundaryCondition H} {f g : W12T}
    (hf : bc.Holds f) (hg : bc.Holds g) :
    0 ≤
      (1 / 2 : ℝ) *
        (‖f.toContinuousMap (rightEndpoint T) - g.toContinuousMap (rightEndpoint T)‖ ^
            (2 : ℕ) -
          ‖f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T)‖ ^
            (2 : ℕ)) := by
  cases bc with
  | initial x0 =>
      -- In the fixed-initial-value case, the left endpoint difference vanishes.
      have hf0 : f.toContinuousMap (leftEndpoint T) = x0 := by
        simpa using hf
      have hg0 : g.toContinuousMap (leftEndpoint T) = x0 := by
        simpa using hg
      have hleft :
          ‖f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T)‖ ^
              (2 : ℕ) = 0 := by
        rw [hf0, hg0, sub_self, norm_zero]
        norm_num
      rw [hleft]
      have hsq :
          0 ≤ ‖f.toContinuousMap (rightEndpoint T) - g.toContinuousMap (rightEndpoint T)‖ ^
            (2 : ℕ) := by
        positivity
      nlinarith
  | periodic =>
      -- In the periodic case, the right and left endpoint differences coincide.
      have hfper : f.toContinuousMap (leftEndpoint T) = f.toContinuousMap (rightEndpoint T) := by
        simpa using hf
      have hgper : g.toContinuousMap (leftEndpoint T) = g.toContinuousMap (rightEndpoint T) := by
        simpa using hg
      have hright :
          f.toContinuousMap (rightEndpoint T) - g.toContinuousMap (rightEndpoint T) =
            f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T) := by
        rw [← hfper, ← hgper]
      rw [hright]
      ring_nf
      exact le_rfl

/-- Example 20.9: for either a prescribed initial value or the periodic boundary condition, the
time-derivative operator on `L²([0,T]; H)` is monotone. -/
theorem timeDerivativeOperator_isMonotone (bc : TimeDerivativeBoundaryCondition H) :
    (timeDerivativeOperator T bc).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hu hv
  rcases (mem_timeDerivativeOperator_iff (T := T) (bc := bc) x u).1 hu with
    ⟨f, rfl, hf, rfl⟩
  rcases (mem_timeDerivativeOperator_iff (T := T) (bc := bc) y v).1 hv with
    ⟨g, rfl, hg, rfl⟩
  -- Reduce the graph pairing to the endpoint-energy expression from the source proof.
  calc
    0 ≤
        (1 / 2 : ℝ) *
          (‖f.toContinuousMap (rightEndpoint T) - g.toContinuousMap (rightEndpoint T)‖ ^
              (2 : ℕ) -
            ‖f.toContinuousMap (leftEndpoint T) - g.toContinuousMap (leftEndpoint T)‖ ^
              (2 : ℕ)) :=
      endpoint_gap_nonneg_of_boundary (T := T) hf hg
    _ =
        ∫ t : IccT, ⟪f.toContinuousMap t - g.toContinuousMap t,
          (((f.deriv - g.deriv : L2T) t) : H)⟫_ℝ :=
      (sobolev_energy_identity (T := T) f g).symm
    _ = ⟪f.toLp - g.toLp, f.deriv - g.deriv⟫_ℝ :=
      (sobolev_pairing_eq_integral (T := T) f g).symm

end Monotonicity

end SetValuedOperator
