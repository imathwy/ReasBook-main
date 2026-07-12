import Mathlib
import DifferentialForms_Cartan_1970.I.section03.«0012_Proposition_6_2»
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

/-- The logarithmic `1`-form `z ↦ dz / (z - a)` on the punctured plane. -/
def indexForm (a : ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ (1 : ℂ →L[ℂ] ℂ).smulRight ((z - a)⁻¹)

/-- The index of a closed path `γ` with respect to a point `a` of `ℂ` outside the image of `γ`
is the normalized contour integral `(1 / (2 * π * i)) ∫_γ dz / (z - a)`. -/
def closedPathIndex {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) : ℂ :=
  (∫ᶜ w in γ, indexForm a.1 w) / (((2 * Real.pi : ℂ) * Complex.I))

/-- The index is the curve integral of the logarithmic form divided by `2 * π * i`. -/
@[simp]
theorem closedPathIndex_def {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) :
    closedPathIndex γ a = (∫ᶜ w in γ, indexForm a.1 w) / (((2 * Real.pi : ℂ) * Complex.I)) := rfl

/-- Helper for Cartan section05 0026_Definition_II_1_extra_16: if two continuous lifts through
`Complex.exp` have the same exponential, then their difference is locally constant. -/
private theorem expLiftDifference_isLocallyConstant
    {J : Type*} [TopologicalSpace J] (f g : C(J, ℂ))
    (hExp : ∀ x : J, Complex.exp (f x) = Complex.exp (g x)) :
    IsLocallyConstant (fun x : J ↦ g x - f x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let δ : C(J, ℂ) := g - f
  refine ⟨δ ⁻¹' Metric.ball (δ x) 1, δ.continuous.isOpen_preimage _ Metric.isOpen_ball, ?_, ?_⟩
  · simp [δ, Metric.mem_ball, zero_lt_one]
  · intro y hy
    have hy_exp : Complex.exp (δ y) = 1 := by
      calc
        Complex.exp (δ y) = Complex.exp (g y) / Complex.exp (f y) := by
          simp [δ, Complex.exp_sub]
        _ = 1 := by
          rw [hExp y]
          field_simp [Complex.exp_ne_zero (g y)]
    have hx_exp : Complex.exp (δ x) = 1 := by
      calc
        Complex.exp (δ x) = Complex.exp (g x) / Complex.exp (f x) := by
          simp [δ, Complex.exp_sub]
        _ = 1 := by
          rw [hExp x]
          field_simp [Complex.exp_ne_zero (g x)]
    have hδ_exp : Complex.exp (δ y) = Complex.exp (δ x) := by rw [hy_exp, hx_exp]
    rcases Complex.exp_eq_exp_iff_exists_int.mp hδ_exp with ⟨n, hn⟩
    by_cases hn0 : n = 0
    · simpa [δ, hn0] using hn
    · have hdist_lt : ‖δ y - δ x‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      have hnorm_n : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
        have hnorm_n' : (1 : ℝ) ≤ |(n : ℝ)| := by
          exact_mod_cast Int.one_le_abs hn0
        simpa [Complex.norm_intCast] using hnorm_n'
      have hdist_ge : 2 * Real.pi ≤ ‖δ y - δ x‖ := by
        have hsub : δ y - δ x = (n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := by
          rw [hn]
          ring
        calc
          2 * Real.pi = 1 * ‖((2 * Real.pi : ℂ) * Complex.I)‖ := by
            simp [abs_of_nonneg Real.pi_pos.le]
          _ ≤ ‖(n : ℂ)‖ * ‖((2 * Real.pi : ℂ) * Complex.I)‖ := by
            gcongr
          _ = ‖(n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I))‖ := by
            simp
          _ = ‖δ y - δ x‖ := by rw [hsub]
      have hlt : (1 : ℝ) < 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      linarith

/-- Helper for Cartan section05 0026_Definition_II_1_extra_16: two continuous lifts with the same
exponential have the same endpoint difference on any preconnected parameter space. -/
private theorem endpointDifference_eq_of_sameExp
    {J : Type*} [TopologicalSpace J] [PreconnectedSpace J] (f g : C(J, ℂ))
    (hExp : ∀ x : J, Complex.exp (f x) = Complex.exp (g x)) (u v : J) :
    f v - f u = g v - g u := by
  have hloc : IsLocallyConstant (fun x : J ↦ g x - f x) :=
    expLiftDifference_isLocallyConstant f g hExp
  have hconst : g u - f u = g v - f v :=
    hloc.apply_eq_of_preconnectedSpace u v
  calc
    f v - f u = f v + (g u - f u) - g u := by ring
    _ = f v + (g v - f v) - g u := by rw [hconst]
    _ = g v - g u := by ring

/-- Helper for Cartan section05 0026_Definition_II_1_extra_16: a continuous lift of
`t ↦ γ t - a` through `Complex.exp` is locally a primitive of the logarithmic form `indexForm a`
along the path `γ`. -/
private theorem expLift_isPrimitiveAlongPath
    {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) (f : C(I, ℂ))
    (hf : ∀ t : I, Complex.exp (f t) = γ t - a.1) :
    IsPrimitiveAlongPath
      (fun w : ℂ ↦ (indexForm a.1 w).restrictScalars ℝ) {w : ℂ | w ≠ a.1} γ f := by
  intro τ
  have hτ_ne : γ τ ≠ a.1 := by
    intro hEq
    exact a.2 ⟨τ, hEq⟩
  let r : ℝ := ‖γ τ - a.1‖ / 2
  have hr_pos : 0 < r := by
    exact half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hτ_ne))
  let V : Set ℂ := Metric.ball (γ τ - a.1) r
  have hV_open : IsOpen V := Metric.isOpen_ball
  have hV_connected : IsConnected V := by
    exact (convex_ball (γ τ - a.1) r).isConnected ⟨γ τ - a.1, Metric.mem_ball_self hr_pos⟩
  have hV_simply : IsSimplyConnected V := by
    letI : ContractibleSpace V :=
      (convex_ball (γ τ - a.1) r).contractibleSpace ⟨γ τ - a.1, Metric.mem_ball_self hr_pos⟩
    exact (inferInstance : SimplyConnectedSpace V)
  have hV_nonzero : (0 : ℂ) ∉ (fun w : ℂ ↦ w) '' V := by
    rintro ⟨w, hwV, hw0⟩
    have hdist : dist (0 : ℂ) (γ τ - a.1) < r := by
      simpa [V, hw0] using hwV
    have hlt : ‖γ τ - a.1‖ < ‖γ τ - a.1‖ / 2 := by
      simpa [r, dist_eq_norm, norm_sub_rev] using hdist
    have hnorm_nonneg : 0 ≤ ‖γ τ - a.1‖ := norm_nonneg _
    nlinarith
  rcases Complex.exists_continuousOn_eqOn_exp_comp hV_simply hV_open continuousOn_id hV_nonzero with
    ⟨L, hL_cont, hL_exp⟩
  have hV_mem : γ τ - a.1 ∈ V := Metric.mem_ball_self hr_pos
  have hcenterExp : Complex.exp (f τ) = Complex.exp (L (γ τ - a.1)) := by
    calc
      Complex.exp (f τ) = γ τ - a.1 := hf τ
      _ = Complex.exp (L (γ τ - a.1)) := by
        symm
        simpa [Function.comp] using hL_exp hV_mem
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hcenterExp
  let primitive : ℂ → ℂ := fun w ↦ L (w - a.1) + k * (2 * Real.pi * Complex.I)
  let U : Set ℂ := (fun w : ℂ ↦ w - a.1) ⁻¹' V
  have hsub_cont : Continuous (fun w : ℂ => w - a.1) := by
    simpa [sub_eq_add_neg] using continuous_id.add continuous_const
  have hU_open : IsOpen U := hsub_cont.isOpen_preimage _ hV_open
  have hγτU : γ τ ∈ U := by
    simpa [U] using hV_mem
  have hU_subset : U ⊆ {w : ℂ | w ≠ a.1} := by
    intro w hw
    have hneq : w - a.1 ≠ 0 := by
      intro hw0
      exact hV_nonzero ⟨w - a.1, by simpa [U] using hw, hw0⟩
    exact sub_ne_zero.mp hneq
  have hbranch : Complex.IsLogBranchOn L V := ⟨hV_open, hV_connected, hL_cont, hL_exp⟩
  have hprimitive :
      IsPrimitiveOn U (fun w : ℂ ↦ (indexForm a.1 w).restrictScalars ℝ) primitive := by
    intro w hw
    have hwV : w - a.1 ∈ V := by simpa [U] using hw
    have hcomp : HasFDerivAt (fun u : ℂ ↦ L (u - a.1)) ((indexForm a.1 w).restrictScalars ℝ) w := by
      have hderiv : HasDerivAt (fun u : ℂ ↦ L (u - a.1)) (w - a.1)⁻¹ w := by
        simpa [one_div, mul_one] using
          (hbranch.hasDerivAt hwV).comp w ((hasDerivAt_id w).sub_const a.1)
      have hlin :
          ContinuousLinearMap.restrictScalars ℝ
              (ContinuousLinearMap.toSpanSingleton ℂ ((w - a.1)⁻¹)) =
            (indexForm a.1 w).restrictScalars ℝ := by
        ext v
        simp [indexForm, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
      rw [← hlin]
      exact hderiv.hasFDerivAt.restrictScalars ℝ
    -- The integer period shift leaves the local derivative unchanged.
    simpa [primitive] using hcomp.add_const (k * (2 * Real.pi * Complex.I))
  let δ : I → ℂ := fun t ↦ f t - primitive (γ t)
  let s₀ : Set I := γ ⁻¹' U
  have hs₀_open : IsOpen s₀ := γ.continuous.isOpen_preimage _ hU_open
  have hδ_cont : ContinuousOn δ s₀ := by
    intro t ht
    have htV : γ t - a.1 ∈ V := by simpa [s₀, U] using ht
    let hshift : I → ℂ := fun s ↦ γ s - a.1
    have hL_at : ContinuousAt L (γ t - a.1) := hL_cont.continuousAt (hV_open.mem_nhds htV)
    have hγsub : ContinuousAt hshift t := by
      simpa [hshift, sub_eq_add_neg] using
        (γ.continuous.continuousAt.add continuousAt_const)
    have hprim_at : ContinuousAt (fun s : I ↦ primitive (γ s)) t := by
      simpa [primitive] using
        (hL_at.comp (f := hshift) hγsub).add_const
          (k * (2 * Real.pi * Complex.I))
    have hf_at : ContinuousAt f t := f.continuous.continuousAt
    exact (hf_at.sub hprim_at).continuousWithinAt
  let s : Set I := s₀ ∩ δ ⁻¹' Metric.ball 0 1
  have hs_open : IsOpen s := by
    simpa [s] using hδ_cont.isOpen_inter_preimage hs₀_open Metric.isOpen_ball
  have hτδ : δ τ = 0 := by
    simp [δ, primitive, hk]
  have hτs : τ ∈ s := by
    refine ⟨hγτU, ?_⟩
    simp [δ, hτδ, Metric.mem_ball]
  refine ⟨s, hs_open, hτs, U, hU_open, hγτU, hU_subset, ?_, primitive, hprimitive, ?_⟩
  · intro t ht
    exact ht.1
  · intro t ht
    have htU : γ t ∈ U := ht.1
    have hδnorm : ‖δ t‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using ht.2
    have htV : γ t - a.1 ∈ V := by simpa [U] using htU
    have hδ_exp : Complex.exp (δ t) = 1 := by
      have hL_exp_t : Complex.exp (L (γ t - a.1)) = γ t - a.1 := by
        simpa [Function.comp] using hL_exp htV
      calc
        Complex.exp (δ t) =
            Complex.exp (f t) /
              (Complex.exp (L (γ t - a.1)) * Complex.exp (k * (2 * Real.pi * Complex.I))) := by
                simp [δ, primitive, Complex.exp_sub, Complex.exp_add]
        _ = (γ t - a.1) / ((γ t - a.1) * 1) := by
              rw [hf t, hL_exp_t, Complex.exp_int_mul_two_pi_mul_I]
        _ = 1 := by
              field_simp [sub_ne_zero.mpr (hU_subset htU)]
    have hδ_zero_exp : Complex.exp (δ t) = Complex.exp 0 := by simpa using hδ_exp
    rcases Complex.exp_eq_exp_iff_exists_int.mp hδ_zero_exp with ⟨n, hn⟩
    by_cases hn0 : n = 0
    · apply sub_eq_zero.mp
      simpa [δ, hn0] using hn
    · have hnorm_n : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
        have hnorm_n' : (1 : ℝ) ≤ |(n : ℝ)| := by
          exact_mod_cast Int.one_le_abs hn0
        simpa [Complex.norm_intCast] using hnorm_n'
      have hδ_ge : 2 * Real.pi ≤ ‖δ t‖ := by
        have hsub : δ t = (n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := by
          simpa [δ] using hn
        calc
          2 * Real.pi = 1 * ‖((2 * Real.pi : ℂ) * Complex.I)‖ := by
            simp [abs_of_nonneg Real.pi_pos.le]
          _ ≤ ‖(n : ℂ)‖ * ‖((2 * Real.pi : ℂ) * Complex.I)‖ := by
            gcongr
          _ = ‖(n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I))‖ := by
            simp
          _ = ‖δ t‖ := by rw [hsub]
      have hlt : (1 : ℝ) < 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      linarith

-- Proof sketch: differentiate the identity `Complex.exp ∘ f = fun t ↦ γ t - a`, rewrite the
-- logarithmic derivative as `f'`, and integrate along the closed path to express the index by the
-- endpoint difference of the logarithm lift.
/-- If `γ(t) - a` admits a continuous logarithm `f` on `[0,1]`, and `γ` has the source text's
piecewise differentiability needed for path integrals, then the integral index is the normalized
endpoint difference of that logarithm. The bare continuous lift only gives the topological
endpoint-jump definition; the integral identity needs this regularity. -/
theorem closedPathIndex_eq_endpoint_log_lift_difference
    {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ}) (f : C(I, ℂ))
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hInt : CurveIntegrable (indexForm a.1) γ)
    (hf : ∀ t, Complex.exp (f t) = γ t - a.1) :
    closedPathIndex γ a = (f 1 - f 0) / (((2 * Real.pi : ℂ) * Complex.I)) := by
  have hprimitive :
      IsPrimitiveAlongPath
        (fun w : ℂ ↦ (indexForm a.1 w).restrictScalars ℝ) {w : ℂ | w ≠ a.1} γ f :=
    expLift_isPrimitiveAlongPath γ a f hf
  have hIntR : CurveIntegrable (fun w : ℂ ↦ (indexForm a.1 w).restrictScalars ℝ) γ := by
    -- Restrict scalars once so the path-primitive theorem from Remark II.1-extra-8 applies.
    simpa using
      (curveIntegrable_restrictScalars_iff (ω := indexForm a.1) (γ := γ) (𝕝 := ℝ)).2 hInt
  have hcurve :
      ∫ᶜ w in γ, (fun w : ℂ ↦ (indexForm a.1 w).restrictScalars ℝ) w = f 1 - f 0 := by
    -- The continuous logarithm lift is locally primitive, so its endpoint jump computes the
    -- curve integral of the logarithmic form.
    simpa using hprimitive.curveIntegral_eq_endpoint_sub hγ_piecewise hIntR
  calc
    closedPathIndex γ a =
        (∫ᶜ w in γ, (fun w : ℂ ↦ (indexForm a.1 w).restrictScalars ℝ) w) /
          (((2 * Real.pi : ℂ) * Complex.I)) := by
            rw [closedPathIndex_def, curveIntegral_restrictScalars]
    _ = (f 1 - f 0) / (((2 * Real.pi : ℂ) * Complex.I)) := by rw [hcurve]

namespace Path

/-- The index of a closed path at a point `a` off its image. -/
abbrev closedPathIndexAt {z : ℂ} (γ : Path z z) (a : ℂ) (ha : a ∉ Set.range γ) : ℂ :=
  closedPathIndex γ ⟨a, ha⟩

@[simp]
theorem closedPathIndexAt_def {z : ℂ} (γ : Path z z) (a : ℂ) (ha : a ∉ Set.range γ) :
    γ.closedPathIndexAt a ha = closedPathIndex γ ⟨a, ha⟩ := rfl

/-- A closed complex loop has winding index `n` about `a` if `γ - a` admits a continuous
logarithm whose endpoint jump is `2πni`. -/
def HasIndexAt {z : ℂ} (γ : Path z z) (a : ℂ) (n : ℤ) : Prop :=
  ∃ w : C(I, ℂ), (∀ t : I, Complex.exp (w t) = γ t - a) ∧
    w 1 = w 0 + ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I

-- Proof sketch: exponentials never vanish, so `exp (w t) = γ t - a` forces `γ t ≠ a`.
/-- A loop with a winding index about `a` avoids the center `a` pointwise. -/
theorem HasIndexAt.ne_center {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ : γ.HasIndexAt a n) (t : I) :
    γ t ≠ a := by
  rcases hγ with ⟨w, hwexp, -⟩
  -- Exponentials never vanish, so the translated loop cannot hit the center.
  intro hEq
  have hne : Complex.exp (w t) ≠ 0 := Complex.exp_ne_zero (w t)
  simp [hwexp t, hEq] at hne

/-- A loop with winding index about `a` avoids `a` on its whole image. -/
theorem HasIndexAt.not_mem_range {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ : γ.HasIndexAt a n) :
    a ∉ Set.range γ := by
  rintro ⟨t, rfl⟩
  exact hγ.ne_center t rfl

-- Proof sketch: apply `closedPathIndex_eq_endpoint_log_lift_difference` to the defining logarithm
-- lift and simplify the endpoint jump by `2 * π * i`.
/-- A logarithmic lift with endpoint jump `2πni` computes the integral index as `n`, provided the
path is piecewise differentiable and the logarithmic form is integrable along it. -/
theorem HasIndexAt.closedPathIndex_eq {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ : γ.HasIndexAt a n) (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hInt : CurveIntegrable (indexForm a) γ) :
    γ.closedPathIndexAt a hγ.not_mem_range = (n : ℂ) := by
  have hγ_range : a ∉ Set.range γ := hγ.not_mem_range
  rcases hγ with ⟨w, hwexp, hwjump⟩
  have hmain :
      closedPathIndex γ ⟨a, hγ_range⟩ =
        (w 1 - w 0) / (((2 * Real.pi : ℂ) * Complex.I)) :=
    closedPathIndex_eq_endpoint_log_lift_difference γ ⟨a, hγ_range⟩ w
      hγ_piecewise hInt hwexp
  have hperiod : w 1 - w 0 = (n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := by
    rw [hwjump]
    ring
  -- The endpoint jump is exactly one period multiple, so dividing by `2π i` recovers `n`.
  calc
    γ.closedPathIndexAt a hγ_range = closedPathIndex γ ⟨a, hγ_range⟩ := rfl
    _ = (w 1 - w 0) / (((2 * Real.pi : ℂ) * Complex.I)) := hmain
    _ = ((n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I))) / (((2 * Real.pi : ℂ) * Complex.I)) := by
          rw [hperiod]
    _ = (n : ℂ) := by
          field_simp [Complex.two_pi_I_ne_zero]

/-- The topological winding index encoded by a continuous logarithmic lift is unique. -/
theorem HasIndexAt.eq {z : ℂ} {γ : Path z z} {a : ℂ} {m n : ℤ}
    (hm : γ.HasIndexAt a m) (hn : γ.HasIndexAt a n) :
    m = n := by
  rcases hm with ⟨wm, hwmexp, hwmjump⟩
  rcases hn with ⟨wn, hwnexp, hwnjump⟩
  have hdiff :
      wm 1 - wm 0 = wn 1 - wn 0 :=
    endpointDifference_eq_of_sameExp wm wn (fun t ↦ by rw [hwmexp t, hwnexp t]) (0 : I) 1
  have hmperiod : wm 1 - wm 0 = (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := by
    rw [hwmjump]
    ring
  have hnperiod : wn 1 - wn 0 = (n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := by
    rw [hwnjump]
    ring
  have hcast : (m : ℂ) = (n : ℂ) := by
    have hperiods :
        (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) =
          (n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := by
      calc
        (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) = wm 1 - wm 0 := hmperiod.symm
        _ = wn 1 - wn 0 := hdiff
        _ = (n : ℂ) * (((2 * Real.pi : ℂ) * Complex.I)) := hnperiod
    have := congrArg (fun z : ℂ ↦ z / (((2 * Real.pi : ℂ) * Complex.I))) hperiods
    simpa [Complex.two_pi_I_ne_zero] using this
  exact Int.cast_injective hcast

/-- Helper for Cartan section05 0026_Definition_II_1_extra_16: a closed path avoiding `a`
admits a winding-index witness about `a`. -/
theorem hasIndexAt_of_closedPath_avoids_point {z : ℂ} {γ : Path z z} {a : ℂ}
    (ha : a ∉ Set.range γ) :
    ∃ n : ℤ, γ.HasIndexAt a n := by
  let loop : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun t ↦ ⟨γ t - a, sub_ne_zero.mpr (by
      intro hEq
      exact ha ⟨t, hEq⟩)⟩, by
      fun_prop⟩
  have hzero :
      loop 0 =
        (⟨Complex.exp (Complex.log (γ 0 - a)),
          Complex.exp_ne_zero (Complex.log (γ 0 - a))⟩ : {w : ℂ // w ≠ 0}) := by
    apply Subtype.ext
    -- Start the covering lift at the principal logarithm of the base point.
    simpa [loop, γ.source] using
      (Complex.exp_log (sub_ne_zero.mpr (by
        intro hEq
        exact ha ⟨0, by simpa [γ.source] using hEq⟩))).symm
  let w : C(I, ℂ) := Complex.isCoveringMap_exp.liftPath loop (Complex.log (γ 0 - a)) hzero
  have hw :
      (fun u : ℂ ↦ (⟨Complex.exp u, Complex.exp_ne_zero u⟩ : {w : ℂ // w ≠ 0})) ∘ w = loop :=
    Complex.isCoveringMap_exp.liftPath_lifts loop _ hzero
  have hwexp : ∀ t : I, Complex.exp (w t) = γ t - a := by
    intro t
    -- Read the covering equation back on the underlying complex values.
    have ht := congrArg Subtype.val (congr_fun hw t)
    simpa [loop] using ht
  have hExp : Complex.exp (w 1) = Complex.exp (w 0) := by
    -- Closedness forces the endpoint values of the lifted exponential to agree.
    rw [hwexp, hwexp, γ.target, γ.source]
  rcases Complex.exp_eq_exp_iff_exists_int.mp hExp with ⟨n, hn⟩
  refine ⟨n, w, ?_, ?_⟩
  · intro t
    simpa using hwexp t
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hn

end Path

-- Proof sketch: lift `γ - a` through the covering map `Complex.exp`, apply
-- `closedPathIndex_eq_endpoint_log_lift_difference`, and use `Complex.exp_eq_exp_iff_exists_int`
-- together with the closedness of `γ` to show that `f 1 - f 0` is an integral multiple of
-- `2 * π * i`.
/-- Cartan section05 0026_Definition_II_1_extra_16 (Definition II.1-extra-16): the integral index
of a piecewise differentiable closed path about a point off its image is an integer under the
integrability assumptions needed to identify it with a logarithmic endpoint jump. -/
theorem closedPathIndex_isInteger
    {z : ℂ} (γ : Path z z) (a : {w : ℂ // w ∉ Set.range γ})
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hInt : CurveIntegrable (indexForm a.1) γ) :
    ∃ n : ℤ, closedPathIndex γ a = (n : ℂ) := by
  rcases Path.hasIndexAt_of_closedPath_avoids_point (γ := γ) (a := a.1) a.2 with ⟨n, hγ⟩
  refine ⟨n, ?_⟩
  -- The covering-map witness computes the normalized logarithmic integral as the integer `n`.
  simpa [Path.closedPathIndexAt_def] using hγ.closedPathIndex_eq hγ_piecewise hInt
