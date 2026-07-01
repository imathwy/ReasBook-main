import Mathlib
import cartan.I.section03.«0006_Definition_I_3_extra_6»
import cartan.III.section12.«0022_Exercise_10»
import cartan.VI.section22.«0006_Definition_VI_1_extra_4»
import cartan.VI.section23.«0006_Proposition_6_1»
import cartan.VI.section24.«0001_Theorem_VI_3_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric Set
open scoped ComplexConjugate

-- Domain sampling note: this file lies in one-variable complex analysis on simply connected planar
-- domains. The relevant owner declarations in the project are:
-- * `HolomorphicIsomorph D D'` for holomorphic isomorphisms of open sets;
-- * `Complex.IsArgument t θ` for the source-facing argument predicate;
-- * `OpenPartialHomeomorph.EqOnSource` in mathlib for the right notion of equality of partial
--   maps, indicating that uniqueness should be extensional on the source rather than literal
--   equality of ambient total functions.
-- The source-facing notion here is the normalization condition, while the biholomorphic datum
-- itself should be the chapter owner `HolomorphicIsomorph`.

/-- A normalized Riemann map from `D` to the open unit disc sending `a` to `b` with prescribed
argument `α` for the derivative at `a`. -/
def IsNormalizedRiemannMap (D : Set ℂ) (a b : ℂ) (α : ℝ)
    (e : HolomorphicIsomorph D (ball (0 : ℂ) 1)) : Prop :=
  e a = b ∧ Complex.IsArgument (derivWithin e D a) α

namespace HolomorphicIsomorph

variable {D D' : Set ℂ}

/-- Helper for Exercise 1: a holomorphic isomorphism maps its prescribed source into its prescribed
target. -/
theorem mapsTo (e : HolomorphicIsomorph D D') :
    MapsTo e D D' := by
  -- Rewrite the source and target memberships to the underlying partial-homeomorphism owner.
  intro z hz
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source

/-- Helper for Exercise 1: the forward branch of a holomorphic isomorphism is analytic at every
point of its source. -/
theorem analyticAt (e : HolomorphicIsomorph D D') {z : ℂ} (hz : z ∈ D) :
    AnalyticAt ℂ e z :=
  e.analyticOn_toFun z hz

/-- Helper for Exercise 1: the inverse branch of a holomorphic isomorphism is analytic at every
point of its target. -/
theorem analyticAt_invFun (e : HolomorphicIsomorph D D') {w : ℂ} (hw : w ∈ D') :
    AnalyticAt ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) w :=
  e.analyticOn_invFun w hw

/-- Helper for Exercise 1: the inverse of a holomorphic isomorphism is again a holomorphic
isomorphism. -/
def symm (e : HolomorphicIsomorph D D') : HolomorphicIsomorph D' D :=
  ⟨(e : OpenPartialHomeomorph ℂ ℂ).symm,
    { source_eq := e.target_eq
      target_eq := e.source_eq
      analyticOn_toFun := e.analyticOn_invFun
      analyticOn_symm := e.analyticOn_toFun }⟩

/-- Helper for Exercise 1: holomorphic isomorphisms compose by composing their underlying open
partial homeomorphisms. -/
def trans {D'' : Set ℂ} (e : HolomorphicIsomorph D D') (e' : HolomorphicIsomorph D' D'') :
    HolomorphicIsomorph D D'' :=
  ⟨(e : OpenPartialHomeomorph ℂ ℂ).trans (e' : OpenPartialHomeomorph ℂ ℂ),
    { source_eq := by
        -- The composition source is the full source of `e` because `e` already lands in `D'`.
        ext z
        constructor
        · intro hz
          rw [OpenPartialHomeomorph.trans_source] at hz
          simpa [e.source_eq] using hz.1
        · intro hz
          have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
            simpa [e.source_eq] using hz
          have hez_source' : e z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).source := by
            simpa [e.target_eq, e'.source_eq] using
              ((e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source)
          rw [OpenPartialHomeomorph.trans_source]
          exact ⟨hz_source, hez_source'⟩
      target_eq := by
        -- Dually, the composition target is the full target of `e'`.
        ext z
        constructor
        · intro hz
          rw [OpenPartialHomeomorph.trans_target] at hz
          simpa [e'.target_eq] using hz.1
        · intro hz
          have hz_target : z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).target := by
            simpa [e'.target_eq] using hz
          have hpre_target : (e' : OpenPartialHomeomorph ℂ ℂ).symm z ∈
              (e : OpenPartialHomeomorph ℂ ℂ).target := by
            simpa [e.target_eq, e'.source_eq] using
              ((e' : OpenPartialHomeomorph ℂ ℂ).map_target hz_target)
          rw [OpenPartialHomeomorph.trans_target]
          exact ⟨hz_target, hpre_target⟩
      analyticOn_toFun := by
        -- The forward branch is the composition `e' ∘ e` on `D`.
        simpa using e'.analyticOn_toFun.comp e.analyticOn_toFun e.mapsTo
      analyticOn_symm := by
        -- The inverse branch is the composition `e.symm ∘ e'.symm` on `D''`.
        simpa using e.analyticOn_invFun.comp e'.analyticOn_invFun e'.symm.mapsTo }⟩

end HolomorphicIsomorph

/-- Helper for Exercise 1: the derivative of a holomorphic isomorphism cannot vanish on its
source. -/
theorem holomorphic_isomorph_deriv_ne_zero {D D' : Set ℂ} (e : HolomorphicIsomorph D D')
    {z : ℂ} (hz : z ∈ D) :
    deriv e z ≠ 0 := by
  -- A vanishing derivative would force the local inverse branch to fail to be differentiable,
  -- contradicting analyticity of the inverse isomorphism.
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  rcases e.analyticAt hz with ⟨p, hp⟩
  have he : HasDerivAt e (deriv e z) z := by
    simpa [HasFPowerSeriesAt.deriv hp] using hp.hasDerivAt
  have hmem_target : e z ∈ D' := by
    simpa [e.target_eq] using ((e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source)
  intro hzero
  have he_zero : HasDerivAt e 0 z := he.congr_deriv hzero
  have hleft : ((e : OpenPartialHomeomorph ℂ ℂ).symm) (e z) = z :=
    (e : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source
  have he_zero_at_inv : HasDerivAt e 0 (((e : OpenPartialHomeomorph ℂ ℂ).symm) (e z)) := by
    simpa [hleft] using he_zero
  have hnot_diff : ¬ DifferentiableAt ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (e z) := by
    exact not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
      (f := e) (g := ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ)) he_zero_at_inv
      ((e : OpenPartialHomeomorph ℂ ℂ).eventually_right_inverse' hz_source)
  exact hnot_diff ((e.analyticAt_invFun hmem_target).differentiableAt)

/-- Helper for Exercise 1: the within-derivative of a holomorphic isomorphism on its open source is
also nonzero. -/
theorem holomorphic_isomorph_derivWithin_ne_zero {D D' : Set ℂ} (e : HolomorphicIsomorph D D')
    {z : ℂ} (hz : z ∈ D) :
    derivWithin e D z ≠ 0 := by
  rw [derivWithin_of_mem_nhds (e.isOpen_source.mem_nhds hz)]
  exact holomorphic_isomorph_deriv_ne_zero e hz

namespace Complex

/-- Helper for Exercise 1: the phase `θ` is an argument of the unit complex number `exp (θ I)`. -/
theorem isArgument_exp_mul_I (θ : ℝ) :
    IsArgument (exp (θ * I)) θ := by
  rw [isArgument_iff_exp_eq_div_norm]
  rw [Complex.norm_exp_ofReal_mul_I]
  simp

/-- Helper for Exercise 1: arguments add under multiplication of nonzero complex numbers. -/
theorem isArgument_mul {u v : ℂ} {α β : ℝ}
    (hu : IsArgument u α) (hv : IsArgument v β) :
    IsArgument (u * v) (α + β) := by
  -- Rewrite both arguments in the angle owner, then use `Complex.arg_mul_coe_angle`.
  refine ⟨mul_ne_zero hu.ne_zero hv.ne_zero, ?_⟩
  calc
    ((α + β : ℝ) : Real.Angle) = (α : Real.Angle) + β := by
      rw [Real.Angle.coe_add]
    _ = arg u + arg v := by
      rw [hu.2, hv.2]
    _ = arg (u * v) := by
      simpa using (Complex.arg_mul_coe_angle hu.ne_zero hv.ne_zero).symm

/-- Helper for Exercise 1: multiplying by a positive real scalar preserves the argument. -/
theorem isArgument_mul_pos_real {u : ℂ} {α r : ℝ}
    (hr : 0 < r) (hu : IsArgument u α) :
    IsArgument (u * (r : ℂ)) α := by
  -- Positive real scaling leaves the complex argument unchanged.
  refine ⟨mul_ne_zero hu.ne_zero (by exact_mod_cast hr.ne'), ?_⟩
  calc
    (α : Real.Angle) = arg u := hu.2
    _ = arg (u * (r : ℂ)) := by
      rw [Complex.arg_mul_real hr]

end Complex

/-- Helper for Exercise 1: the centering Möbius map of the unit disc packages to a holomorphic
disc automorphism. -/
theorem unit_disc_center_automorphism {c : ℂ} (hc : c ∈ ball (0 : ℂ) 1) :
    ∃ φ : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1),
      EqOn φ (discCenter c) (ball (0 : ℂ) 1) := by
  have hneg : -c ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using hc
  have hright : Set.LeftInvOn (discCenter c) (discUncenter c) (ball (0 : ℂ) 1) := by
    -- The right inverse is the left inverse for the opposite center.
    intro z hz
    simpa [discUncenter] using (disc_uncenter_leftInvOn_disc_center hneg hz)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine
        { toFun := discCenter c
          invFun := discUncenter c
          source := ball (0 : ℂ) 1
          target := ball (0 : ℂ) 1
          map_source' := disc_center_mapsTo_unit_ball hc
          map_target' := disc_uncenter_mapsTo_unit_ball hc
          left_inv' := disc_uncenter_leftInvOn_disc_center hc
          right_inv' := hright
          open_source := Metric.isOpen_ball
          open_target := Metric.isOpen_ball
          continuousOn_toFun := by
            -- Holomorphicity on the open disc gives continuity there.
            exact ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_center_differentiableOn hc)).continuousOn
          continuousOn_invFun := by
            -- The inverse Möbius branch is holomorphic on the same disc.
            exact ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_uncenter_differentiableOn hc)).continuousOn }
    · refine
        { source_eq := rfl
          target_eq := rfl
          analyticOn_toFun := by
            -- Convert differentiability on the open disc back to the analytic owner.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_center_differentiableOn hc)
          analyticOn_symm := by
            -- The inverse branch is the uncentering map.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_uncenter_differentiableOn hc) }
  · intro z hz
    rfl

/-- Helper for Exercise 1: the uncentering Möbius map of the unit disc packages to a holomorphic
disc automorphism. -/
theorem unit_disc_uncenter_automorphism {c : ℂ} (hc : c ∈ ball (0 : ℂ) 1) :
    ∃ φ : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1),
      EqOn φ (discUncenter c) (ball (0 : ℂ) 1) := by
  have hneg : -c ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using hc
  -- `discUncenter c` is `discCenter (-c)`.
  simpa [discUncenter, neg_neg] using unit_disc_center_automorphism hneg

/-- Helper for Exercise 1: multiplication by `exp (θ I)` packages to a holomorphic unit-disc
rotation automorphism. -/
theorem unit_disc_rotation_automorphism (θ : ℝ) :
    ∃ φ : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1),
      EqOn φ (fun z ↦ Complex.exp (θ * Complex.I) * z) (ball (0 : ℂ) 1) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine
        { toFun := fun z ↦ Complex.exp (θ * Complex.I) * z
          invFun := fun z ↦ Complex.exp (-θ * Complex.I) * z
          source := ball (0 : ℂ) 1
          target := ball (0 : ℂ) 1
          map_source' := by
            intro z hz
            -- Rotations preserve the norm, so they preserve the open unit disc.
            simpa [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I] using hz
          map_target' := by
            intro z hz
            -- The inverse rotation has the same norm-preserving property.
            have hnorm : ‖Complex.exp (-(θ * Complex.I))‖ = 1 := by
              simpa [neg_mul] using (Complex.norm_exp_ofReal_mul_I (-θ))
            simpa [mem_ball_zero_iff, norm_mul, hnorm] using hz
          left_inv' := by
            intro z hz
            -- The two opposite rotations cancel.
            rw [← mul_assoc, ← Complex.exp_add]
            have hsum : -θ * Complex.I + θ * Complex.I = 0 := by
              ring
            rw [hsum]
            simp
          right_inv' := by
            intro z hz
            -- The inverse branch cancels in the opposite order as well.
            rw [← mul_assoc, ← Complex.exp_add]
            have hsum : θ * Complex.I + -θ * Complex.I = 0 := by
              ring
            rw [hsum]
            simp
          open_source := Metric.isOpen_ball
          open_target := Metric.isOpen_ball
          continuousOn_toFun := by
            -- A complex-linear map is holomorphic, hence continuous on the disc.
            exact
              ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
                ((differentiableOn_const (Complex.exp (θ * Complex.I))).mul
                  differentiableOn_id)).continuousOn
          continuousOn_invFun := by
            -- The inverse rotation is the same kind of linear map.
            exact
              ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
                ((differentiableOn_const (Complex.exp (-θ * Complex.I))).mul
                  differentiableOn_id)).continuousOn }
    · refine
        { source_eq := rfl
          target_eq := rfl
          analyticOn_toFun := by
            -- Holomorphicity follows from differentiability of the linear rotation.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              ((differentiableOn_const (Complex.exp (θ * Complex.I))).mul differentiableOn_id)
          analyticOn_symm := by
            -- Likewise for the inverse rotation.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              ((differentiableOn_const (Complex.exp (-θ * Complex.I))).mul
                differentiableOn_id) }
  · intro z hz
    rfl

/-- Helper for Exercise 1: an analytic complex map differentiates with derivative `deriv f z`. -/
theorem analyticAt_hasDerivAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    HasDerivAt f (deriv f z) z := by
  -- Unpack the local power series and read off the first derivative coefficient.
  rcases hf with ⟨p, hp⟩
  simpa [HasFPowerSeriesAt.deriv hp] using hp.hasDerivAt

/-- Helper for Exercise 1: the raw quotient defining `discCenter c` differentiates at `c`
with the expected quotient-rule scalar. -/
theorem disc_center_raw_hasDerivAt_self {c : ℂ} (hc : c ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun z ↦ (z - c) / (1 - conj c * z)) ((((1 : ℂ) - conj c * c)⁻¹)) c := by
  -- Differentiate numerator and denominator separately in the exact quotient-rule form.
  have hnum : HasDerivAt (fun z : ℂ ↦ z - c) 1 c := by
    simpa using (hasDerivAt_id c).sub_const c
  have hden_mul : HasDerivAt (fun z : ℂ ↦ conj c * z) (conj c) c := by
    simpa [one_mul] using (hasDerivAt_id c).const_mul (conj c)
  have hden : HasDerivAt (fun z : ℂ ↦ 1 - conj c * z) (-conj c) c := by
    simpa using (hasDerivAt_const c (1 : ℂ)).sub hden_mul
  -- The numerator vanishes at `c`, so the second quotient-rule term drops out.
  convert hnum.div hden (disc_center_denom_ne_zero hc hc) using 1
  field_simp [pow_two, disc_center_denom_ne_zero hc hc]
  ring

/-- Helper for Exercise 1: the centered Möbius map has the expected derivative at its center. -/
theorem disc_center_hasDerivAt_self {c : ℂ} (hc : c ∈ ball (0 : ℂ) 1) :
    HasDerivAt (discCenter c) ((((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹) c := by
  -- Bridge the raw quotient derivative back to the owner `discCenter`.
  simpa [discCenter, Complex.conj_mul'] using disc_center_raw_hasDerivAt_self hc

/-- Helper for Exercise 1: the raw quotient defining `discUncenter b` differentiates at `0`
with the expected quotient-rule scalar. -/
theorem disc_uncenter_raw_hasDerivAt_zero {b : ℂ} :
    HasDerivAt (fun z ↦ (z + b) / (1 + conj b * z)) (((1 : ℂ) - b * conj b)) 0 := by
  -- Differentiate the explicit numerator and denominator at the origin.
  have hnum : HasDerivAt (fun z : ℂ ↦ z + b) 1 0 := by
    simpa using (hasDerivAt_id 0).add_const b
  have hden_mul : HasDerivAt (fun z : ℂ ↦ conj b * z) (conj b) 0 := by
    simpa [one_mul] using (hasDerivAt_id 0).const_mul (conj b)
  have hden : HasDerivAt (fun z : ℂ ↦ 1 + conj b * z) (conj b) 0 := by
    simpa only [Pi.add_apply, zero_add] using ((hasDerivAt_const 0 (1 : ℂ)).add hden_mul)
  -- At `0` the denominator equals `1`, so the quotient-rule scalar simplifies immediately.
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hnum.div hden (by simp)

/-- Helper for Exercise 1: the uncentering Möbius map has the expected derivative at the origin. -/
theorem disc_uncenter_hasDerivAt_zero {b : ℂ} :
    HasDerivAt (discUncenter b) (((1 - ‖b‖ ^ 2 : ℝ) : ℂ)) 0 := by
  -- Bridge the raw quotient derivative back to the owner `discUncenter`.
  convert disc_uncenter_raw_hasDerivAt_zero (b := b) using 1
  · ext z
    simp [discUncenter, discCenter]
  · rw [Complex.mul_conj']
    simp

/-- Helper for Exercise 1: the explicit center-rotate-uncenter normalizer has argument `θ` for
its derivative at the centering point. -/
theorem centered_disc_normalizer_deriv_isArgument {c b : ℂ}
    (hc : c ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    Complex.IsArgument
      (deriv (fun z ↦ discUncenter b (Complex.exp (θ * Complex.I) * discCenter c z)) c) θ := by
  -- Differentiate the centered map, then the rotation, and finally compose with the uncentering
  -- map at the special value `0`.
  have hcenter : HasDerivAt (discCenter c) ((((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹) c :=
    disc_center_hasDerivAt_self hc
  have hinner :
      HasDerivAt
        (fun z ↦ Complex.exp (θ * Complex.I) * discCenter c z)
        (Complex.exp (θ * Complex.I) * ((((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹)) c := by
    simpa using hcenter.const_mul (Complex.exp (θ * Complex.I))
  have houter :
      HasDerivAt (discUncenter b) (((1 - ‖b‖ ^ 2 : ℝ) : ℂ))
        ((fun z ↦ Complex.exp (θ * Complex.I) * discCenter c z) c) := by
    simpa using disc_uncenter_hasDerivAt_zero (b := b)
  have hcomp :
      HasDerivAt
        (fun z ↦ discUncenter b (Complex.exp (θ * Complex.I) * discCenter c z))
        ((((1 - ‖b‖ ^ 2 : ℝ) : ℂ)) *
          (Complex.exp (θ * Complex.I) * ((((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹))) c := by
    -- Route correction: compose through the concrete special-point derivatives before transporting
    -- back to the source-facing argument condition.
    exact houter.comp c hinner
  have hb_pos : 0 < 1 - ‖b‖ ^ 2 := by
    have hb_lt : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
    nlinarith [norm_nonneg b, hb_lt]
  have hc_pos : 0 < 1 - ‖c‖ ^ 2 := by
    have hc_lt : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
    nlinarith [norm_nonneg c, hc_lt]
  have harg_rot : Complex.IsArgument (Complex.exp (θ * Complex.I)) θ :=
    Complex.isArgument_exp_mul_I θ
  have harg_center :
      Complex.IsArgument
        (Complex.exp (θ * Complex.I) * (((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹) θ :=
    by
      simpa using
        (Complex.isArgument_mul_pos_real (r := (1 - ‖c‖ ^ 2)⁻¹) (inv_pos.mpr hc_pos) harg_rot)
  have harg_full :
      Complex.IsArgument
        ((Complex.exp (θ * Complex.I) * ((((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹)) *
          (((1 - ‖b‖ ^ 2 : ℝ) : ℂ))) θ :=
    Complex.isArgument_mul_pos_real hb_pos harg_center
  have hderiv :
      deriv (fun z ↦ discUncenter b (Complex.exp (θ * Complex.I) * discCenter c z)) c =
        ((((1 - ‖b‖ ^ 2 : ℝ) : ℂ)) *
          (Complex.exp (θ * Complex.I) * ((((1 - ‖c‖ ^ 2 : ℝ) : ℂ))⁻¹))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp.deriv
  -- Rewrite the chain-rule derivative into the same positive-real scaling normal form.
  rw [hderiv]
  simpa [mul_comm, mul_left_comm, mul_assoc] using harg_full

/-- Helper for Exercise 1: on an open set, an `EqOn` identity transports directly to equality of
ordinary derivatives at points of that set. -/
theorem eqOn_deriv_eq_of_isOpen {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ U) (hEq : EqOn f g U) :
    deriv f z = deriv g z := by
  -- Pass from the open-set equality to eventual equality in the neighborhood filter, then
  -- invoke the canonical derivative congruence owner.
  exact Filter.EventuallyEq.deriv_eq (Set.EqOn.eventuallyEq_of_mem hEq (hU.mem_nhds hz))

/-- Helper for Exercise 1: if a disc automorphism agrees with the explicit centered normalizer on
the open unit disc, then its derivative at the centering point has the prescribed argument. -/
theorem eqOn_centered_disc_normalizer_deriv_isArgument {c b : ℂ} {φ : ℂ → ℂ}
    (hc : c ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1) (θ : ℝ)
    (hEq : EqOn φ (fun z ↦ discUncenter b (Complex.exp (θ * Complex.I) * discCenter c z))
      (ball (0 : ℂ) 1)) :
    Complex.IsArgument (deriv φ c) θ := by
  -- Transport the packaged `EqOn` formula to an ordinary derivative identity and reuse the
  -- concrete derivative-angle computation from the source-faithful normalizer formula.
  rw [eqOn_deriv_eq_of_isOpen Metric.isOpen_ball hc hEq]
  exact centered_disc_normalizer_deriv_isArgument hc hb θ

/-- Helper for Exercise 1: once the residual rotation factor has exponential `1`, the centered
rotation model collapses to the identity on the unit disc. -/
theorem centered_rotation_eqOn_id_of_exp_eq_one {b : ℂ} (hb : b ∈ ball (0 : ℂ) 1) {τ : ℝ}
    (hexp : Complex.exp (τ * Complex.I) = 1) :
    EqOn (fun z ↦ discUncenter b (Complex.exp (τ * Complex.I) * discCenter b z)) id
      (ball (0 : ℂ) 1) := by
  -- Rewrite the rotation factor to `1`, then cancel the centering/uncentering pair on the disc.
  intro z hz
  rw [hexp]
  simpa using disc_uncenter_leftInvOn_disc_center hb hz

/-- Helper for Exercise 1: a disc automorphism fixing `b` is a centered rotation about `b`. -/
theorem unit_disc_automorphism_fixing_point_is_centered_rotation {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) 1)
    (h : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hfix : h b = b) :
    ∃ τ : ℝ,
      EqOn h
        (fun z ↦ discUncenter b (Complex.exp (τ * Complex.I) * discCenter b z))
        (ball (0 : ℂ) 1) := by
  -- Conjugate the `b`-fixed automorphism to one fixing `0`, classify it, then un-conjugate.
  rcases unit_disc_center_automorphism hb with ⟨κ, hκ⟩
  rcases unit_disc_uncenter_automorphism hb with ⟨υ, hυ⟩
  let g : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := (υ.trans h).trans κ
  have hg_fix : Function.IsFixedPt g 0 := by
    -- Route correction: prove the fixed-point classification by centered conjugation, not by
    -- treating the `b`-fixed case as a fresh Schwarz-lemma problem.
    have hzero_mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
    change κ (h (υ 0)) = 0
    rw [hυ hzero_mem, disc_uncenter_zero, hfix, hκ hb]
    simp
  rcases unit_disc_automorphism_fixing_zero_is_rotation g hg_fix with ⟨τ, hτ⟩
  refine ⟨τ, ?_⟩
  intro z hz
  have hz_center : discCenter b z ∈ ball (0 : ℂ) 1 := disc_center_mapsTo_unit_ball hb hz
  have hz_rot : Complex.exp (τ * Complex.I) * discCenter b z ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I] using hz_center
  have h_pullback : υ (discCenter b z) = z := by
    rw [hυ hz_center]
    exact disc_uncenter_leftInvOn_disc_center hb hz
  have hτ_eval : g (discCenter b z) = Complex.exp (τ * Complex.I) * discCenter b z := hτ hz_center
  have hhz : h z ∈ ball (0 : ℂ) 1 := h.mapsTo hz
  have hk_hz : κ (h z) = discCenter b (h z) := hκ hhz
  have hk_hz_mem : κ (h z) ∈ ball (0 : ℂ) 1 := κ.mapsTo hhz
  have hrecover : υ (κ (h z)) = h z := by
    rw [hυ hk_hz_mem, hk_hz]
    exact disc_uncenter_leftInvOn_disc_center hb hhz
  have hg_formula : g (discCenter b z) = κ (h z) := by
    change κ (h (υ (discCenter b z))) = κ (h z)
    rw [h_pullback]
  have hg_center : κ (h z) = Complex.exp (τ * Complex.I) * discCenter b z := by
    calc
      κ (h z) = g (discCenter b z) := hg_formula.symm
      _ = Complex.exp (τ * Complex.I) * discCenter b z := hτ_eval
  calc
    h z = υ (κ (h z)) := hrecover.symm
    _ = υ (Complex.exp (τ * Complex.I) * discCenter b z) := by rw [hg_center]
    _ = discUncenter b (Complex.exp (τ * Complex.I) * discCenter b z) := hυ hz_rot

/-- Exercise 1: for a proper simply connected open set `D ⊆ ℂ`, a point `a ∈ D`, a target point
`b` in the open unit disc, and a prescribed argument `α`, there is a unique holomorphic
biholomorphism from `D` to the unit disc sending `a` to `b` and with argument `α` for its
derivative at `a`, unique on `D`. -/
theorem existsUnique_normalized_riemann_map {D : Set ℂ} (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D) (hD_proper : D ≠ univ) {a : ℂ} (ha : a ∈ D)
    {b : ℂ} (hb : ‖b‖ < 1) (α : ℝ) :
    ∃ e : HolomorphicIsomorph D (ball (0 : ℂ) 1),
      IsNormalizedRiemannMap D a b α e ∧
        ∀ e' : HolomorphicIsomorph D (ball (0 : ℂ) 1),
          IsNormalizedRiemannMap D a b α e' → EqOn e e' D := by
  -- Route correction: first pin down the base Riemann map and the nonvanishing derivative that
  -- controls the later argument normalization.
  rcases simply_connected_open_set_biholomorphic_to_open_unit_disc
      hD_open hD_simplyConnected hD_proper with ⟨e₀⟩
  have hderiv₀ : derivWithin e₀ D a ≠ 0 :=
    holomorphic_isomorph_derivWithin_ne_zero e₀ ha
  have he₀a_mem : e₀ a ∈ ball (0 : ℂ) 1 := e₀.mapsTo ha
  have hb_mem : b ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hb
  let β : ℝ := Complex.arg (derivWithin e₀ D a)
  let θ : ℝ := α - β
  rcases unit_disc_center_automorphism he₀a_mem with ⟨κ, hκ⟩
  rcases unit_disc_rotation_automorphism θ with ⟨ρ, hρ⟩
  rcases unit_disc_uncenter_automorphism hb_mem with ⟨υ, hυ⟩
  let φ : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := (κ.trans ρ).trans υ
  have hφ_formula :
      EqOn φ
        (fun z ↦ discUncenter b (Complex.exp (θ * Complex.I) * discCenter (e₀ a) z))
        (ball (0 : ℂ) 1) := by
    -- The packaged automorphism is exactly the source-faithful center-rotate-uncenter formula.
    intro z hz
    have hz_center : discCenter (e₀ a) z ∈ ball (0 : ℂ) 1 :=
      disc_center_mapsTo_unit_ball he₀a_mem hz
    have hkz : κ z = discCenter (e₀ a) z := hκ hz
    have hkz_mem : κ z ∈ ball (0 : ℂ) 1 := κ.mapsTo hz
    have hρkz : ρ (κ z) = Complex.exp (θ * Complex.I) * κ z := hρ hkz_mem
    have hz_rot : Complex.exp (θ * Complex.I) * discCenter (e₀ a) z ∈ ball (0 : ℂ) 1 := by
      have hrot_map :
          MapsTo (fun w : ℂ ↦ Complex.exp (θ * Complex.I) * w)
            (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
        intro w hw
        simpa [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I] using hw
      exact hrot_map hz_center
    calc
      φ z = υ (ρ (κ z)) := rfl
      _ = discUncenter b (ρ (κ z)) := by
        have hρkz_mem : ρ (κ z) ∈ ball (0 : ℂ) 1 := ρ.mapsTo hkz_mem
        exact hυ hρkz_mem
      _ = discUncenter b (Complex.exp (θ * Complex.I) * κ z) := by
        rw [hρkz]
      _ = discUncenter b (Complex.exp (θ * Complex.I) * discCenter (e₀ a) z) := by
        rw [hkz]
  let e : HolomorphicIsomorph D (ball (0 : ℂ) 1) := e₀.trans φ
  have hea : e a = b := by
    -- Evaluate the normalized candidate at `a` by collapsing the centered automorphism at `e₀ a`.
    calc
      e a = φ (e₀ a) := rfl
      _ = discUncenter b (Complex.exp (θ * Complex.I) * discCenter (e₀ a) (e₀ a)) := by
        rw [hφ_formula he₀a_mem]
      _ = b := by
        simp
  have harg_e₀ : Complex.IsArgument (deriv e₀ a) β := by
    -- Rewrite the base Riemann-map derivative from the within-derivative on the open domain.
    simpa [β, derivWithin_of_mem_nhds (hD_open.mem_nhds ha)] using
      (show Complex.IsArgument (derivWithin e₀ D a) β from ⟨hderiv₀, rfl⟩)
  have harg_φ : Complex.IsArgument (deriv φ (e₀ a)) θ :=
    eqOn_centered_disc_normalizer_deriv_isArgument he₀a_mem hb_mem θ hφ_formula
  have he_deriv :
      deriv e a = deriv φ (e₀ a) * deriv e₀ a := by
    -- Differentiate the composed normalized candidate `e = φ ∘ e₀` at the source basepoint.
    have he₀_hasDerivAt : HasDerivAt e₀ (deriv e₀ a) a :=
      analyticAt_hasDerivAt (e₀.analyticAt ha)
    have hφ_hasDerivAt : HasDerivAt φ (deriv φ (e₀ a)) (e₀ a) :=
      analyticAt_hasDerivAt (φ.analyticAt he₀a_mem)
    have hcomp : HasDerivAt e (deriv φ (e₀ a) * deriv e₀ a) a := by
      simpa [e, OpenPartialHomeomorph.trans_apply, Function.comp_def] using
        hφ_hasDerivAt.comp a he₀_hasDerivAt
    simpa using hcomp.deriv
  have harg_e : Complex.IsArgument (derivWithin e D a) α := by
    -- Combine the angle of the explicit disc normalizer with the base Riemann-map derivative.
    rw [derivWithin_of_mem_nhds (hD_open.mem_nhds ha), he_deriv]
    simpa [θ, sub_add_cancel] using Complex.isArgument_mul harg_φ harg_e₀
  refine ⟨e, ⟨hea, harg_e⟩, ?_⟩
  intro e' he'_norm
  rcases he'_norm with ⟨he'a, harg_e'⟩
  let h : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := e.symm.trans e'
  have ha_source : a ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using ha
  have hsymm_b : ((e : OpenPartialHomeomorph ℂ ℂ).symm) b = a := by
    -- The chosen normalization point `a` is the unique preimage of `b` under `e`.
    calc
      ((e : OpenPartialHomeomorph ℂ ℂ).symm) b = ((e : OpenPartialHomeomorph ℂ ℂ).symm) (e a) := by
        rw [hea]
      _ = a := (e : OpenPartialHomeomorph ℂ ℂ).left_inv ha_source
  have hh_fix : h b = b := by
    -- The residual automorphism `h = e.symm.trans e'` fixes `b` because both maps send `a` to `b`.
    calc
      h b = e' (((e : OpenPartialHomeomorph ℂ ℂ).symm) b) := rfl
      _ = e' a := by rw [hsymm_b]
      _ = b := he'a
  rcases unit_disc_automorphism_fixing_point_is_centered_rotation hb_mem h hh_fix with ⟨τ, hτ⟩
  have harg_h : Complex.IsArgument (deriv h b) τ :=
    eqOn_centered_disc_normalizer_deriv_isArgument hb_mem hb_mem τ hτ
  have hEq_comp : EqOn (fun z ↦ h (e z)) e' D := by
    -- Pull the residual automorphism back along `e`; on `D` this recovers `e'`.
    intro z hz
    have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
      simpa [e.source_eq] using hz
    calc
      h (e z) = e' (((e : OpenPartialHomeomorph ℂ ℂ).symm) (e z)) := rfl
      _ = e' z := by rw [(e : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source]
  have harg_e_ord : Complex.IsArgument (deriv e a) α := by
    -- Rewrite the normalization condition for `e` to the ordinary derivative on the open domain.
    simpa [derivWithin_of_mem_nhds (hD_open.mem_nhds ha)] using harg_e
  have harg_e'_ord : Complex.IsArgument (deriv e' a) α := by
    -- Do the same for the competing normalized map `e'`.
    simpa [derivWithin_of_mem_nhds (hD_open.mem_nhds ha)] using harg_e'
  have hderiv_comp :
      deriv (fun z ↦ h (e z)) a = deriv h b * deriv e a := by
    -- Differentiate the pulled-back residual automorphism `h ∘ e` at `a`.
    have he_hasDerivAt : HasDerivAt e (deriv e a) a :=
      analyticAt_hasDerivAt (e.analyticAt ha)
    have hh_hasDerivAt : HasDerivAt h (deriv h b) b :=
      analyticAt_hasDerivAt (h.analyticAt hb_mem)
    have hh_hasDerivAt' : HasDerivAt h (deriv h b) (e a) := by
      simpa [hea] using hh_hasDerivAt
    have hcomp : HasDerivAt (fun z ↦ h (e z)) (deriv h b * deriv e a) a :=
      hh_hasDerivAt'.comp a he_hasDerivAt
    simpa using hcomp.deriv
  have harg_comp : Complex.IsArgument (deriv (fun z ↦ h (e z)) a) (τ + α) := by
    -- The derivative of `h ∘ e` carries the sum of the residual angle and the normalization angle.
    rw [hderiv_comp]
    exact Complex.isArgument_mul harg_h harg_e_ord
  have harg_comp' : Complex.IsArgument (deriv (fun z ↦ h (e z)) a) α := by
    -- The pullback equality identifies the same derivative with the derivative of `e'`.
    rw [eqOn_deriv_eq_of_isOpen hD_open ha hEq_comp]
    exact harg_e'_ord
  have hτ_angle : ((τ : ℝ) : Real.Angle) = 0 := by
    -- Compare the two argument descriptions of the same nonzero derivative.
    have hsum : ((τ + α : ℝ) : Real.Angle) = (α : Real.Angle) := by
      calc
        ((τ + α : ℝ) : Real.Angle) = Complex.arg (deriv (fun z ↦ h (e z)) a) := harg_comp.2
        _ = (α : Real.Angle) := harg_comp'.2.symm
    have hsum' : ((τ : ℝ) : Real.Angle) + (α : Real.Angle) = (0 : Real.Angle) + (α : Real.Angle) := by
      simpa [Real.Angle.coe_add]
        using hsum
    exact add_right_cancel hsum'
  have hexpτ : Complex.exp (τ * Complex.I) = 1 := by
    -- Convert the vanishing angle class back to the exponential normalization factor.
    have hcircle :
        ((((τ : ℝ) : Real.Angle).toCircle : Circle) : ℂ) =
          (((0 : Real.Angle).toCircle : Circle) : ℂ) := by
      simpa using congrArg (fun η : Real.Angle ↦ (((η.toCircle : Circle) : ℂ))) hτ_angle
    simpa [Real.Angle.toCircle_coe, Circle.coe_exp] using hcircle
  have h_id : EqOn h id (ball (0 : ℂ) 1) := by
    -- First compare `h` with the centered-rotation model, then collapse that model to the identity.
    intro z hz
    calc
      h z = discUncenter b (Complex.exp (τ * Complex.I) * discCenter b z) := hτ hz
      _ = z := centered_rotation_eqOn_id_of_exp_eq_one hb_mem hexpτ hz
  -- Collapse the residual automorphism to the identity and pull that identity back to `D`.
  intro z hz
  have hz_ball : e z ∈ ball (0 : ℂ) 1 := e.mapsTo hz
  calc
    e z = h (e z) := by
      simpa using (h_id hz_ball).symm
    _ = e' z := hEq_comp hz
