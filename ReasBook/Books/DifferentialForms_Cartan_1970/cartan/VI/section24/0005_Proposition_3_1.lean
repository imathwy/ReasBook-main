import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section03.«0012_Proposition_6_2»
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0005_Corollary_VI_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0006_Definition_VI_1_extra_4»
import DifferentialForms_Cartan_1970.cartan.VI.section23.«0007_Proposition_6_2»
import DifferentialForms_Cartan_1970.cartan.VI.section24.«0006_Lemma_VI_3_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ComplexConjugate

-- Domain sampling note:
-- * primary domain: one-variable complex analysis on simply connected planar domains;
-- * source-facing data here: a normalized injective holomorphic map from `D` into the unit disc;
-- * core/canonical chapter owner: `HolomorphicIsomorph D D'`;
-- * bridge layer needed here: once the source-facing map has image exactly the unit disc, it should
--   yield the canonical holomorphic-isomorphism owner.
-- Primitive data is only injectivity, holomorphicity on `D`, normalization at `0`, and the map
-- into the unit disc. The biholomorphic owner is derived from this stronger surjective case.

open Set

/-- A normalized univalent map on a domain `D` is an injective holomorphic map on `D` that sends
`0` to `0` and maps `D` into the unit disc. -/
def IsNormalizedUnivalentDiscMapOn (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  Set.InjOn f D ∧
    AnalyticOnNhd ℂ f D ∧
      f 0 = 0 ∧
        MapsTo f D (Metric.ball (0 : ℂ) 1)

namespace IsNormalizedUnivalentDiscMapOn

variable {D : Set ℂ} {f : ℂ → ℂ}

/-- The injectivity part of a normalized univalent disc map. -/
theorem injOn (hf : IsNormalizedUnivalentDiscMapOn D f) :
    Set.InjOn f D :=
  hf.1

/-- The holomorphicity part of a normalized univalent disc map. -/
theorem analyticOnNhd (hf : IsNormalizedUnivalentDiscMapOn D f) :
    AnalyticOnNhd ℂ f D :=
  hf.2.1

/-- A normalized univalent disc map fixes `0`. -/
theorem map_zero (hf : IsNormalizedUnivalentDiscMapOn D f) :
    f 0 = 0 :=
  hf.2.2.1

/-- A normalized univalent disc map sends its domain into the unit disc. -/
theorem mapsTo (hf : IsNormalizedUnivalentDiscMapOn D f) :
    MapsTo f D (Metric.ball (0 : ℂ) 1) :=
  hf.2.2.2

/-- Differentiability on the domain is derived from holomorphicity. -/
theorem differentiableOn (hf : IsNormalizedUnivalentDiscMapOn D f) :
    DifferentiableOn ℂ f D :=
  hf.analyticOnNhd.differentiableOn

private theorem exists_preimage_unitDisc
    (himage : f '' D = Metric.ball (0 : ℂ) 1) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    ∃ z ∈ D, f z = w := by
  have hw' : w ∈ f '' D := by simpa [himage] using hw
  rcases hw' with ⟨z, hz, rfl⟩
  exact ⟨z, hz, rfl⟩

private noncomputable def invFun
    (himage : f '' D = Metric.ball (0 : ℂ) 1) : ℂ → ℂ :=
  open scoped Classical in
  fun w ↦
    if hw : w ∈ Metric.ball (0 : ℂ) 1 then
      Classical.choose (exists_preimage_unitDisc himage hw)
    else
      0

private theorem invFun_mem
    (himage : f '' D = Metric.ball (0 : ℂ) 1) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    invFun himage w ∈ D := by
  classical
  unfold invFun
  simpa [hw] using (Classical.choose_spec (exists_preimage_unitDisc himage hw)).1

private theorem apply_invFun
    (himage : f '' D = Metric.ball (0 : ℂ) 1) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    f (invFun himage w) = w := by
  classical
  unfold invFun
  simpa [hw] using (Classical.choose_spec (exists_preimage_unitDisc himage hw)).2

private theorem invFun_apply (hf : IsNormalizedUnivalentDiscMapOn D f)
    (himage : f '' D = Metric.ball (0 : ℂ) 1) {z : ℂ}
    (hz : z ∈ D) :
    invFun himage (f z) = z := by
  have hfz : f z ∈ Metric.ball (0 : ℂ) 1 := hf.mapsTo hz
  apply hf.injOn (invFun_mem himage hfz) hz
  simpa using (apply_invFun himage hfz)

/-- Helper for Proposition 3.1: on the unit disc, the chosen inverse from the surjective image
description agrees with the canonical inverse branch `Function.invFunOn`. -/
private theorem invFun_eq_invFunOn_on_unit_disc
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    (himage : f '' D = Metric.ball (0 : ℂ) 1) :
    Set.EqOn (invFun himage) (Function.invFunOn f D) (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  -- Both inverse branches lie in `D` and map back to the same point `w`.
  apply hf.injOn
  · exact invFun_mem himage hw
  · exact Function.invFunOn_mem (exists_preimage_unitDisc himage hw)
  · calc
      f (invFun himage w) = w := apply_invFun himage hw
      _ = f (Function.invFunOn f D w) := by
        symm
        exact Function.invFunOn_eq (exists_preimage_unitDisc himage hw)

/-- Bridge to the chapter owner: if a normalized univalent disc map has image equal to the unit
disc, then it yields the canonical holomorphic isomorphism from `D` onto the unit disc. -/
noncomputable def toHolomorphicIsomorph (hf : IsNormalizedUnivalentDiscMapOn D f)
    (hD_open : IsOpen D) (himage : f '' D = Metric.ball (0 : ℂ) 1) :
    HolomorphicIsomorph D (Metric.ball (0 : ℂ) 1) := by
  refine ⟨?_, ?_⟩
  · exact {
    toFun := f
    invFun := invFun himage
    source := D
    target := Metric.ball (0 : ℂ) 1
    map_source' := hf.mapsTo
    map_target' := fun x hx ↦ invFun_mem himage hx
    left_inv' := fun x hx ↦ invFun_apply hf himage hx
    right_inv' := fun x hx ↦ apply_invFun himage hx
    open_source := hD_open
    open_target := Metric.isOpen_ball
    continuousOn_toFun := hf.analyticOnNhd.continuousOn
    continuousOn_invFun := by
      -- Replace the ad hoc inverse by the canonical inverse branch on the image disc.
      have hcont :
          ContinuousOn (Function.invFunOn f D) (Metric.ball (0 : ℂ) 1) := by
        simpa [himage] using
          (corollary_VI_1_extra_3_invFunOn_analyticOnNhd
            hf.analyticOnNhd hf.injOn hD_open).continuousOn
      exact ContinuousOn.congr hcont (invFun_eq_invFunOn_on_unit_disc hf himage)
  }
  · exact {
    source_eq := rfl
    target_eq := rfl
    analyticOn_toFun := hf.analyticOnNhd
    analyticOn_symm := by
      -- The analytic inverse-function theorem is already packaged for `Function.invFunOn`.
      have hanalytic :
          AnalyticOnNhd ℂ (Function.invFunOn f D) (Metric.ball (0 : ℂ) 1) := by
        simpa [himage] using
          corollary_VI_1_extra_3_invFunOn_analyticOnNhd hf.analyticOnNhd hf.injOn hD_open
      have hinv :
          AnalyticOnNhd ℂ (invFun himage) (Metric.ball (0 : ℂ) 1) :=
        AnalyticOnNhd.congr Metric.isOpen_ball hanalytic
          (invFun_eq_invFunOn_on_unit_disc hf himage).symm
      simpa using hinv
  }

/-- The canonical holomorphic isomorphism attached to a surjective normalized univalent disc map
acts by the original function. -/
@[simp] theorem toHolomorphicIsomorph_apply (hf : IsNormalizedUnivalentDiscMapOn D f)
    (hD_open : IsOpen D) (himage : f '' D = Metric.ball (0 : ℂ) 1) (z : ℂ) :
    hf.toHolomorphicIsomorph hD_open himage z = f z := by
  simp [toHolomorphicIsomorph]

/-- On the source domain, the canonical holomorphic isomorphism attached to a surjective normalized
univalent disc map agrees with the original function. -/
theorem toHolomorphicIsomorph_eqOn (hf : IsNormalizedUnivalentDiscMapOn D f)
    (hD_open : IsOpen D) (himage : f '' D = Metric.ball (0 : ℂ) 1) :
    Set.EqOn (hf.toHolomorphicIsomorph hD_open himage) f D :=
  fun z hz ↦ by simp

/-- Helper for Proposition 3.1: if the image of `f` is already the unit disc, then every other
normalized univalent disc map on `D` has no larger derivative norm at `0`. -/
private theorem deriv_norm_maximal_at_zero_of_image_eq_unitDisc
    {D : Set ℂ}
    (hD_open : IsOpen D)
    (h0D : (0 : ℂ) ∈ D)
    {f : ℂ → ℂ}
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    (himage : f '' D = Metric.ball (0 : ℂ) 1) :
    ∀ g : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn D g → ‖deriv g 0‖ ≤ ‖deriv f 0‖ := by
  intro g hg
  let e : HolomorphicIsomorph D (Metric.ball (0 : ℂ) 1) := hf.toHolomorphicIsomorph hD_open himage
  let φ : ℂ → ℂ := g ∘ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ)
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff] using (show ‖(0 : ℂ)‖ < 1 by norm_num)
  have hsymm_maps :
      MapsTo ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (Metric.ball (0 : ℂ) 1) D := by
    intro z hz
    have hz_target : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
      simpa [e.target_eq] using hz
    simpa [e.source_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
  have hφ_diff : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) := by
    -- Differentiate the conjugated map `g ∘ e.symm` on the unit disc.
    simpa [φ] using hg.differentiableOn.comp e.analyticOn_invFun.differentiableOn hsymm_maps
  have hφ_maps_ball : MapsTo φ (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact hg.mapsTo (hsymm_maps hz)
  have hzero_source : (0 : ℂ) ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using h0D
  have hφ0 : φ 0 = 0 := by
    have he_apply_zero : e 0 = 0 := by
      calc
        e 0 = f 0 := by
          simpa [e] using hf.toHolomorphicIsomorph_apply hD_open himage 0
        _ = 0 := hf.map_zero
    -- The inverse branch sends `0` back to the unique preimage `0`, so `φ` fixes the origin.
    calc
      φ 0 = g (((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (e 0)) := by
        rw [he_apply_zero]
        simp [φ]
      _ = g 0 := by
        rw [(e : OpenPartialHomeomorph ℂ ℂ).left_inv hzero_source]
      _ = 0 := hg.map_zero
  have hφ_maps_closed :
      MapsTo φ (Metric.ball (0 : ℂ) 1) (Metric.closedBall (φ 0) 1) := by
    intro z hz
    have hz_ball : φ z ∈ Metric.ball (0 : ℂ) 1 := hφ_maps_ball hz
    have hz_closed : ‖φ z‖ ≤ 1 := (mem_ball_zero_iff.mp hz_ball).le
    simpa [hφ0, mem_closedBall_zero_iff] using hz_closed
  have hφ_bound : ‖deriv φ 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hφ_diff hφ_maps_closed (by norm_num)
  have hEqOn : Set.EqOn (fun z ↦ φ (f z)) g D := by
    intro z hz
    have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
      simpa [e.source_eq] using hz
    have he_apply : e z = f z := by
      simpa [e] using hf.toHolomorphicIsomorph_apply hD_open himage z
    -- Reinsert the inverse branch of `e` and cancel it on the genuine source set.
    calc
      φ (f z) = g (((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) (e z)) := by
        rw [← he_apply]
        simp [φ]
      _ = g z := by
        rw [(e : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source]
  have hEq_nhds : (fun z ↦ φ (f z)) =ᶠ[nhds (0 : ℂ)] g := by
    exact Set.EqOn.eventuallyEq_of_mem hEqOn (hD_open.mem_nhds h0D)
  have hφ_analyticAt_zero : AnalyticAt ℂ φ 0 := by
    have hsymm_analyticAt_zero :
        AnalyticAt ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) 0 :=
      e.analyticOn_invFun 0 hzero_mem
    have hg_analyticAt_symm_zero :
        AnalyticAt ℂ g (((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) 0) :=
      hg.analyticOnNhd (((e : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) 0)
        (hsymm_maps hzero_mem)
    simpa [φ] using hg_analyticAt_symm_zero.comp hsymm_analyticAt_zero
  have hf_hasDerivAt : HasDerivAt f (deriv f 0) 0 :=
    (hf.analyticOnNhd 0 h0D).differentiableAt.hasDerivAt
  have hφ_hasDerivAt : HasDerivAt φ (deriv φ 0) 0 :=
    hφ_analyticAt_zero.differentiableAt.hasDerivAt
  have hderiv_event :
      deriv (fun z ↦ φ (f z)) 0 = deriv g 0 := by
    simpa using hEq_nhds.deriv_eq
  have hderiv_comp :
      deriv (fun z ↦ φ (f z)) 0 = deriv φ 0 * deriv f 0 := by
    -- The chain rule turns the local factorization into the product formula at `0`.
    simpa [Function.comp, hf.map_zero] using
      deriv_comp_of_eq (x := 0) (y := 0) hφ_analyticAt_zero.differentiableAt
        (hf.analyticOnNhd 0 h0D).differentiableAt hf.map_zero
  have hmul :
      ‖deriv φ 0‖ * ‖deriv f 0‖ ≤ ‖deriv f 0‖ := by
    simpa using mul_le_mul_of_nonneg_right hφ_bound (norm_nonneg (deriv f 0))
  calc
    ‖deriv g 0‖ = ‖deriv (fun z ↦ φ (f z)) 0‖ := by
      rw [hderiv_event]
    _ = ‖deriv φ 0 * deriv f 0‖ := by
      rw [hderiv_comp]
    _ = ‖deriv φ 0‖ * ‖deriv f 0‖ := norm_mul _ _
    _ ≤ ‖deriv f 0‖ := hmul

end IsNormalizedUnivalentDiscMapOn

/-- Helper for Proposition 3.1: an omitted point of the image cannot be the origin, because a
normalized univalent disc map already sends `0` to `0`. -/
private theorem omitted_point_ne_zero
    {D : Set ℂ} {f : ℂ → ℂ}
    (h0D : (0 : ℂ) ∈ D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha_omit : a ∉ f '' D) :
    a ≠ 0 := by
  -- The normalization `f 0 = 0` exhibits `0` as a point of the image.
  intro ha0
  apply ha_omit
  refine ⟨0, h0D, ?_⟩
  simpa [ha0] using hf.map_zero

/-- Helper for Proposition 3.1: the omitted-value disc automorphism `discCenter a ∘ f` maps `D`
into the punctured unit disc. -/
private theorem disc_center_comp_mapsTo_punctured_unitDisc
    {D : Set ℂ} {f : ℂ → ℂ}
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (ha_omit : a ∉ f '' D) :
    MapsTo (fun z ↦ discCenter a (f z)) D (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) := by
  intro z hz
  constructor
  · -- The disc automorphism preserves the unit disc after `f`.
    exact disc_center_mapsTo_unit_ball ha (hf.mapsTo hz)
  · -- If the centered value vanished, then `f z = a`, contradicting omission.
    intro hzero
    apply ha_omit
    refine ⟨z, hz, ?_⟩
    have hleft : Set.LeftInvOn (discUncenter a) (discCenter a) (Metric.ball (0 : ℂ) 1) :=
      disc_uncenter_leftInvOn_disc_center ha
    have hfz_ball : f z ∈ Metric.ball (0 : ℂ) 1 := hf.mapsTo hz
    have hzero' : discCenter a (f z) = 0 := by simpa using hzero
    calc
      f z = discUncenter a (discCenter a (f z)) := by
        symm
        exact hleft hfz_ball
      _ = discUncenter a 0 := by rw [hzero']
      _ = a := by simp

/-- Helper for Proposition 3.1: the omitted-value transform admits a continuous logarithm branch
on the simply connected domain. -/
private theorem disc_center_comp_exists_continuous_log_branch
    {D : Set ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hD_simply : IsSimplyConnected D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (ha_omit : a ∉ f '' D) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F D ∧
        Set.EqOn (Complex.exp ∘ F) (fun z ↦ discCenter a (f z)) D := by
  let m : ℂ → ℂ := fun z ↦ discCenter a (f z)
  have hdisc_analytic : AnalyticOnNhd ℂ (discCenter a) (Metric.ball (0 : ℂ) 1) := by
    -- Convert the known differentiability of `discCenter a` on the unit disc into analyticity.
    exact
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
        (disc_center_differentiableOn ha)
  have hm_cont : ContinuousOn m D := by
    -- The omitted-value transform is the composition of two holomorphic maps on their domains.
    exact hdisc_analytic.continuousOn.comp hf.analyticOnNhd.continuousOn hf.mapsTo
  have hm_nonzero : (0 : ℂ) ∉ m '' D := by
    -- The centered map never reaches `0`, precisely because `a` is omitted by `f`.
    intro hz
    rcases hz with ⟨z, hzD, hz0⟩
    exact (disc_center_comp_mapsTo_punctured_unitDisc hf ha ha_omit hzD).2 (by simp [m, hz0])
  -- Apply the simply connected logarithm-branch existence theorem to `discCenter a ∘ f`.
  rcases Complex.exists_continuousOn_eqOn_exp_comp hD_simply hD_open hm_cont hm_nonzero with
    ⟨F, hF_cont, hF_exp⟩
  exact ⟨F, hF_cont, hF_exp⟩

/-- Helper for Proposition 3.1: the continuous logarithm branch of the omitted-value transform has
negative real part on `D`, and its value at `0` has real part `log ‖a‖`. -/
private theorem continuous_log_branch_re_neg_and_center_re
    {D : Set ℂ} {f F : ℂ → ℂ}
    (h0D : (0 : ℂ) ∈ D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (ha_omit : a ∉ f '' D)
    (hF_exp : Set.EqOn (Complex.exp ∘ F) (fun z ↦ discCenter a (f z)) D) :
    (∀ z ∈ D, (F z).re < 0) ∧ (F 0).re = Real.log ‖a‖ := by
  have hmaps :
      MapsTo (fun z ↦ discCenter a (f z)) D (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) :=
    disc_center_comp_mapsTo_punctured_unitDisc hf ha ha_omit
  have ha_ne_zero : a ≠ 0 := omitted_point_ne_zero h0D hf ha_omit
  have hnorm_a_pos : 0 < ‖a‖ := norm_pos_iff.2 ha_ne_zero
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz_ball : discCenter a (f z) ∈ Metric.ball (0 : ℂ) 1 := (hmaps hz).1
    have hnorm_lt : ‖Complex.exp (F z)‖ < 1 := by
      have hEq : Complex.exp (F z) = discCenter a (f z) := by
        simpa [Function.comp] using hF_exp hz
      rw [hEq]
      simpa using hz_ball
    -- `‖exp (F z)‖ = exp (Re (F z))`, so being inside the unit disc forces `Re (F z) < 0`.
    rw [Complex.norm_exp] at hnorm_lt
    exact Real.exp_lt_one_iff.1 hnorm_lt
  · have hcenter_exp : Complex.exp (F 0) = -a := by
      -- At the origin the centered omitted-value transform is exactly `-a`.
      calc
        Complex.exp (F 0) = discCenter a (f 0) := by
          simpa [Function.comp] using hF_exp h0D
        _ = discCenter a 0 := by rw [hf.map_zero]
        _ = -a := by
          simp [discCenter]
    have hnorm : Real.exp ((F 0).re) = ‖a‖ := by
      calc
        Real.exp ((F 0).re) = ‖Complex.exp (F 0)‖ := by
          rw [Complex.norm_exp]
        _ = ‖-a‖ := by rw [hcenter_exp]
        _ = ‖a‖ := norm_neg a
    -- Taking the real logarithm identifies the real part of the branch value at the origin.
    have hlog := congrArg Real.log hnorm
    simpa [Real.log_exp, hnorm_a_pos.ne'] using hlog

/-- Helper for Proposition 3.1: the omitted-value transform `discCenter a ∘ f` stays injective on
`D`. -/
private theorem disc_center_comp_injOn
    {D : Set ℂ} {f : ℂ → ℂ}
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    Set.InjOn (fun z ↦ discCenter a (f z)) D := by
  intro z₁ hz₁ z₂ hz₂ hcenter
  have hleft : Set.LeftInvOn (discUncenter a) (discCenter a) (Metric.ball (0 : ℂ) 1) :=
    disc_uncenter_leftInvOn_disc_center ha
  -- Cancel the disc automorphism inside the unit disc and fall back to injectivity of `f`.
  apply hf.injOn hz₁ hz₂
  calc
    f z₁ = discUncenter a (discCenter a (f z₁)) := by
      symm
      exact hleft (hf.mapsTo hz₁)
    _ = discUncenter a (discCenter a (f z₂)) := by
      simpa using congrArg (discUncenter a) hcenter
    _ = f z₂ := hleft (hf.mapsTo hz₂)

/-- Helper for Proposition 3.1: the image of the omitted-value transform is an open connected set,
which is the correct domain for the transported logarithm branch. -/
private theorem disc_center_comp_image_open_connected
    {D : Set ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hD_simply : IsSimplyConnected D)
    (h0D : (0 : ℂ) ∈ D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    IsOpen ((fun z ↦ discCenter a (f z)) '' D) ∧
      IsConnected ((fun z ↦ discCenter a (f z)) '' D) := by
  let m : ℂ → ℂ := fun z ↦ discCenter a (f z)
  have hm_inj : Set.InjOn m D := disc_center_comp_injOn hf ha
  have hdisc_analytic : AnalyticOnNhd ℂ (discCenter a) (Metric.ball (0 : ℂ) 1) := by
    -- Convert the known differentiability of the disc automorphism into analyticity.
    exact
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
        (disc_center_differentiableOn ha)
  have hm_analytic : AnalyticOnNhd ℂ m D := by
    -- The omitted-value transform is the composition `discCenter a ∘ f`.
    exact hdisc_analytic.comp hf.analyticOnNhd hf.mapsTo
  have hm_nonconst : ¬ ∃ w : ℂ, ∀ z ∈ D, m z = w := by
    intro hconst
    rcases hconst with ⟨w, hw⟩
    rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds h0D) with ⟨r, hr_pos, hrD⟩
    let z : ℂ := ((r / 2 : ℝ) : ℂ)
    have hr_abs : |r| = r := abs_of_pos hr_pos
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      -- Openness around `0` gives a second domain point distinct from the base point.
      simpa [z, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, hr_abs] using
        half_lt_self hr_pos
    have hzD : z ∈ D := hrD hz_ball
    have hz_ne : z ≠ 0 := by
      have hz_real : (((r / 2 : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast (show (r / 2 : ℝ) ≠ 0 by linarith)
      simpa [z] using hz_real
    have hsame : m z = m 0 := by
      rw [hw z hzD, hw 0 h0D]
    exact hz_ne (hm_inj hzD h0D hsame)
  have hD_connected : IsConnected D := hD_simply.isPathConnected.isConnected
  refine ⟨?_, ?_⟩
  · -- The open mapping theorem applies because the transform is injective and nonconstant.
    simpa [m] using
      (hm_analytic.is_constant_or_isOpen hD_connected.isPreconnected).resolve_left hm_nonconst
        D subset_rfl hD_open
  · -- Connectedness is preserved under continuous images.
    simpa [m] using hD_connected.image m hm_analytic.continuousOn

/-- Helper for Proposition 3.1: transport the continuous logarithm branch on `D` to a genuine
`Complex.IsLogBranchOn` on the image of `discCenter a ∘ f`. -/
private theorem disc_center_comp_image_isLogBranch
    {D : Set ℂ} {f F : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hD_simply : IsSimplyConnected D)
    (h0D : (0 : ℂ) ∈ D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (hF_cont : ContinuousOn F D)
    (hF_exp : Set.EqOn (Complex.exp ∘ F) (fun z ↦ discCenter a (f z)) D) :
    ∃ L : ℂ → ℂ,
      Complex.IsLogBranchOn L ((fun z ↦ discCenter a (f z)) '' D) ∧
        Set.EqOn (fun z ↦ L (discCenter a (f z))) F D := by
  let m : ℂ → ℂ := fun z ↦ discCenter a (f z)
  let U : Set ℂ := m '' D
  let L : ℂ → ℂ := fun w ↦ F (Function.invFunOn m D w)
  have hm_inj : Set.InjOn m D := disc_center_comp_injOn hf ha
  have hdisc_analytic : AnalyticOnNhd ℂ (discCenter a) (Metric.ball (0 : ℂ) 1) := by
    -- Reuse the analytic owner of the disc automorphism in the inverse-branch theorem.
    exact
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
        (disc_center_differentiableOn ha)
  have hm_analytic : AnalyticOnNhd ℂ m D := by
    -- The source-proof controlled object is the centered map `m = discCenter a ∘ f`.
    exact hdisc_analytic.comp hf.analyticOnNhd hf.mapsTo
  have hU_open_connected : IsOpen U ∧ IsConnected U :=
    disc_center_comp_image_open_connected hD_open hD_simply h0D hf ha
  have hInv_analytic : AnalyticOnNhd ℂ (Function.invFunOn m D) U := by
    -- The inverse branch on the image is already packaged by the chapter's inverse theorem.
    simpa [U] using corollary_VI_1_extra_3_invFunOn_analyticOnNhd hm_analytic hm_inj hD_open
  have hInv_maps : MapsTo (Function.invFunOn m D) U D := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    exact Function.invFunOn_mem ⟨z, hz, rfl⟩
  have hpullback : Set.EqOn (fun z ↦ L (m z)) F D := by
    intro z hz
    -- On the source set, the transported branch collapses back to the original branch `F`.
    simp [L, m, hm_inj.leftInvOn_invFunOn hz]
  have hL_cont : ContinuousOn L U := by
    -- Continuity comes from composing `F` with the analytic inverse branch on the image.
    simpa [L] using hF_cont.comp hInv_analytic.continuousOn hInv_maps
  have hL_exp : Set.EqOn (Complex.exp ∘ L) id U := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    -- Pull back to `D`, where the branch identity was already constructed.
    have hz_eq : L (m z) = F z := hpullback hz
    calc
      Complex.exp (L (m z)) = Complex.exp (F z) := by rw [hz_eq]
      _ = m z := by simpa [Function.comp] using hF_exp hz
      _ = id (m z) := rfl
  refine ⟨L, ?_, ?_⟩
  · -- This is the corrected image-domain logarithm branch required by Proposition I.3.6.2.
    exact ⟨hU_open_connected.1, hU_open_connected.2, hL_cont, hL_exp⟩
  · simpa [m] using hpullback

/-- Helper for Proposition 3.1: the raw quotient defining `discCenter a` differentiates at `0`
with the textbook scalar `1 - ‖a‖^2`. -/
private theorem disc_center_raw_hasDerivAt_zero {a : ℂ} :
    HasDerivAt (fun z ↦ (z - a) / (1 - conj a * z)) (((1 : ℂ) - a * conj a)) 0 := by
  -- Differentiate the explicit numerator and denominator at the base point `0`.
  have hnum : HasDerivAt (fun z : ℂ ↦ z - a) 1 0 := by
    simpa using (hasDerivAt_id 0).sub_const a
  have hden_mul : HasDerivAt (fun z : ℂ ↦ conj a * z) (conj a) 0 := by
    simpa [one_mul] using (hasDerivAt_id 0).const_mul (conj a)
  have hden : HasDerivAt (fun z : ℂ ↦ 1 - conj a * z) (-conj a) 0 := by
    simpa using (hasDerivAt_const 0 (1 : ℂ)).sub hden_mul
  -- At `0` the denominator is `1`, so the quotient-rule scalar simplifies immediately.
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hnum.div hden (by simp)

/-- Helper for Proposition 3.1: `discCenter a` has derivative `1 - ‖a‖^2` at the origin. -/
private theorem disc_center_hasDerivAt_zero {a : ℂ} :
    HasDerivAt (discCenter a) (((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) 0 := by
  -- Bridge the raw quotient derivative back to the canonical owner `discCenter`.
  simpa [discCenter, Complex.mul_conj'] using disc_center_raw_hasDerivAt_zero (a := a)

/-- Helper for Proposition 3.1: the centered omitted-value map `discCenter a ∘ f` has the source
derivative factor `(1 - ‖a‖^2) * deriv f 0` at the origin. -/
private theorem disc_center_comp_hasDerivAt_zero
    {D : Set ℂ} {f : ℂ → ℂ}
    (h0D : (0 : ℂ) ∈ D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (fun z ↦ discCenter a (f z))
      ((((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) * deriv f 0) 0 := by
  let _ := ha
  have hf_hasDerivAt : HasDerivAt f (deriv f 0) 0 :=
    (hf.analyticOnNhd 0 h0D).differentiableAt.hasDerivAt
  -- Compose the derivative of `f` at `0` with the disc automorphism derivative at the centered
  -- base point `f 0 = 0`.
  simpa [hf.map_zero, mul_assoc] using
    (HasDerivAt.comp_of_eq
      (hh₂ := disc_center_hasDerivAt_zero (a := a))
      (hh := hf_hasDerivAt)
      (hy := hf.map_zero.symm))

/-- Helper for Proposition 3.1: once the logarithm branch lives on the image of
`discCenter a ∘ f`, its pullback has the textbook derivative norm at `0`. -/
private theorem disc_center_comp_log_deriv_norm_at_zero
    {D : Set ℂ} {f L : ℂ → ℂ}
    (h0D : (0 : ℂ) ∈ D)
    (hf : IsNormalizedUnivalentDiscMapOn D f)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (ha_omit : a ∉ f '' D)
    (hL_branch : Complex.IsLogBranchOn L ((fun z ↦ discCenter a (f z)) '' D))
    (hminus_a_mem : -a ∈ ((fun z ↦ discCenter a (f z)) '' D)) :
    ‖deriv (fun z ↦ L (discCenter a (f z))) 0‖ =
      ((1 - ‖a‖ ^ 2) / ‖a‖) * ‖deriv f 0‖ := by
  have ha_ne_zero : a ≠ 0 := omitted_point_ne_zero h0D hf ha_omit
  have hnorm_a_pos : 0 < ‖a‖ := norm_pos_iff.2 ha_ne_zero
  have hnorm_a_lt_one : ‖a‖ < 1 := by
    simpa [mem_ball_zero_iff] using ha
  have hcenter_hasDerivAt :
      HasDerivAt (fun z ↦ discCenter a (f z))
        ((((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) * deriv f 0) 0 :=
    disc_center_comp_hasDerivAt_zero h0D hf ha
  have hlog_hasDerivAt : HasDerivAt L (1 / (-a)) (-a) := by
    simpa using hL_branch.hasDerivAt hminus_a_mem
  have hdisc_zero : discCenter a (f 0) = -a := by
    rw [hf.map_zero]
    simp [discCenter]
  have hpull_hasDerivAt :
      HasDerivAt (fun z ↦ L (discCenter a (f z)))
        (((1 / (-a)) * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ))) * deriv f 0) 0 := by
    -- Apply the chain rule on the genuine image-domain logarithm branch.
    simpa [hdisc_zero, mul_assoc] using
      (HasDerivAt.comp_of_eq
        (hh₂ := hlog_hasDerivAt)
        (hh := hcenter_hasDerivAt)
        (hy := hdisc_zero.symm))
  have hscalar_norm :
      ‖(1 / (-a)) * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ))‖ = (1 - ‖a‖ ^ 2) / ‖a‖ := by
    have hfactor_nonneg : 0 ≤ 1 - ‖a‖ ^ 2 := by
      nlinarith [sq_nonneg ‖a‖, hnorm_a_lt_one]
    -- Separate the norm into the logarithm-branch factor and the disc-center factor.
    rw [norm_mul, one_div, norm_inv, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hfactor_nonneg]
    simp [div_eq_mul_inv, mul_comm]
  have hderiv_eq :
      deriv (fun z ↦ L (discCenter a (f z))) 0 =
        ((1 / (-a)) * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ))) * deriv f 0 := by
    simpa [mul_assoc] using hpull_hasDerivAt.deriv
  -- Taking norms produces the source formula `((1 - ‖a‖^2) / ‖a‖) * ‖deriv f 0‖`.
  calc
    ‖deriv (fun z ↦ L (discCenter a (f z))) 0‖ =
        ‖((1 / (-a)) * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ))) * deriv f 0‖ := by
      rw [hderiv_eq]
    _ = ‖(1 / (-a)) * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ))‖ * ‖deriv f 0‖ := norm_mul _ _
    _ = ((1 - ‖a‖ ^ 2) / ‖a‖) * ‖deriv f 0‖ := by
      rw [hscalar_norm]

/-- Helper for Proposition 3.1: the denominator in the left-half-plane normalization never
vanishes on `D`, because its real part stays strictly negative. -/
private theorem left_half_plane_normalization_denominator_ne_zero
    {D : Set ℂ} (h0D : (0 : ℂ) ∈ D) {K : ℂ → ℂ}
    (hK_re_neg : ∀ z ∈ D, (K z).re < 0) {z : ℂ} (hz : z ∈ D) :
    K z + conj (K 0) ≠ 0 := by
  intro hzero
  have hden_re : (K z + conj (K 0)).re < 0 := by
    simpa [Complex.add_re, Complex.conj_re] using add_lt_add (hK_re_neg z hz) (hK_re_neg 0 h0D)
  have : ¬ ((0 : ℂ).re < 0) := by simp
  exact this (hzero ▸ hden_re)

/-- Helper for Proposition 3.1: the Möbius normalization of a left-half-plane-valued map lands in
the unit disc. -/
private theorem left_half_plane_normalization_mapsTo_unitDisc
    {D : Set ℂ} (h0D : (0 : ℂ) ∈ D) {K : ℂ → ℂ}
    (hK_re_neg : ∀ z ∈ D, (K z).re < 0) :
    MapsTo (fun z ↦ (K z - K 0) / (K z + conj (K 0))) D (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  -- Apply the textbook half-plane lemma pointwise with `u = K 0` and `v = K z`.
  have hnorm_lt :
      ‖(K z - K 0) / (K z + conj (K 0))‖ < 1 :=
    complex_abs_sub_div_add_conj_lt_one_of_re_neg (hK_re_neg 0 h0D) (hK_re_neg z hz)
  simpa [mem_ball_zero_iff] using hnorm_lt

/-- Helper for Proposition 3.1: the Möbius normalization of a left-half-plane-valued analytic map
is analytic on the source domain. -/
private theorem left_half_plane_normalization_analyticOnNhd
    {D : Set ℂ} (h0D : (0 : ℂ) ∈ D) {K : ℂ → ℂ}
    (hK_analytic : AnalyticOnNhd ℂ K D) (hK_re_neg : ∀ z ∈ D, (K z).re < 0) :
    AnalyticOnNhd ℂ (fun z ↦ (K z - K 0) / (K z + conj (K 0))) D := by
  intro z hz
  -- The denominator is pointwise nonzero, so analyticity is preserved under division.
  exact
    (hK_analytic z hz).sub analyticAt_const |>.div
      ((hK_analytic z hz).add analyticAt_const)
      (left_half_plane_normalization_denominator_ne_zero h0D hK_re_neg hz)

/-- Helper for Proposition 3.1: the Möbius normalization preserves injectivity on the source
domain. -/
private theorem left_half_plane_normalization_injOn
    {D : Set ℂ} (h0D : (0 : ℂ) ∈ D) {K : ℂ → ℂ}
    (hK_inj : Set.InjOn K D) (hK_re_neg : ∀ z ∈ D, (K z).re < 0) :
    Set.InjOn (fun z ↦ (K z - K 0) / (K z + conj (K 0))) D := by
  intro z₁ hz₁ z₂ hz₂ hnorm
  have hz₁_den :
      K z₁ + conj (K 0) ≠ 0 :=
    left_half_plane_normalization_denominator_ne_zero h0D hK_re_neg hz₁
  have hz₂_den :
      K z₂ + conj (K 0) ≠ 0 :=
    left_half_plane_normalization_denominator_ne_zero h0D hK_re_neg hz₂
  have hcross :
      (K z₁ - K 0) * (K z₂ + conj (K 0)) =
        (K z₂ - K 0) * (K z₁ + conj (K 0)) := by
    exact (div_eq_div_iff hz₁_den hz₂_den).1 hnorm
  have hfactor :
      (K 0 + conj (K 0)) * (K z₁ - K z₂) = 0 := by
    calc
      (K 0 + conj (K 0)) * (K z₁ - K z₂) =
          (K z₁ - K 0) * (K z₂ + conj (K 0)) -
            (K z₂ - K 0) * (K z₁ + conj (K 0)) := by ring
      _ = 0 := by rw [hcross]; ring
  have hcenter_den :
      K 0 + conj (K 0) ≠ 0 :=
    left_half_plane_normalization_denominator_ne_zero h0D hK_re_neg h0D
  have hK_eq : K z₁ = K z₂ := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hcenter_den)
  exact hK_inj hz₁ hz₂ hK_eq

/-- Helper for Proposition 3.1: the derivative norm of the left-half-plane normalization at the
origin is the derivative norm of `K` divided by `-2 * Re (K 0)`. -/
private theorem left_half_plane_normalization_deriv_norm_at_zero
    {D : Set ℂ} (h0D : (0 : ℂ) ∈ D) {K : ℂ → ℂ}
    (hK_analytic : AnalyticOnNhd ℂ K D) (hK_re_neg : ∀ z ∈ D, (K z).re < 0) :
    ‖deriv (fun z ↦ (K z - K 0) / (K z + conj (K 0))) 0‖ =
      ‖deriv K 0‖ / (-2 * (K 0).re) := by
  let g : ℂ → ℂ := fun z ↦ (K z - K 0) / (K z + conj (K 0))
  have hK0 : HasDerivAt K (deriv K 0) 0 :=
    (hK_analytic 0 h0D).differentiableAt.hasDerivAt
  have hnum :
      HasDerivAt (fun z ↦ K z - K 0) (deriv K 0) 0 := by
    simpa using hK0.sub_const (K 0)
  have hden :
      HasDerivAt (fun z ↦ K z + conj (K 0)) (deriv K 0) 0 := by
    simpa using hK0.add_const (conj (K 0))
  have hden_ne :
      K 0 + conj (K 0) ≠ 0 :=
    left_half_plane_normalization_denominator_ne_zero h0D hK_re_neg h0D
  have hderiv_eq :
      deriv g 0 = deriv K 0 / (K 0 + conj (K 0)) := by
    have hquot :
        HasDerivAt g
          ((deriv K 0 * (K 0 + conj (K 0)) -
              (K 0 - K 0) * deriv K 0) /
            (K 0 + conj (K 0)) ^ 2)
          0 := by
      simpa [g] using hnum.div hden hden_ne
    have hquot_simplified :
        ((deriv K 0 * (K 0 + conj (K 0)) -
              (K 0 - K 0) * deriv K 0) /
            (K 0 + conj (K 0)) ^ 2) =
          deriv K 0 / (K 0 + conj (K 0)) := by
      field_simp [hden_ne]
      ring
    calc
      deriv g 0 =
          ((deriv K 0 * (K 0 + conj (K 0)) -
                (K 0 - K 0) * deriv K 0) /
              (K 0 + conj (K 0)) ^ 2) := hquot.deriv
      _ = deriv K 0 / (K 0 + conj (K 0)) := hquot_simplified
  have hden_real :
      K 0 + conj (K 0) = (((2 * (K 0).re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.conj_re]
      ring
    · simp [Complex.add_im, Complex.conj_im]
  have hden_norm :
      ‖K 0 + conj (K 0)‖ = -2 * (K 0).re := by
    rw [hden_real, Complex.norm_real, Real.norm_eq_abs]
    have hre : 2 * (K 0).re < 0 := by
      nlinarith [hK_re_neg 0 h0D]
    rw [abs_of_neg hre]
    ring
  -- Rewrite the quotient-rule derivative into the textbook norm formula.
  calc
    ‖deriv g 0‖ = ‖deriv K 0 / (K 0 + conj (K 0))‖ := by rw [hderiv_eq]
    _ = ‖deriv K 0‖ / ‖K 0 + conj (K 0)‖ := norm_div _ _
    _ = ‖deriv K 0‖ / (-2 * (K 0).re) := by rw [hden_norm]

/-- Helper for Proposition 3.1: a normalized univalent map has nonzero derivative at the origin,
because the analytic inverse branch differentiates the identity `invFunOn ∘ f = id`. -/
private theorem normalized_univalent_deriv_ne_zero_at_zero
    {D : Set ℂ} (hD_open : IsOpen D) (h0D : (0 : ℂ) ∈ D) {f : ℂ → ℂ}
    (hf : IsNormalizedUnivalentDiscMapOn D f) :
    deriv f 0 ≠ 0 := by
  let ψ : ℂ → ℂ := Function.invFunOn f D
  have hψ_analytic : AnalyticOnNhd ℂ ψ (f '' D) :=
    corollary_VI_1_extra_3_invFunOn_analyticOnNhd hf.analyticOnNhd hf.injOn hD_open
  have hzero_image : (0 : ℂ) ∈ f '' D := ⟨0, h0D, hf.map_zero⟩
  have hψ_analyticAt_zero : AnalyticAt ℂ ψ 0 := hψ_analytic 0 hzero_image
  have hEqOn : Set.EqOn (fun z ↦ ψ (f z)) id D := by
    intro z hz
    apply hf.injOn (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz
    exact Function.invFunOn_eq ⟨z, hz, rfl⟩
  have hEq_nhds : (fun z ↦ ψ (f z)) =ᶠ[nhds (0 : ℂ)] id := by
    exact Set.EqOn.eventuallyEq_of_mem hEqOn (hD_open.mem_nhds h0D)
  have hderiv_event : deriv (fun z ↦ ψ (f z)) 0 = 1 := by
    simpa using hEq_nhds.deriv_eq
  have hderiv_comp :
      deriv (fun z ↦ ψ (f z)) 0 = deriv ψ 0 * deriv f 0 := by
    -- Differentiate the inverse-branch identity near `0`.
    simpa [Function.comp, hf.map_zero] using
      deriv_comp_of_eq (x := 0) (y := 0) hψ_analyticAt_zero.differentiableAt
        (hf.analyticOnNhd 0 h0D).differentiableAt hf.map_zero
  intro hderiv
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = deriv (fun z ↦ ψ (f z)) 0 := by symm; exact hderiv_event
      _ = deriv ψ 0 * deriv f 0 := hderiv_comp
      _ = 0 := by rw [hderiv, mul_zero]
  exact one_ne_zero this

/-- Helper for Proposition 3.1: the scalar gain from the omitted-value transform is strictly
larger than `1`. -/
private theorem disc_center_gain_gt_one
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    1 < ((1 - t ^ 2) / t) / (-2 * Real.log t) := by
  let φ : ℝ → ℝ := fun x ↦ x⁻¹ + (-x + (Real.log x + Real.log x))
  have hφ_cont : ContinuousOn φ (Set.Icc t 1) := by
    have hinv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Set.Icc t 1) := by
      refine ContinuousOn.inv₀ continuousOn_id ?_
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le ht0 hx.1)
    have hlog : ContinuousOn Real.log (Set.Icc t 1) := by
      refine ContinuousOn.mono Real.continuousOn_log ?_
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le ht0 hx.1)
    -- The scalar comparison function is continuous on the compact interval `[t, 1]`.
    simpa [φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hinv.add (hlog.add hlog)).sub continuousOn_id
  have hφ_deriv_neg : ∀ x ∈ interior (Set.Icc t 1), deriv φ x < 0 := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo t 1 := by
      simpa [interior_Icc, Set.mem_Ioo] using hx
    have hx_pos : 0 < x := lt_trans ht0 hxIoo.1
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hderiv :
        HasDerivAt φ (-(x ^ 2)⁻¹ - 1 + 2 * x⁻¹) x := by
      have hinv : HasDerivAt (fun y : ℝ ↦ y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx_ne
      have hlog :
          HasDerivAt (fun y : ℝ ↦ Real.log y * 2) (x⁻¹ * 2) x := by
        simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (Real.hasDerivAt_log hx_ne).mul_const (2 : ℝ)
      have hraw := (hinv.add hlog).sub (hasDerivAt_id x)
      convert hraw using 1
      · funext y
        simp [φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_mul]
        ring
      · ring
    have hderiv_eq : deriv φ x = -(x ^ 2)⁻¹ - 1 + 2 * x⁻¹ := hderiv.deriv
    have hrewrite :
        (-(x ^ 2)⁻¹ - 1 + 2 * x⁻¹) = -((1 - x) ^ 2 / x ^ 2) := by
      field_simp [hx_ne]
      ring
    rw [hderiv_eq, hrewrite]
    have hratio_pos : 0 < (1 - x) ^ 2 / x ^ 2 := by
      refine div_pos ?_ ?_
      · exact sq_pos_iff.mpr (sub_ne_zero.mpr hxIoo.2.ne')
      · exact sq_pos_iff.mpr hx_ne
    linarith
  have hanti :
      StrictAntiOn φ (Set.Icc t 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc t 1) hφ_cont hφ_deriv_neg
  have hφ_pos : 0 < φ t := by
    have hstrict : φ 1 < φ t := hanti ⟨le_rfl, ht1.le⟩ ⟨ht1.le, le_rfl⟩ ht1
    simpa [φ] using hstrict
  have hineq :
      -2 * Real.log t < (1 - t ^ 2) / t := by
    have hscaled : 0 < t * φ t := mul_pos ht0 hφ_pos
    have hscaled_eq : t * φ t = 1 + t * Real.log t * 2 - t ^ 2 := by
      simp [φ]
      field_simp [ht0.ne']
      ring
    rw [hscaled_eq] at hscaled
    have hmul : (-2 * Real.log t) * t < 1 - t ^ 2 := by
      linarith
    exact (lt_div_iff₀ ht0).2 (by simpa [mul_comm] using hmul)
  have hden_pos : 0 < -2 * Real.log t := by
    have hlog_neg : Real.log t < 0 := Real.log_neg ht0 ht1
    linarith
  -- Rewrite the positivity of the comparison function into the desired gain inequality.
  rw [one_lt_div_iff]
  exact Or.inl ⟨hden_pos, hineq⟩

/-- Proposition 3.1. For a simply connected proper domain `D` containing `0`, a normalized
univalent holomorphic map `f` on `D` has image exactly the unit disc if and only if the derivative
norm `‖deriv f 0‖` is maximal among all normalized univalent holomorphic maps of `D` into the unit
disc. -/
theorem image_eq_unitDisc_iff_deriv_norm_maximal_at_zero
    {D : Set ℂ}
    (hD_open : IsOpen D)
    (hD_simply : IsSimplyConnected D)
    (hD_proper : D ≠ univ)
    (h0D : (0 : ℂ) ∈ D)
    {f : ℂ → ℂ}
    (hf : IsNormalizedUnivalentDiscMapOn D f) :
    f '' D = Metric.ball (0 : ℂ) 1 ↔
      ∀ g : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn D g → ‖deriv g 0‖ ≤ ‖deriv f 0‖ := by
  constructor
  · intro himage
    -- The surjective case is the source-proof necessity direction via Schwarz on `g ∘ f⁻¹`.
    exact IsNormalizedUnivalentDiscMapOn.deriv_norm_maximal_at_zero_of_image_eq_unitDisc
      hD_open h0D hf himage
  · intro hmax
    -- Route correction: the continuous logarithm branch must live on the image
    -- `(discCenter a ∘ f) '' D`, not as `Complex.IsLogBranchOn` on `D` itself.
    -- The verified frontier below constructs the continuous branch on `D` and proves the
    -- real-part identities needed for the textbook normalization step.
    by_contra himage
    have hsubset_ball : f '' D ⊆ Metric.ball (0 : ℂ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      exact hf.mapsTo hz
    have hnot_subset : ¬ Metric.ball (0 : ℂ) 1 ⊆ f '' D := by
      intro hball_subset
      exact himage <| by
        ext z
        constructor
        · intro hz
          exact hsubset_ball hz
        · intro hz
          exact hball_subset hz
    rcases Set.not_subset.1 hnot_subset with ⟨a, ha_ball, ha_omit⟩
    rcases
      disc_center_comp_exists_continuous_log_branch
        hD_open hD_simply hf ha_ball ha_omit with
      ⟨F, hF_cont, hF_exp⟩
    have hF_geometry :
        (∀ z ∈ D, (F z).re < 0) ∧ (F 0).re = Real.log ‖a‖ :=
      continuous_log_branch_re_neg_and_center_re h0D hf ha_ball ha_omit hF_exp
    rcases
      disc_center_comp_image_isLogBranch hD_open hD_simply h0D hf ha_ball hF_cont hF_exp with
      ⟨L, hL_branch, hLF_eq⟩
    have hL_center_re : (L (-a)).re = Real.log ‖a‖ := by
      have hdisc_zero : discCenter a (f 0) = -a := by
        rw [hf.map_zero]
        simp [discCenter]
      have hpull_zero : L (discCenter a (f 0)) = F 0 := hLF_eq h0D
      -- Pull the transported branch back to the base point where the continuous branch was normalized.
      calc
        (L (-a)).re = (L (discCenter a (f 0))).re := by rw [hdisc_zero]
        _ = (F 0).re := by rw [hpull_zero]
        _ = Real.log ‖a‖ := hF_geometry.2
    have hL_re_neg : ∀ z ∈ D, (L (discCenter a (f z))).re < 0 := by
      intro z hz
      -- The real-part control is imported from the original branch on `D`.
      have hz_eq : L (discCenter a (f z)) = F z := hLF_eq hz
      rw [hz_eq]
      exact hF_geometry.1 z hz
    have hminus_a_mem : -a ∈ ((fun z ↦ discCenter a (f z)) '' D) := by
      refine ⟨0, h0D, ?_⟩
      change discCenter a (f 0) = -a
      rw [hf.map_zero]
      simp [discCenter]
    have hK_deriv_norm :
        ‖deriv (fun z ↦ L (discCenter a (f z))) 0‖ =
          ((1 - ‖a‖ ^ 2) / ‖a‖) * ‖deriv f 0‖ :=
      disc_center_comp_log_deriv_norm_at_zero
        h0D hf ha_ball ha_omit hL_branch hminus_a_mem
    let K : ℂ → ℂ := fun z ↦ L (discCenter a (f z))
    let g : ℂ → ℂ := fun z ↦ (K z - K 0) / (K z + conj (K 0))
    have hnorm_a_pos : 0 < ‖a‖ := by
      exact norm_pos_iff.2 (omitted_point_ne_zero h0D hf ha_omit)
    have hnorm_a_lt_one : ‖a‖ < 1 := by
      simpa [mem_ball_zero_iff] using ha_ball
    have hcenter_analytic : AnalyticOnNhd ℂ (fun z ↦ discCenter a (f z)) D := by
      have hdisc_analytic : AnalyticOnNhd ℂ (discCenter a) (Metric.ball (0 : ℂ) 1) := by
        exact
          (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
            (disc_center_differentiableOn ha_ball)
      -- The source-controlled centered map is holomorphic on `D`.
      exact hdisc_analytic.comp hf.analyticOnNhd hf.mapsTo
    have hK_re_neg : ∀ z ∈ D, (K z).re < 0 := by
      intro z hz
      simpa [K] using hL_re_neg z hz
    have hK_inj : Set.InjOn K D := by
      intro z₁ hz₁ z₂ hz₂ hK_eq
      have hcenter_eq : discCenter a (f z₁) = discCenter a (f z₂) := by
        -- Exponentiating the transported logarithm branch recovers the centered map.
        calc
          discCenter a (f z₁) = Complex.exp (K z₁) := by
            change discCenter a (f z₁) = Complex.exp (L (discCenter a (f z₁)))
            symm
            exact hL_branch.2.2.2 ⟨z₁, hz₁, rfl⟩
          _ = Complex.exp (K z₂) := by rw [hK_eq]
          _ = discCenter a (f z₂) := by
            change Complex.exp (L (discCenter a (f z₂))) = discCenter a (f z₂)
            exact hL_branch.2.2.2 ⟨z₂, hz₂, rfl⟩
      exact disc_center_comp_injOn hf ha_ball hz₁ hz₂ hcenter_eq
    have hK_diff : DifferentiableOn ℂ K D := by
      intro z hz
      have hm_mem : discCenter a (f z) ∈ ((fun w ↦ discCenter a (f w)) '' D) := ⟨z, hz, rfl⟩
      have hL_hasDeriv :
          HasDerivAt L (1 / (discCenter a (f z))) (discCenter a (f z)) :=
        hL_branch.hasDerivAt hm_mem
      have hm_hasDeriv :
          HasDerivAt (fun w ↦ discCenter a (f w))
            (deriv (fun w ↦ discCenter a (f w)) z) z :=
        (hcenter_analytic z hz).differentiableAt.hasDerivAt
      -- Compose the image-domain logarithm derivative with the centered source map.
      have hK_hasDeriv :
          HasDerivAt K ((1 / (discCenter a (f z))) * deriv (fun w ↦ discCenter a (f w)) z) z := by
        simpa [K] using
          (HasDerivAt.comp_of_eq (hh₂ := hL_hasDeriv) (hh := hm_hasDeriv) (hy := rfl))
      exact hK_hasDeriv.differentiableAt.differentiableWithinAt
    have hK_analytic : AnalyticOnNhd ℂ K D := by
      exact (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 hK_diff
    have hK0_re : (K 0).re = Real.log ‖a‖ := by
      have hdisc_zero : discCenter a (f 0) = -a := by
        rw [hf.map_zero]
        simp [discCenter]
      -- The branch value at the base point is normalized exactly as in the source proof.
      calc
        (K 0).re = (L (discCenter a (f 0))).re := rfl
        _ = (L (-a)).re := by rw [hdisc_zero]
        _ = Real.log ‖a‖ := hL_center_re
    have hg : IsNormalizedUnivalentDiscMapOn D g := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact left_half_plane_normalization_injOn h0D hK_inj hK_re_neg
      · simpa [g] using left_half_plane_normalization_analyticOnNhd h0D hK_analytic hK_re_neg
      · simp [g]
      · simpa [g] using left_half_plane_normalization_mapsTo_unitDisc h0D hK_re_neg
    have hbound : ‖deriv g 0‖ ≤ ‖deriv f 0‖ := hmax g hg
    have hg_deriv :
        ‖deriv g 0‖ =
          (((1 - ‖a‖ ^ 2) / ‖a‖) / (-2 * Real.log ‖a‖)) * ‖deriv f 0‖ := by
      calc
        ‖deriv g 0‖ = ‖deriv K 0‖ / (-2 * (K 0).re) := by
          simpa [g] using left_half_plane_normalization_deriv_norm_at_zero h0D hK_analytic hK_re_neg
        _ = (((1 - ‖a‖ ^ 2) / ‖a‖) * ‖deriv f 0‖) / (-2 * Real.log ‖a‖) := by
          rw [hK_deriv_norm, hK0_re]
        _ = (((1 - ‖a‖ ^ 2) / ‖a‖) / (-2 * Real.log ‖a‖)) * ‖deriv f 0‖ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    have hgain :
        1 < (((1 - ‖a‖ ^ 2) / ‖a‖) / (-2 * Real.log ‖a‖)) :=
      disc_center_gain_gt_one hnorm_a_pos hnorm_a_lt_one
    have hf_deriv_ne : deriv f 0 ≠ 0 :=
      normalized_univalent_deriv_ne_zero_at_zero hD_open h0D hf
    have hnorm_f_pos : 0 < ‖deriv f 0‖ := norm_pos_iff.2 hf_deriv_ne
    have hstrict :
        ‖deriv f 0‖ <
          (((1 - ‖a‖ ^ 2) / ‖a‖) / (-2 * Real.log ‖a‖)) * ‖deriv f 0‖ := by
      simpa using mul_lt_mul_of_pos_right hgain hnorm_f_pos
    have hbound' :
        (((1 - ‖a‖ ^ 2) / ‖a‖) / (-2 * Real.log ‖a‖)) * ‖deriv f 0‖ ≤ ‖deriv f 0‖ := by
      simpa [hg_deriv] using hbound
    exact (not_lt_of_ge hbound') hstrict
