import DifferentialForms_Cartan_1970.cartan.III.section12.«0022_Exercise_10»
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»
import DifferentialForms_Cartan_1970.VI.section23.«0006_Proposition_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Function Metric Set
open scoped ComplexConjugate

-- Domain sampling note: this proposition lives in one-variable complex analysis on the unit disc.
-- The source-facing owner for biholomorphic self-maps of the disc is already
-- `HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)`, while the primitive Möbius model is
-- `discUncenter`. The theorem below therefore quantifies over a single disc automorphism and uses
-- `discUncenter` only for the normal-form conclusion.

/-- Helper for Proposition 6.2: a holomorphic isomorphism maps its prescribed source into its
prescribed target. -/
private theorem holomorphicIsomorph_mapsTo {D D' : Set ℂ} (e : HolomorphicIsomorph D D') :
    MapsTo e D D' := by
  -- Rewrite the source membership to the underlying partial-homeomorphism source.
  intro z hz
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  -- Then transport the image back through the prescribed target equality.
  simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source

/-- Helper for Proposition 6.2: the composition of two holomorphic isomorphisms is again a
holomorphic isomorphism. -/
private theorem holomorphicIsomorph_comp_isHolomorphicIsoOn
    {D D' D'' : Set ℂ} (e : HolomorphicIsomorph D D') (e' : HolomorphicIsomorph D' D'') :
    OpenPartialHomeomorph.IsHolomorphicIsoOn
      ((e : OpenPartialHomeomorph ℂ ℂ).trans (e' : OpenPartialHomeomorph ℂ ℂ)) D D'' := by
  refine
    { source_eq := ?_
      target_eq := ?_
      analyticOn_toFun := ?_
      analyticOn_symm := ?_ }
  · -- The composed source is all of `D` because `e` already lands in `D'`.
    ext z
    constructor
    · intro hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      simpa [e.source_eq] using hz.1
    · intro hz
      have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
        simpa [e.source_eq] using hz
      have hez_source : e z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).source := by
        simpa [e.target_eq, e'.source_eq] using
          (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨hz_source, hez_source⟩
  · -- Dually, the composed target is all of `D''`.
    ext z
    constructor
    · intro hz
      rw [OpenPartialHomeomorph.trans_target] at hz
      simpa [e'.target_eq] using hz.1
    · intro hz
      have hz_target : z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e'.target_eq] using hz
      have hpre_target :
          (e' : OpenPartialHomeomorph ℂ ℂ).symm z ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e.target_eq, e'.source_eq] using
          (e' : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
      rw [OpenPartialHomeomorph.trans_target]
      exact ⟨hz_target, hpre_target⟩
  · -- The forward branch is the usual composition `e' ∘ e`.
    simpa using e'.analyticOn_toFun.comp e.analyticOn_toFun (holomorphicIsomorph_mapsTo e)
  · -- The inverse branch is the reverse composition of the inverse branches.
    have hsymm_mapsTo :
        MapsTo ((e' : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) D'' D' := by
      intro z hz
      have hz_target : z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e'.target_eq] using hz
      simpa [e'.source_eq] using (e' : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
    simpa using e.analyticOn_invFun.comp e'.analyticOn_invFun hsymm_mapsTo

/-- Helper for Proposition 6.2: compose two holomorphic isomorphisms by composing their underlying
open partial homeomorphisms. -/
private noncomputable def holomorphicIsomorph_comp {D D' D'' : Set ℂ}
    (e : HolomorphicIsomorph D D') (e' : HolomorphicIsomorph D' D'') :
    HolomorphicIsomorph D D'' :=
  ⟨(e : OpenPartialHomeomorph ℂ ℂ).trans (e' : OpenPartialHomeomorph ℂ ℂ),
    holomorphicIsomorph_comp_isHolomorphicIsoOn e e'⟩

/-- Helper for Proposition 6.2: the centering Möbius map of the unit disc packages to a
holomorphic automorphism of the disc. -/
private theorem disc_center_automorphism_local {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ κ : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1),
      EqOn κ (discCenter a) (ball (0 : ℂ) 1) := by
  have hneg : -a ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using ha
  have hright : Set.LeftInvOn (discCenter a) (discUncenter a) (ball (0 : ℂ) 1) := by
    -- The right inverse comes from the left inverse at the opposite center.
    intro z hz
    simpa [discUncenter] using (disc_uncenter_leftInvOn_disc_center hneg hz)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine
        { toFun := discCenter a
          invFun := discUncenter a
          source := ball (0 : ℂ) 1
          target := ball (0 : ℂ) 1
          map_source' := disc_center_mapsTo_unit_ball ha
          map_target' := disc_uncenter_mapsTo_unit_ball ha
          left_inv' := disc_uncenter_leftInvOn_disc_center ha
          right_inv' := hright
          open_source := Metric.isOpen_ball
          open_target := Metric.isOpen_ball
          continuousOn_toFun := by
            -- Holomorphicity on the open ball gives the forward continuity data.
            exact ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_center_differentiableOn ha)).continuousOn
          continuousOn_invFun := by
            -- The inverse branch is holomorphic on the same open ball.
            exact ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_uncenter_differentiableOn ha)).continuousOn }
    · refine
        { source_eq := rfl
          target_eq := rfl
          analyticOn_toFun := by
            -- Convert differentiability back to the analytic owner expected here.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_center_differentiableOn ha)
          analyticOn_symm := by
            -- The inverse branch is the uncentering map.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_uncenter_differentiableOn ha) }
  · -- On the disc, this packaged automorphism is definitionally the centering map.
    intro z hz
    rfl

/-- Helper for Proposition 6.2: uncentering after a rotation can be rewritten into the textbook
homographic normal form with a rotated center parameter. -/
private theorem disc_uncenter_rotation_rewrite {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    discUncenter a (Complex.exp (θ * Complex.I) * z) =
      Complex.exp (θ * Complex.I) * discUncenter (Complex.exp (-θ * Complex.I) * a) z := by
  let rot : ℂ := Complex.exp (θ * Complex.I)
  let invRot : ℂ := Complex.exp (-θ * Complex.I)
  have hrot_norm : ‖rot‖ = 1 := by
    simp [rot]
  have hinvRot_norm : ‖invRot‖ = 1 := by
    simpa [invRot] using (Complex.norm_exp_ofReal_mul_I (-θ))
  have hz_rot : rot * z ∈ ball (0 : ℂ) 1 := by
    -- The rotation factor preserves the unit disc.
    rw [mem_ball_zero_iff] at hz ⊢
    calc
      ‖rot * z‖ = ‖rot‖ * ‖z‖ := norm_mul _ _
      _ = ‖z‖ := by rw [hrot_norm, one_mul]
      _ < 1 := hz
  have ha_rot : invRot * a ∈ ball (0 : ℂ) 1 := by
    -- The rotated center parameter stays in the unit disc as well.
    rw [mem_ball_zero_iff] at ha ⊢
    calc
      ‖invRot * a‖ = ‖invRot‖ * ‖a‖ := norm_mul _ _
      _ = ‖a‖ := by rw [hinvRot_norm, one_mul]
      _ < 1 := ha
  have hrot_inv : rot * invRot = 1 := by
    -- The two exponential factors are inverse rotations.
    calc
      rot * invRot = Complex.exp (θ * Complex.I) * Complex.exp (-θ * Complex.I) := by
        rfl
      _ = Complex.exp (θ * Complex.I + -θ * Complex.I) := by
        rw [← Complex.exp_add]
      _ = 1 := by
        have hsum : θ * Complex.I + -θ * Complex.I = 0 := by
          ring
        rw [hsum, Complex.exp_zero]
  have hconj_invRot : conj invRot = rot := by
    -- Complex conjugation inverts the rotation factor `exp (-θ I)`.
    simpa [rot, invRot] using (Complex.exp_conj (-θ * Complex.I)).symm
  have hnum :
      rot * z + a = rot * (z + invRot * a) := by
    -- The rotated center parameter is exactly `invRot * a`.
    calc
      rot * z + a = rot * z + (rot * invRot) * a := by
        rw [hrot_inv]
        ring
      _ = rot * (z + invRot * a) := by
        ring
  have hden :
      1 - conj (-(invRot * a)) * z = 1 + conj a * (rot * z) := by
    -- Conjugating the rotated center turns the right denominator into the left one.
    have _ := hz_rot
    have _ := ha_rot
    calc
      1 - conj (-(invRot * a)) * z = 1 + conj (invRot * a) * z := by
        simp
      _ = 1 + (conj invRot * conj a) * z := by
        simp [mul_assoc]
      _ = 1 + (rot * conj a) * z := by
        rw [hconj_invRot]
      _ = 1 + conj a * (rot * z) := by
        ring
  -- Rewrite both sides to the same numerator-denominator presentation.
  calc
    discUncenter a (Complex.exp (θ * Complex.I) * z) =
        (rot * z + a) / (1 + conj a * (rot * z)) := by
      simp [discUncenter, discCenter, rot]
    _ = (rot * (z + invRot * a)) / (1 + conj a * (rot * z)) := by
      rw [hnum]
    _ = rot * ((z + invRot * a) / (1 + conj a * (rot * z))) := by
      rw [mul_div_assoc]
    _ = rot * ((z + invRot * a) / (1 - conj (-(invRot * a)) * z)) := by
      rw [hden]
    _ = Complex.exp (θ * Complex.I) * discUncenter (Complex.exp (-θ * Complex.I) * a) z := by
      simp [discUncenter, discCenter, rot, invRot]

/-- Proposition 6.2: every biholomorphic automorphism of the open unit disc has the homographic
normal form
`z' = exp (θ I) * (z + z₀) / (1 + conj z₀ * z)` with `θ : ℝ` and `‖z₀‖ < 1`. -/
theorem unit_disc_automorphism_has_homographic_form
    (e : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    ∃ (θ : ℝ) (z₀ : ℂ),
      ‖z₀‖ < 1 ∧
        EqOn e
          (fun z ↦ Complex.exp (θ * Complex.I) * discUncenter z₀ z)
          (ball (0 : ℂ) 1) := by
  let a : ℂ := e 0
  have hzero_mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp
  have ha : a ∈ ball (0 : ℂ) 1 := by
    -- The image of the origin still lies in the unit disc.
    exact holomorphicIsomorph_mapsTo e hzero_mem
  rcases disc_center_automorphism_local ha with ⟨κ, hκ⟩
  let g : HolomorphicIsomorph (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    holomorphicIsomorph_comp e κ
  have hg_fix : Function.IsFixedPt g 0 := by
    -- The centered automorphism sends the image of `0` back to the origin.
    change κ a = 0
    rw [hκ ha, disc_center_self]
  rcases unit_disc_automorphism_fixing_zero_is_rotation g hg_fix with ⟨θ, hθ⟩
  let z₀ : ℂ := Complex.exp (-θ * Complex.I) * a
  have hz₀_norm : ‖z₀‖ < 1 := by
    -- Rotating the center parameter does not change its norm.
    have hrot_norm : ‖Complex.exp (-θ * Complex.I)‖ = 1 := by
      simpa using (Complex.norm_exp_ofReal_mul_I (-θ))
    calc
      ‖z₀‖ = ‖Complex.exp (-θ * Complex.I)‖ * ‖a‖ := by
        simp [z₀]
      _ = ‖a‖ := by
        rw [hrot_norm, one_mul]
      _ < 1 := mem_ball_zero_iff.1 ha
  refine ⟨θ, z₀, hz₀_norm, ?_⟩
  intro z hz
  have hez : e z ∈ ball (0 : ℂ) 1 := holomorphicIsomorph_mapsTo e hz
  have hk_eval : κ (e z) = Complex.exp (θ * Complex.I) * z := by
    -- Evaluate the centered automorphism formula at `z`.
    simpa [g, holomorphicIsomorph_comp, OpenPartialHomeomorph.trans_apply, Function.comp_def] using
      hθ hz
  have hrecover : discUncenter a (κ (e z)) = e z := by
    -- Cancel the centering map at the point `e z`.
    rw [hκ hez]
    exact disc_uncenter_leftInvOn_disc_center ha hez
  -- Pull the centered classification back through `discUncenter` and normalize the center.
  calc
    e z = discUncenter a (κ (e z)) := hrecover.symm
    _ = discUncenter a (Complex.exp (θ * Complex.I) * z) := by
      rw [hk_eval]
    _ = Complex.exp (θ * Complex.I) * discUncenter z₀ z := by
      simpa [z₀] using disc_uncenter_rotation_rewrite ha hz θ
