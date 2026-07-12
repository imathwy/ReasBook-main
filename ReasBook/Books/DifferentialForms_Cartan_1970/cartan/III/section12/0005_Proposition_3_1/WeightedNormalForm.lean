import DifferentialForms_Cartan_1970.III.section12.«0005_Proposition_3_1».FourierJordanDecay

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Proposition 3.1: for all sufficiently large radii, every pole from the prescribed
finite upper-half-plane set lies strictly inside the upper half-disk, so the outer semicircle is
pole-free. -/
lemma eventually_good_upper_half_disk_radius
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s) :
    ∀ᶠ r : ℝ in atTop,
      0 < r ∧
        (∀ z ∈ s, ‖z‖ < r) ∧
        (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
  obtain ⟨B, hB⟩ := (s.finite_toSet.isCompact).isBounded.exists_norm_le
  let R : ℝ := max 1 (B + 1)
  filter_upwards [Filter.eventually_ge_atTop R] with r hr
  have hR_one : 1 ≤ R := le_max_left 1 (B + 1)
  have hr_one : 1 ≤ r := le_trans hR_one hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_one
  have hinside_radius : ∀ z ∈ s, ‖z‖ < r := by
    -- Large radius puts each prescribed pole strictly inside the semicircle.
    intro z hz
    have hz_bound : ‖z‖ ≤ B := hB z hz
    have hz_lt : ‖z‖ + 1 ≤ r := le_trans (le_trans (by linarith) (le_max_right 1 _)) hr
    linarith
  refine ⟨hr_pos, hinside_radius, ?_⟩
  · -- Route correction: split the boundary check into the real endpoints and the open arc.
    intro θ hθ hpole
    have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
    have him_nonneg :
        0 ≤ (circleMap 0 r θ).im :=
      circleMap_mem_closed_upper_half_plane hr_nonneg hθ
    by_cases him_zero : (circleMap 0 r θ).im = 0
    · -- On the real axis, the standing hypothesis `hreal` rules out poles.
      have hreal_point : circleMap 0 r θ = ((circleMap 0 r θ).re : ℂ) := by
        apply Complex.ext <;> simp [him_zero]
      rw [hreal_point] at hpole
      exact hreal (circleMap 0 r θ).re hpole
    · -- In the open upper half-plane, `hpoles` forces the point into `s`, contradicting `‖z‖ = r`.
      have him_ne : 0 ≠ (circleMap 0 r θ).im := by
        intro h
        exact him_zero h.symm
      have him_pos : 0 < (circleMap 0 r θ).im := lt_of_le_of_ne him_nonneg him_ne
      have hmem_s : circleMap 0 r θ ∈ s := by
        exact (hpoles (circleMap 0 r θ)).mp ⟨hpole, by simpa using him_pos⟩
      have hinside : ‖circleMap 0 r θ‖ < r := by
        exact hinside_radius _ hmem_s
      rw [norm_circleMap_upper_semicircle hr_nonneg] at hinside
      exact lt_irrefl _ hinside

/-- Helper for Proposition 3.1: away from the finite pole set `s`, the weighted normal-form
integrand is analytic at every point of the closed upper half-plane. -/
lemma analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {z : ℂ} (hzU : z ∈ {z : ℂ | 0 ≤ z.im}) (hzs : z ∉ s) :
    AnalyticAt ℂ
      (fun w ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
          Complex.exp (Complex.I * w))
      z := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- A point of `U` outside `s` cannot be a pole: on the boundary this is `hreal`, and in the
    -- open upper half-plane it would contradict the pole-classification hypothesis `hpoles`.
    by_contra hneg
    by_cases him_zero : z.im = 0
    · have hreal_point : z = ((z.re : ℂ)) := by
        apply Complex.ext <;> simp [him_zero]
      rw [hreal_point] at hneg
      exact hreal z.re (lt_of_not_ge hneg)
    · have him_pos : 0 < z.im := lt_of_le_of_ne hzU (Ne.symm him_zero)
      have hmem_s : z ∈ s := by
        exact
          (hpoles z).mp
            ⟨lt_of_not_ge hneg, by simpa [UpperHalfPlane.upperHalfPlaneSet] using him_pos⟩
      exact hzs hmem_s
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) z := by
    -- On `U`, passing to the meromorphic normal form preserves the local meromorphic order.
    rw [
      meromorphicOrderAt_toMeromorphicNFOn
        (f := f) (U := U) hmeromorphic (by simpa [U] using hzU)
    ]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f U) z :=
    (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := U)) (by simpa [U] using hzU)
  have hanalytic_nf : AnalyticAt ℂ (fun w : ℂ ↦ toMeromorphicNFOn f U w) z := by
    -- The normal form is analytic exactly when its meromorphic order is nonnegative.
    exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf
  -- Multiply by the entire exponential factor to recover the weighted integrand from the source.
  simpa [U] using hanalytic_nf.mul ((analyticAt_const.mul analyticAt_id).cexp)

/-- Helper for Proposition 3.1: a holomorphic kernel of the form `g(z) / (z - a)` realizes the
residue `g(a)` on every small circle contained in both `interior K` and `D`. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall a r ⊆ interior K)
    (hD : Metric.closedBall a r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun z ↦ g z / (z - a)) a (g a) := by
  -- Use the given radius as the source-faithful residue circle and restrict differentiability to
  -- that closed ball.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall a r) := hg.mono hD
  have ha_ball : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  -- The standard small-circle Cauchy kernel integral computes the residue as `g(a)`.
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul ha_ball

/-- Helper for Proposition 3.1: on a punctured domain, a differentiable numerator gives a
differentiable simple-pole kernel `g(z) / (z - a)`. -/
lemma differentiableOn_div_sub_of_differentiableOn
    {D : Set ℂ} {g : ℂ → ℂ} {a : ℂ}
    (hg : DifferentiableOn ℂ g D) :
    DifferentiableOn ℂ (fun z ↦ g z / (z - a)) (D \ ({a} : Set ℂ)) := by
  intro z hz
  rcases hz with ⟨hzD, hzA⟩
  have hza : z ≠ a := by
    simpa using hzA
  have hnum :
      DifferentiableWithinAt ℂ g (D \ ({a} : Set ℂ)) z :=
    (hg z hzD).mono (by intro w hw; exact hw.1)
  have hden :
      DifferentiableWithinAt ℂ (fun w : ℂ ↦ w - a) (D \ ({a} : Set ℂ)) z :=
    (differentiableAt_id.sub_const a).differentiableWithinAt.mono
      (by intro w hw; exact Set.mem_univ w)
  -- Away from the center, the denominator does not vanish, so the quotient is holomorphic.
  exact hnum.div hden (sub_ne_zero.mpr hza)

/-- Helper for Proposition 3.1: the weighted meromorphic normal form is itself in meromorphic
normal form at every point of the closed upper half-plane. -/
lemma weighted_normal_form_meromorphicNFAt
    {z : ℂ} (hzU : z ∈ {z : ℂ | 0 ≤ z.im}) :
    MeromorphicNFAt
      (fun w ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
          Complex.exp (Complex.I * w))
      z := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f U) z :=
    (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := U)) (by simpa [U] using hzU)
  have hexp :
      AnalyticAt ℂ (fun w : ℂ ↦ Complex.exp (Complex.I * w)) z := by
    -- The exponential weight is entire and never vanishes.
    simpa using ((analyticAt_const.mul analyticAt_id).cexp : AnalyticAt ℂ _ z)
  -- Multiply the normal form by the nonvanishing entire factor `exp (i z)`.
  exact
    (meromorphicNFAt_mul_iff_left (f := toMeromorphicNFOn f U)
      (g := fun w : ℂ ↦ Complex.exp (Complex.I * w))
      (x := z) hexp (Complex.exp_ne_zero _)).2 hNF

/-- Helper for Proposition 3.1: away from the pole finset `s`, the weighted normal-form integrand
is differentiable on the punctured closed upper half-plane. -/
lemma weighted_normal_form_differentiableOn_upper_half_plane_punctured
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s) :
    DifferentiableOn ℂ
      (fun z ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
          Complex.exp (Complex.I * z))
      ({z : ℂ | 0 ≤ z.im} \ (↑s : Set ℂ)) := by
  intro z hz
  rcases hz with ⟨hzU, hzs⟩
  -- Pointwise analyticity on the punctured set upgrades immediately to differentiability.
  exact
    (analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
      (f := f) (s := s) hmeromorphic hreal hpoles hzU hzs).differentiableAt.differentiableWithinAt

/-- Helper for Proposition 3.1: the weighted normal form and the literal weighted integrand have
the same trailing coefficient at every point of the closed upper half-plane. -/
lemma meromorphicTrailingCoeffAt_weighted_normal_form_eq
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    {z : ℂ} (hzU : z ∈ {z : ℂ | 0 ≤ z.im}) :
    meromorphicTrailingCoeffAt
        (fun w ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
            Complex.exp (Complex.I * w))
        z =
      meromorphicTrailingCoeffAt
        (fun w ↦ f w * Complex.exp (Complex.I * w))
        z := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  apply meromorphicTrailingCoeffAt_congr_nhdsNE
  have hEqNF := hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (by simpa [U] using hzU)
  -- The normal form differs from `f` only at the center, so multiplying by the same entire factor
  -- preserves punctured-neighborhood equality.
  filter_upwards [hEqNF] with w hw
  simp [hw]

/-- Helper for Proposition 3.1: every source-side local residue circle for the literal weighted
integrand is also a local residue circle for the weighted meromorphic normal form, because the two
integrands differ only on a codiscrete subset of each admissible circle. -/
lemma weighted_normal_form_localResidueCircle
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        LocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    ∀ z ∈ s,
      LocalResidueCircle
        {z : ℂ | 0 ≤ z.im}
        {z : ℂ | 0 ≤ z.im}
        (fun w ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
            Complex.exp (Complex.I * w))
        z
        (residue z) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  intro z hz
  rcases hresidue z hz with ⟨R, hR, hRK, hRD, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, ?_⟩
  have hsphere_subset : Metric.sphere z |R| ⊆ U := by
    intro w hw
    have hw_le : dist w z ≤ R := by
      have hw_eq : dist w z = |R| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      rw [abs_of_pos hR] at hw_eq
      exact le_of_eq hw_eq
    exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
  have hEq :
      (fun w ↦ toMeromorphicNFOn f U w * Complex.exp (Complex.I * w))
        =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
      (fun w ↦ f w * Complex.exp (Complex.I * w)) := by
    have hEqNF :
        (fun w ↦ toMeromorphicNFOn f U w)
          =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        f := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono hsphere_subset)
    -- Multiply the codiscrete equality by the common exponential factor.
    filter_upwards [hEqNF] with w hw
    simp [hw]
  -- The circle integral is unchanged under codiscrete modifications of the integrand.
  calc
    (∮ w in C(z, R),
        toMeromorphicNFOn f U w * Complex.exp (Complex.I * w)) =
        ∮ w in C(z, R), f w * Complex.exp (Complex.I * w) := by
          exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
    _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR

/-- Helper for Proposition 3.1: once a radius strictly contains every pole from `s`, those poles
all lie in the interior of the corresponding closed upper half-disk. -/
lemma pole_finset_subset_interior_upper_half_disk
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ}
    (hinside : ∀ z ∈ s, ‖z‖ < r) :
    (↑s : Set ℂ) ⊆ interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
  intro z hz
  have hz_norm : ‖z‖ < r := hinside z hz
  have hz_upper : z ∈ upperHalfPlaneSet := ((hpoles z).mpr hz).2
  have hz_im : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hz_upper
  let V : Set ℂ := Metric.ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}
  have hV_open : IsOpen V := by
    -- The strict-radius/strict-imaginary-part model is an open neighborhood inside the semidisk.
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hV_subset :
      V ⊆ ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    intro w hw
    have hw_norm : ‖w‖ < r := by
      simpa [V, Metric.mem_ball, dist_eq_norm] using hw.1
    constructor
    · exact hw_norm.le
    · exact hw.2.le
  have hzV : z ∈ V := by
    constructor
    · simpa [V, Metric.mem_ball, dist_eq_norm] using hz_norm
    · exact hz_im
  -- Membership in the open model upgrades immediately to interior membership in the semidisk.
  exact ((IsOpen.subset_interior_iff hV_open).2 hV_subset) hzV

/-- Helper for Proposition 3.1: a point with strict radius bound and strictly positive imaginary
part lies in the interior of the closed upper half-disk. -/
lemma mem_interior_upper_half_disk_of_norm_lt_im_pos
    {r : ℝ} {z : ℂ} (hz_norm : ‖z‖ < r) (hz_im : 0 < z.im) :
    z ∈ interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
  let V : Set ℂ := Metric.ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}
  have hV_open : IsOpen V := by
    -- The strict-radius/strict-imaginary-part model is an open neighborhood inside the semidisk.
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hV_subset :
      V ⊆ ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    intro w hw
    have hw_norm : ‖w‖ < r := by
      simpa [V, Metric.mem_ball, dist_eq_norm] using hw.1
    constructor
    · exact hw_norm.le
    · exact hw.2.le
  have hzV : z ∈ V := by
    constructor
    · simpa [V, Metric.mem_ball, dist_eq_norm] using hz_norm
    · exact hz_im
  -- Membership in the same open model upgrades directly to semidisk interior membership.
  exact ((IsOpen.subset_interior_iff hV_open).2 hV_subset) hzV

end
