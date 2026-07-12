import DifferentialForms_Cartan_1970.III.section12.«0005_Proposition_3_1».WeightedNormalForm
import DifferentialForms_Cartan_1970.III.section12.«0005_Proposition_3_1».UpperHalfDiskContourBridge

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the `lean_leansearch` tool was unavailable in this runner, so the
-- statement surface was checked directly against mathlib's `MeromorphicOn`,
-- `UpperHalfPlane.upperHalfPlaneSet`, `meromorphicOrderAt`,
-- `meromorphicTrailingCoeffAt`, and interval-integral notation.

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Cartan section12 0005_Proposition_3_1: once a good upper-half-disk radius,
an analytic owner, and isolated residue circles are fixed for `G`, the boundary decomposition of the
semidisk yields the corresponding finite-radius contour identity. -/
lemma upper_half_disk_contour_identity_of_owner
    {G : ℂ → ℂ} {s : Finset ℂ} {residue : ℂ → ℂ} {r : ℝ} {D : Set ℂ}
    (hr_pos : 0 < r)
    (hboundary_r : Disjoint (Set.range (upperHalfDiskBoundaryPath r)) (↑s : Set ℂ))
    (hDopen : IsOpen D)
    (hKD : ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D)
    (hholD : DifferentiableOn ℂ G (D \ (↑s : Set ℂ)))
    (hresD :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
          D
          s
          G
          z
          (residue z)) :
    (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi =
      ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (upperHalfDiskBoundaryPath r).toClosedPath
  have hΓ : IsOrientedBoundaryOf K Γ := by
    -- Package the explicit semidisk contour as the oriented boundary of the closed upper
    -- half-disk before invoking the frozen residue theorem.
    simpa [K, Γ] using upper_half_disk_boundary_isOrientedBoundaryOf (r := r) hr_pos
  have hΓdisjoint :
      ∀ i : Unit, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) := by
    intro i
    cases i
    -- Collapse the singleton family back to the explicit contour range disjointness.
    simpa [Γ, Path.toClosedPath] using hboundary_r
  have hboundary_sum :
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, (G dz) z =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
    -- Apply the frozen oriented-boundary residue theorem to the singleton semidisk owner.
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (K := K) (D := D) (f := G) (s := s) (residue := residue)
        hΓ hKD hDopen hΓdisjoint hholD hresD
  have hKclosed : IsClosed K := by
    -- The semidisk is cut out by two closed inequalities.
    exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  have hboundary_subset :
      Set.range (upperHalfDiskBoundaryPath r) ⊆ D \ (↑s : Set ℂ) := by
    intro z hz
    have hzFront :
        z ∈ frontier ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
      rwa [upper_half_disk_boundary_path_range_eq_frontier hr_pos] at hz
    have hzFrontK : z ∈ frontier K := by
      simpa [K] using hzFront
    have hzK : z ∈ K := by
      -- The contour is the frontier of a closed set, so it still lies inside the set.
      simpa [hKclosed.closure_eq] using frontier_subset_closure hzFrontK
    have hz_not_mem : z ∉ s := by
      intro hzS
      exact (Set.disjoint_left.mp hboundary_r) hz hzS
    exact ⟨hKD hzK, hz_not_mem⟩
  have hdiam_range :
      Set.range (Path.segment (-(r : ℂ)) (r : ℂ)) ⊆ D \ (↑s : Set ℂ) := by
    intro z hz
    apply hboundary_subset
    -- The diameter branch is one of the two pieces of the explicit semidisk contour.
    rw [upper_half_disk_boundary_path_range_eq_union]
    exact Or.inl hz
  have harc_range :
      Set.range (upperSemicirclePath r) ⊆ D \ (↑s : Set ℂ) := by
    intro z hz
    apply hboundary_subset
    -- The upper semicircle branch is the other piece of the semidisk contour.
    rw [upper_half_disk_boundary_path_range_eq_union]
    exact Or.inr hz
  have hGform :
      ContinuousOn (Complex.realScalarOneForm G) (D \ (↑s : Set ℂ)) := by
    -- Package the scalar coefficient as a continuous complex-linear one-form on the pole-free
    -- owner.
    rw [show Complex.realScalarOneForm G =
        fun z ↦ G z • (1 : ℂ →L[ℝ] ℂ) by
          funext z
          exact Complex.realScalarOneForm_eq_smul G z]
    exact hholD.continuousOn.smul
      (continuousOn_const :
        ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) (D \ (↑s : Set ℂ)))
  have hdiam :
      CurveIntegrable (G dz) (Path.segment (-(r : ℂ)) (r : ℂ)) := by
    -- On the affine diameter branch, continuity on the owner is enough once the segment is known
    -- to be piecewise differentiable.
    have hdiamReal :
        CurveIntegrable (Complex.realScalarOneForm G) (Path.segment (-(r : ℂ)) (r : ℂ)) := by
      exact
        Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
          (ω := Complex.realScalarOneForm G)
          hGform
          (Path.segment_isPiecewiseDifferentiable (-(r : ℂ)) (r : ℂ))
          hdiam_range
    simpa [Complex.realScalarOneForm] using hdiamReal
  have harc :
      CurveIntegrable (G dz) (upperSemicirclePath r) := by
    -- The same owner continuity applies to the smooth upper-semicircle branch.
    have harcReal : CurveIntegrable (Complex.realScalarOneForm G) (upperSemicirclePath r) := by
      exact
        Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
          (ω := Complex.realScalarOneForm G)
          hGform
          (upper_semicircle_path_isDifferentiable r).isPiecewiseDifferentiable
          harc_range
    simpa [Complex.realScalarOneForm] using harcReal
  have hcontour_eq :
      ∫ᶜ z in upperHalfDiskBoundaryPath r, (G dz) z =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
    have hclosed_eq :
        ∫ᶜ z in ((upperHalfDiskBoundaryPath r).toClosedPath.toPath), (G dz) z =
          ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
      -- Collapse the singleton boundary sum to the unique closed path in the family.
      simpa [Γ] using hboundary_sum
    have hclosed_cast :
        ∫ᶜ z in ((upperHalfDiskBoundaryPath r).toClosedPath.toPath), (G dz) z =
          ∫ᶜ z in upperHalfDiskBoundaryPath r, (G dz) z := by
      rw [loop_toClosedPath_toPath_eq_cast (γ := upperHalfDiskBoundaryPath r)]
      simp
    -- Unpack the closed-path wrapper back to the original loop.
    exact hclosed_cast.symm.trans hclosed_eq
  -- Rewrite the unique boundary loop into the source diameter-plus-arc decomposition.
  calc
    (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi =
        ∫ᶜ z in upperHalfDiskBoundaryPath r, (G dz) z := by
          symm
          exact
            upper_half_disk_boundary_curveIntegral_eq_intervalIntegral_add_sectorArcIntegral
              (g := G) hdiam harc
    _ = ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := hcontour_eq

/-- Helper for Cartan section12 0005_Proposition_3_1: on a circle whose closed disk stays in the
closed upper half-plane, the weighted meromorphic normal form and the literal weighted integrand
have the same circle integral. -/
lemma weighted_normal_form_circleIntegral_eq_source
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im}) {z : ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hρD : Metric.closedBall z ρ ⊆ {w : ℂ | 0 ≤ w.im}) :
    (∮ w in C(z, ρ),
        toMeromorphicNFOn f {w : ℂ | 0 ≤ w.im} w * Complex.exp (Complex.I * w)) =
      ∮ w in C(z, ρ), f w * Complex.exp (Complex.I * w) := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  have hsphere_subset : Metric.sphere z |ρ| ⊆ U := by
    intro w hw
    have hw_le : dist w z ≤ ρ := by
      have hw_eq : dist w z = |ρ| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      rw [abs_of_pos hρpos] at hw_eq
      exact le_of_eq hw_eq
    exact hρD (by simpa [Metric.mem_closedBall] using hw_le)
  have hEq :
      (fun w ↦ toMeromorphicNFOn f U w * Complex.exp (Complex.I * w))
        =ᶠ[Filter.codiscreteWithin (Metric.sphere z |ρ|)]
      (fun w ↦ f w * Complex.exp (Complex.I * w)) := by
    have hEqNF :
        (fun w ↦ toMeromorphicNFOn f U w)
          =ᶠ[Filter.codiscreteWithin (Metric.sphere z |ρ|)]
        f := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono hsphere_subset)
    -- Multiply the codiscrete equality for the meromorphic factor by the common exponential
    -- weight to keep the circle integral unchanged.
    filter_upwards [hEqNF] with w hw
    simp [U, hw]
  exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hρpos.ne'

/-- Helper for Cartan section12 0005_Proposition_3_1: once explicit source residue-circle radii are
fixed, any large enough upper-half-disk owner upgrades them to isolated residue circles for the
weighted meromorphic normal form. -/
lemma isolated_residue_owner_of_large_upper_half_disk
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (residue : ℂ → ℂ) {ρ : s → ℝ} {r : ℝ} {D : Set ℂ}
    (hKD : ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D)
    (hholD :
      DifferentiableOn ℂ
        (fun z ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
            Complex.exp (Complex.I * z))
        (D \ (↑s : Set ℂ)))
    (hρpos : ∀ z : s, 0 < ρ z)
    (hρK : ∀ z : s, Metric.closedBall (z : ℂ) (ρ z) ⊆ interior {w : ℂ | 0 ≤ w.im})
    (hρD : ∀ z : s, Metric.closedBall (z : ℂ) (ρ z) ⊆ {w : ℂ | 0 ≤ w.im})
    (hρsep :
      ∀ z : s, ∀ w ∈ s, w ≠ (z : ℂ) → w ∉ Metric.closedBall (z : ℂ) (ρ z))
    (hρcircle :
      ∀ z : s,
        (∮ w in C((z : ℂ), ρ z), f w * Complex.exp (Complex.I * w)) =
          (2 * Real.pi * Complex.I : ℂ) * residue z)
    (hlarge : ∀ z : s, ‖(z : ℂ)‖ + ρ z < r) :
    ∀ z ∈ s,
      IsolatedLocalResidueCircle
        ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ)
        D
        s
        (fun w ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
            Complex.exp (Complex.I * w))
        z
        (residue z) := by
  intro z hz
  let z' : s := ⟨z, hz⟩
  have hupper :
      Metric.closedBall z (ρ z') ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hwU : w ∈ interior ({u : ℂ | 0 ≤ u.im} : Set ℂ) := hρK z' hw
    -- The source closed ball lies in the interior of the closed upper half-plane, hence in the
    -- strict upper half-plane needed by the semidisk-interior lemma.
    simpa [Complex.interior_setOf_le_im] using hwU
  have hballK :
      Metric.closedBall z (ρ z') ⊆
        interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    -- The eventual large-radius estimate places the whole source ball inside the semidisk.
    exact
      closedBall_subset_interior_upper_half_disk_of_upper_half_plane hupper
        (hlarge z')
  have hballD :
      Metric.closedBall z (ρ z') ⊆ D := by
    -- After entering the semidisk interior, the owner inclusion upgrades the same ball to `D`.
    exact hballK.trans (interior_subset.trans hKD)
  have hdiff_ball :
      DifferentiableOn ℂ
        (fun z ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
            Complex.exp (Complex.I * z))
        (Metric.ball z (ρ z') \ ({z} : Set ℂ)) := by
    -- The punctured source ball avoids every other pole from `s`, so the owner holomorphy of the
    -- weighted normal form restricts to the desired punctured neighborhood.
    refine hholD.mono ?_
    intro w hw
    refine ⟨hballD (Metric.ball_subset_closedBall hw.1), ?_⟩
    intro hwS
    have hwne : w ≠ z := by
      simpa using hw.2
    exact hρsep z' w hwS hwne (Metric.ball_subset_closedBall hw.1)
  refine ⟨ρ z', hρpos z', hballK, hballD, ?_, hdiff_ball, ?_⟩
  · simpa [z'] using hρsep z'
  · calc
      (∮ w in C(z, ρ z'),
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w * Complex.exp (Complex.I * w)) =
          ∮ w in C(z, ρ z'), f w * Complex.exp (Complex.I * w) := by
            exact
              weighted_normal_form_circleIntegral_eq_source
                (f := f) hmeromorphic (hρpos z') (hρD z')
      _ = (2 * Real.pi * Complex.I : ℂ) * residue z := by
          simpa [z'] using hρcircle z'

/-- Helper for Cartan section12 0005_Proposition_3_1: any radius eventually dominates the finite
family of source pole radii. -/
lemma eventually_large_radius_dominates_source_circles
    {ρ : s → ℝ} (hρpos : ∀ z : s, 0 < ρ z) :
    ∀ᶠ r : ℝ in atTop, ∀ z : s, ‖(z : ℂ)‖ + ρ z < r := by
  let M : ℝ := Finset.sum s.attach fun z ↦ ‖(z : ℂ)‖ + ρ z
  have hterm_nonneg : ∀ z : s, 0 ≤ ‖(z : ℂ)‖ + ρ z := by
    intro z
    exact add_nonneg (norm_nonneg _) (le_of_lt (hρpos z))
  filter_upwards [Filter.eventually_ge_atTop (M + 1)] with r hr z
  have hz_le_M : ‖(z : ℂ)‖ + ρ z ≤ M := by
    -- Each pole-plus-radius contribution is bounded by the total finite sum.
    simpa [M] using
      (Finset.single_le_sum (s := s.attach) (a := z)
        (f := fun w : s ↦ ‖(w : ℂ)‖ + ρ w)
        (fun w hw ↦ hterm_nonneg w)
        (by simp) :
          ‖(z : ℂ)‖ + ρ z ≤ Finset.sum s.attach (fun w ↦ ‖(w : ℂ)‖ + ρ w))
  -- Any radius larger than `M + 1` strictly contains every fixed source residue circle.
  linarith

/-- Helper for Cartan section12 0005_Proposition_3_1: on the real diameter `[-r, r]`, the literal
weighted integrand agrees almost everywhere with its weighted meromorphic normal form. -/
lemma intervalIntegral_mul_exp_eq_weighted_normal_form
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im}) (r : ℝ) :
    ∫ x in -r..r, f x * Complex.exp (Complex.I * x) =
      ∫ x in -r..r,
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} x * Complex.exp (Complex.I * x) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  have hreal_ae :
      (fun x : ℝ ↦ f x * Complex.exp (Complex.I * x))
        =ᵐ[MeasureTheory.volume.restrict (Ι (-r) r)]
      (fun x : ℝ ↦ G (x : ℂ)) := by
    have hreal_codiscrete :
        (fun x : ℝ ↦ f x * Complex.exp (Complex.I * x))
          =ᶠ[Filter.codiscreteWithin (Ι (-r) r)]
        (fun x : ℝ ↦ G (x : ℂ)) := by
      simpa [G, U] using
        real_segment_mul_exp_codiscrete_eq_normalForm
          (f := f) hmeromorphic (r := r)
    exact
      hreal_codiscrete.filter_mono
        (ae_restrict_le_codiscreteWithin measurableSet_uIoc)
  -- Along the real diameter, the literal weighted integrand agrees a.e. with its normal form.
  apply intervalIntegral.integral_congr_ae_restrict
  exact hreal_ae

/-- Helper for Cartan section12 0005_Proposition_3_1: on the upper semicircle of positive radius,
the literal weighted arc integrand agrees almost everywhere with its weighted meromorphic normal
form. -/
lemma sectorArcIntegral_mul_exp_eq_weighted_normal_form
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im}) {r : ℝ} (hr_pos : 0 < r) :
    sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
      sectorArcIntegral
        (fun z ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
            Complex.exp (Complex.I * z))
        r
        0
        Real.pi := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  have harc_ae :
      (fun θ : ℝ ↦
        Complex.I * circleMap 0 r θ *
          (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
        =ᵐ[MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi)]
      (fun θ : ℝ ↦
        Complex.I * circleMap 0 r θ *
          (G (circleMap 0 r θ))) := by
    have harc_codiscrete :
        (fun θ : ℝ ↦
          Complex.I * circleMap 0 r θ *
            (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          =ᶠ[Filter.codiscreteWithin (Ι (0 : ℝ) Real.pi)]
        (fun θ : ℝ ↦
          Complex.I * circleMap 0 r θ *
            (G (circleMap 0 r θ))) := by
      simpa [G, U] using
        upper_semicircle_mul_exp_codiscrete_eq_normalForm
          (f := f) hmeromorphic hr_pos
    exact
      harc_codiscrete.filter_mono
        (ae_restrict_le_codiscreteWithin measurableSet_uIoc)
  -- The same codiscrete comparison rewrites the semicircle integral back to the literal source
  -- integrand.
  rw [sectorArcIntegral_def, sectorArcIntegral_def]
  apply intervalIntegral.integral_congr_ae_restrict
  exact harc_ae

/-- Helper for Cartan section12 0005_Proposition_3_1: for any integrable complex-valued function on
`ℝ`, the symmetric interval integrals `∫_{-r}^r` converge to the whole-space integral. -/
lemma tendsto_symmetric_intervalIntegral_of_integrable
    {g : ℝ → ℂ} (hg_integrable : Integrable g) :
    Tendsto (fun r : ℝ ↦ ∫ x in -r..r, g x) atTop (𝓝 (∫ x : ℝ, g x)) := by
  have hleft_tendsto :
      Tendsto (fun r : ℝ ↦ ∫ x in -r..0, g x) atTop (𝓝 (∫ x in Set.Iic 0, g x)) := by
    -- The left half-line improper integral is the limit of the intervals `[-r, 0]`.
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral_Iic
        (μ := MeasureTheory.volume) (f := g) (l := atTop) (a := fun r : ℝ ↦ -r) 0
        (show IntegrableOn g (Set.Iic 0) MeasureTheory.volume from hg_integrable.integrableOn)
        tendsto_neg_atTop_atBot)
  have hright_tendsto :
      Tendsto (fun r : ℝ ↦ ∫ x in 0..r, g x) atTop (𝓝 (∫ x in Set.Ioi 0, g x)) := by
    -- The right half-line improper integral is the limit of the intervals `[0, r]`.
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        (μ := MeasureTheory.volume) (f := g) (l := atTop) 0
        (b := fun r : ℝ ↦ r)
        (show IntegrableOn g (Set.Ioi 0) MeasureTheory.volume from hg_integrable.integrableOn)
        tendsto_id)
  have hsplit :
      ∀ᶠ r : ℝ in atTop,
        ∫ x in -r..r, g x = (∫ x in -r..0, g x) + ∫ x in 0..r, g x := by
    filter_upwards with r
    -- Split the symmetric interval at the origin.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (μ := MeasureTheory.volume) (f := g) (a := -r) (b := 0) (c := r)
        (hg_integrable.intervalIntegrable (a := -r) (b := 0))
        (hg_integrable.intervalIntegrable (a := 0) (b := r))).symm
  have hsymmetric_tendsto :
      Tendsto
        (fun r : ℝ ↦ ∫ x in -r..r, g x)
        atTop
        (𝓝 ((∫ x in Set.Iic 0, g x) + ∫ x in Set.Ioi 0, g x)) := by
    have hsplit_eq :
        (fun r : ℝ ↦ ∫ x in -r..r, g x)
          =ᶠ[atTop]
            fun r : ℝ ↦ (∫ x in -r..0, g x) + ∫ x in 0..r, g x := by
      filter_upwards [hsplit] with r hr
      exact hr
    -- The split limits add to the full symmetric-interval limit.
    exact Tendsto.congr' hsplit_eq.symm (hleft_tendsto.add hright_tendsto)
  have hwhole :
      (∫ x in Set.Iic 0, g x) + ∫ x in Set.Ioi 0, g x = ∫ x : ℝ, g x := by
    exact
      intervalIntegral.integral_Iic_add_Ioi
        (μ := MeasureTheory.volume) (f := g) (b := 0)
        (show IntegrableOn g (Set.Iic 0) MeasureTheory.volume from hg_integrable.integrableOn)
        (show IntegrableOn g (Set.Ioi 0) MeasureTheory.volume from hg_integrable.integrableOn)
  -- Reassemble the two half-line integrals into the whole-space integral.
  simpa [hwhole] using hsymmetric_tendsto

/-- Helper for Proposition 3.1: for all sufficiently large radii, the explicit upper-half-disk
contour identity holds, namely the real diameter integral plus the upper-semicircle integral equals
the prescribed source residue sum for the weighted meromorphic integrand. -/
lemma eventually_upper_half_disk_isolated_residue_owner
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          s
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    ∀ᶠ r : ℝ in atTop,
      ∃ D : Set ℂ,
        IsOpen D ∧
          ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
          DifferentiableOn ℂ
            (fun z ↦
              toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
                Complex.exp (Complex.I * z))
            (D \ (↑s : Set ℂ)) ∧
          ∀ z ∈ s,
            IsolatedLocalResidueCircle
              ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
              D
              s
              (fun w ↦
                toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
                  Complex.exp (Complex.I * w))
              z
              (residue z) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  have hgood_radius :
      ∀ᶠ r : ℝ in atTop,
        0 < r ∧
          (∀ z ∈ s, ‖z‖ < r) ∧
          (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
    -- First freeze a large upper-half-disk containing every prescribed pole and keeping the outer
    -- semicircle free of poles.
    exact eventually_good_upper_half_disk_radius (f := f) (s := s) hreal hpoles
  have howner :
      ∀ᶠ r : ℝ in atTop,
        ∃ D : Set ℂ,
          IsOpen D ∧
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
            DifferentiableOn ℂ G (D \ (↑s : Set ℂ)) := by
    filter_upwards [hgood_radius] with r hr
    rcases hr with ⟨hr_pos, _, hboundary⟩
    -- The owner is the union of the semidisk interior with the analytic boundary locus.
    exact
      upper_half_disk_differentiable_owner
        (f := f) (s := s) hmeromorphic hreal hpoles hr_pos hboundary
  have hsource_isolated_radii :
      ∀ z : s,
        ∃ ρ > 0,
          Metric.closedBall (z : ℂ) ρ ⊆ interior U ∧
            Metric.closedBall (z : ℂ) ρ ⊆ U ∧
              (∀ w ∈ s, w ≠ (z : ℂ) → w ∉ Metric.closedBall (z : ℂ) ρ) ∧
                (∮ w in C((z : ℂ), ρ), f w * Complex.exp (Complex.I * w)) =
                  (2 * Real.pi * Complex.I : ℂ) * residue z := by
    intro z
    -- Keep the original isolated source circles from `hresidue`, since the intermediate
    -- `LocalResidueCircle` packaging loses the separation field needed below.
    rcases hresidue z.1 z.2 with ⟨ρ, hρ, hρK, hρD, hρsep, _hρdiff, hρcircle⟩
    exact ⟨ρ, hρ, hρK, hρD, hρsep, hρcircle⟩
  choose ρ hρpos hρK hρD hρsep hρcircle using hsource_isolated_radii
  have hlarge_source_radius :
      ∀ᶠ r : ℝ in atTop, ∀ z : s, ‖(z : ℂ)‖ + ρ z < r := by
    exact eventually_large_radius_dominates_source_circles (s := s) hρpos
  filter_upwards [howner, hlarge_source_radius] with r howner_r hlarge_r
  rcases howner_r with ⟨D, hDopen, hKD, hholD⟩
  refine ⟨D, hDopen, hKD, hholD, ?_⟩
  simpa [G, U] using
    isolated_residue_owner_of_large_upper_half_disk
      (f := f) (s := s) hmeromorphic residue hKD hholD hρpos hρK hρD hρsep hρcircle
      hlarge_r

/-- Helper for Proposition 3.1: for all sufficiently large radii, the explicit upper-half-disk
contour identity holds, namely the real diameter integral plus the upper-semicircle integral equals
the prescribed source residue sum for the weighted meromorphic integrand. -/
lemma eventually_upper_half_disk_contour_identity
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          s
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    ∀ᶠ r : ℝ in atTop,
      (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
          sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
  classical
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  have hgood_radius :
      ∀ᶠ r : ℝ in atTop,
        0 < r ∧
          (∀ z ∈ s, ‖z‖ < r) ∧
          (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
    -- The source route first freezes a large radius that contains every pole and keeps the outer
    -- semicircle free of poles.
    exact eventually_good_upper_half_disk_radius (f := f) (s := s) hreal hpoles
  have hboundary_disjoint :
      ∀ᶠ r : ℝ in atTop,
        Disjoint (Set.range (upperHalfDiskBoundaryPath r)) (↑s : Set ℂ) := by
    filter_upwards [hgood_radius] with r hr
    rcases hr with ⟨hr_pos, hinside, _⟩
    -- The contour range lives on the frontier while every pole lies strictly inside the semidisk.
    exact upper_half_disk_boundary_disjoint_pole_finset (f := f) (s := s) hpoles hr_pos hinside
  have howner :
      ∀ᶠ r : ℝ in atTop,
        ∃ D : Set ℂ,
          IsOpen D ∧
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
            DifferentiableOn ℂ G (D \ (↑s : Set ℂ)) := by
    filter_upwards [hgood_radius] with r hr
    rcases hr with ⟨hr_pos, _, hboundary⟩
    -- The owner is the union of the semidisk interior with the analytic boundary locus.
    exact
      upper_half_disk_differentiable_owner
        (f := f) (s := s) hmeromorphic hreal hpoles hr_pos hboundary
  have hresidue_owner :
      ∀ᶠ r : ℝ in atTop,
        ∃ D : Set ℂ,
          IsOpen D ∧
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
            DifferentiableOn ℂ G (D \ (↑s : Set ℂ)) ∧
            ∀ z ∈ s,
              IsolatedLocalResidueCircle
                ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
                D
                s
                G
                z
                (residue z) := by
    simpa [G, U] using
      eventually_upper_half_disk_isolated_residue_owner
        (f := f) (s := s) hmeromorphic hreal hpoles residue hresidue
  filter_upwards [hgood_radius, hboundary_disjoint, hresidue_owner] with
    r hr hboundary_r hresidue_r
  rcases hr with ⟨hr_pos, _, _⟩
  rcases hresidue_r with ⟨D, hDopen, hKD, hholD, hresD⟩
  have hnormal_eq :
      (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
    exact
      upper_half_disk_contour_identity_of_owner
        (G := G) (s := s) (residue := residue) hr_pos hboundary_r hDopen hKD hholD hresD
  have hrealIntegral :
      ∫ x in -r..r, f x * Complex.exp (Complex.I * x) =
        ∫ x in -r..r, G (x : ℂ) := by
    simpa [G, U] using intervalIntegral_mul_exp_eq_weighted_normal_form (f := f) hmeromorphic r
  have harcIntegral :
      sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
        sectorArcIntegral G r 0 Real.pi := by
    simpa [G, U] using
      sectorArcIntegral_mul_exp_eq_weighted_normal_form (f := f) hmeromorphic hr_pos
  calc
    (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
        sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
      (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi := by
        rw [hrealIntegral, harcIntegral]
    _ = ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := hnormal_eq

/-- Auxiliary limit form for Cartan section12 0005_Proposition_3_1: Proposition 3.1 (1): if `f`
tends to `0` at infinity on
the closed upper half-plane, has no
real poles, is meromorphic on the closed upper half-plane, and has exactly the poles in `s` inside
the open upper half-plane, then the symmetric real-line integrals of
`x ↦ f x * exp (i x)` converge to `2π i` times the source residue data of
`z ↦ f z * exp (i z)` at those poles. -/
theorem residue_fourier_intervalIntegral_tendsto_upper_half_plane
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hdecay :
      Tendsto
        (fun z : {z : ℂ // 0 ≤ z.im} ↦ f z.1)
        (cocompact {z : ℂ // 0 ≤ z.im})
        (𝓝 0))
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          s
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    Tendsto
      (fun r : ℝ ↦ ∫ x in -r..r, f x * Complex.exp (Complex.I * x))
      atTop
        (𝓝
        ((2 * Real.pi * Complex.I : ℂ) *
          s.sum residue)) := by
  have hgood_radius :
      ∀ᶠ r : ℝ in atTop,
        0 < r ∧
          (∀ z ∈ s, ‖z‖ < r) ∧
          (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
    -- First freeze a large upper-half-disk containing every prescribed pole and avoiding poles on
    -- the outer semicircle.
    exact eventually_good_upper_half_disk_radius (f := f) (s := s) hreal hpoles
  have hint :
      ∀ᶠ r : ℝ in Filter.atTop,
        IntervalIntegrable
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          MeasureTheory.volume
          0
          Real.pi := by
    -- The meromorphic input and the good-radius invariant provide interval integrability of the
    -- weighted upper-semicircle parametrization for all large radii.
    exact
      eventually_intervalIntegrable_upper_semicircle_weighted_integrand
        (f := f) (s := s) hmeromorphic hgood_radius
  have harc_tendsto :
      Tendsto
        (fun r : ℝ ↦
          sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
        atTop
        (𝓝 0) := by
    -- Jordan decay on the upper semicircle removes the arc contribution in the limit.
    exact upper_semicircle_integral_tendsto_zero_mul_exp (f := f) hint hdecay
  have hcontour_tendsto :
      Tendsto
        (fun r : ℝ ↦
          (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
            sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
        atTop
        (𝓝 ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
    have hcontour_eq :
        (fun r : ℝ ↦
          (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
            sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
          =ᶠ[atTop]
            fun _ : ℝ ↦ (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
      filter_upwards
        [eventually_upper_half_disk_contour_identity
          (f := f) (s := s) hmeromorphic hreal hpoles residue hresidue] with r hr
      exact hr
    -- The finite-radius contour identity is eventually constant in the target residue sum.
    exact Tendsto.congr' hcontour_eq.symm tendsto_const_nhds
  -- Subtract the vanishing arc term to recover the symmetric real-axis integrals.
  simpa using hcontour_tendsto.sub harc_tendsto

/-- Helper for Proposition 3.1: absolute integrability of `f` on `ℝ` implies integrability of the
oscillatory weighting `x ↦ f x * exp (i x)`. -/
lemma integrable_mul_exp_of_integrable
    (hintegrable : Integrable (fun x : ℝ ↦ f x)) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (Complex.I * x)) := by
  -- The exponential factor has constant norm `1`, so it is globally bounded.
  refine hintegrable.mul_bdd (c := 1) ?_ ?_
  · have hcont : Continuous (fun x : ℝ ↦ Complex.exp (Complex.I * x)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    exact le_of_eq <| by
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I x

/-- Cartan section12 0005_Proposition_3_1: Proposition 3.1 (2): if, in addition, `f` is
absolutely integrable on the real axis, then the
improper integral of `x ↦ f x * exp (i x)` over `ℝ` equals the same residue sum. -/
theorem residue_fourier_integral_eq_sum_upper_half_plane
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hdecay :
      Tendsto
        (fun z : {z : ℂ // 0 ≤ z.im} ↦ f z.1)
        (cocompact {z : ℂ // 0 ≤ z.im})
        (𝓝 0))
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          s
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z))
    (hintegrable : Integrable (fun x : ℝ ↦ f x)) :
    ∫ x : ℝ, f x * Complex.exp (Complex.I * x) =
      (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
  let g : ℝ → ℂ := fun x ↦ f x * Complex.exp (Complex.I * x)
  have hg_integrable : Integrable g := by
    -- Absolute integrability of `f` transfers to the oscillatory integrand because `|exp (ix)|=1`.
    simpa [g] using integrable_mul_exp_of_integrable (f := f) hintegrable
  have hinterval_tendsto_integral :
      Tendsto (fun r : ℝ ↦ ∫ x in -r..r, g x) atTop (𝓝 (∫ x : ℝ, g x)) := by
    exact tendsto_symmetric_intervalIntegral_of_integrable hg_integrable
  have hresidue_tendsto :
      Tendsto
        (fun r : ℝ ↦ ∫ x in -r..r, g x)
        atTop
        (𝓝 ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
    -- Part (1) already identified the symmetric-interval limit with the residue sum.
    simpa [g] using
      residue_fourier_intervalIntegral_tendsto_upper_half_plane
        (f := f) (s := s) hmeromorphic hdecay hreal hpoles residue hresidue
  -- The two limits of the same net must agree.
  exact tendsto_nhds_unique hinterval_tendsto_integral hresidue_tendsto

end
