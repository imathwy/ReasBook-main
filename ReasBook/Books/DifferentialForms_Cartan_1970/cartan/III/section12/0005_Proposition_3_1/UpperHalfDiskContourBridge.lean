import DifferentialForms_Cartan_1970.cartan.III.section12.«0005_Proposition_3_1».UpperHalfDiskBoundaryStraightening

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Proposition 3.1: the curve integral along the real diameter `[-r, r]` is the
ordinary interval integral on the real axis. -/
lemma upper_half_disk_diameter_curveIntegral_eq_intervalIntegral
    (g : ℂ → ℂ) (r : ℝ) :
    ∫ᶜ z in Path.segment (-(r : ℂ)) (r : ℂ), (g dz) z =
      ∫ x in -r..r, g (x : ℂ) := by
  -- Rewrite the diameter integral through the affine segment parametrization `x = (2r)t - r`.
  rw [curveIntegral_segment]
  have hline :
      ∀ t : ℝ,
        AffineMap.lineMap (-(r : ℂ)) (r : ℂ) t = (((2 * r) * t - r : ℝ) : ℂ) := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  have hdir : (r : ℂ) - (-(r : ℂ)) = (((2 * r : ℝ)) : ℂ) := by
    simp [two_mul]
  calc
    ∫ t in (0 : ℝ)..1,
        (g dz) (AffineMap.lineMap (-(r : ℂ)) (r : ℂ) t) ((r : ℂ) - (-(r : ℂ))) =
        ∫ t in (0 : ℝ)..1, (((2 * r : ℝ)) : ℂ) * g ((((2 * r) * t - r : ℝ) : ℂ)) := by
          refine intervalIntegral.integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro t ht
          rw [hline, hdir, Complex.scalarOneForm_apply]
    _ = (((2 * r : ℝ)) : ℂ) * ∫ t in (0 : ℝ)..1, g ((((2 * r) * t - r : ℝ) : ℂ)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (2 * r) • ∫ t in (0 : ℝ)..1, g ((((2 * r) * t - r : ℝ) : ℂ)) := by
          simp
    _ = ∫ x in (2 * r) * (0 : ℝ) + -r..(2 * r) * 1 + -r, g (x : ℂ) := by
          simpa using
            (intervalIntegral.smul_integral_comp_mul_add
              (f := fun x : ℝ ↦ g (x : ℂ)) (a := (0 : ℝ)) (b := 1) (c := 2 * r) (d := -r))
    _ = ∫ x in -r..r, g (x : ℂ) := by
          ring_nf

/-- Helper for Proposition 3.1: once both boundary pieces are curve-integrable, the explicit
upper-half-disk contour integral splits into the diameter contribution plus the arc contribution. -/
lemma upper_half_disk_boundary_curveIntegral_eq_diameter_add_arc
    (g : ℂ → ℂ) {r : ℝ}
    (hdiam : CurveIntegrable (g dz) (Path.segment (-(r : ℂ)) (r : ℂ)))
    (harc : CurveIntegrable (g dz) (upperSemicirclePath r)) :
    ∫ᶜ z in upperHalfDiskBoundaryPath r, (g dz) z =
      (∫ᶜ z in Path.segment (-(r : ℂ)) (r : ℂ), (g dz) z) +
        ∫ᶜ z in upperSemicirclePath r, (g dz) z := by
  -- Expand the concatenated contour into its two curve-integrable source pieces.
  simpa [upperHalfDiskBoundaryPath] using curveIntegral_trans hdiam harc

/-- Helper for Proposition 3.1: the explicit upper-semicircle path integral is exactly the
source-facing sector-arc integral on `0 ≤ θ ≤ π`. -/
lemma upper_semicircle_curveIntegral_eq_sectorArcIntegral
    (g : ℂ → ℂ) (r : ℝ) :
    ∫ᶜ z in upperSemicirclePath r, (g dz) z =
      sectorArcIntegral g r 0 Real.pi := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (g dz) z
  let h : ℝ → ℂ := fun θ ↦ ω (circleMap 0 r θ) (deriv (circleMap 0 r) θ)
  have hcongr_ae :
      (fun t : ℝ ↦
        ω ((upperSemicirclePath r).extend t) (deriv ((upperSemicirclePath r).extend) t))
        =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
          (fun t ↦ (Real.pi : ℝ) • h (t * Real.pi)) := by
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hlocal :
        (upperSemicirclePath r).extend =ᶠ[nhds t]
          fun s : ℝ ↦ circleMap 0 r (s * Real.pi) := by
      have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [hIoo] with s hs
      have hline : AffineMap.lineMap (0 : ℝ) Real.pi s = s * Real.pi := by
        simp [AffineMap.lineMap_apply_module]
      rw [Path.extend_apply (upperSemicirclePath r) ⟨hs.1.le, hs.2.le⟩]
      simp [upperSemicirclePath, Path.map_coe, Path.segment_apply, hline]
    have hderiv :
        deriv (upperSemicirclePath r).extend t =
          (Real.pi : ℂ) * deriv (circleMap 0 r) (t * Real.pi) := by
      rw [Filter.EventuallyEq.deriv_eq hlocal]
      simpa [smul_eq_mul] using
        (((hasDerivAt_circleMap 0 r (t * Real.pi)).scomp t
          (hasDerivAt_mul_const (Real.pi : ℝ))).deriv)
    have hext :
        (upperSemicirclePath r).extend t = circleMap 0 r (t * Real.pi) :=
      Filter.EventuallyEq.eq_of_nhds hlocal
    -- Evaluate the scalar one-form on the chain-rule tangent vector of the upper semicircle.
    calc
      ω ((upperSemicirclePath r).extend t) (deriv ((upperSemicirclePath r).extend) t) =
          ω (circleMap 0 r (t * Real.pi))
            ((Real.pi : ℂ) * deriv (circleMap 0 r) (t * Real.pi)) := by
        rw [hext, hderiv]
      _ = (Real.pi : ℝ) • h (t * Real.pi) := by
        simp [h, ω, smul_eq_mul, Complex.scalarOneForm_apply, deriv_circleMap, mul_assoc,
          mul_comm, mul_left_comm]
  have hsmul :
      ∫ t in (0 : ℝ)..1, (Real.pi : ℝ) • h (t * Real.pi) =
        (Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * Real.pi) := by
    simpa using intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
      (r := (Real.pi : ℝ)) (f := fun t ↦ h (t * Real.pi))
  -- Rewrite the curve integral into the angular interval form and then perform `θ = π t`.
  rw [curveIntegral_eq_intervalIntegral_deriv, sectorArcIntegral_def]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((upperSemicirclePath r).extend t) (deriv ((upperSemicirclePath r).extend) t) =
      ∫ t in (0 : ℝ)..1, (Real.pi : ℝ) • h (t * Real.pi) := by
        exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
    _ = (Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * Real.pi) := hsmul
    _ = ∫ θ in (0 : ℝ) * Real.pi..1 * Real.pi, h θ := by
          simpa using
            (intervalIntegral.smul_integral_comp_mul_right
              (f := h) (a := (0 : ℝ)) (b := 1) (c := Real.pi))
    _ = ∫ θ in (0 : ℝ)..Real.pi, h θ := by
          simp
    _ = ∫ θ in (0 : ℝ)..Real.pi, Complex.I * circleMap 0 r θ * g (circleMap 0 r θ) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with θ
          simp [h, ω, Complex.scalarOneForm_apply, deriv_circleMap, mul_assoc, mul_comm,
            mul_left_comm]

/-- Helper for Proposition 3.1: once the boundary is split into the diameter and the upper
semicircle, both source-facing rewrites can be performed in one step. -/
lemma upper_half_disk_boundary_curveIntegral_eq_intervalIntegral_add_sectorArcIntegral
    (g : ℂ → ℂ) {r : ℝ}
    (hdiam : CurveIntegrable (g dz) (Path.segment (-(r : ℂ)) (r : ℂ)))
    (harc : CurveIntegrable (g dz) (upperSemicirclePath r)) :
    ∫ᶜ z in upperHalfDiskBoundaryPath r, (g dz) z =
      (∫ x in -r..r, g (x : ℂ)) + sectorArcIntegral g r 0 Real.pi := by
  -- First split the contour into its diameter and arc pieces, then rewrite each piece in the
  -- source coordinates used by Proposition 3.1.
  rw [upper_half_disk_boundary_curveIntegral_eq_diameter_add_arc (g := g) hdiam harc,
    upper_half_disk_diameter_curveIntegral_eq_intervalIntegral,
    upper_semicircle_curveIntegral_eq_sectorArcIntegral]

/-- Helper for Proposition 3.1: if a closed ball stays in the strict upper half-plane and its
center-plus-radius is strictly smaller than `r`, then that whole ball lies in the interior of the
closed upper half-disk of radius `r`. -/
lemma closedBall_subset_interior_upper_half_disk_of_upper_half_plane
    {z : ℂ} {ρ r : ℝ}
    (hupper : Metric.closedBall z ρ ⊆ {w : ℂ | 0 < w.im})
    (hlarge : ‖z‖ + ρ < r) :
    Metric.closedBall z ρ ⊆ interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
  let V : Set ℂ := Metric.ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}
  have hV_open : IsOpen V := by
    -- The strict-radius/strict-imaginary-part model is open in `ℂ`.
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hV_subset :
      V ⊆ ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    intro w hw
    constructor
    · have hw_norm : ‖w‖ < r := by
        simpa [V, Metric.mem_ball, dist_eq_norm] using hw.1
      exact hw_norm.le
    · exact hw.2.le
  intro w hw
  have hw_im : 0 < w.im := hupper hw
  have hw_dist : dist w z ≤ ρ := by
    simpa [Metric.mem_closedBall] using hw
  have hw_norm_le : ‖w‖ ≤ ρ + ‖z‖ := by
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
      _ ≤ ρ + ‖z‖ := by linarith
  have hw_norm_lt : ‖w‖ < r := by
    have hzρ : ρ + ‖z‖ < r := by simpa [add_comm] using hlarge
    exact lt_of_le_of_lt hw_norm_le hzρ
  have hwV : w ∈ V := by
    constructor
    · simpa [V, Metric.mem_ball, dist_eq_norm] using hw_norm_lt
    · exact hw_im
  -- Membership in the open model upgrades immediately to interior membership in the semidisk.
  exact ((IsOpen.subset_interior_iff hV_open).2 hV_subset) hwV

/-- Helper for Proposition 3.1: once the original source residue-circle radii are fixed, any large
upper half-disk that contains those full circles may reuse the same circles as local residue
circles for the semidisk owner. -/
lemma upper_half_disk_localResidueCircle_of_large_radius
    (residue : ℂ → ℂ) {ρ : s → ℝ} {r : ℝ} {D : Set ℂ} {G : ℂ → ℂ}
    (hρpos : ∀ z : s, 0 < ρ z)
    (hρU :
      ∀ z : s,
        Metric.closedBall (z : ℂ) (ρ z) ⊆ interior ({w : ℂ | 0 ≤ w.im} : Set ℂ))
    (hρcircle :
      ∀ z : s,
        (∮ w in C((z : ℂ), ρ z), G w) = (2 * Real.pi * Complex.I : ℂ) * residue z)
    (hKD : ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) ⊆ D)
    (hlarge : ∀ z : s, ‖(z : ℂ)‖ + ρ z < r) :
    ∀ z ∈ s,
      LocalResidueCircle
        ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ)
        D
        G
        z
        (residue z) := by
  intro z hz
  let z' : s := ⟨z, hz⟩
  have hupper :
      Metric.closedBall z (ρ z') ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hwU : w ∈ interior ({u : ℂ | 0 ≤ u.im} : Set ℂ) := hρU z' hw
    simpa [Complex.interior_setOf_le_im] using hwU
  have hballK :
      Metric.closedBall z (ρ z') ⊆
        interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    -- The same source circle lies strictly inside the large semidisk.
    exact
      closedBall_subset_interior_upper_half_disk_of_upper_half_plane hupper
        (hlarge z')
  have hballD :
      Metric.closedBall z (ρ z') ⊆ D := by
    -- After entering the semidisk interior, the owner inclusion upgrades it to `D`.
    exact hballK.trans (interior_subset.trans hKD)
  -- Reuse the original source circle unchanged; only the owner inclusions change.
  refine ⟨ρ z', hρpos z', hballK, hballD, ?_⟩
  simpa [z'] using hρcircle z'

end
