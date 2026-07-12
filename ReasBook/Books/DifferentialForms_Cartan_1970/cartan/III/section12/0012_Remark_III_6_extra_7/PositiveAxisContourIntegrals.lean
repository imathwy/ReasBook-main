import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2».BoundaryCircleIntegrals
import DifferentialForms_Cartan_1970.III.section12.SectorArc
import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeBranchCoordinates
import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeSegments

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the complementary lip angle
`π - positiveAxisKeyholeAngle R ε` stays in the principal strip `(0, π)` whenever `0 < ε < R`. -/
lemma positiveAxisKeyhole_complementaryAngle_mem_Ioo
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    Real.pi - positiveAxisKeyholeAngle R ε ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hR : 0 < R := lt_trans hε hεR
  have hθpos : 0 < positiveAxisKeyholeAngle R ε := by
    -- The keyhole opening angle is an acute arctangent because `ε / R > 0`.
    simpa [positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hθlt : positiveAxisKeyholeAngle R ε < Real.pi / 2 := by
    -- The same arctangent is always strictly smaller than `π / 2`.
    simpa [positiveAxisKeyholeAngle] using Real.arctan_lt_pi_div_two (ε / R)
  constructor
  · -- Subtracting an acute angle from `π` leaves a positive complementary angle.
    linarith [hθlt, Real.pi_pos]
  · -- The complement is also strictly smaller than `π` because the angle itself is positive.
    linarith

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: mapping an angular segment through
`circleMap` turns its curve integral into the chapter-local `sectorArcIntegral`. -/
lemma positiveAxisCircleArc_curveIntegral_eq_sectorArcIntegral
    (g : ℂ → ℂ) (ρ α β : ℝ) :
    ∫ᶜ z in ((Path.segment α β).map (continuous_circleMap 0 ρ)), (g dz) z =
      sectorArcIntegral g ρ α β := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (g dz) z
  let h : ℝ → ℂ := fun θ ↦ ω (circleMap 0 ρ θ) (deriv (circleMap 0 ρ) θ)
  have hcongr_ae :
      (fun t : ℝ ↦
        ω ((((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t))
          (deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t))
        =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
          (fun t ↦ (β - α : ℝ) • h ((β - α) * t + α)) := by
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hlocal :
        (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) =ᶠ[nhds t]
          fun s : ℝ ↦ circleMap 0 ρ (((β - α) * s + α)) := by
      have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [hIoo] with s hs
      rw [Path.extend_apply (((Path.segment α β).map (continuous_circleMap 0 ρ)))
        ⟨hs.1.le, hs.2.le⟩]
      simp [Path.map_coe, Path.segment_apply, AffineMap.lineMap_apply_module, sub_eq_add_neg]
      ring_nf
    have hderiv :
        deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t =
          ((β - α : ℝ) : ℂ) * deriv (circleMap 0 ρ) (((β - α) * t + α)) := by
      rw [Filter.EventuallyEq.deriv_eq hlocal]
      simpa using
        (((hasDerivAt_circleMap 0 ρ (((β - α) * t + α))).scomp t
          (((hasDerivAt_id t).const_mul (β - α)).add_const α)).deriv)
    have hext :
        (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t) =
          circleMap 0 ρ (((β - α) * t + α)) :=
      Filter.EventuallyEq.eq_of_nhds hlocal
    -- Evaluate the scalar one-form against the affine angle tangent on the mapped circle segment.
    calc
      ω ((((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t))
          (deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t) =
        ω (circleMap 0 ρ (((β - α) * t + α)))
          (((β - α : ℝ) : ℂ) * deriv (circleMap 0 ρ) (((β - α) * t + α))) := by
            rw [hext, hderiv]
      _ = (β - α : ℝ) • h (((β - α) * t + α)) := by
            simp [h, ω, smul_eq_mul, mul_comm, mul_left_comm]
  -- Rewrite the mapped path integral by `curveIntegral_eq_intervalIntegral_deriv`, then move the
  -- affine angle parameter directly to the `sectorArcIntegral` owner.
  rw [curveIntegral_eq_intervalIntegral_deriv, sectorArcIntegral]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((((Path.segment α β).map (continuous_circleMap 0 ρ)).extend t))
          (deriv (((Path.segment α β).map (continuous_circleMap 0 ρ)).extend) t) =
      ∫ t in (0 : ℝ)..1, (β - α : ℝ) • h ((β - α) * t + α) := by
        exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
    _ = (β - α : ℝ) • ∫ t in (0 : ℝ)..1, h ((β - α) * t + α) := by
        rw [intervalIntegral.integral_smul]
    _ = ∫ θ in (β - α) * (0 : ℝ) + α..(β - α) * 1 + α, h θ := by
        simpa using
          (intervalIntegral.smul_integral_comp_mul_add
            (f := h) (a := (0 : ℝ)) (b := 1) (c := β - α) (d := α))
    _ = ∫ θ in α..β, h θ := by
        simp

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: along any fixed ray, the contour
integral of a complex-valued kernel reparametrizes directly to the radius interval with tangent
factor `exp (α i)`. This is the common contour-to-interval bridge for both slit lips. -/
lemma positiveAxisRadialSegment_curveIntegral_eq_intervalIntegral
    (g : ℂ → ℂ) (ρ₀ ρ₁ α : ℝ) (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) :
    ∫ᶜ z in Path.segment (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α), ((g dz) z) =
      ∫ x in ρ₀..ρ₁, Complex.exp (α * Complex.I) * g (circleMap 0 x α) := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (g dz) z
  let h : ℝ → ℂ := fun x ↦ Complex.exp (α * Complex.I) * g (circleMap 0 x α)
  -- Rewrite the ray segment with `curveIntegral_segment`, then transport the affine radius
  -- parameter to the interval `ρ₀..ρ₁`.
  rw [curveIntegral_segment]
  have hcongr :
      ∫ t in (0 : ℝ)..1,
          (ω
            (AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t))
            (circleMap 0 ρ₁ α - circleMap 0 ρ₀ α) =
        ∫ t in (0 : ℝ)..1, (ρ₁ - ρ₀ : ℝ) • h (AffineMap.lineMap ρ₀ ρ₁ t) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have hline :
          AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t =
            circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ t) α :=
        positiveAxisKeyhole_lineMap_circleMap_same_angle ρ₀ ρ₁ α t
      have hdir :
          circleMap 0 ρ₁ α - circleMap 0 ρ₀ α =
            ((ρ₁ - ρ₀ : ℝ) : ℂ) * Complex.exp (α * Complex.I) := by
        rw [circleMap_zero, circleMap_zero]
        calc
          (ρ₁ : ℂ) * Complex.exp (α * Complex.I) - (ρ₀ : ℂ) * Complex.exp (α * Complex.I) =
              (((ρ₁ : ℂ) - (ρ₀ : ℂ)) * Complex.exp (α * Complex.I)) := by
                ring
          _ = (((ρ₁ - ρ₀ : ℝ) : ℂ) * Complex.exp (α * Complex.I)) := by
                simp
      -- Evaluate the scalar one-form against the fixed ray tangent and normalize the affine
      -- interpolation back to the common radius variable.
      have hpoint :
          (ω
              (AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t))
              (circleMap 0 ρ₁ α - circleMap 0 ρ₀ α) =
            (ρ₁ - ρ₀ : ℝ) • h (AffineMap.lineMap ρ₀ ρ₁ t) := by
        rw [Complex.scalarOneForm_apply, hline, hdir]
        simp [h, ω, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      simpa using hpoint
  calc
    ∫ t in (0 : ℝ)..1,
        (ω
          (AffineMap.lineMap (circleMap 0 ρ₀ α) (circleMap 0 ρ₁ α) t))
          (circleMap 0 ρ₁ α - circleMap 0 ρ₀ α) =
      ∫ t in (0 : ℝ)..1, (ρ₁ - ρ₀ : ℝ) • h (AffineMap.lineMap ρ₀ ρ₁ t) := hcongr
    _ = ∫ x in (ρ₁ - ρ₀) * (0 : ℝ) + ρ₀..(ρ₁ - ρ₀) * 1 + ρ₀, h x := by
          simpa [AffineMap.lineMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm] using
            (intervalIntegral.smul_integral_comp_mul_add
              (f := h) (a := (0 : ℝ)) (b := 1) (c := ρ₁ - ρ₀) (d := ρ₀))
    _ = ∫ x in ρ₀..ρ₁, h x := by
          simp
    _ = ∫ x in ρ₀..ρ₁, Complex.exp (α * Complex.I) * g (circleMap 0 x α) := by
          rfl

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the upper radial lip runs from radius
`R` down to radius `ε`, so rewriting it against the common truncation interval contributes the
negative of the forward interval integral. -/
lemma positiveAxisUpperLip_curveIntegral_eq_intervalIntegral
    (g : ℂ → ℂ) (R ε α : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 ε α), ((g dz) z) =
      -∫ x in ε..R, Complex.exp (α * Complex.I) * g (circleMap 0 x α) := by
  -- Reverse the interval orientation so both slit lips use the same truncation window `ε..R`.
  rw [positiveAxisRadialSegment_curveIntegral_eq_intervalIntegral g R ε α hR hε,
    intervalIntegral.integral_symm]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: after rewriting the upper and lower
positive-axis slit lips against the shared truncation interval, their sum is one interval integral
of the paired boundary kernel. -/
lemma positiveAxisUpperLower_curveIntegral_eq_lipPairInterval
    (g : ℂ → ℂ) (R ε α β : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (hupperInt :
      IntervalIntegrable
        (fun x : ℝ ↦ Complex.exp (α * Complex.I) * g (circleMap 0 x α))
        volume ε R)
    (hlowerInt :
      IntervalIntegrable
        (fun x : ℝ ↦ Complex.exp (β * Complex.I) * g (circleMap 0 x β))
        volume ε R) :
    (∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 ε α), ((g dz) z)) +
      (∫ᶜ z in Path.segment (circleMap 0 ε β) (circleMap 0 R β), ((g dz) z)) =
      ∫ x in ε..R,
        (Complex.exp (β * Complex.I) * g (circleMap 0 x β) -
          Complex.exp (α * Complex.I) * g (circleMap 0 x α)) := by
  have hupper :
      ∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 ε α), ((g dz) z) =
        -∫ x in ε..R, Complex.exp (α * Complex.I) * g (circleMap 0 x α) := by
    simpa using positiveAxisUpperLip_curveIntegral_eq_intervalIntegral g R ε α hR hε
  have hlower :
      ∫ᶜ z in Path.segment (circleMap 0 ε β) (circleMap 0 R β), ((g dz) z) =
        ∫ x in ε..R, Complex.exp (β * Complex.I) * g (circleMap 0 x β) := by
    simpa using positiveAxisRadialSegment_curveIntegral_eq_intervalIntegral g ε R β hε hR
  -- Package the two lip contributions into a single interval integral of the paired kernel.
  calc
    (∫ᶜ z in Path.segment (circleMap 0 R α) (circleMap 0 ε α), ((g dz) z)) +
        (∫ᶜ z in Path.segment (circleMap 0 ε β) (circleMap 0 R β), ((g dz) z)) =
      (∫ x in ε..R, Complex.exp (β * Complex.I) * g (circleMap 0 x β)) -
        ∫ x in ε..R, Complex.exp (α * Complex.I) * g (circleMap 0 x α) := by
          rw [hupper, hlower]
          abel
    _ =
      ∫ x in ε..R,
        (Complex.exp (β * Complex.I) * g (circleMap 0 x β) -
          Complex.exp (α * Complex.I) * g (circleMap 0 x α)) := by
          symm
          simpa using intervalIntegral.integral_sub hlowerInt hupperInt

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the repaired positive-axis keyhole
loop integral is the sum of its four explicit source-facing branch integrals. This isolates the
remaining analytic work from the path-concatenation bookkeeping. -/
lemma positiveAxisKeyhole_curveIntegral_eq_segmentSum
    (g : ℂ → ℂ) (R ε : ℝ)
    (hupper :
      CurveIntegrable
        (g dz)
        (Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))))
    (hinner :
      CurveIntegrable
        (g dz)
        ((Path.segment
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)).map
              (continuous_circleMap 0 ε)))
    (hlower :
      CurveIntegrable
        (g dz)
        (Path.segment
          (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))))
    (houter :
      CurveIntegrable
        (g dz)
        ((Path.segment
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)).map
              (continuous_circleMap 0 R))) :
    ∫ᶜ z in (positiveAxisKeyhole R ε).toClosedPath.toPath, (g dz) z =
      (∫ᶜ z in Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε)),
        (g dz) z) +
        (∫ᶜ z in ((Path.segment
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)).map
              (continuous_circleMap 0 ε)),
          (g dz) z) +
        (∫ᶜ z in Path.segment
            (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
            (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε)),
          (g dz) z) +
        ∫ᶜ z in ((Path.segment
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)).map
              (continuous_circleMap 0 R)),
          (g dz) z := by
  let upper := positiveAxisKeyholeUpperAngle R ε
  let lower := positiveAxisKeyholeLowerAngle R ε
  let upperLip : Path (circleMap 0 R upper) (circleMap 0 ε upper) :=
    Path.segment (circleMap 0 R upper) (circleMap 0 ε upper)
  let innerArc : Path (circleMap 0 ε upper) (circleMap 0 ε lower) :=
    (Path.segment upper lower).map (continuous_circleMap 0 ε)
  let lowerLip : Path (circleMap 0 ε lower) (circleMap 0 R lower) :=
    Path.segment (circleMap 0 ε lower) (circleMap 0 R lower)
  let outerArc : Path (circleMap 0 R lower) (circleMap 0 R upper) :=
    (Path.segment lower upper).map (continuous_circleMap 0 R)
  have hcast :
      ∫ᶜ z in (positiveAxisKeyhole R ε).toClosedPath.toPath, (g dz) z =
        ∫ᶜ z in positiveAxisKeyhole R ε, (g dz) z := by
    -- Remove the harmless closed-path cast before expanding the explicit branch concatenation.
    rw [loop_toClosedPath_toPath_eq_cast (γ := positiveAxisKeyhole R ε)]
    simp
  have hpath :
      positiveAxisKeyhole R ε = (((upperLip.trans innerArc).trans lowerLip).trans outerArc) := by
    -- This is exactly the source-facing upper-lip, inner-arc, lower-lip, outer-arc splitting.
    simp [positiveAxisKeyhole, upper, lower, upperLip, innerArc, lowerLip, outerArc]
  have hupper' : CurveIntegrable (g dz) upperLip := by
    simpa [upper, upperLip] using hupper
  have hinner' : CurveIntegrable (g dz) innerArc := by
    simpa [upper, lower, innerArc] using hinner
  have hlower' : CurveIntegrable (g dz) lowerLip := by
    simpa [lower, lowerLip] using hlower
  have houter' : CurveIntegrable (g dz) outerArc := by
    simpa [upper, lower, outerArc] using houter
  calc
    ∫ᶜ z in (positiveAxisKeyhole R ε).toClosedPath.toPath, (g dz) z =
        ∫ᶜ z in positiveAxisKeyhole R ε, (g dz) z := hcast
    _ = ∫ᶜ z in (((upperLip.trans innerArc).trans lowerLip).trans outerArc), (g dz) z := by
          rw [hpath]
    _ = (∫ᶜ z in upperLip, (g dz) z) +
          (∫ᶜ z in innerArc, (g dz) z) +
          (∫ᶜ z in lowerLip, (g dz) z) +
          ∫ᶜ z in outerArc, (g dz) z := by
          -- Peel the loop apart one concatenation at a time.
          rw [curveIntegral_trans
            (CurveIntegrable.trans (CurveIntegrable.trans hupper' hinner') hlower')
            houter']
          rw [curveIntegral_trans (CurveIntegrable.trans hupper' hinner') hlower']
          rw [curveIntegral_trans hupper' hinner']
    _ = (∫ᶜ z in Path.segment
            (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε)),
          (g dz) z) +
          (∫ᶜ z in ((Path.segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)).map
                (continuous_circleMap 0 ε)),
            (g dz) z) +
          (∫ᶜ z in Path.segment
              (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
              (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε)),
            (g dz) z) +
          ∫ᶜ z in ((Path.segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)).map
                (continuous_circleMap 0 R)),
            (g dz) z := by
          simp [upper, lower, upperLip, innerArc, lowerLip, outerArc]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the two radial slit-lip pieces of the
positive-axis keyhole contour grouped as one summand. -/
abbrev positiveAxisKeyholeLipPairIntegral
    (g : ℂ → ℂ) (R ε : ℝ) : ℂ :=
  (∫ᶜ z in Path.segment
      (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
      (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε)),
    (g dz) z) +
    ∫ᶜ z in Path.segment
      (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
      (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε)),
      (g dz) z

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the two circular arc pieces of the
positive-axis keyhole contour grouped as one summand. -/
abbrev positiveAxisKeyholeArcPairIntegral
    (g : ℂ → ℂ) (R ε : ℝ) : ℂ :=
  (∫ᶜ z in ((Path.segment
      (positiveAxisKeyholeUpperAngle R ε)
      (positiveAxisKeyholeLowerAngle R ε)).map
        (continuous_circleMap 0 ε)),
    (g dz) z) +
    ∫ᶜ z in ((Path.segment
        (positiveAxisKeyholeLowerAngle R ε)
        (positiveAxisKeyholeUpperAngle R ε)).map
          (continuous_circleMap 0 R)),
      (g dz) z

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: after expanding the repaired keyhole
loop into its four branches, the two radial lips and the two circular arcs can be grouped
separately. This is the contour-level normal form used by the remaining remainder estimate. -/
lemma positiveAxisKeyhole_curveIntegral_eq_lipPairIntegral_add_arcIntegrals
    (g : ℂ → ℂ) (R ε : ℝ)
    (hupper :
      CurveIntegrable
        (g dz)
        (Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))))
    (hinner :
      CurveIntegrable
        (g dz)
        ((Path.segment
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)).map
              (continuous_circleMap 0 ε)))
    (hlower :
      CurveIntegrable
        (g dz)
        (Path.segment
          (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))))
    (houter :
      CurveIntegrable
        (g dz)
        ((Path.segment
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)).map
              (continuous_circleMap 0 R))) :
    ∫ᶜ z in (positiveAxisKeyhole R ε).toClosedPath.toPath, (g dz) z =
      positiveAxisKeyholeLipPairIntegral g R ε +
        positiveAxisKeyholeArcPairIntegral g R ε := by
  have hsum :=
    positiveAxisKeyhole_curveIntegral_eq_segmentSum g R ε hupper hinner hlower houter
  -- Reorder the four explicit branch integrals into the lip pair and the arc pair.
  calc
    ∫ᶜ z in (positiveAxisKeyhole R ε).toClosedPath.toPath, (g dz) z =
        (∫ᶜ z in Path.segment
            (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε)),
          (g dz) z) +
          (∫ᶜ z in ((Path.segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)).map
                (continuous_circleMap 0 ε)),
            (g dz) z) +
          (∫ᶜ z in Path.segment
              (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
              (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε)),
            (g dz) z) +
          ∫ᶜ z in ((Path.segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)).map
                (continuous_circleMap 0 R)),
            (g dz) z := hsum
    _ = positiveAxisKeyholeLipPairIntegral g R ε +
          positiveAxisKeyholeArcPairIntegral g R ε := by
          simp [positiveAxisKeyholeLipPairIntegral, positiveAxisKeyholeArcPairIntegral]
          abel
