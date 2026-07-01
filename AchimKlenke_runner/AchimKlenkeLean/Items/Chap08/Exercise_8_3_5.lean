import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The ambient Euclidean space `ℝ^3` used for the Earth/sphere model in Borel's paradox. -/
local notation "Earth" => EuclideanSpace ℝ (Fin 3)

/-- The Earth's surface, modeled as the unit sphere in `ℝ^3`. -/
local notation "EarthSurface" => Metric.sphere (0 : Earth) 1

/-- The unit sphere in `ℝ^3` is nonempty. -/
instance : Nonempty EarthSurface := by
  let h : (Metric.sphere (0 : Earth) (1 : ℝ)).Nonempty ↔ 0 ≤ (1 : ℝ) :=
    NormedSpace.sphere_nonempty
  exact h.2 zero_le_one |>.to_subtype

/-- The uniform distribution on the Earth's surface, modeled as the normalized spherical surface
measure on the unit sphere in `ℝ^3`. -/
noncomputable def earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface :=
  FiniteMeasure.normalize
    (⟨(volume : Measure Earth).toSphere, inferInstance⟩ : FiniteMeasure EarthSurface)

/-- The textbook longitude-latitude parametrization used in Borel's paradox: `θ ∈ [0, π)` picks
the vertical great circle and `φ ∈ [-π, π)` runs once around that great circle. -/
def earthPointOfLongitudeLatitude (θ φ : ℝ) : EarthSurface :=
  ⟨WithLp.toLp 2
      (fun i : Fin 3 ↦
        if i = 0 then Real.cos θ * Real.cos φ
        else if i = 1 then Real.sin θ * Real.cos φ
        else Real.sin φ),
    by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_three, pow_two]
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]⟩

/-- The canonical longitude coordinate in the textbook Borel-paradox parametrization of the unit
sphere. It records the meridian as an angle in `[0, π]`, i.e. modulo antipodal reversal in the
equatorial plane. -/
noncomputable def borelParadoxLongitude (x : EarthSurface) : ℝ :=
  let θ := Complex.arg (x.1 0 + x.1 1 * Complex.I)
  if θ < 0 then θ + Real.pi else θ

/-- The canonical latitude coordinate in the textbook Borel-paradox parametrization of the unit
sphere. After choosing the meridian via `borelParadoxLongitude`, this is the signed angle of `x`
along that great circle, valued in `[-π, π]`. -/
noncomputable def borelParadoxLatitude (x : EarthSurface) : ℝ :=
  let θ := borelParadoxLongitude x
  Complex.arg ((x.1 0 * Real.cos θ + x.1 1 * Real.sin θ) + x.1 2 * Complex.I)

/-- The canonical Borel-paradox coordinates reconstruct the original point on the sphere. -/
theorem earthPointOfLongitudeLatitude_borelParadoxCoordinates (x : EarthSurface) :
    earthPointOfLongitudeLatitude (borelParadoxLongitude x) (borelParadoxLatitude x) = x := by
  sorry

/-- The canonical Borel-paradox longitude lies in `[0, π]`; this is the closed-interval version of
the textbook range `[0, π)`, differing only by an endpoint convention. -/
theorem borelParadoxLongitude_mem_Icc (x : EarthSurface) :
    borelParadoxLongitude x ∈ Set.Icc 0 Real.pi := by
  sorry

/-- The canonical Borel-paradox latitude lies in `[-π, π]`; this is the closed-interval version of
the textbook range `[-π, π)`, differing only by an endpoint convention. -/
theorem borelParadoxLatitude_mem_Icc (x : EarthSurface) :
    borelParadoxLatitude x ∈ Set.Icc (-Real.pi) Real.pi := by
  sorry

/-- The longitude law in Borel's paradox: the uniform probability measure on `[0, π)`, realized
as the conditioned Lebesgue measure on `[0, π]`. -/
noncomputable def borelParadoxLongitudeMeasure : Measure ℝ :=
  volume[|Set.Icc 0 Real.pi]

/-- The longitude law in Borel's paradox has constant Lebesgue density `1 / π` on `[0, π]`. -/
theorem borelParadoxLongitudeMeasure_def :
    borelParadoxLongitudeMeasure =
      volume.withDensity
        (Set.indicator (Set.Icc 0 Real.pi) fun _ ↦ ENNReal.ofReal (1 / Real.pi)) := by
  calc
    borelParadoxLongitudeMeasure = (volume (Set.Icc 0 Real.pi))⁻¹ • volume.restrict (Set.Icc 0 Real.pi) := by
      rfl
    _ = (volume.restrict (Set.Icc 0 Real.pi)).withDensity
          ((volume (Set.Icc 0 Real.pi))⁻¹ • (1 : ℝ → ℝ≥0∞)) := by
        rw [withDensity_smul _ measurable_one, withDensity_one]
    _ = volume.withDensity
          (Set.indicator (Set.Icc 0 Real.pi) ((volume (Set.Icc 0 Real.pi))⁻¹ • (1 : ℝ → ℝ≥0∞))) := by
        rw [← withDensity_indicator measurableSet_Icc]
    _ = volume.withDensity
          (Set.indicator (Set.Icc 0 Real.pi) fun _ ↦ ENNReal.ofReal (1 / Real.pi)) := by
        congr with x
        simp [Real.volume_Icc, Real.pi_pos, ENNReal.ofReal_inv_of_pos]

/-- The latitude law in Borel's paradox: the probability measure on `[-π, π)` with density
`φ ↦ |cos φ| / 4`, written on `[-π, π]` since the endpoint change is null for Lebesgue measure. -/
noncomputable def borelParadoxLatitudeMeasure : Measure ℝ :=
  volume.withDensity
    (Set.indicator (Set.Icc (-Real.pi) Real.pi) fun φ ↦
      ENNReal.ofReal (|Real.cos φ| / 4))

/-- The defining density formula for the latitude law in Borel's paradox. -/
theorem borelParadoxLatitudeMeasure_def :
    borelParadoxLatitudeMeasure =
      volume.withDensity
        (Set.indicator (Set.Icc (-Real.pi) Real.pi) fun φ ↦
          ENNReal.ofReal (|Real.cos φ| / 4)) := rfl

instance : IsProbabilityMeasure borelParadoxLongitudeMeasure := by
  exact cond_isProbabilityMeasure_of_finite
    (by
      exact ne_of_gt <| by
        simpa [Real.volume_Icc] using (ENNReal.ofReal_pos.mpr Real.pi_pos))
    (by simp [Real.volume_Icc])

instance : IsProbabilityMeasure borelParadoxLatitudeMeasure := by
  sorry

section BorelParadox

variable (P : Measure Ω) (X : Ω → EarthSurface) (Θ Φ : Ω → ℝ)

-- Proof sketch: push the uniform surface law on the sphere through the textbook longitude-latitude
-- parametrization to obtain the product law of `(Θ, Φ)`.
private theorem hasLaw_longitude_latitude_pair_of_uniformOnEarthSurface
    (hX : HasLaw X earthSurfaceUniformMeasure P)
    (hcoords : ∀ᵐ ω ∂P, X ω = earthPointOfLongitudeLatitude (Θ ω) (Φ ω))
    (hΘ_range : ∀ᵐ ω ∂P, Θ ω ∈ Set.Icc 0 Real.pi)
    (hΦ_range : ∀ᵐ ω ∂P, Φ ω ∈ Set.Icc (-Real.pi) Real.pi) :
    HasLaw (fun ω ↦ (Θ ω, Φ ω))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P := by
  sorry

private theorem hasLaw_borelParadoxCoordinates_of_uniformOnEarthSurface
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    HasLaw (fun ω ↦ (borelParadoxLongitude (X ω), borelParadoxLatitude (X ω)))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P := by
  refine
    hasLaw_longitude_latitude_pair_of_uniformOnEarthSurface P X
      (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) hX
      ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun ω ↦
      (earthPointOfLongitudeLatitude_borelParadoxCoordinates (X ω)).symm
  · exact Filter.Eventually.of_forall fun ω ↦ borelParadoxLongitude_mem_Icc (X ω)
  · exact Filter.Eventually.of_forall fun ω ↦ borelParadoxLatitude_mem_Icc (X ω)

-- Proof sketch: identify the joint law of `(Θ, Φ)` with the product of the longitude and
-- latitude measures, then use `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd` with
-- the constant kernel having value `borelParadoxLatitudeMeasure`.
private theorem condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel_of_pair_law
    (P : Measure Ω) (Θ Φ : Ω → ℝ)
    (hΘΦ : HasLaw (fun ω ↦ (Θ ω, Φ ω))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P) :
    let _ : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
    condDistrib Φ Θ P =ᵐ[borelParadoxLongitudeMeasure]
      Kernel.const ℝ borelParadoxLatitudeMeasure := by
  letI : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
  have hΘ :
      HasLaw Θ borelParadoxLongitudeMeasure P :=
    let hfst : HasLaw Prod.fst borelParadoxLongitudeMeasure
        (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) :=
      ⟨measurable_fst.aemeasurable, by
        rw [Measure.map_fst_prod]
        simp⟩
    by exact hfst.comp hΘΦ
  have hΦ : AEMeasurable Φ P := measurable_snd.comp_aemeasurable hΘΦ.aemeasurable
  have h :
      condDistrib Φ Θ P =ᵐ[P.map Θ]
        Kernel.const ℝ borelParadoxLatitudeMeasure := by
    refine condDistrib_ae_eq_of_measure_eq_compProd Θ hΦ ?_
    rw [hΘΦ.map_eq, hΘ.map_eq, Measure.compProd_const]
  simpa [hΘ.map_eq] using h

/-- Exercise 8.3.5 (1), in kernel form: if `X` is uniformly distributed on the Earth's surface and
`borelParadoxLongitude ∘ X` and `borelParadoxLatitude ∘ X` are its textbook longitude and latitude,
then the regular conditional distribution of `borelParadoxLatitude ∘ X` given
`borelParadoxLongitude ∘ X` is almost everywhere the constant kernel with value
`borelParadoxLatitudeMeasure`. -/
theorem condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    condDistrib (borelParadoxLatitude ∘ X) (borelParadoxLongitude ∘ X) P
      =ᵐ[borelParadoxLongitudeMeasure]
      Kernel.const ℝ borelParadoxLatitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  have hΘΦ :=
    hasLaw_borelParadoxCoordinates_of_uniformOnEarthSurface P X hX
  exact
    condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel_of_pair_law
      P (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) hΘΦ

/-- Exercise 8.3.5 (1): if `X` is uniformly distributed on the Earth's surface, then for almost
every textbook longitude `θ` the regular conditional distribution of
`borelParadoxLatitude ∘ X` given `borelParadoxLongitude ∘ X = θ` has density
`φ ↦ |cos φ| / 4` on `[-π, π)`. -/
theorem condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitude
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    ∀ᵐ θ ∂borelParadoxLongitudeMeasure,
      condDistrib (borelParadoxLatitude ∘ X) (borelParadoxLongitude ∘ X) P θ =
        borelParadoxLatitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  simpa using
    condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel
      P X hX

-- Proof sketch: the same product-law description shows that the joint law also disintegrates over
-- the latitude coordinate with the constant kernel equal to the longitude law; then apply
-- a.e.-uniqueness of `ProbabilityTheory.condDistrib`.
private theorem condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel_of_pair_law
    (P : Measure Ω) (Θ Φ : Ω → ℝ)
    (hΘΦ : HasLaw (fun ω ↦ (Θ ω, Φ ω))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P) :
    let _ : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
    condDistrib Θ Φ P =ᵐ[borelParadoxLatitudeMeasure]
      Kernel.const ℝ borelParadoxLongitudeMeasure := by
  letI : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
  have hΦ :
      HasLaw Φ borelParadoxLatitudeMeasure P :=
    let hsnd : HasLaw Prod.snd borelParadoxLatitudeMeasure
        (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) :=
      ⟨measurable_snd.aemeasurable, by
        rw [Measure.map_snd_prod]
        simp⟩
    by exact hsnd.comp hΘΦ
  have hΘ : AEMeasurable Θ P := measurable_fst.comp_aemeasurable hΘΦ.aemeasurable
  have h :
      condDistrib Θ Φ P =ᵐ[P.map Φ]
        Kernel.const ℝ borelParadoxLongitudeMeasure := by
    refine condDistrib_ae_eq_of_measure_eq_compProd Φ hΘ ?_
    calc
      P.map (fun x ↦ (Φ x, Θ x))
          = (P.map (fun x ↦ (Θ x, Φ x))).map Prod.swap := by
            rw [show (fun x ↦ (Φ x, Θ x)) = Prod.swap ∘ fun x ↦ (Θ x, Φ x) by rfl]
            rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hΘΦ.aemeasurable]
      _ = (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure).map Prod.swap := by
            rw [hΘΦ.map_eq]
      _ = borelParadoxLatitudeMeasure.prod borelParadoxLongitudeMeasure := by
            rw [Measure.prod_swap]
      _ = P.map Φ ⊗ₘ Kernel.const ℝ borelParadoxLongitudeMeasure := by
            rw [hΦ.map_eq, Measure.compProd_const]
  simpa [hΦ.map_eq] using h

/-- Exercise 8.3.5 (2), in kernel form: if `X` is uniformly distributed on the Earth's surface and
`borelParadoxLongitude ∘ X` and `borelParadoxLatitude ∘ X` are its textbook longitude and latitude,
then the regular conditional distribution of `borelParadoxLongitude ∘ X` given
`borelParadoxLatitude ∘ X` is almost everywhere the constant kernel with value
`borelParadoxLongitudeMeasure`. -/
theorem condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    condDistrib (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) P
      =ᵐ[borelParadoxLatitudeMeasure]
      Kernel.const ℝ borelParadoxLongitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  have hΘΦ :=
    hasLaw_borelParadoxCoordinates_of_uniformOnEarthSurface P X hX
  exact
    condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel_of_pair_law
      P (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) hΘΦ

/-- Exercise 8.3.5 (2): if `X` is uniformly distributed on the Earth's surface, then for almost
every textbook latitude `φ` the regular conditional distribution of
`borelParadoxLongitude ∘ X` given `borelParadoxLatitude ∘ X = φ` is the uniform law on `[0, π)`.
-/
theorem condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitude
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    ∀ᵐ φ ∂borelParadoxLatitudeMeasure,
      condDistrib (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) P φ =
        borelParadoxLongitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  simpa using
    condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel
      P X hX

end BorelParadox
