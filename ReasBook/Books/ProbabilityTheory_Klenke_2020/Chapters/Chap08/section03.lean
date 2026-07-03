import Mathlib
import Mathlib.Probability.ConditionalProbability

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_8_3_1 (from Items/Chap08) -/
open MeasureTheory
open Set

universe u

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E]
variable (μ : Measure E) [NoAtoms μ] {A : Set E} (n : ℕ+)

/-- Exercise 8.3.1: In a standard Borel space with an atom-free measure, every measurable set
admits an equal-measure partition into `n` measurable pieces. A canonical library-facing
bridge/view is a measurable map `f : E → Fin n`; the pieces are its fibers measured with respect
to the restricted measure `μ.restrict A`. -/
-- Proof sketch: Embed the standard Borel space measurably into `ℝ`, transfer the restricted
-- measure on `A` to the image, cut the image into `n` measurable pieces of equal mass by
-- successive one-dimensional measure cuts, and pull the pieces back to `E`.
theorem exists_measurable_fiber_partition_eq_of_noAtoms
    (hA : MeasurableSet A) :
    ∃ f : E → Fin n, Measurable f ∧ ∀ i, μ.restrict A (f ⁻¹' {i}) = μ A / n := sorry

/-- Exercise 8.3.1 in the source-text family-of-sets form: the equal-measure partition pieces may
be empty, so the public textbook-facing statement is an indexed family of measurable sets rather
than a `Finpartition`. -/
theorem exists_pairwiseDisjoint_iUnion_eq_measure_eq_of_noAtoms
    (hA : MeasurableSet A) :
    ∃ s : Fin n → Set E,
      (Pairwise fun i j ↦ Disjoint (s i) (s j)) ∧
      (∀ i, MeasurableSet (s i)) ∧
      (⋃ i, s i) = A ∧
      ∀ i, μ (s i) = μ A / n := by
  obtain ⟨f, hf, hμ⟩ := exists_measurable_fiber_partition_eq_of_noAtoms μ n hA
  refine ⟨fun i ↦ A ∩ f ⁻¹' {i}, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj ↦ ?_
    have hix : f x = i := by simpa using hxi.2
    have hjx : f x = j := by simpa using hxj.2
    exact hij (hix.symm.trans hjx)
  · intro i
    exact hA.inter (hf (measurableSet_singleton i))
  · ext x
    simp
  · intro i
    simpa [Measure.restrict_apply' hA, Set.inter_comm] using hμ i

/-! ### Exercise_8_3_2 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω}

-- Proof sketch: use `ProbabilityTheory.condExpKernel` to rewrite conditional expectations as
-- fiberwise integrals, apply `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` on each fiber with
-- the canonical exponent relation `hpq`, and discharge the moment side conditions from `hX` and
-- `hY`. The side case `¬ ℱ ≤ mΩ` is automatic from `condExp_of_not_le`.
/-- Exercise 8.3.2: conditional Hölder's inequality. If `p` and `q` are Hölder-conjugate and
`X ∈ ℒ^p(P)`, `Y ∈ ℒ^q(P)`, then the conditional expectation of `|XY|` is bounded almost surely
by the product of the conditional `L^p` and `L^q` moments. This is the canonical
`Real.HolderConjugate` formulation of the textbook assumptions `p, q ∈ (1, ∞)` and
`1 / p + 1 / q = 1`. -/
theorem condExp_abs_mul_ae_le_of_holderConjugate {ℱ : MeasurableSpace Ω} {p q : ℝ}
    (hpq : p.HolderConjugate q) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal q) P) :
    P[fun ω ↦ |X ω * Y ω| | ℱ] ≤ᵐ[P]
      P[fun ω ↦ |X ω| ^ p | ℱ] ^ (1 / p) * P[fun ω ↦ |Y ω| ^ q | ℱ] ^ (1 / q) := sorry

/-! ### Exercise_8_3_3 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

def closedUnitDisc : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def unitSquare : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

/-- The uniform law on the closed unit disc in `ℝ²`. -/
def unitDiscUniformMeasure : Measure (ℝ × ℝ) :=
  volume[|closedUnitDisc]

/-- The uniform law on the square `[-1,1]^2` in `ℝ²`. -/
def unitSquareUniformMeasure : Measure (ℝ × ℝ) :=
  volume[|unitSquare]

private theorem closedUnitDisc_subset_unitSquare : closedUnitDisc ⊆ unitSquare := by
  intro z hz
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1 at hz
  rw [unitSquare]
  constructor
  · constructor
    · nlinarith [sq_nonneg z.2, hz]
    · nlinarith [sq_nonneg z.2, hz]
  · constructor
    · nlinarith [sq_nonneg z.1, hz]
    · nlinarith [sq_nonneg z.1, hz]

private theorem halfUnitSquare_subset_closedUnitDisc :
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) : Set (ℝ × ℝ)) ⊆
      closedUnitDisc := by
  intro z hz
  rcases hz with ⟨hx, hy⟩
  have hx_sq : z.1 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hy_sq : z.2 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hy.1, hy.2]
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1
  nlinarith

private theorem volume_unitSquare_pos : 0 < volume unitSquare := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_unitSquare_ne_top : volume unitSquare ≠ ⊤ := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_closedUnitDisc_pos : 0 < volume closedUnitDisc := by
  refine lt_of_lt_of_le ?_ (measure_mono halfUnitSquare_subset_closedUnitDisc)
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_closedUnitDisc_ne_top : volume closedUnitDisc ≠ ⊤ := by
  refine ne_of_lt <| lt_of_le_of_lt (measure_mono closedUnitDisc_subset_unitSquare) ?_
  exact lt_top_iff_ne_top.mpr volume_unitSquare_ne_top

-- Proof sketch: apply the standard fact that conditioned Lebesgue measure on a set of positive
-- finite volume is a probability measure; here the unit disc has finite positive area.
/-- The uniform law on the closed unit disc is a probability measure. -/
instance : IsProbabilityMeasure unitDiscUniformMeasure := by
  rw [unitDiscUniformMeasure]
  exact cond_isProbabilityMeasure_of_finite volume_closedUnitDisc_pos.ne' volume_closedUnitDisc_ne_top

-- Proof sketch: apply the same conditioned-volume probability-measure fact to the square
-- `[-1,1]^2`, whose Lebesgue measure is finite and nonzero.
/-- The uniform law on `[-1,1]^2` is a probability measure. -/
instance : IsProbabilityMeasure unitSquareUniformMeasure := by
  rw [unitSquareUniformMeasure]
  exact cond_isProbabilityMeasure_of_finite volume_unitSquare_pos.ne' volume_unitSquare_ne_top

/-- The radius `R = sqrt (x^2 + y^2)` associated to a point `(x, y) ∈ ℝ²`. -/
abbrev planarRadius (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

/-- The textbook angle variable `Θ = arctan (y / x)`. In Lean, division by `0` is defined, so
this gives a total measurable function on `ℝ²`. -/
abbrev principalAngle (z : ℝ × ℝ) : ℝ :=
  Real.arctan (z.2 / z.1)

/-- The support of the principal angle on the circle of radius `r` inside the square `[-1,1]^2`.
-/
def squarePrincipalAngleSupport (r : ℝ) : Set ℝ :=
  Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ∩
    {θ | 0 ≤ r ∧ r * |Real.cos θ| ≤ 1 ∧ r * |Real.sin θ| ≤ 1}

-- Proof sketch: view the unit-disc law as a constant density on the disc and apply the density
-- formula for regular conditional distributions. The marginal in `x` is proportional to the length
-- of the vertical chord, so the fiber law is the normalized Lebesgue measure on that chord.
/-- Exercise 8.3.3 (1): In part (i), for the uniform law on the unit disc, the conditional
distribution of `Y` given `X = x` is the uniform law on
`[-sqrt (1 - x^2), sqrt (1 - x^2)]` for `P.map X`-almost every `x`. -/
theorem condDistrib_snd_given_fst_unitDisc_ae_eq_uniform_segment :
    ∀ᵐ x ∂(unitDiscUniformMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst unitDiscUniformMeasure x =
        volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] := sorry

-- Proof sketch: identify the uniform law on `[-1,1]^2` with the product of the two uniform laws
-- on `[-1,1]` and use the a.e.-uniqueness of `condDistrib` for a product decomposition.
/-- Exercise 8.3.3 (2): In part (i), for the uniform law on `[-1,1]^2`, the conditional
distribution of `Y` given `X = x` is the uniform law on `[-1,1]` for `P.map X`-almost every
`x`. -/
theorem condDistrib_snd_given_fst_unitSquare_ae_eq_uniform_interval :
    ∀ᵐ x ∂(unitSquareUniformMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst unitSquareUniformMeasure x =
        volume[|Set.Icc (-1 : ℝ) 1] := sorry

-- Proof sketch: pass to polar coordinates on the disc. The angular component is independent of
-- the radius and is uniform on the full circle; pushing that law forward by the principal-angle
-- map gives the uniform law on `[-π / 2, π / 2]`.
/-- Exercise 8.3.3 (3): In part (ii), for the uniform law on the unit disc, the conditional
distribution of `Θ = arctan (Y / X)` given `R = sqrt (X^2 + Y^2)` is the uniform law on
`[-π / 2, π / 2]` for `P.map R`-almost every `r`. -/
theorem condDistrib_principalAngle_given_radius_unitDisc_ae_eq_uniform_interval :
    ∀ᵐ r ∂(unitDiscUniformMeasure.map planarRadius),
      condDistrib principalAngle planarRadius unitDiscUniformMeasure r =
        volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := sorry

-- Proof sketch: condition on the radius and describe the fiber as the arc of the circle of radius
-- `r` lying in `[-1,1]^2`. The conditional law is uniform in arc length on that fiber, and the
-- principal-angle map pushes it forward to the conditioned Lebesgue measure on the angle support.
/-- Exercise 8.3.3 (4): In part (ii), for the uniform law on `[-1,1]^2`, the conditional
distribution of `Θ = arctan (Y / X)` given `R = sqrt (X^2 + Y^2)` is the uniform law on the
principal-angle support cut out by the circle of radius `r` inside the square, for `P.map R`-almost
every `r`. -/
theorem condDistrib_principalAngle_given_radius_unitSquare_ae_eq_uniform_support :
    ∀ᵐ r ∂(unitSquareUniformMeasure.map planarRadius),
      condDistrib principalAngle planarRadius unitSquareUniformMeasure r =
        volume[|squarePrincipalAngleSupport r] := sorry

/-! ### Remark_8_3 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: if `P B = 0`, then `P (B ∩ A) = 0` by `measure_inter_null_of_null_left`, while
-- `c * P B = c * 0 = 0`. So the defining equation from Definition 8.2 is automatically satisfied
-- for every `c`.
/-- Remark 8.3: if the conditioning event `B` has probability `0`, then every
chosen value `c` satisfies the defining equation `c * P B = P (B ∩ A)`. Thus Definition 8.2 does
not determine a unique conditional-probability value on null conditioning events. -/
theorem null_conditioning_value_irrelevant
    (P : Measure Ω) {A B : Set Ω}
    (hB : P B = 0) (c : ℝ≥0∞) :
    c * P B = P (B ∩ A) := by
  simpa [hB, Set.inter_comm] using (measure_inter_null_of_null_left A hB).symm

-- Proof sketch: `ProbabilityTheory.cond_eq_zero_of_meas_eq_zero` identifies the conditioned
-- measure `P[|B]` with `0` when `P B = 0`. Evaluating that measure at `A` gives `P[A | B] = 0`.
/-- Auxiliary canonical consequence of Remark 8.3: when `P B = 0`, the conditioned measure `P[|B]`
is `0`, so the canonical conditional probability `P[A | B]` evaluates to `0`. -/
theorem cond_apply_eq_zero_of_null
    (P : Measure Ω) {A B : Set Ω} (hB : P B = 0) :
    P[A | B] = 0 := by
  simpa using congrArg (fun ν : Measure Ω ↦ ν A) (cond_eq_zero_of_meas_eq_zero hB)

/-! ### Exercise_8_3_4 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ}

-- Proof sketch: push the conditioned measure `P[|X ⁻¹' B]` forward along `X`; by
-- `Measure.restrict_map_of_aemeasurable` and `hX.map_eq` this is exactly the conditioned
-- pushforward measure `(volume[|A])[|B]`. Since `A` has finite Lebesgue measure,
-- `ProbabilityTheory.cond_cond_eq_cond_inter'` rewrites this to
-- `volume[|A ∩ B]`, which simplifies to `volume[|B]` because `B ⊆ A`.
/-- Exercise 8.3.4: Let `A, B ⊆ ℝ^n` with `B ⊆ A`. If `A` and `B` are Borel measurable,
`A` has finite Lebesgue measure and `X` has law `volume[|A]` under `P`, then under the
conditioned measure `P[|X ⁻¹' B]` the random variable `X` has law `volume[|B]`. -/
theorem hasLaw_conditioned_on_mem_eq_volume_cond_subset
    {P : Measure Ω} {X : Ω → EuclideanSpace ℝ (Fin n)}
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B) (hBA : B ⊆ A)
    (hA_finite : volume A ≠ ⊤)
    (hX : HasLaw X (volume[|A]) P) :
    HasLaw X (volume[|B]) P[|X ⁻¹' B] := by
  refine ⟨hX.aemeasurable.mono_ac cond_absolutelyContinuous, ?_⟩
  calc
    P[|X ⁻¹' B].map X = (P.map X)[|B] := by
      rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
        Measure.restrict_map_of_aemeasurable hX.aemeasurable hB_meas,
        Measure.map_apply_of_aemeasurable hX.aemeasurable hB_meas]
    _ = (volume[|A])[|B] := by rw [hX.map_eq]
    _ = volume[|B] := by
      rw [cond_cond_eq_cond_inter' hA_meas hB_meas hA_finite]
      simp [Set.inter_eq_right.2 hBA]

/-! ### Exercise_8_3_5 (from Items/Chap08) -/
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

/-! ### Exercise_8_3_6 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

/-- The rejection-sampling index is the infimum of the accepted-index set; when that set is
nonempty, it is the first accepted proposal index. -/
noncomputable def rejectionSamplingIndex
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) : Ω → ℕ :=
  fun ω ↦ sInf {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}

/-- The rejection-sampling sample is the proposal evaluated at the rejection-sampling index; when
the accepted-index set is nonempty, this is the first accepted proposal value. -/
noncomputable def rejectionSamplingValue
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) : Ω → E :=
  fun ω ↦ X (rejectionSamplingIndex X U accept ω) ω

/-- If the accepted-index set is nonempty, then the rejection-sampling index is its least
element. -/
theorem isLeast_rejectionSamplingIndex
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) {ω : Ω}
    (hω : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty) :
    IsLeast {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} (rejectionSamplingIndex X U accept ω) := by
  constructor
  · simpa [rejectionSamplingIndex] using Nat.sInf_mem hω
  · intro n hn
    simpa [rejectionSamplingIndex] using (Nat.sInf_le hn)

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- The acceptance probability used by rejection sampling for the proposal law `p` and the target
law `q`, with rejection constant `c`. -/
noncomputable def rejectionAcceptanceProb (p q : PMF E) (c : ℝ) (e : E) : ℝ :=
  if p e = 0 then 0 else (q e).toReal / (c * (p e).toReal)

-- Proof sketch: split on whether `p e = 0`. In the zero-mass case the definition is `0`. In the
-- nonzero case, rewrite `rejectionAcceptanceProb` and divide the domination inequality by the
-- positive number `c * (p e).toReal`.
/-- Under the domination bound `q ≤ c p`, every rejection-sampling acceptance probability is at
most `1`. -/
theorem rejectionAcceptanceProb_le_one
    (p q : PMF E) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal) (e : E) :
    rejectionAcceptanceProb p q c e ≤ 1 := sorry

-- Proof sketch: for each `e`, compute the probability that the first accepted proposal equals
-- `e` by summing over the first acceptance time. The pairwise i.i.d. hypothesis gives a geometric
-- factor from the previous rejections and identifies the acceptance probability at time `n` with
-- `q e / c`; summing the geometric series yields exactly `q e`. Equality of singleton masses then
-- gives `HasLaw Y q.toMeasure μ`.
/-- Canonical paired formulation of Exercise 8.3.6: if the proposal-auxiliary pairs `(X n, U n)`
form an independent sequence with common law `p × uniform[0,1]`, then the rejection-sampling
value associated to `rejectionAcceptanceProb p q c` has law `q`. -/
theorem hasLaw_of_rejection_sampling_of_pair_iIndep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ)
    (h_pair_law : ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω))
      (p.toMeasure.prod volume) μ) :
    HasLaw (rejectionSamplingValue X U (rejectionAcceptanceProb p q c)) q.toMeasure μ := sorry

/-- Independent random variables with laws `ν` and `η` have joint law `ν.prod η`. -/
theorem hasLaw_prod_of_hasLaw_of_indep
    {F G : Type*} [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ν : Measure F} {η : Measure G}
    (X : Ω → F) (Y : Ω → G)
    (hX_law : HasLaw X ν μ) (hY_law : HasLaw Y η μ)
    (hXY : X ⟂ᵢ[μ] Y) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (ν.prod η) μ := by
  refine
    { aemeasurable := hX_law.aemeasurable.prodMk hY_law.aemeasurable
      map_eq := ?_ }
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX_law.aemeasurable hY_law.aemeasurable).mp hXY,
    hX_law.map_eq, hY_law.map_eq]

omit [MeasurableSingletonClass E] [Countable E] in
/-- If `X` and `U` are i.i.d. families and the sequence-valued random elements are independent,
then the paired family `n ↦ (X n, U n)` is independent. -/
theorem iIndepFun_pair_of_iIndepFun_of_indepFun
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ν : Measure E}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) ν μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ := by
  rw [iIndepFun_iff_finset]
  intro s
  have hX_restrict' : iIndepFun (fun i : s ↦ X i) μ :=
    hX_iIndep.precomp Subtype.val_injective
  have hX_restrict : iIndepFun (s.restrict X) μ := by
    simpa [Finset.restrict] using hX_restrict'
  have hU_restrict' : iIndepFun (fun i : s ↦ U i) μ :=
    hU_iIndep.precomp Subtype.val_injective
  have hU_restrict : iIndepFun (s.restrict U) μ := by
    simpa [Finset.restrict] using hU_restrict'
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · change μ.map (fun ω (i : s) ↦ (X i ω, U i ω)) =
      Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω)))
    let φ : (ℕ → E) → (s → E) := fun f i ↦ f i
    let ψ : (ℕ → unitInterval) → (s → unitInterval) := fun f i ↦ f i
    have h_indep_restrict :
        IndepFun (fun ω (i : s) ↦ X i ω) (fun ω (i : s) ↦ U i ω) μ := by
      have hφ : Measurable φ := by
        fun_prop
      have hψ : Measurable ψ := by
        fun_prop
      simpa [φ, ψ] using h_seq_indep.comp hφ hψ
    have h_map_eq :
        μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ U i ω)) =
          (Measure.pi fun i : s ↦ μ.map (X i)).prod
            (Measure.pi fun i : s ↦ μ.map (U i)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (aemeasurable_pi_lambda _ fun i : s ↦ (hX_law i).aemeasurable)
        (aemeasurable_pi_lambda _ fun i : s ↦ (hU_law i).aemeasurable)).mp h_indep_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ (hX_law i).aemeasurable).mp hX_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ (hU_law i).aemeasurable).mp hU_restrict]
    have h_pair_map_eq (i : s) :
        μ.map (fun ω ↦ (X i ω, U i ω)) = (μ.map (X i)).prod (μ.map (U i)) := by
      have h_indep_i : X i ⟂ᵢ[μ] U i := by
        simpa using h_seq_indep.comp (measurable_pi_apply (i : ℕ)) (measurable_pi_apply (i : ℕ))
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (hX_law i).aemeasurable (hU_law i).aemeasurable).mp h_indep_i]
    let e := MeasurableEquiv.arrowProdEquivProdArrow E unitInterval s
    have h_pair_vec_aemeasurable : AEMeasurable (fun ω (i : s) ↦ (X i ω, U i ω)) μ :=
      aemeasurable_pi_lambda _ fun i : s ↦
        ((hX_law i).aemeasurable).prodMk ((hU_law i).aemeasurable)
    rw [← e.map_measurableEquiv_injective.eq_iff]
    rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable h_pair_vec_aemeasurable]
    change μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ U i ω)) =
      Measure.map e (Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω))))
    refine h_map_eq.trans ?_
    symm
    calc
      Measure.map e (Measure.pi fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω)))
          = Measure.map e (Measure.pi fun i : s ↦ (μ.map (X i)).prod (μ.map (U i))) := by
              simp [h_pair_map_eq]
      _ = (Measure.pi fun i : s ↦ μ.map (X i)).prod (Measure.pi fun i : s ↦ μ.map (U i)) :=
            (measurePreserving_arrowProdEquivProdArrow E unitInterval s
              (fun i : s ↦ μ.map (X i)) (fun i : s ↦ μ.map (U i))).map_eq
  · intro i
    simpa [Finset.restrict] using
      (((hX_law i).aemeasurable).prodMk ((hU_law i).aemeasurable) :
        AEMeasurable (fun ω ↦ (X i ω, U i ω)) μ)

/-- Exercise 8.3.6: if the proposals `X n` are i.i.d. with law `p`, the auxiliary variables `U n`
are i.i.d. uniform on `[0,1]`, and the two sequences are independent, then the associated
rejection-sampling value has law `q`. -/
theorem hasLaw_of_rejection_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) p.toMeasure μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    HasLaw (rejectionSamplingValue X U (rejectionAcceptanceProb p q c)) q.toMeasure μ := by
  have h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ :=
    iIndepFun_pair_of_iIndepFun_of_indepFun μ (ν := p.toMeasure) X U
      hX_iIndep hX_law hU_iIndep hU_law h_seq_indep
  have h_pair_law : ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (p.toMeasure.prod volume) μ := by
    intro n
    have h_indep_n : X n ⟂ᵢ[μ] U n := by
      simpa using h_seq_indep.comp (measurable_pi_apply n) (measurable_pi_apply n)
    exact hasLaw_prod_of_hasLaw_of_indep μ (X n) (U n) (hX_law n) (hU_law n) h_indep_n
  exact hasLaw_of_rejection_sampling_of_pair_iIndep μ p q c X U hc hdom h_pair_iIndep h_pair_law

/-- If `N` is almost surely the first accepted proposal index, then the associated proposal value
agrees almost surely with the canonical rejection-sampling value. -/
theorem ae_eq_rejectionSamplingValue_of_ae_isLeast
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) (N : Ω → ℕ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} (N ω)) :
    (fun ω ↦ X (N ω) ω) =ᵐ[μ] rejectionSamplingValue X U accept := by
  filter_upwards [hN] with ω hω
  dsimp [rejectionSamplingValue, rejectionSamplingIndex]
  rw [hω.isGLB.csInf_eq hω.nonempty]

/-- Textbook-form bridge for Exercise 8.3.6: if `N` is almost surely the first accepted index and
`Y = X N` almost surely, then `Y` has law `q`. -/
theorem hasLaw_of_rejection_sampling_of_ae_isLeast
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (N : Ω → ℕ) (Y : Ω → E)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) p.toMeasure μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ rejectionAcceptanceProb p q c (X n ω)} (N ω))
    (hY : Y =ᵐ[μ] fun ω ↦ X (N ω) ω) :
    HasLaw Y q.toMeasure μ := by
  refine (hasLaw_of_rejection_sampling μ p q c X U hc hdom
    hX_iIndep hX_law hU_iIndep hU_law h_seq_indep).congr ?_
  exact hY.trans (ae_eq_rejectionSamplingValue_of_ae_isLeast μ X U
    (rejectionAcceptanceProb p q c) N hN)

/-! ### Exercise_8_3_7 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

-- Proof sketch: view each proposal-auxiliary pair `(X n, U n)` as i.i.d. with common law
-- `P.prod volume`. The acceptance event at step `n` has conditional probability
-- `(Q.rnDeriv P (X n ·)).toReal / c`, and `Q ≪ P` together with the bound by `c` identifies the
-- accepted proposal law with `Q`. Summing over the first accepted index yields the law of the
-- selected sample.
/-- Exercise 8.3.7: if `Q ≪ P` and the Radon--Nikodym derivative `dQ/dP` is bounded by `c`, then
the rejection-sampling value with acceptance probability `x ↦ (dQ/dP)(x) / c` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ)
    (h_pair_law :
      ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (P.prod (volume : Measure unitInterval)) μ) :
    HasLaw (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) Q μ := sorry

/-- Exercise 8.3.7 in textbook hypothesis form: if the proposals `X n` are i.i.d. with law `P`,
the auxiliary variables `U n` are i.i.d. uniform on `[0,1]`, and the two sequences are
independent, then the rejection-sampling value with acceptance probability
`x ↦ (dQ/dP)(x) / c` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_iIndep_of_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) P μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) (volume : Measure unitInterval) μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    HasLaw (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) Q μ := by
  have h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ :=
    iIndepFun_pair_of_iIndepFun_of_indepFun μ X U
      hX_iIndep hX_law hU_iIndep hU_law h_seq_indep
  have h_pair_law :
      ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (P.prod (volume : Measure unitInterval)) μ := by
    intro n
    have h_indep_n : X n ⟂ᵢ[μ] U n := by
      simpa using h_seq_indep.comp (measurable_pi_apply n) (measurable_pi_apply n)
    exact hasLaw_prod_of_hasLaw_of_indep μ (X n) (U n) (hX_law n) (hU_law n) h_indep_n
  exact hasLaw_rejectionSamplingValue_of_rnDeriv_le μ P Q c hc hQP hbounded X U
    h_pair_iIndep h_pair_law

/-- Textbook-form bridge for Exercise 8.3.7: if `N` is almost surely the first accepted index and
`Y = X N` almost surely, then `Y` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_ae_isLeast
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (N : Ω → ℕ) (Y : Ω → E)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) P μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) (volume : Measure unitInterval) μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ (Q.rnDeriv P (X n ω)).toReal / c} (N ω))
    (hY : Y =ᵐ[μ] fun ω ↦ X (N ω) ω) :
    HasLaw Y Q μ := by
  let accept : E → ℝ := fun x ↦ (Q.rnDeriv P x).toReal / c
  refine (hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_iIndep_of_indep μ P Q c hc hQP
    hbounded X U hX_iIndep hX_law hU_iIndep hU_law h_seq_indep).congr ?_
  refine hY.trans ?_
  simpa [accept] using ae_eq_rejectionSamplingValue_of_ae_isLeast μ X U accept N hN

/-! ### Exercise_8_3_8 (from Items/Chap08) -/
open MeasureTheory

-- Proof sketch: for `n > 0`, the first coordinate gives an injection `ℝ ↪ EuclideanSpace ℝ (Fin n)`,
-- so `EuclideanSpace ℝ (Fin n)` is uncountable; then apply the general classification theorem
-- `PolishSpace.measurableEquivOfNotCountable`.
private theorem euclideanSpace_not_countable {n : ℕ} (hn : 0 < n) :
    ¬ Countable (EuclideanSpace ℝ (Fin n)) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hsingle : Function.Injective (EuclideanSpace.single i0 : ℝ → EuclideanSpace ℝ (Fin n)) := by
    intro x y hxy
    simpa using congrArg (fun v ↦ v i0) hxy
  exact hsingle.uncountable.not_countable

/-- Exercise 8.3.8 (1): for every positive dimension `n`, the measurable spaces `ℝ` and
`EuclideanSpace ℝ (Fin n)`, both equipped with their Borel sigma-algebras, are isomorphic. -/
noncomputable def euclideanSpace_measurableEquiv_real {n : ℕ} (hn : 0 < n) :
    EuclideanSpace ℝ (Fin n) ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable (euclideanSpace_not_countable hn) not_countable

-- Proof sketch: `EuclideanSpace ℝ (Fin n)` is a standard Borel space, and every measurable
-- subset of a standard Borel space is again standard Borel by `MeasurableSet.standardBorel`.
/- Exercise 8.3.8 (2): every Borel subset of `EuclideanSpace ℝ (Fin n)` is a Borel space in the
textbook sense, via the owner theorem `MeasurableSet.standardBorel` for measurable subsets of
standard Borel spaces. -/
recall MeasurableSet.standardBorel
