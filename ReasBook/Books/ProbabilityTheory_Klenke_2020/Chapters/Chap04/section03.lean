import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_4_3_1 (from Items/Chap04) -/
open MeasureTheory BoxIntegral

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1
local notation "unitIntervalVolume" => volume.restrict unitIntervalSet

-- Proof sketch: use the chapter's canonical notion `RiemannIntegrableOnUnitInterval`. For the
-- forward direction, use the classical criterion that a bounded Riemann integrable function is
-- a.e. continuous on `[0,1]`. For the reverse direction, apply
-- `BoxIntegral.integrable_of_bounded_and_ae_continuous` to the lifted function `fun x ↦ f (x 0)`
-- and transport the boundedness and a.e.-continuity hypotheses from `[0,1]` to the canonical
-- one-dimensional box model.
private theorem exists_norm_bound_on_unitInterval {f : ℝ → ℝ}
    (hb : Bornology.IsBounded (f '' unitIntervalSet)) :
    ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C := by
  rcases hb.exists_norm_le with ⟨C, hC⟩
  exact ⟨C, fun x hx ↦ hC (f x) (Set.mem_image_of_mem f hx)⟩

/-- Exercise 4.3.1: for a bounded function on `[0,1]`, Riemann integrability on `[0,1]` in the
chapter's canonical one-dimensional box model is equivalent to `volume`-almost everywhere
continuity on `[0,1]`. -/
theorem riemannIntegrableOn_unitInterval_iff_aeContinuousWithinAt
    {f : ℝ → ℝ} (hb : Bornology.IsBounded (f '' unitIntervalSet)) :
    RiemannIntegrableOnUnitInterval f ↔
      ∀ᵐ x ∂unitIntervalVolume, ContinuousWithinAt f unitIntervalSet x := by
  constructor
  · intro hf
    sorry
  · intro hc
    have hb' : ∃ C : ℝ, ∀ x ∈ unitIntervalSet, ‖f x‖ ≤ C :=
      exists_norm_bound_on_unitInterval hb
    sorry

/-! ### Exercise_4_3_2 (from Items/Chap04) -/
open MeasureTheory

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1
local notation "unitIntervalVolume" => volume.restrict unitIntervalSet

-- Proof sketch: apply `integrableOn_Icc_and_integral_eq_of_riemannIntegrable` with `a = 0`,
-- `b = 1` to obtain `IntegrableOn f unitIntervalSet volume`, then use `Integrable.aemeasurable`
-- for the restricted measure.
/-- Exercise 4.3.2: if `f` is Riemann integrable on `[0,1]`, then `f` is Lebesgue measurable on
`[0,1]`. -/
theorem aemeasurable_restrict_unitInterval_of_riemannIntegrable
    {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f) :
    AEMeasurable f unitIntervalVolume := by
  rcases integrableOn_Icc_and_integral_eq_of_riemannIntegrable zero_lt_one hf with ⟨hf_int, _⟩
  exact hf_int.integrable.aemeasurable

-- Proof sketch: choose a non-Borel subset of a closed null subset of `[0,1]`, take its indicator
-- function, note that it vanishes almost everywhere on `[0,1]` and hence is Riemann integrable,
-- but its restriction to `[0,1]` cannot be Borel measurable because the level set `{1}` recovers
-- the chosen non-Borel subset.
/-- There exists a function on `[0,1]` that is Riemann integrable but whose restriction to the
interval subtype is not Borel measurable. -/
theorem exists_riemannIntegrable_unitInterval_not_borelMeasurable :
    ∃ f : ℝ → ℝ,
      RiemannIntegrableOnUnitInterval f ∧
      ¬ Measurable (f ∘ Subtype.val : unitIntervalSet → ℝ) := sorry

/-! ### Exercise_4_3_3 (from Items/Chap04) -/
open MeasureTheory BoxIntegral intervalIntegral

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1

-- Proof sketch: use Theorem 4.23 to identify the chapter's Riemann box integral on `[0,1]` with
-- the interval integral on `0..1`, then prove positivity of that interval integral.
/-- Exercise 4.3.3: if `f` is Riemann integrable on `[0,1]` and `f` is strictly positive on
`[0,1]`, then its Riemann integral on `[0,1]`, encoded by the chapter's box integral, is strictly
positive. -/
theorem riemannIntegral_pos_of_posOn_unitInterval
    {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f)
    (hpos : ∀ x ∈ unitIntervalSet, 0 < f x) :
    0 <
      integral (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := by
  rcases intervalIntegrable_and_intervalIntegral_eq_of_riemannIntegrable zero_lt_one hf with
    ⟨hf_interval, h_integral_eq⟩
  have h_interval_pos : 0 < ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral_pos_of_pos_on hf_interval
      (fun x hx ↦ hpos x <| Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩) zero_lt_one
  simpa [h_integral_eq] using h_interval_pos

/-! ### Lemma_4_3 (from Items/Chap04) -/
open MeasureTheory

universe u

variable {α : Type u} [MeasurableSpace α] (μ : Measure α)

/- Lemma 4.3 (1): Part (i): the map `I` on nonnegative elementary functions is homogeneous for
nonnegative scalars. -/
recall SimpleFunc.const_mul_lintegral

/- Lemma 4.3 (2): Part (ii): the map `I` on nonnegative elementary functions is additive. -/
recall SimpleFunc.add_lintegral

/- Lemma 4.3 (3): Part (iii): the map `I` on nonnegative elementary functions is monotone
increasing. -/
recall SimpleFunc.lintegral_mono_fun
