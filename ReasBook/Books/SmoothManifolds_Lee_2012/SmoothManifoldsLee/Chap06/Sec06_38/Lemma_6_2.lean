import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

namespace EuclideanSpace

/-- The canonical measurable identification `ℝ^(n+1) ≃ ℝ × ℝ^n` obtained by splitting off the
first coordinate. -/
noncomputable def firstCoordinateMeasurableEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin n) :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ))

/-- The canonical first-coordinate identification preserves Lebesgue measure. -/
theorem firstCoordinateMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (firstCoordinateMeasurableEquiv n) := by
  have h_toPi :
      MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))
  have h_split :
      MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have h_tail :
      MeasurePreserving
        (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.toLp 2 (Fin n → ℝ)))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    simpa using
      (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_toLp (Fin n))
  simpa [firstCoordinateMeasurableEquiv] using h_tail.comp (h_split.comp h_toPi)

end EuclideanSpace

open EuclideanSpace

/-- Under the canonical product identification `ℝ^(n+1) ≃ ℝ × ℝ^n`, if every
first-coordinate slice of a measurable set has measure zero,
then the set itself has measure zero. -/
theorem volume_eq_zero_of_measurableSet_of_forall_first_coordinate_slice_volume_eq_zero
    {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : MeasurableSet A)
    (hslice :
      ∀ c : ℝ, volume (Prod.mk c ⁻¹' (firstCoordinateMeasurableEquiv n '' A)) = 0) :
    volume A = 0 := by
  let e := firstCoordinateMeasurableEquiv n
  have he : MeasurePreserving e := firstCoordinateMeasurableEquiv_measurePreserving n
  have hAe : MeasurableSet (e '' A) := e.measurableSet_image.2 hA
  have hzero : volume (e '' A) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.measure_prod_null_of_ae_null hAe (Filter.Eventually.of_forall hslice)
  rw [← he.map_eq, Measure.map_apply e.measurable hAe] at hzero
  simpa [e.injective.preimage_image] using hzero

/-- Lemma 6.2: under the canonical product identification `ℝ^(n+1) ≃ ℝ × ℝ^n`, if every
first-projection fiber of a compact set has measure zero, then the set itself has measure zero. -/
theorem volume_eq_zero_of_isCompact_of_forall_first_coordinate_slice_volume_eq_zero
    {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : IsCompact A)
    (hslice :
      ∀ c : ℝ, volume (Prod.mk c ⁻¹' (firstCoordinateMeasurableEquiv n '' A)) = 0) :
    volume A = 0 := by
  exact
    volume_eq_zero_of_measurableSet_of_forall_first_coordinate_slice_volume_eq_zero
      hA.measurableSet hslice
