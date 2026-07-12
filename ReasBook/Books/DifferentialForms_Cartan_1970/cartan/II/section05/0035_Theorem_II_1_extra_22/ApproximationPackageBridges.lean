import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackages

open MeasureTheory
open scoped BigOperators

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: exact coordinate half-formulas on
`interior K` can be repackaged as the constant direct measurable approximation family on
`interior K`. -/
theorem directSetApproximationPackage_of_coordinateHalfFormulasOnInterior
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    (hQ :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z)
    (hP :
      (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        - ∫ z in interior K, dPdy z) :
    ∃ U : ℕ → Set ℂ,
      ∃ eQ : ℕ → ℝ,
        ∃ eP : ℕ → ℝ,
          (∀ n, U n ⊆ interior K) ∧
          (∀ n, MeasurableSet (U n)) ∧
          (∀ n,
            ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
                (∫ z in U n, dQdx z) + eQ n) ∧
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
                -(∫ z in U n, dPdy z) + eP n)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dQdx z)
            Filter.atTop
            (nhds (∫ z in interior K, dQdx z)) ∧
          Filter.Tendsto
            (fun n ↦ ∫ z in U n, dPdy z)
            Filter.atTop
            (nhds (∫ z in interior K, dPdy z)) ∧
          Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
          Filter.Tendsto eP Filter.atTop (nhds 0) := by
  -- Package the exact half-formulas as the constant direct approximation family `U n = interior K`
  -- with identically zero scalar errors.
  refine ⟨fun _ ↦ interior K, fun _ ↦ 0, fun _ ↦ 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n z hz
    exact hz
  · intro n
    exact isOpen_interior.measurableSet
  · intro n
    constructor
    · simpa using hQ
    · simpa using hP
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a direct measurable approximation
package already contains enough information to recover the exact coordinate half-formulas on
`interior K`. -/
theorem coordinateHalfFormulas_onInterior_of_directSetApproximationPackage
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    (hApprox :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n, U n ⊆ interior K) ∧
            (∀ n, MeasurableSet (U n)) ∧
            (∀ n,
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
                  (∫ z in U n, dQdx z) + eQ n) ∧
                ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
                  -(∫ z in U n, dPdy z) + eP n)) ∧
            Filter.Tendsto
              (fun n ↦ ∫ z in U n, dQdx z)
              Filter.atTop
              (nhds (∫ z in interior K, dQdx z)) ∧
            Filter.Tendsto
              (fun n ↦ ∫ z in U n, dPdy z)
              Filter.atTop
              (nhds (∫ z in interior K, dPdy z)) ∧
            Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
            Filter.Tendsto eP Filter.atTop (nhds 0)) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        - ∫ z in interior K, dPdy z) := by
  rcases hApprox with ⟨U, eQ, eP, hU_subset, hU_meas, hStage, hSetQ, hSetP, heQ, heP⟩
  exact
    coordinateHalfFormulas_onInterior_of_setApproximation
      (Γ := Γ) (K := K) (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
      ⟨U, eQ, eP, hStage, hSetQ, hSetP, heQ, heP⟩
