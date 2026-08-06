import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Corollary_14_3_3

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Chapter 14 already exposes the canonical sphere-shift comparison
-- `reducedHomologySphereShift H q n` from `basedSphere n` to `pointHomology H (q - n)`.
-- This file records the source-facing degree-`n` and off-degree consequences on the canonical
-- owner `ModuleCat.of ℤ (basedReducedHomology H q (basedSphere n))`.

private theorem pointHomologyWithCoefficients_zero
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π) :
    Nonempty (ModuleCat.of ℤ (pointHomology H 0) ≅ ModuleCat.of ℤ π) := by
  simpa [pointHomology, pairHomologyGroup] using H.dimensionZero

private theorem pointHomologyWithCoefficients_isZero_of_ne
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) (hq : q ≠ 0) :
    IsZero (ModuleCat.of ℤ (pointHomology H q)) := by
  simpa [pointHomology, pairHomologyGroup] using H.dimensionHigher q hq

/-- Calculation 13.5.1 (1): the degree-`n` reduced homology object of `S^n` with coefficients in
`π`, on the canonical owner `ModuleCat.of ℤ (basedReducedHomology H (n : ℤ) (basedSphere n))`,
is isomorphic to the coefficient module `π`. -/
theorem sphereReducedHomologyWithCoefficients_self
    [CategoryWithCofibrations BasedSpace]
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π) (n : ℕ) :
    Nonempty
      (ModuleCat.of ℤ (basedReducedHomology H (n : ℤ) (basedSphere n)) ≅ ModuleCat.of ℤ π) := by
  rcases reducedHomologySphereShift H (n : ℤ) n with ⟨sphereShiftIso⟩
  rcases pointHomologyWithCoefficients_zero H with ⟨pointIso⟩
  refine ⟨sphereShiftIso ≪≫ eqToIso (by simp) ≪≫ pointIso⟩

/-- Calculation 13.5.1 (2): every reduced homology object of `S^n` with coefficients in `π`
away from degree `n` is zero. -/
theorem sphereReducedHomologyWithCoefficients_isZero_of_ne
    [CategoryWithCofibrations BasedSpace]
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π) (n : ℕ) (q : ℤ)
    (hq : q ≠ (n : ℤ)) :
    IsZero (ModuleCat.of ℤ (basedReducedHomology H q (basedSphere n))) := by
  rcases reducedHomologySphereShift H q n with ⟨sphereShiftIso⟩
  refine IsZero.of_iso (pointHomologyWithCoefficients_isZero_of_ne H (q - n) ?_) ?_
  · exact sub_ne_zero.mpr hq
  · exact sphereShiftIso
