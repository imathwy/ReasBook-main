/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06_part2

section Chap06
section Section06

/-- Helper for Theorem 6.8: for an odd continuous map `S² → ℝ²`, each coordinate
function has a zero. -/
lemma helperForTheorem_6_8_continuous_odd_euclideanTwo_coordinate_exists_zero
    (h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2)) (hcont : Continuous h)
    (hodd : ∀ x : UnitSphereTwo, h (-x) = -h x) (i : Fin 2) :
    ∃ x : UnitSphereTwo, h x i = 0 := by
  let hi : UnitSphereTwo → ℝ := fun x => EuclideanSpace.proj i (h x)
  have hconti : Continuous hi := by
    simpa [hi] using (EuclideanSpace.proj i).continuous.comp hcont
  have hoddi : ∀ x : UnitSphereTwo, hi (-x) = -hi x := by
    intro x
    dsimp [hi]
    simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj i v) (hodd x)
  rcases helperForTheorem_6_8_continuous_odd_real_exists_zero hi hconti hoddi with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [hi] using hx

/-- Helper for Theorem 6.8: in `ℝ²`, vanishing of both coordinate projections implies
the vector is zero. -/
lemma helperForTheorem_6_8_euclideanTwo_eq_zero_of_proj_zero
    {v : EuclideanSpace ℝ (Fin 2)}
    (h0 : EuclideanSpace.proj (0 : Fin 2) v = 0)
    (h1 : EuclideanSpace.proj (1 : Fin 2) v = 0) :
    v = 0 := by
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- Helper for Theorem 6.8: an odd-zero principle for continuous maps `S² → ℝ²`
implies antipodal equality for continuous maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2)) (hg : Continuous g) :
    ∃ x : UnitSphereTwo, g x = g (-x) := by
  let h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2) := fun x => g x - g (-x)
  have hhcont : Continuous h := by
    simpa [h] using helperForTheorem_6_8_continuous_sub_antipode g hg
  have hhodd : ∀ x : UnitSphereTwo, h (-x) = -h x := by
    simpa [h] using (helperForTheorem_6_8_odd_sub_antipode g)
  rcases hoddZero h hhcont hhodd with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact sub_eq_zero.mp hx

/-- Helper for Theorem 6.8: combining a `S² → ℝ²` odd-zero principle with a reduction
from antipodal equality to self-map fixed/anti-fixed alternatives yields the global
fixed/anti-fixed existence principle on `S²`. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_odd_zero_pipeline
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  have hborsukUlam :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)) := by
    intro g hg
    exact
      helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
        hoddZero g hg
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_borsuk_ulam_pipeline
      hborsukUlam hreduction

/-- Helper for Theorem 6.8: an odd-zero principle on `S² → ℝ²`, together with a
reduction from antipodal equality to self-map fixed/anti-fixed alternatives, yields
the local fixed/anti-fixed witness for any given continuous self-map of `S²`. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_odd_zero_pipeline
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_odd_zero_pipeline
      hoddZero hreduction f hcont

/-- Helper for Theorem 6.8: an odd-zero-plus-reduction pipeline gives the local
fixed-point/antipode-equality alternative for continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_continuous_of_odd_zero_pipeline
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    (∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, f x = helperForTheorem_6_8_antipode x) := by
  have hfixedOrAntifixed : ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 :=
    helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_odd_zero_pipeline
      hoddZero hreduction f hcont
  exact helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_exists_fixed_or_antifixed hfixedOrAntifixed


end Section06
end Chap06
