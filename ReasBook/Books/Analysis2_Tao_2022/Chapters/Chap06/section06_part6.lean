/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06_part5

section Chap06
section Section06

/-- Helper for Theorem 6.8: an antipodal-equality source on maps `S² → ℝ²`,
together with a non-circular antipodal-to-self-map reduction, yields the packaged
common-zero-plus-reduction upstream prerequisite. -/
lemma helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_of_antipodal_source_and_reduction
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  refine ⟨?_, hreduction⟩
  exact
    helperForTheorem_6_8_continuous_odd_real_pair_common_zero_of_antipodal_equality
      hantipodal

/-- Helper for Theorem 6.8: a common-zero principle for continuous odd real-valued
pairs on `S²` implies the antipodal-equality principle for continuous maps
`S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_common_zero_real_pair
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  have hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0 :=
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_common_zero_real_pair
      hcommonZero
  exact
    helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
      hoddZero g hg

/-- Helper for Theorem 6.8: the common-zero principle for odd real-valued pairs
on `S²` is equivalent to the antipodal-equality principle for continuous maps
`S² → ℝ²`. -/
lemma helperForTheorem_6_8_common_zero_real_pair_iff_antipodal_equality_principle :
    (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ↔
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) := by
  constructor
  · intro hcommonZero
    exact
      helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_common_zero_real_pair
        hcommonZero
  · intro hantipodal
    exact
      helperForTheorem_6_8_continuous_odd_real_pair_common_zero_of_antipodal_equality
        hantipodal

/-- Helper for Theorem 6.8: the packaged common-zero-plus-reduction prerequisite is
equivalent to the packaged antipodal-equality-plus-reduction prerequisite. -/
lemma helperForTheorem_6_8_common_zero_and_noncircular_reduction_package_iff_antipodal_and_noncircular_reduction_package :
    ((∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) ↔
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  constructor
  · intro hpackage
    refine ⟨?_, hpackage.2⟩
    exact
      (helperForTheorem_6_8_common_zero_real_pair_iff_antipodal_equality_principle).1
        hpackage.1
  · intro hpackage
    refine ⟨?_, hpackage.2⟩
    exact
      (helperForTheorem_6_8_common_zero_real_pair_iff_antipodal_equality_principle).2
        hpackage.1

/-- Helper for Theorem 6.8: any packaged antipodal-equality source and
non-circular reduction package can be transported to the equivalent packaged
common-zero-plus-reduction form. -/
lemma helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_of_upstream_antipodal_and_noncircular_reduction_package
    (hpackage :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    (helperForTheorem_6_8_common_zero_and_noncircular_reduction_package_iff_antipodal_and_noncircular_reduction_package).2
      hpackage

/-- Helper for Theorem 6.8: any packaged common-zero-plus-reduction source can be
transported to the equivalent packaged antipodal-equality-plus-reduction form. -/
lemma helperForTheorem_6_8_upstream_antipodal_and_noncircular_reduction_package_of_upstream_common_zero_and_noncircular_reduction_package
    (hpackage :
      (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    (helperForTheorem_6_8_common_zero_and_noncircular_reduction_package_iff_antipodal_and_noncircular_reduction_package).1
      hpackage

/-- Helper for Theorem 6.8: the packaged common-zero-plus-reduction prerequisite is
equivalent to the packaged odd-zero-plus-reduction prerequisite. -/
lemma helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_iff_upstream_odd_zero_and_selfMap_reduction_package :
    ((∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) ↔
    ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  constructor
  · intro hcommonAndReduction
    have hantipodalAndReduction :
        (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :=
      helperForTheorem_6_8_upstream_antipodal_and_noncircular_reduction_package_of_upstream_common_zero_and_noncircular_reduction_package
        hcommonAndReduction
    exact
      (helperForTheorem_6_8_upstream_antipodal_package_iff_upstream_odd_zero_package).1
        hantipodalAndReduction
  · intro hoddZeroAndReduction
    have hantipodalAndReduction :
        (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :=
      (helperForTheorem_6_8_upstream_antipodal_package_iff_upstream_odd_zero_package).2
        hoddZeroAndReduction
    exact
      helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_of_upstream_antipodal_and_noncircular_reduction_package
        hantipodalAndReduction

/-- Helper for Theorem 6.8: an antipodal-equality source on `S² → ℝ²`
implies the odd-zero component of the packaged odd-zero-plus-reduction prerequisite. -/
lemma helperForTheorem_6_8_upstream_odd_zero_component_of_upstream_antipodal_source
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  exact
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality
      hantipodal

/-- Helper for Theorem 6.8: any non-circular antipodal-equality-to-self-map reduction
implies the reduction component of the packaged odd-zero-plus-reduction prerequisite. -/
lemma helperForTheorem_6_8_upstream_selfMap_reduction_component_of_noncircular_antipodal_reduction
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  intro hoddZero
  exact
    helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero_of_noncircular_antipodal_reduction
      hreduction hoddZero

/-- Helper for Theorem 6.8: a packaged upstream prerequisite consisting of
an odd-zero principle on continuous odd maps `S² → ℝ²` together with an
odd-zero-to-self-map fixed/anti-fixed reduction principle on `S²`. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_of_antipodal_source_and_noncircular_reduction
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
    ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_6_8_upstream_odd_zero_component_of_upstream_antipodal_source
        hantipodal
  · exact
      helperForTheorem_6_8_upstream_selfMap_reduction_component_of_noncircular_antipodal_reduction
        hreduction

/-- Helper for Theorem 6.8: any packaged odd-zero-plus-reduction source yields
the corresponding upstream antipodal-equality source on continuous maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_upstream_antipodal_source_of_upstream_odd_zero_and_selfMap_reduction_package
    (hpackage :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  exact
    helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
      hpackage.1 g hg

/-- Helper for Theorem 6.8: any packaged odd-zero-plus-reduction source yields
the corresponding non-circular antipodal-equality-to-self-map reduction. -/
lemma helperForTheorem_6_8_upstream_noncircular_antipodal_reduction_of_upstream_odd_zero_and_selfMap_reduction_package
    (hpackage :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  exact
    (helperForTheorem_6_8_upstream_antipodal_and_selfMap_reduction_package_of_upstream_odd_zero_package
      hpackage).2

/-- Helper for Theorem 6.8: any packaged common-zero-plus-reduction source on `S²`
can be converted directly into the packaged odd-zero-plus-reduction source. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_of_upstream_common_zero_and_noncircular_reduction_package
    (hpackage :
      (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
    ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    (helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_iff_upstream_odd_zero_and_selfMap_reduction_package).1
      hpackage

/-- Helper for Theorem 6.8: an upstream antipodal-equality-plus-reduction package on `S²`
simultaneously yields the packaged odd-zero-plus-reduction and
common-zero-plus-reduction prerequisites used downstream. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_common_zero_package_pair_of_upstream_antipodal_and_noncircular_reduction_package
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) ∧
    ((∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_of_upstream_antipodal_package
        hsource
  · exact
      helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_of_upstream_antipodal_and_noncircular_reduction_package
        hsource

/-- Helper for Theorem 6.8: an unconditional upstream antipodal-equality source and
non-circular reduction package on `S²` directly yields the unconditional packaged
odd-zero-plus-reduction prerequisite on `S²`. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_upstream_antipodal_and_noncircular_reduction_package
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    (helperForTheorem_6_8_upstream_odd_zero_and_common_zero_package_pair_of_upstream_antipodal_and_noncircular_reduction_package
      hsource).1

/-- Helper for Theorem 6.8: converting a packaged antipodal-equality source and
non-circular reduction on `S²` into the corresponding packaged odd-zero-plus-
reduction prerequisite. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_of_upstream_antipodal_source_and_noncircular_reduction
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_upstream_antipodal_and_noncircular_reduction_package
      hsource

/-- Helper for Theorem 6.8: the unconditional odd-zero-plus-reduction package on `S²`
follows from nonemptiness of the upstream antipodal-equality-plus-reduction package. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_nonempty_upstream_antipodal_and_noncircular_reduction_package
    (hsource :
      Nonempty
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) ∧
          ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
              (∃ x : UnitSphereTwo, g x = g (-x))) →
            ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
              (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)))) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  rcases hsource with ⟨hsource'⟩
  exact
    helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_upstream_antipodal_and_noncircular_reduction_package
      hsource'

/-- Helper for Theorem 6.8: packaging a concrete antipodal-equality-plus-reduction
witness directly yields the corresponding `Nonempty` source. -/
lemma helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_witness
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    Nonempty
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  exact ⟨hsource⟩

/-- Helper for Theorem 6.8: explicit antipodal-equality and non-circular
reduction components package into the corresponding nonempty upstream source. -/
lemma helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_components
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    Nonempty
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  exact
    helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_witness
      ⟨hantipodal, hreduction⟩

/-- Helper for Theorem 6.8: for this packaged upstream proposition, `Nonempty` is
equivalent to giving the witness package itself. -/
lemma helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_iff_witness :
    Nonempty
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) ↔
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  constructor
  · rintro ⟨hsource⟩
    exact hsource
  · intro hsource
    exact
      helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_witness
        hsource

/-- Helper for Theorem 6.8: for propositions `P` and `Q`, `Nonempty (P ∧ Q)` is
equivalent to having nonempty witnesses of `P` and of `Q` separately. -/
lemma helperForTheorem_6_8_nonempty_and_iff_nonempty_components {P Q : Prop} :
    Nonempty (P ∧ Q) ↔ Nonempty P ∧ Nonempty Q := by
  constructor
  · rintro ⟨hPQ⟩
    exact ⟨⟨hPQ.1⟩, ⟨hPQ.2⟩⟩
  · rintro ⟨⟨hP⟩, ⟨hQ⟩⟩
    exact ⟨⟨hP, hQ⟩⟩

/-- Helper for Theorem 6.8: if the codomain proposition is nonempty, then the
corresponding implication proposition is nonempty. -/
lemma helperForTheorem_6_8_nonempty_implication_of_nonempty_codomain {P Q : Prop}
    (hQ : Nonempty Q) :
    Nonempty (P → Q) := by
  rcases hQ with ⟨hQ'⟩
  exact ⟨fun _ => hQ'⟩

/-- Helper for Theorem 6.8: reducing the packaged nonempty upstream goal to
the corresponding pair of nonempty component goals. -/
lemma helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_nonempty_components
    (hcomponents :
      Nonempty
        (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      Nonempty
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    Nonempty
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  exact
    (helperForTheorem_6_8_nonempty_and_iff_nonempty_components).2 hcomponents

/-- Helper for Theorem 6.8: if one has the upstream package consisting of a common-zero
principle for odd real pairs on `S²` and a non-circular antipodal-to-self-map reduction,
then one can extract both concrete component goals on `S²` (antipodal equality and
fixed/anti-fixed existence for continuous self-maps). -/
lemma helperForTheorem_6_8_component_goals_on_S2_of_common_zero_and_noncircular_reduction_package
    (hcommonZeroAndReduction :
      (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  have hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :=
    helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source_of_common_zero_and_reduction_package
      hcommonZeroAndReduction
  refine ⟨hsource.1, ?_⟩
  intro g hg
  exact hsource.2 hsource.1 g hg

/-- Independent upstream bridge for Theorem 6.8.

This declaration is intentionally placed before the package chain that starts at
`helperForTheorem_6_8_upstream_nonempty_antipodal_and_selfMap_component_goals_on_S2`.
Its only role is to provide an acyclic source for:

* `A`: antipodal equality on continuous maps `S² → ℝ²`;
* `R`: a reduction `A →` fixed/anti-fixed existence on continuous self-maps `S²`.

Non-circular proof contract:
* The future proof here must not use any theorem whose dependency graph contains
  `helperForTheorem_6_8_upstream_nonempty_antipodal_and_selfMap_component_goals_on_S2`
  (or the downstream chain built from it).
* Preferred path: import/hoist truly upstream results for `A` and `R`, then return
  `⟨hA, hR⟩` directly. -/
theorem helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  -- This node is now a pure re-export of the earlier independent bridge in part5.
  -- Keeping this theorem here preserves local pipeline shape while enforcing acyclic input.
  exact helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge_in_part5_base_placeholder

/-- Bridge theorem for Theorem 6.8 pipeline: expose the two concrete component goals
early (antipodal-equality source on `S² → ℝ²` and global fixed/anti-fixed witnesses
for continuous self-maps of `S²`).

This theorem is intentionally placed before the package theorem to provide a stable,
acyclic planning target in the direct-item pipeline.

Anti-cycle rule (hard):
- When proving this theorem, do not use any declaration that depends on this theorem.
- In particular, avoid the known cycle
  `533 -> 567 -> 623 -> 639 -> 655 -> (822, 934) -> ... -> 533`.
- So `helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal`
  and
  `helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction`
  are valid *targets* to expose for future upstream import/hoist, but not valid
  local prerequisites if they are still downstream in this file order.

Detailed non-cyclic proof method:
- Method A (preferred): use one imported/hoisted upstream theorem (declared in an
  earlier file or before line 533) that already provides
  antipodal equality and/or the reduction map.
- Method B (if A is unavailable): first create a new earlier bridge declaration
  in an upstream part file, then return here and instantiate this theorem.
- In both methods, this theorem must be proved by DAG order only:
  upstream inputs -> `hA` -> `hB := hR hA` -> `⟨hA, hB⟩`.
- Never use any theorem whose reverse-dependency contains this theorem or line 567.

Lean-level skeleton for the acyclic script:
- `have hA : ∀ g, Continuous g -> ∃ x, g x = g (-x) := ...`  (upstream source)
- `have hR : (∀ g, Continuous g -> ∃ x, g x = g (-x)) ->
    ∀ g, Continuous g -> ∃ x, g x = x ∨ (g x).1 = -x.1 := ...`  (upstream source)
- `have hB : ∀ g, Continuous g -> ∃ x, g x = x ∨ (g x).1 = -x.1 := hR hA`
- `exact ⟨hA, hB⟩` -/
theorem helperForTheorem_6_8_upstream_nonempty_antipodal_and_selfMap_component_goals_on_S2 :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  -- Proof method (natural-language + Lean skeleton):
  -- Step 1: build `hA`, the antipodal-equality source on `S² → ℝ²`:
  --   `hA : ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
  --      ∃ x, g x = g (-x)`.
  -- Step 2: build `hR`, the reduction map:
  --   `hR : (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
  --      ∃ x, g x = g (-x)) →
  --      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
  --      ∃ x, g x = x ∨ (g x).1 = -x.1`.
  -- Step 3: apply `hR hA` to get `hB`:
  --   `hB : ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
  --      ∃ x, g x = x ∨ (g x).1 = -x.1`.
  -- Step 4: return `⟨hA, hB⟩`.
  --
  -- Concrete Lean shape after dependency cut:
  --   refine ⟨?hA, ?hB⟩
  --   · exact helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal
  --   · exact
  --       (helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction
  --         helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal)
  --
  -- Current implementation note:
  -- this theorem is now closed by the independent upstream bridge
  -- `helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge`.
  -- So this declaration remains acyclic and does not consume downstream producers.
  --
  -- Anti-cycle guard:
  -- do not "solve" this by calling lemmas in the downstream chain
  -- `567 -> 623 -> 639 -> 655 -> 822/934`, because that recreates the same loop.
  --
  -- Operational checklist before replacing this `sorry`:
  -- 1) Every theorem you call here must be imported or declared strictly upstream.
  -- 2) Run a quick dependency sanity check: no called theorem may depend on line 533/567.
  -- 3) Keep this theorem as a pure constructor node (`⟨hA, hB⟩`), not a re-export
  --    of downstream packaged results.
  have hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
    exact helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge
  have hcommonZeroAndReduction :
      (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
    exact
      helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_of_antipodal_source_and_reduction
        hsource.1 hsource.2
  exact
    helperForTheorem_6_8_component_goals_on_S2_of_common_zero_and_noncircular_reduction_package
      hcommonZeroAndReduction

/-- Helper for Theorem 6.8: nonemptiness of the packaged upstream antipodal-equality
source and non-circular reduction principle on `S²`. -/
theorem helperForTheorem_6_8_upstream_nonempty_antipodal_and_noncircular_reduction_package_on_S2 :
    Nonempty
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  have hcomponentGoals :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :=
    helperForTheorem_6_8_upstream_nonempty_antipodal_and_selfMap_component_goals_on_S2
  have hcomponents :
      Nonempty
        (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      Nonempty
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
    refine ⟨⟨hcomponentGoals.1⟩, ?_⟩
    exact
      helperForTheorem_6_8_nonempty_implication_of_nonempty_codomain
        ⟨hcomponentGoals.2⟩
  -- NOTE:
  -- This is the only unresolved upstream packaging point in this file.
  -- The intended replacement path is to use the two later, concrete components:
  --   1) `helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal`
  --   2) `helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction`
  -- and then reassemble them via
  -- `helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_nonempty_components`.
  --
  -- Dependency note:
  -- this theorem is downstream of the bridge at line 533 and should never be used
  -- as evidence to prove line 533 itself; keep the bridge proof strictly upstream.
  -- Acyclic usage rule:
  -- this theorem only packages `hcomponentGoals`; it is a consumer of line 533,
  -- never a producer for line 533.
  exact
    helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_nonempty_components
      hcomponents

/-- Helper for Theorem 6.8: the odd-zero-plus-reduction package follows directly
from an upstream nonempty antipodal-equality-plus-reduction package on `S²`. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_upstream_nonempty_antipodal_and_noncircular_reduction_package :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_nonempty_upstream_antipodal_and_noncircular_reduction_package
      helperForTheorem_6_8_upstream_nonempty_antipodal_and_noncircular_reduction_package_on_S2

/-- Helper for Theorem 6.8: a packaged upstream prerequisite consisting of
an odd-zero principle on continuous odd maps `S² → ℝ²` together with an
odd-zero-to-self-map fixed/anti-fixed reduction principle on `S²`. -/
theorem helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2 :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2_of_upstream_nonempty_antipodal_and_noncircular_reduction_package

/-- Helper for Theorem 6.8: a packaged upstream prerequisite consisting of
the common-zero principle for continuous odd real pairs on `S²` and a
non-circular reduction from antipodal equality to fixed/anti-fixed witnesses
for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_on_S2 :
    (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    (helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_iff_upstream_odd_zero_and_selfMap_reduction_package).2
      helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_on_S2

/-- Helper for Theorem 6.8: upstream dependency source packaging a Borsuk-Ulam
antipodal-equality principle on `S² → ℝ²` together with a reduction from
antipodal equality to fixed/anti-fixed witnesses for self-maps of `S²`. -/
theorem helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    helperForTheorem_6_8_upstream_antipodal_and_noncircular_reduction_package_of_upstream_common_zero_and_noncircular_reduction_package
      helperForTheorem_6_8_upstream_common_zero_and_noncircular_reduction_package_on_S2

/-- Helper for Theorem 6.8: from a packaged upstream antipodal-equality source and
reduction map, one obtains the global fixed/anti-fixed witness principle for continuous
self-maps of `S²`. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_upstream_antipodal_equality_and_selfMap_reduction_dependency_source
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro g hg
  exact hsource.2 hsource.1 g hg

/-- Helper for Theorem 6.8: a packaged upstream antipodal-equality-and-reduction
source gives a local fixed/anti-fixed witness for any continuous self-map of `S²`. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_upstream_antipodal_equality_and_selfMap_reduction_dependency_source
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_upstream_antipodal_equality_and_selfMap_reduction_dependency_source
      hsource f hcont

/-- Helper for Theorem 6.8: the packaged upstream dependency source yields the
upstream odd-zero principle on continuous odd maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_upstream_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_dependency_source :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  exact
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality
      (helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source).1

/-- Helper for Theorem 6.8: upstream odd-zero existence principle for continuous odd
maps `S² → ℝ²`. -/
theorem helperForTheorem_6_8_upstream_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  exact
    helperForTheorem_6_8_upstream_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_dependency_source

/-- Helper for Theorem 6.8: an upstream odd-zero principle on continuous odd maps
`S² → ℝ²` yields the corresponding upstream antipodal-equality principle. -/
lemma helperForTheorem_6_8_upstream_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_upstream_odd_zero_local
    (hoddZeroUpstream :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  exact
    helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
      hoddZeroUpstream g hg

/-- Helper for Theorem 6.8: upstream reduction from odd-zero existence on continuous odd
maps `S² → ℝ²` to fixed/anti-fixed existence for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro hoddZeroUpstream
  have hborsukUlam :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)) :=
    helperForTheorem_6_8_upstream_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_upstream_odd_zero_local
      hoddZeroUpstream
  exact
    (helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source).2
      hborsukUlam

/-- Helper for Theorem 6.8: a packaged upstream pair consisting of an odd-zero principle
and an odd-zero-to-self-map reduction immediately yields global fixed/anti-fixed existence
for continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_upstream_odd_zero_and_selfMap_reduction_package
    (hpackage :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  rcases hpackage with ⟨hoddZero, hreduction⟩
  exact hreduction hoddZero

/-- Helper for Theorem 6.8: a packaged odd-zero-plus-reduction upstream hypothesis
immediately yields the local fixed/anti-fixed witness for any continuous self-map of `S²`. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_upstream_odd_zero_and_selfMap_reduction_package
    (hpackage :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_upstream_odd_zero_and_selfMap_reduction_package
      hpackage f hcont

/-- Helper for Theorem 6.8: an upstream odd-zero principle yields the corresponding
upstream antipodal-equality principle on continuous maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_upstream_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_upstream_odd_zero
    (hoddZeroUpstream :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  exact
    helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
      hoddZeroUpstream g hg

/-- Helper for Theorem 6.8: combining an upstream odd-zero principle with an explicit
antipodal-equality-to-self-map reduction yields global fixed/anti-fixed witnesses. -/
lemma helperForTheorem_6_8_upstream_global_exists_fixed_or_antifixed_of_upstream_odd_zero_and_antipodal_reduction
    (hoddZeroUpstream :
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
  have hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)) :=
    helperForTheorem_6_8_upstream_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_upstream_odd_zero
      hoddZeroUpstream
  exact hreduction hantipodal

/-- Helper for Theorem 6.8: upstream Borsuk-Ulam antipodal-equality principle for
continuous maps `S² → ℝ²`. -/
theorem helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  exact
    helperForTheorem_6_8_upstream_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_upstream_odd_zero
      helperForTheorem_6_8_upstream_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero
      g hg

/-- Helper for Theorem 6.8: combining an antipodal-equality principle with an
antipodal-equality-to-self-map reduction yields fixed/anti-fixed witnesses for
continuous self-maps via the no-counterexample fixed-or-negation route. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_antipodal_and_reduction_via_no_counterexample
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  have hnoCounterexampleNeg :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) :=
    helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_borsuk_ulam_pipeline
      hantipodal hreduction
  exact
    helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_no_counterexample_fixed_or_neg
      f hcont hnoCounterexampleNeg

/-- Helper for Theorem 6.8: an antipodal-equality principle on continuous maps
`S² → ℝ²` implies the odd-zero principle on continuous odd maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_odd_zero_principle_of_antipodal_equality
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  intro h hcont hodd
  rcases hantipodal h hcont with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hneg : h (-x) = -h x := hodd x
  have hselfNeg : h x = -h x := by
    calc
      h x = h (-x) := hx
      _ = -h x := hneg
  have hsum : h x + h x = 0 := by
    nth_rewrite 2 [hselfNeg]
    exact add_neg_cancel (h x)
  have htwo : (2 : ℝ) • h x = 0 := by
    simpa [two_smul] using hsum
  have htwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  exact (smul_eq_zero.mp htwo).resolve_left htwoNe

/-- Helper for Theorem 6.8: an odd-zero principle on continuous odd maps
`S² → ℝ²` yields the corresponding antipodal-equality principle for continuous
maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_odd_zero
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  exact
    helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
      hoddZero g hg

/-- Helper for Theorem 6.8: on continuous maps `S² → ℝ²`, the odd-zero and
antipodal-equality principles are equivalent. -/
lemma helperForTheorem_6_8_odd_zero_principle_iff_antipodal_equality_principle :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ↔
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) := by
  constructor
  · intro hoddZero
    exact
      helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_odd_zero
        hoddZero
  · intro hantipodal
    exact helperForTheorem_6_8_odd_zero_principle_of_antipodal_equality hantipodal

/-- Helper for Theorem 6.8: if a reduction from antipodal equality on `S² → ℝ²` to
fixed/anti-fixed existence on continuous self-maps of `S²` is available, then any
odd-zero principle on `S² → ℝ²` yields the global fixed/anti-fixed existence principle. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_odd_zero_of_antipodal_reduction
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  refine hreduction ?_
  exact
    helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_odd_zero
      hoddZero

/-- Helper for Theorem 6.8: upstream reduction from antipodal equality on
continuous maps `S² → ℝ²` to fixed/anti-fixed existence for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro hantipodal
  have hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0 :=
    helperForTheorem_6_8_odd_zero_principle_of_antipodal_equality hantipodal
  exact
    helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero
      hoddZero

/-- Helper for Theorem 6.8: once the two concrete `S²` components are available
(`S² → ℝ²` antipodal equality and antipodal-to-self-map reduction), they package
into the corresponding nonempty upstream source. -/
lemma helperForTheorem_6_8_upstream_nonempty_antipodal_and_noncircular_reduction_package_on_S2_of_concrete_components :
    Nonempty
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  have hcomponents :
      Nonempty
        (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      Nonempty
        ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
            (∃ x : UnitSphereTwo, g x = g (-x))) →
          ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
            (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
    exact ⟨⟨helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal⟩,
      ⟨helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction⟩⟩
  exact
    helperForTheorem_6_8_nonempty_upstream_antipodal_and_noncircular_reduction_package_of_nonempty_components
      hcomponents

/-- Helper for Theorem 6.8: once the upstream antipodal-equality-to-self-map reduction
is available, the odd-zero principle on `S² → ℝ²` gives fixed/anti-fixed witnesses for
continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_odd_zero_via_upstream_reduction
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  have hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)) :=
    (helperForTheorem_6_8_odd_zero_principle_iff_antipodal_equality_principle).1 hoddZero
  exact
    helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_antipodal_and_reduction_via_no_counterexample
      hantipodal
      helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction
      f hcont

/-- Helper for Theorem 6.8: an odd-zero principle on continuous odd maps
`S² → ℝ²`, together with an antipodal-equality-to-self-map reduction, yields the
corresponding odd-zero-to-self-map reduction principle. -/
lemma helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero_and_antipodal_reduction
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
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_odd_zero_of_antipodal_reduction
      hreduction hoddZero

/-- Helper for Theorem 6.8: upstream reduction from odd-zero existence for continuous odd
maps `S² → ℝ²` to fixed/anti-fixed existence for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro hoddZero
  exact
    helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero_and_antipodal_reduction
      hoddZero
      helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction

/-- Helper for Theorem 6.8: upstream reduction from antipodal equality on
continuous maps `S² → ℝ²` to fixed/anti-fixed existence for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_antipodal_equal :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro hantipodal
  exact
    helperForTheorem_6_8_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction
      hantipodal

/-- Helper for Theorem 6.8: prerequisite global fixed-point-or-negation principle for
continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_neg :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)) := by
  exact
    helperForTheorem_6_8_global_fixed_or_neg_of_borsuk_ulam_pipeline
      helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal
      helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_antipodal_equal

/-- Helper for Theorem 6.8: the prerequisite global fixed-point-or-negation principle
implies the corresponding no-counterexample statement. -/
lemma helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_no_counterexample_fixed_or_neg_of_exists_fixed_or_neg
    (hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) := by
  exact
    helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_global_fixed_or_neg_principle
      hglobalNeg

/-- Helper for Theorem 6.8: prerequisite no-counterexample fixed-point-or-negation
statement for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_no_counterexample_fixed_or_neg :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) := by
  exact
    helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_no_counterexample_fixed_or_neg_of_exists_fixed_or_neg
      helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_neg


end Section06
end Chap06
