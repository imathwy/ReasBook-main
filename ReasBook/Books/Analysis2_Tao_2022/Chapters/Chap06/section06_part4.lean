/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06_part3

section Chap06
section Section06

/-- Helper for Theorem 6.8: a global fixed-point-or-antipode-equality principle on
continuous self-maps of `S²` implies the global fixed/anti-fixed existence principle. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_fixed_eq_antipode_principle
    (hprinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro g hg
  exact helperForTheorem_6_8_exists_of_fixed_or_fixed_eq_antipode (hprinciple g hg)

/-- Helper for Theorem 6.8: existence of a continuous counterexample to the
fixed/anti-fixed witness is equivalent to existence of a continuous counterexample to
the fixed-point-or-antipode-equality disjunction. -/
lemma helperForTheorem_6_8_exists_counterexample_fixed_or_antifixed_iff_exists_counterexample_fixed_or_fixed_eq_antipode :
    (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) ↔
      (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) := by
  constructor
  · rintro ⟨g, hg, hnot⟩
    refine ⟨g, hg, ?_⟩
    intro hdisj
    exact hnot (helperForTheorem_6_8_exists_of_fixed_or_fixed_eq_antipode hdisj)
  · rintro ⟨g, hg, hnot⟩
    refine ⟨g, hg, ?_⟩
    intro hexists
    exact hnot
      ((helperForTheorem_6_8_exists_fixed_or_antifixed_iff_fixed_or_fixed_eq_antipode
        (f := g)).1 hexists)

/-- Helper for Theorem 6.8: a global fixed/anti-fixed existence principle is equivalent
to nonexistence of a continuous counterexample to that principle. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample :
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) ↔
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  constructor
  · intro hglobal hcounterexample
    rcases hcounterexample with ⟨g, hg, hnot⟩
    exact hnot (hglobal g hg)
  · intro hnoCounterexample g hg
    by_contra hnot
    exact hnoCounterexample ⟨g, hg, hnot⟩

/-- Helper for Theorem 6.8: a global fixed-point-or-antipode-equality principle is
equivalent to nonexistence of a continuous counterexample to that principle. -/
lemma helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_iff_no_counterexample :
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) ↔
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) := by
  constructor
  · intro hglobal hcounterexample
    rcases hcounterexample with ⟨g, hg, hnot⟩
    exact hnot (hglobal g hg)
  · intro hnoCounterexample g hg
    by_contra hnot
    exact hnoCounterexample ⟨g, hg, hnot⟩

/-- Upstream helper for Theorem 6.8 in part4:
an antipodal-equality principle on `S² → ℝ²` implies the odd-zero principle on
continuous odd maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality_in_part4
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

/-- Upstream helper for Theorem 6.8 in part4:
the antipodal-equality principle and the odd-zero principle on `S² → ℝ²` are equivalent. -/
lemma helperForTheorem_6_8_odd_zero_principle_iff_antipodal_equality_principle_in_part4 :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ↔
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) := by
  constructor
  · intro hoddZero g hg
    exact
      helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
        hoddZero g hg
  · intro hantipodal
    exact
      helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality_in_part4
        hantipodal

/-- Upstream helper for Theorem 6.8 in part4:
an antipodal-equality principle on `S² → ℝ²` yields a common zero for every pair
of continuous odd real-valued maps on `S²`. -/
lemma helperForTheorem_6_8_continuous_odd_real_pair_common_zero_of_antipodal_equality_in_part4
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) :
    ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0 := by
  intro u v huCont hvCont huOdd hvOdd
  let hpair : UnitSphereTwo → EuclideanSpace ℝ (Fin 2) :=
    fun x => WithLp.toLp (2 : ENNReal) ![u x, v x]
  have hpairCont : Continuous hpair := by
    refine (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)).comp ?_
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [hpair] using huCont
    · simpa [hpair] using hvCont
  have hpairOdd : ∀ x : UnitSphereTwo, hpair (-x) = -hpair x := by
    intro x
    ext i
    fin_cases i
    · simp [hpair, huOdd x]
    · simp [hpair, hvOdd x]
  have hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0 :=
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality_in_part4
      hantipodal
  rcases hoddZero hpair hpairCont hpairOdd with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hx0 : EuclideanSpace.proj (0 : Fin 2) (hpair x) = 0 := by
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (0 : Fin 2) y) hx
  have hx1 : EuclideanSpace.proj (1 : Fin 2) (hpair x) = 0 := by
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (1 : Fin 2) y) hx
  constructor
  · simpa [hpair] using hx0
  · simpa [hpair] using hx1

/-- Upstream helper for Theorem 6.8 in part4:
a common-zero principle for continuous odd real-valued pairs on `S²` implies the
odd-zero principle on continuous odd maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_common_zero_real_pair_in_part4
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  intro h hcont hodd
  let u : UnitSphereTwo → ℝ := fun x => EuclideanSpace.proj (0 : Fin 2) (h x)
  let v : UnitSphereTwo → ℝ := fun x => EuclideanSpace.proj (1 : Fin 2) (h x)
  have huCont : Continuous u := by
    simpa [u] using (EuclideanSpace.proj (0 : Fin 2)).continuous.comp hcont
  have hvCont : Continuous v := by
    simpa [v] using (EuclideanSpace.proj (1 : Fin 2)).continuous.comp hcont
  have huOdd : ∀ x : UnitSphereTwo, u (-x) = -u x := by
    intro x
    dsimp [u]
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (0 : Fin 2) y) (hodd x)
  have hvOdd : ∀ x : UnitSphereTwo, v (-x) = -v x := by
    intro x
    dsimp [v]
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (1 : Fin 2) y) (hodd x)
  rcases hcommonZero u v huCont hvCont huOdd hvOdd with ⟨x, hux, hvx⟩
  refine ⟨x, ?_⟩
  refine helperForTheorem_6_8_euclideanTwo_eq_zero_of_proj_zero ?_ ?_
  · simpa [u] using hux
  · simpa [v] using hvx

/-- Upstream helper for Theorem 6.8 in part4:
a common-zero principle for continuous odd real-valued pairs on `S²` implies the
antipodal-equality principle on continuous maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_common_zero_real_pair_in_part4
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
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_common_zero_real_pair_in_part4
      hcommonZero
  exact
    helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
      hoddZero g hg

/-- Upstream helper for Theorem 6.8 in part4:
on maps `S² → ℝ²`, the odd-real-pair common-zero principle is equivalent to the
antipodal-equality principle. -/
lemma helperForTheorem_6_8_common_zero_real_pair_iff_antipodal_equality_principle_in_part4 :
    (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ↔
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) := by
  constructor
  · intro hcommonZero
    exact
      helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_common_zero_real_pair_in_part4
        hcommonZero
  · intro hantipodal
    exact
      helperForTheorem_6_8_continuous_odd_real_pair_common_zero_of_antipodal_equality_in_part4
        hantipodal

/-- On `S²`, every point has ambient Euclidean norm `1`. -/
lemma helperForTheorem_6_8_norm_eq_one_unitSphereTwo_in_part4
    (x : UnitSphereTwo) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  have hx : dist (x : EuclideanSpace ℝ (Fin 3)) 0 = 1 := by
    simpa [Metric.mem_sphere] using x.property
  simpa [dist_eq_norm] using hx

/-- If two unit vectors in `ℝ^3` are linearly dependent, they are equal or antipodal. -/
lemma helperForTheorem_6_8_eq_or_eq_neg_of_not_linearIndependent_unitSphereTwo_in_part4
    (x y : UnitSphereTwo)
    (hdep : ¬ LinearIndependent ℝ ![(x : Fin 3 → ℝ), (y : Fin 3 → ℝ)]) :
    y = x ∨ y = -x := by
  have hx0E : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro hx0
    have hnorm0 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 0 := by simpa [hx0]
    have hnorm1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
      helperForTheorem_6_8_norm_eq_one_unitSphereTwo_in_part4 x
    linarith
  have hx0 : (x : Fin 3 → ℝ) ≠ 0 := by
    intro hx0
    apply hx0E
    ext i
    exact congrArg (fun f : Fin 3 → ℝ => f i) hx0
  have hexistsScalar : ∃ a : ℝ, a • (x : Fin 3 → ℝ) = (y : Fin 3 → ℝ) := by
    by_contra hno
    apply hdep
    refine (LinearIndependent.pair_iff' hx0).2 ?_
    intro a ha
    exact hno ⟨a, ha⟩
  rcases hexistsScalar with ⟨a, ha⟩
  have haE : a • (x : EuclideanSpace ℝ (Fin 3)) = (y : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    exact congrArg (fun f : Fin 3 → ℝ => f i) ha
  have habs : |a| = (1 : ℝ) := by
    calc
      |a| = |a| * ‖(x : EuclideanSpace ℝ (Fin 3))‖ := by
        simp [helperForTheorem_6_8_norm_eq_one_unitSphereTwo_in_part4 x]
      _ = ‖a • (x : EuclideanSpace ℝ (Fin 3))‖ := by
        simpa [norm_smul]
      _ = ‖(y : EuclideanSpace ℝ (Fin 3))‖ := by
        simpa [haE]
      _ = 1 := by
        simp [helperForTheorem_6_8_norm_eq_one_unitSphereTwo_in_part4 y]
  have haEq : a = 1 ∨ a = -1 := by
    exact (abs_eq (a := a) (b := (1 : ℝ)) (by norm_num)).1 habs
  rcases haEq with ha1 | haNeg1
  · left
    apply Subtype.ext
    have hxyE : (x : EuclideanSpace ℝ (Fin 3)) = (y : EuclideanSpace ℝ (Fin 3)) := by
      simpa [ha1] using haE
    simpa using hxyE.symm
  · right
    apply Subtype.ext
    have hxyE : -(x : EuclideanSpace ℝ (Fin 3)) = (y : EuclideanSpace ℝ (Fin 3)) := by
      simpa [haNeg1] using haE
    simpa using hxyE.symm

/-- Coercion of a point on `S²` to `Fin 3 → ℝ` is nonzero. -/
lemma helperForTheorem_6_8_ne_zero_coe_unitSphereTwo_fin3_in_part4
    (x : UnitSphereTwo) :
    (x : Fin 3 → ℝ) ≠ 0 := by
  have hx0E : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro hx0
    have hnorm0 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 0 := by simpa [hx0]
    have hnorm1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
      helperForTheorem_6_8_norm_eq_one_unitSphereTwo_in_part4 x
    linarith
  intro hx0
  apply hx0E
  ext i
  exact congrArg (fun f : Fin 3 → ℝ => f i) hx0

/-- In `ℝ^3`, `x × y = 0` implies that `y` is a scalar multiple of nonzero `x`. -/
lemma helperForTheorem_6_8_cross_eq_zero_implies_exists_smul_in_part4
    (x y : Fin 3 → ℝ)
    (hx : x ≠ 0)
    (hcross : crossProduct x y = 0) :
    ∃ a : ℝ, a • x = y := by
  have hdep : ¬ LinearIndependent ℝ ![x, y] := by
    intro hlin
    exact ((crossProduct_ne_zero_iff_linearIndependent).2 hlin) hcross
  by_contra hno
  have hall : ∀ a : ℝ, a • x ≠ y := by
    intro a ha
    exact hno ⟨a, ha⟩
  exact hdep ((LinearIndependent.pair_iff' (x := x) (y := y) hx).2 hall)

/-- If `x × p = (-x) × q`, then `p + q` is parallel to `x`. -/
lemma helperForTheorem_6_8_crossEq_neg_implies_sum_parallel_in_part4
    (x p q : Fin 3 → ℝ)
    (hx : x ≠ 0)
    (hcrossEq : crossProduct x p = crossProduct (-x) q) :
    ∃ a : ℝ, a • x = p + q := by
  have hcrossSumZero : crossProduct x (p + q) = 0 := by
    calc
      crossProduct x (p + q) = crossProduct x p + crossProduct x q := by
        rw [LinearMap.map_add]
      _ = crossProduct (-x) q + crossProduct x q := by simpa [hcrossEq]
      _ = 0 := by
        simp
  exact
    helperForTheorem_6_8_cross_eq_zero_implies_exists_smul_in_part4 x (p + q) hx hcrossSumZero

/-- Non-antipodal and non-identical unit vectors in `ℝ^3` have nonzero cross product. -/
lemma helperForTheorem_6_8_crossProduct_ne_zero_of_ne_self_and_ne_antipode_unitSphereTwo_in_part4
    (x y : UnitSphereTwo)
    (hxy : y ≠ x)
    (hneg : y ≠ -x) :
    crossProduct (x : Fin 3 → ℝ) (y : Fin 3 → ℝ) ≠ 0 := by
  intro hcross
  have hdep : ¬ LinearIndependent ℝ ![(x : Fin 3 → ℝ), (y : Fin 3 → ℝ)] := by
    intro hlin
    exact ((crossProduct_ne_zero_iff_linearIndependent).2 hlin) hcross
  rcases
      helperForTheorem_6_8_eq_or_eq_neg_of_not_linearIndependent_unitSphereTwo_in_part4 x y hdep
    with hyx | hyneg
  · exact hxy hyx
  · exact hneg hyneg

/-- For a self-map with no fixed/anti-fixed point, every point has nonzero cross
product with its image. -/
lemma helperForTheorem_6_8_crossProduct_selfMap_ne_zero_of_no_fixed_or_antifixed_in_part4
    (g : UnitSphereTwo → UnitSphereTwo)
    (hno : ¬ ∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :
    ∀ x : UnitSphereTwo, crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) ≠ 0 := by
  intro x
  have hgx_ne_x : g x ≠ x := by
    intro hEq
    exact hno ⟨x, Or.inl hEq⟩
  have hgx_ne_negx : g x ≠ -x := by
    intro hEq
    have hEqAmbient : (g x).1 = -x.1 := by
      simpa using congrArg (fun z : UnitSphereTwo => z.1) hEq
    exact hno ⟨x, Or.inr hEqAmbient⟩
  exact
    helperForTheorem_6_8_crossProduct_ne_zero_of_ne_self_and_ne_antipode_unitSphereTwo_in_part4
      x (g x) hgx_ne_x hgx_ne_negx

/-- A common-zero source for odd real pairs produces a point where the first two
coordinates of `c x - c (-x)` vanish, for any continuous `c : S² → ℝ^3`. -/
lemma helperForTheorem_6_8_exists_firstTwoCoord_zero_of_commonZero_on_antipodal_sub_in_part4
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0)
    (c : UnitSphereTwo → (Fin 3 → ℝ))
    (hcCont : Continuous c) :
    ∃ x : UnitSphereTwo,
      (c x - c (-x)) (0 : Fin 3) = 0 ∧
      (c x - c (-x)) (1 : Fin 3) = 0 := by
  let u : UnitSphereTwo → ℝ := fun x => (c x - c (-x)) (0 : Fin 3)
  let v : UnitSphereTwo → ℝ := fun x => (c x - c (-x)) (1 : Fin 3)
  have huCont : Continuous u := by
    dsimp [u]
    exact (continuous_apply (0 : Fin 3)).comp (hcCont.sub (hcCont.comp continuous_neg))
  have hvCont : Continuous v := by
    dsimp [v]
    exact (continuous_apply (1 : Fin 3)).comp (hcCont.sub (hcCont.comp continuous_neg))
  have huOdd : ∀ x : UnitSphereTwo, u (-x) = -u x := by
    intro x
    dsimp [u]
    simp
  have hvOdd : ∀ x : UnitSphereTwo, v (-x) = -v x := by
    intro x
    dsimp [v]
    simp
  rcases hcommonZero u v huCont hvCont huOdd hvOdd with ⟨x, hux, hvx⟩
  exact ⟨x, hux, hvx⟩

/-- In `ℝ^3`, if the first two coordinates of `d` vanish and `x ⬝ d = 0`, then
`d = 0` whenever the third coordinate of `x` is nonzero. -/
lemma helperForTheorem_6_8_eq_zero_of_firstTwoCoord_eq_zero_of_dot_eq_zero_and_third_ne_zero_in_part4
    (x d : Fin 3 → ℝ)
    (hd0 : d (0 : Fin 3) = 0)
    (hd1 : d (1 : Fin 3) = 0)
    (hdot : x ⬝ᵥ d = 0)
    (hx2 : x (2 : Fin 3) ≠ 0) :
    d = 0 := by
  funext i
  fin_cases i
  · exact hd0
  · exact hd1
  · have h2 : x (2 : Fin 3) * d (2 : Fin 3) = 0 := by
      have hsum :
          x (0 : Fin 3) * d (0 : Fin 3) +
            x (1 : Fin 3) * d (1 : Fin 3) +
            x (2 : Fin 3) * d (2 : Fin 3) = 0 := by
        simpa [dotProduct, Fin.sum_univ_three, add_assoc] using hdot
      simpa [hd0, hd1] using hsum
    exact (mul_eq_zero.mp h2).resolve_left hx2

/-- Specialized form for `d = (x × g x) - ((-x) × g(-x))`: if its first two
coordinates vanish and `x₂ ≠ 0`, then the two cross-product terms are equal. -/
lemma helperForTheorem_6_8_cross_diff_eq_zero_of_firstTwoCoord_zero_and_thirdCoord_nonzero_in_part4
    (g : UnitSphereTwo → UnitSphereTwo)
    (x : UnitSphereTwo)
    (hx0 :
      (crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
        crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) (0 : Fin 3) = 0)
    (hx1 :
      (crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
        crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) (1 : Fin 3) = 0)
    (hx2 : (x : Fin 3 → ℝ) (2 : Fin 3) ≠ 0) :
    crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) =
      crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) := by
  let d : Fin 3 → ℝ :=
    crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
      crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)
  have hdot0 : (x : Fin 3 → ℝ) ⬝ᵥ d = 0 := by
    have hdotA :
        (x : Fin 3 → ℝ) ⬝ᵥ crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) = 0 := by
      simpa using dot_self_cross (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ)
    have hdotB :
        (x : Fin 3 → ℝ) ⬝ᵥ crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) = 0 := by
      have hneg :
          (-x : Fin 3 → ℝ) ⬝ᵥ crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) = 0 := by
        simpa using dot_self_cross (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)
      simpa using hneg
    dsimp [d]
    simpa [dotProduct_sub, hdotA, hdotB]
  have hdEq0 : d = 0 := by
    apply
      helperForTheorem_6_8_eq_zero_of_firstTwoCoord_eq_zero_of_dot_eq_zero_and_third_ne_zero_in_part4
      (x := (x : Fin 3 → ℝ))
      (d := d)
    · simpa [d] using hx0
    · simpa [d] using hx1
    · exact hdot0
    · exact hx2
  have hdEq :
      crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
        crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) = 0 := by
    simpa [d] using hdEq0
  exact sub_eq_zero.mp hdEq

/-- If the first two coordinates of
`(x × p) - ((-x) × q)` vanish and `x₂ = 0`, then `(p + q)₂ = 0`. -/
lemma helperForTheorem_6_8_sum_third_eq_zero_of_two_cross_diff_coords_zero_and_x2_zero_in_part4
    (x p q : Fin 3 → ℝ)
    (hxne : x ≠ 0)
    (hx2 : x (2 : Fin 3) = 0)
    (h0 : (crossProduct x p - crossProduct (-x) q) (0 : Fin 3) = 0)
    (h1 : (crossProduct x p - crossProduct (-x) q) (1 : Fin 3) = 0) :
    (p + q) (2 : Fin 3) = 0 := by
  have h0' : x (1 : Fin 3) * ((p + q) (2 : Fin 3)) = 0 := by
    have h0exp :
        x (1 : Fin 3) * p (2 : Fin 3) - x (2 : Fin 3) * p (1 : Fin 3) -
          (x (2 : Fin 3) * q (1 : Fin 3) - x (1 : Fin 3) * q (2 : Fin 3)) = 0 := by
      simpa [cross_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h0
    have h0sum : x (1 : Fin 3) * p (2 : Fin 3) + x (1 : Fin 3) * q (2 : Fin 3) = 0 := by
      have h0exp' := h0exp
      simp [hx2] at h0exp'
      nlinarith [h0exp']
    simpa [Pi.add_apply, left_distrib] using h0sum
  have h1' : x (0 : Fin 3) * ((p + q) (2 : Fin 3)) = 0 := by
    have h1exp :
        x (2 : Fin 3) * p (0 : Fin 3) - x (0 : Fin 3) * p (2 : Fin 3) -
          (x (0 : Fin 3) * q (2 : Fin 3) - x (2 : Fin 3) * q (0 : Fin 3)) = 0 := by
      simpa [cross_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
    have h1sum : x (0 : Fin 3) * p (2 : Fin 3) + x (0 : Fin 3) * q (2 : Fin 3) = 0 := by
      have h1exp' := h1exp
      simp [hx2] at h1exp'
      nlinarith [h1exp']
    simpa [Pi.add_apply, left_distrib] using h1sum
  have hx01 : x (0 : Fin 3) ≠ 0 ∨ x (1 : Fin 3) ≠ 0 := by
    by_contra hx01
    push_neg at hx01
    apply hxne
    funext i
    fin_cases i
    · exact hx01.1
    · exact hx01.2
    · exact hx2
  rcases hx01 with hx0ne | hx1ne
  · exact (mul_eq_zero.mp h1').resolve_left hx0ne
  · exact (mul_eq_zero.mp h0').resolve_left hx1ne

/-- Rewriting identity for the cross-difference field used in the part4 reduction:
`x × g(x) - ((-x) × g(-x)) = x × (g(x) + g(-x))`. -/
lemma helperForTheorem_6_8_cross_selfMap_diff_eq_cross_sum_with_antipode_in_part4
    (g : UnitSphereTwo → UnitSphereTwo) (x : UnitSphereTwo) :
    crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
      crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) =
      crossProduct (x : Fin 3 → ℝ) ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) := by
  have hnegMap :
      crossProduct (-((x : Fin 3 → ℝ))) =
        -crossProduct (x : Fin 3 → ℝ) := by
    simpa using
      (LinearMap.map_neg
        (crossProduct : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ)
        (x : Fin 3 → ℝ))
  have hnegEval :
      crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) =
        -(crossProduct (x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) := by
    exact congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ => f (g (-x) : Fin 3 → ℝ)) hnegMap
  calc
    crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
        crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)
        = crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) +
            crossProduct (x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ) := by
              rw [hnegEval, sub_eq_add_neg, neg_neg]
    _ = crossProduct (x : Fin 3 → ℝ)
          ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) := by
            rw [LinearMap.map_add]

/-- The scalar map `x ↦ x · (g x + g(-x))` is continuous on `S²`. -/
lemma helperForTheorem_6_8_continuous_dot_sum_with_antipode_selfMap_in_part4
    (g : UnitSphereTwo → UnitSphereTwo) (hg : Continuous g) :
    Continuous (fun x : UnitSphereTwo =>
      (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ))) := by
  fun_prop

/-- The scalar map `x ↦ x · (g x + g(-x))` is odd on `S²`. -/
lemma helperForTheorem_6_8_dot_sum_with_antipode_selfMap_odd_in_part4
    (g : UnitSphereTwo → UnitSphereTwo) :
    ∀ x : UnitSphereTwo,
      (((-x : UnitSphereTwo) : Fin 3 → ℝ) ⬝ᵥ
        ((g (-x) : Fin 3 → ℝ) + (g x : Fin 3 → ℝ))) =
        -((x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ))) := by
  intro x
  calc
    (((-x : UnitSphereTwo) : Fin 3 → ℝ) ⬝ᵥ
      ((g (-x) : Fin 3 → ℝ) + (g x : Fin 3 → ℝ)))
      = (-(x : Fin 3 → ℝ)) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) := by
          simp [add_comm]
    _ = -((x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ))) := by
          simpa using neg_dotProduct (v := (x : Fin 3 → ℝ))
            (w := ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)))

/-- Upstream odd-zero consequence used in the long-line part4 reduction:
there exists a point where `x · (g x + g(-x)) = 0`. -/
lemma helperForTheorem_6_8_exists_dot_sum_with_antipode_eq_zero_in_part4
    (g : UnitSphereTwo → UnitSphereTwo) (hg : Continuous g) :
    ∃ x : UnitSphereTwo,
      (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) = 0 := by
  let u : UnitSphereTwo → ℝ := fun x =>
    (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ))
  have huCont : Continuous u :=
    helperForTheorem_6_8_continuous_dot_sum_with_antipode_selfMap_in_part4 g hg
  have huOdd : ∀ x : UnitSphereTwo, u (-x) = -u x := by
    intro x
    dsimp [u]
    simpa using helperForTheorem_6_8_dot_sum_with_antipode_selfMap_odd_in_part4 g x
  rcases helperForTheorem_6_8_continuous_odd_real_exists_zero u huCont huOdd with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Common-zero bridge (coordinate 0 + dot-sum) for the cross-difference field in part4. -/
lemma helperForTheorem_6_8_exists_cross_diff_first_coord_zero_and_dot_sum_zero_of_commonZero_in_part4
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0)
    (g : UnitSphereTwo → UnitSphereTwo) (hg : Continuous g) :
    ∃ x : UnitSphereTwo,
      (crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
        crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) (0 : Fin 3) = 0 ∧
      (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) = 0 := by
  let u : UnitSphereTwo → ℝ := fun x =>
    (crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
      crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) (0 : Fin 3)
  let v : UnitSphereTwo → ℝ := fun x =>
    (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ))
  have huCont : Continuous u := by
    dsimp [u]
    fun_prop
  have hvCont : Continuous v := by
    simpa [v] using
      helperForTheorem_6_8_continuous_dot_sum_with_antipode_selfMap_in_part4 g hg
  have huOdd : ∀ x : UnitSphereTwo, u (-x) = -u x := by
    intro x
    dsimp [u]
    simp
    abel_nf
  have hvOdd : ∀ x : UnitSphereTwo, v (-x) = -v x := by
    intro x
    dsimp [v]
    simpa using helperForTheorem_6_8_dot_sum_with_antipode_selfMap_odd_in_part4 g x
  rcases hcommonZero u v huCont hvCont huOdd hvOdd with ⟨x, hux, hvx⟩
  exact ⟨x, hux, hvx⟩

/-- Common-zero bridge (coordinate 1 + dot-sum) for the cross-difference field in part4. -/
lemma helperForTheorem_6_8_exists_cross_diff_second_coord_zero_and_dot_sum_zero_of_commonZero_in_part4
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0)
    (g : UnitSphereTwo → UnitSphereTwo) (hg : Continuous g) :
    ∃ x : UnitSphereTwo,
      (crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
        crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) (1 : Fin 3) = 0 ∧
      (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) = 0 := by
  let u : UnitSphereTwo → ℝ := fun x =>
    (crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) -
      crossProduct (-x : Fin 3 → ℝ) (g (-x) : Fin 3 → ℝ)) (1 : Fin 3)
  let v : UnitSphereTwo → ℝ := fun x =>
    (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ))
  have huCont : Continuous u := by
    dsimp [u]
    fun_prop
  have hvCont : Continuous v := by
    simpa [v] using
      helperForTheorem_6_8_continuous_dot_sum_with_antipode_selfMap_in_part4 g hg
  have huOdd : ∀ x : UnitSphereTwo, u (-x) = -u x := by
    intro x
    dsimp [u]
    simp
    abel_nf
  have hvOdd : ∀ x : UnitSphereTwo, v (-x) = -v x := by
    intro x
    dsimp [v]
    simpa using helperForTheorem_6_8_dot_sum_with_antipode_selfMap_odd_in_part4 g x
  rcases hcommonZero u v huCont hvCont huOdd hvOdd with ⟨x, hux, hvx⟩
  exact ⟨x, hux, hvx⟩

/-- Independent upstream bridge for Theorem 6.8.

This theorem is intentionally placed in `section06_part4` (strictly earlier than
`section06_part5`/`section06_part6`) so downstream files can consume it without
forming a declaration-order cycle.

Non-circularity contract:
* Do not prove this by using any declaration from `section06_part6`.
* Future completion should use genuinely upstream ingredients only. -/
lemma helperForTheorem_6_8_upstream_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction_in_part4 :
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  intro hantipodal g hg
  have hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0 :=
    helperForTheorem_6_8_continuous_odd_real_pair_common_zero_of_antipodal_equality_in_part4
      hantipodal
  by_contra hno
  have hcrossNe :
      ∀ x : UnitSphereTwo, crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ) ≠ 0 :=
    helperForTheorem_6_8_crossProduct_selfMap_ne_zero_of_no_fixed_or_antifixed_in_part4 g hno
  let c : UnitSphereTwo → (Fin 3 → ℝ) := fun x =>
    crossProduct (x : Fin 3 → ℝ) (g x : Fin 3 → ℝ)
  have hcCont : Continuous c := by
    fun_prop
  have hcNe : ∀ x : UnitSphereTwo, c x ≠ 0 := by
    intro x
    exact hcrossNe x
  have hdotZeroPoint :
      ∃ x : UnitSphereTwo,
        (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) = 0 :=
    helperForTheorem_6_8_exists_dot_sum_with_antipode_eq_zero_in_part4 g hg
  have hcoordZero :
      ∃ x : UnitSphereTwo,
        (c x - c (-x)) (0 : Fin 3) = 0 ∧
        (c x - c (-x)) (1 : Fin 3) = 0 :=
    helperForTheorem_6_8_exists_firstTwoCoord_zero_of_commonZero_on_antipodal_sub_in_part4
      hcommonZero c hcCont
  rcases hcoordZero with ⟨x0, hx0, hx1⟩
  have hcrossDiffEq :
      c x0 - c (-x0) =
        crossProduct (x0 : Fin 3 → ℝ) ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ)) := by
    simpa [c] using
      helperForTheorem_6_8_cross_selfMap_diff_eq_cross_sum_with_antipode_in_part4 g x0
  have hxCrossSum0 :
      (crossProduct (x0 : Fin 3 → ℝ) ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ)))
          (0 : Fin 3) = 0 ∧
      (crossProduct (x0 : Fin 3 → ℝ) ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ)))
          (1 : Fin 3) = 0 := by
    have hx0eq :
        (c x0 - c (-x0)) (0 : Fin 3) =
          (crossProduct (x0 : Fin 3 → ℝ)
            ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ))) (0 : Fin 3) := by
      simpa using congrArg (fun w : Fin 3 → ℝ => w (0 : Fin 3)) hcrossDiffEq
    have hx1eq :
        (c x0 - c (-x0)) (1 : Fin 3) =
          (crossProduct (x0 : Fin 3 → ℝ)
            ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ))) (1 : Fin 3) := by
      simpa using congrArg (fun w : Fin 3 → ℝ => w (1 : Fin 3)) hcrossDiffEq
    constructor
    · calc
        (crossProduct (x0 : Fin 3 → ℝ)
          ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ))) (0 : Fin 3)
            = (c x0 - c (-x0)) (0 : Fin 3) := by simpa [hx0eq] using hx0eq.symm
        _ = 0 := hx0
    · calc
        (crossProduct (x0 : Fin 3 → ℝ)
          ((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ))) (1 : Fin 3)
            = (c x0 - c (-x0)) (1 : Fin 3) := by simpa [hx1eq] using hx1eq.symm
        _ = 0 := hx1
  have hcoord2OrCrossEq :
      ((x0 : Fin 3 → ℝ) (2 : Fin 3) = 0) ∨
        crossProduct (x0 : Fin 3 → ℝ) (g x0 : Fin 3 → ℝ) =
          crossProduct (-x0 : Fin 3 → ℝ) (g (-x0) : Fin 3 → ℝ) := by
    by_cases hx02 : (x0 : Fin 3 → ℝ) (2 : Fin 3) = 0
    · exact Or.inl hx02
    · have hx02_ne : (x0 : Fin 3 → ℝ) (2 : Fin 3) ≠ 0 := hx02
      have hcrossEq :
          crossProduct (x0 : Fin 3 → ℝ) (g x0 : Fin 3 → ℝ) =
            crossProduct (-x0 : Fin 3 → ℝ) (g (-x0) : Fin 3 → ℝ) :=
        helperForTheorem_6_8_cross_diff_eq_zero_of_firstTwoCoord_zero_and_thirdCoord_nonzero_in_part4
          g x0 hx0 hx1 hx02_ne
      exact Or.inr hcrossEq
  have hcoord2OrSumParallel :
      ((x0 : Fin 3 → ℝ) (2 : Fin 3) = 0) ∨
        (∃ a : ℝ, a • (x0 : Fin 3 → ℝ) = (g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ)) := by
    rcases hcoord2OrCrossEq with hx02 | hcrossEq
    · exact Or.inl hx02
    · right
      exact
        helperForTheorem_6_8_crossEq_neg_implies_sum_parallel_in_part4
          (x0 : Fin 3 → ℝ)
          (g x0 : Fin 3 → ℝ)
          (g (-x0) : Fin 3 → ℝ)
          (helperForTheorem_6_8_ne_zero_coe_unitSphereTwo_fin3_in_part4 x0)
          hcrossEq
  have hx2AndSumThirdOrParallel :
      (((x0 : Fin 3 → ℝ) (2 : Fin 3) = 0) ∧
        (((g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ)) (2 : Fin 3) = 0)) ∨
        (∃ a : ℝ, a • (x0 : Fin 3 → ℝ) = (g x0 : Fin 3 → ℝ) + (g (-x0) : Fin 3 → ℝ)) := by
    rcases hcoord2OrSumParallel with hx02 | hpar
    · left
      refine ⟨hx02, ?_⟩
      exact
        helperForTheorem_6_8_sum_third_eq_zero_of_two_cross_diff_coords_zero_and_x2_zero_in_part4
            (x := (x0 : Fin 3 → ℝ))
            (p := (g x0 : Fin 3 → ℝ))
            (q := (g (-x0) : Fin 3 → ℝ))
            (hxne := helperForTheorem_6_8_ne_zero_coe_unitSphereTwo_fin3_in_part4 x0)
            (hx2 := hx02)
            (h0 := hx0)
            (h1 := hx1)
    · exact Or.inr hpar
  have hfirstCoordAndDot :
      ∃ x : UnitSphereTwo,
        (c x - c (-x)) (0 : Fin 3) = 0 ∧
        (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) = 0 := by
    rcases
        helperForTheorem_6_8_exists_cross_diff_first_coord_zero_and_dot_sum_zero_of_commonZero_in_part4
          hcommonZero g hg with
      ⟨x, hx0', hdot⟩
    refine ⟨x, ?_, hdot⟩
    simpa [c] using hx0'
  have hsecondCoordAndDot :
      ∃ x : UnitSphereTwo,
        (c x - c (-x)) (1 : Fin 3) = 0 ∧
        (x : Fin 3 → ℝ) ⬝ᵥ ((g x : Fin 3 → ℝ) + (g (-x) : Fin 3 → ℝ)) = 0 := by
    rcases
        helperForTheorem_6_8_exists_cross_diff_second_coord_zero_and_dot_sum_zero_of_commonZero_in_part4
          hcommonZero g hg with
      ⟨x, hx1', hdot⟩
    refine ⟨x, ?_, hdot⟩
    simpa [c] using hx1'
  rcases hfirstCoordAndDot with ⟨xa, hxa0, hxadot⟩
  rcases hsecondCoordAndDot with ⟨xb, hxb1, hxbdot⟩
  have hxaCrossDiffEq :
      c xa - c (-xa) =
        crossProduct (xa : Fin 3 → ℝ) ((g xa : Fin 3 → ℝ) + (g (-xa) : Fin 3 → ℝ)) := by
    simpa [c] using
      helperForTheorem_6_8_cross_selfMap_diff_eq_cross_sum_with_antipode_in_part4 g xa
  have hxbCrossDiffEq :
      c xb - c (-xb) =
        crossProduct (xb : Fin 3 → ℝ) ((g xb : Fin 3 → ℝ) + (g (-xb) : Fin 3 → ℝ)) := by
    simpa [c] using
      helperForTheorem_6_8_cross_selfMap_diff_eq_cross_sum_with_antipode_in_part4 g xb
  have hxaCross0 :
      (crossProduct (xa : Fin 3 → ℝ) ((g xa : Fin 3 → ℝ) + (g (-xa) : Fin 3 → ℝ)))
          (0 : Fin 3) = 0 := by
    have hxa0eq :
        (c xa - c (-xa)) (0 : Fin 3) =
          (crossProduct (xa : Fin 3 → ℝ)
            ((g xa : Fin 3 → ℝ) + (g (-xa) : Fin 3 → ℝ))) (0 : Fin 3) := by
      simpa using congrArg (fun w : Fin 3 → ℝ => w (0 : Fin 3)) hxaCrossDiffEq
    calc
      (crossProduct (xa : Fin 3 → ℝ) ((g xa : Fin 3 → ℝ) + (g (-xa) : Fin 3 → ℝ)))
          (0 : Fin 3)
          = (c xa - c (-xa)) (0 : Fin 3) := by simpa [hxa0eq] using hxa0eq.symm
      _ = 0 := hxa0
  have hxbCross1 :
      (crossProduct (xb : Fin 3 → ℝ) ((g xb : Fin 3 → ℝ) + (g (-xb) : Fin 3 → ℝ)))
          (1 : Fin 3) = 0 := by
    have hxb1eq :
        (c xb - c (-xb)) (1 : Fin 3) =
          (crossProduct (xb : Fin 3 → ℝ)
            ((g xb : Fin 3 → ℝ) + (g (-xb) : Fin 3 → ℝ))) (1 : Fin 3) := by
      simpa using congrArg (fun w : Fin 3 → ℝ => w (1 : Fin 3)) hxbCrossDiffEq
    calc
      (crossProduct (xb : Fin 3 → ℝ) ((g xb : Fin 3 → ℝ) + (g (-xb) : Fin 3 → ℝ)))
          (1 : Fin 3)
          = (c xb - c (-xb)) (1 : Fin 3) := by simpa [hxb1eq] using hxb1eq.symm
      _ = 0 := hxb1
  -- Remaining hard topological core for part4:
  -- from the nonvanishing cross-product field `c`, build two continuous odd
  -- real-valued maps with no common zero, contradicting `hcommonZero`.
  -- Current reduced frontier: use `hx0`,`hx1`,`hcoord2OrCrossEq`,
  -- `hcoord2OrSumParallel`,`hx2AndSumThirdOrParallel` and structure
  -- of `c = x × g x` to derive a fixed/anti-fixed witness, contradicting `hno`.
  -- Newly available common-zero/dot bridges in this file:
  -- * `helperForTheorem_6_8_exists_cross_diff_first_coord_zero_and_dot_sum_zero_of_commonZero_in_part4`
  -- * `helperForTheorem_6_8_exists_cross_diff_second_coord_zero_and_dot_sum_zero_of_commonZero_in_part4`
  -- The next step is a same-point coupling argument that combines these bridges
  -- with the current `x0`-branch analysis. The witnesses are now explicit:
  -- `xa : d0(xa)=0 ∧ dot(xa)=0`, `xb : d1(xb)=0 ∧ dot(xb)=0`.
  sorry

/-- Core upstream Borsuk-Ulam source required by Theorem 6.8 in the part4 stage. -/
theorem helperForTheorem_6_8_upstream_antipodal_equality_source_in_part4 :
    ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x)) := by
  intro g hg
  -- Long-line topological source isolated in part4:
  -- build common-zero points for every pair of continuous odd real-valued maps on `S²`.
  have hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0 := by
    sorry
  exact
    helperForTheorem_6_8_continuous_map_unitSphereTwo_to_euclideanTwo_exists_antipodal_equal_of_common_zero_real_pair_in_part4
      hcommonZero g hg

theorem helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge_in_part4_placeholder :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    ⟨helperForTheorem_6_8_upstream_antipodal_equality_source_in_part4,
      helperForTheorem_6_8_upstream_antipodal_equality_to_selfMap_fixed_or_antifixed_reduction_in_part4⟩


end Section06
end Chap06
