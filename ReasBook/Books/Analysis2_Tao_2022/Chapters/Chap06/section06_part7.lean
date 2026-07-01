/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06_part6

section Chap06
section Section06

/-- Helper for Theorem 6.8: prerequisite global fixed-point-or-antipode-equality principle for
continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_fixed_eq_antipode :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) := by
  exact
    (helperForTheorem_6_8_no_counterexample_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).1
      helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_no_counterexample_fixed_or_neg

/-- Helper for Theorem 6.8: prerequisite no-counterexample statement for continuous
self-maps of `S²` in fixed-point-or-antipode-equality form. -/
theorem helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_no_counterexample_fixed_or_fixed_eq_antipode :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) := by
  exact
    (helperForTheorem_6_8_no_counterexample_fixed_or_fixed_eq_antipode_iff_global_fixed_or_fixed_eq_antipode).2
      helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_fixed_eq_antipode

/-- Helper for Theorem 6.8: the no-counterexample statement yields the corresponding
global fixed-point-or-antipode-equality principle. -/
lemma helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_no_counterexample_fixed_or_fixed_eq_antipode
    (hnoCounterexample :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) := by
  exact
    (helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_iff_no_counterexample).2
      hnoCounterexample

/-- Helper for Theorem 6.8: the no-counterexample statement in fixed-point-or-
antipode-equality form yields the global fixed/anti-fixed existence principle. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_no_counterexample_fixed_or_fixed_eq_antipode
    (hnoCounterexample :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_fixed_eq_antipode_principle
      (helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_no_counterexample_fixed_or_fixed_eq_antipode
        hnoCounterexample)

/-- Helper for Theorem 6.8: prerequisite global fixed/anti-fixed existence for continuous
self-maps of `S²`. -/
theorem helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_continuous_prereq :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  exact
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_no_counterexample_fixed_or_fixed_eq_antipode
      helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_no_counterexample_fixed_or_fixed_eq_antipode

/-- Helper for Theorem 6.8: a global fixed/anti-fixed existence principle directly yields
the local fixed/anti-fixed witness for any continuous self-map of `S²`. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_global_exists_fixed_or_antifixed_principle
    (hprinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact hprinciple f hcont

/-- Helper for Theorem 6.8: a global fixed-point-or-antipode-composed-fixed principle
directly yields the local fixed/anti-fixed witness for any continuous self-map of `S²`. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_global_fixed_or_antipode_comp_fixed_principle
    (hprinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, helperForTheorem_6_8_antipode (g x) = x)))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    helperForTheorem_6_8_exists_of_fixed_or_antipode_comp_fixed
      (hprinciple f hcont)

/-- Helper for Theorem 6.8: a global fixed-point-or-antipode-composed-fixed principle
on continuous self-maps of `S²` implies the global fixed/anti-fixed existence principle. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_antipode_comp_fixed_principle
    (hprinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, helperForTheorem_6_8_antipode (g x) = x))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro g hg
  exact
    helperForTheorem_6_8_exists_of_fixed_or_antipode_comp_fixed
      (hprinciple g hg)

/-- Helper for Theorem 6.8: prerequisite fixed-point/antipode-equality alternative on `S²`
derived from continuity. -/
theorem helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_continuous_prereq
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    (∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, f x = helperForTheorem_6_8_antipode x) := by
  have hfixedOrAntifixedPrinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_continuous_prereq
  have hfixedOrFixedEqAntipodePrinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) :=
    helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_global_exists_fixed_or_antifixed
      hfixedOrAntifixedPrinciple
  exact
    helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_continuous_of_global_principle
      hfixedOrFixedEqAntipodePrinciple f hcont

/-- Helper for Theorem 6.8: upstream fixed/anti-fixed existence for continuous self-maps of `S²`. -/
theorem helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    (helperForTheorem_6_8_fixed_or_fixed_eq_antipode_iff_exists_fixed_or_antifixed
      (f := f)).1
      (helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_continuous_prereq f hcont)

/-- Helper for Theorem 6.8: topological fixed-point/antipode-equality existence from continuity on
`S²`. -/
theorem helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_continuous
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    (∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, f x = helperForTheorem_6_8_antipode x) := by
  have htarget :
      ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 :=
    helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous f hcont
  exact helperForTheorem_6_8_fixed_or_fixed_eq_antipode_of_exists_fixed_or_antifixed htarget

/-- Helper for Theorem 6.8: prerequisite fixed-point/antipode-fixed alternative on `S²`. -/
theorem helperForTheorem_6_8_fixed_or_antipode_comp_fixed_prereq
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    (∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, helperForTheorem_6_8_antipode (f x) = x) := by
  have hfixedOrAntifixedPrinciple :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_continuous_prereq
  exact
    helperForTheorem_6_8_global_fixed_or_antipode_comp_fixed_of_global_exists_fixed_or_antifixed
      hfixedOrAntifixedPrinciple f hcont

/-- Theorem 6.8 (Hairy ball theorem, fixed point/anti-fixed point alternative):
for any continuous self-map `f : S² → S²`, there exists `x ∈ S²` such that either
`f x = x` or `f x = -x` (expressed on ambient vectors). -/
theorem hairy_ball_fixed_or_antifixed_alternative_6_8
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous f hcont

/-- The origin belongs to the open ball centered at the origin with positive radius. -/
lemma origin_mem_ball_origin_of_pos {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
  simpa [Metric.mem_ball, dist_eq_norm] using hr

/-- Lemma 6.7: Let `r > 0` and let `g : B(0,r) → ℝ^n` satisfy `g(0) = 0` and
`‖g(x) - g(y)‖ ≤ (1/2) ‖x - y‖` for all `x,y ∈ B(0,r)`. If `f(x) = x + g(x)` on `B(0,r)`,
then `f` is injective and `B(0,r/2) ⊆ f(B(0,r))`. -/
theorem contraction_perturbation_injective_and_ball_half_subset_range
    {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (g : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r → EuclideanSpace ℝ (Fin n))
    (hzero : g ⟨0, origin_mem_ball_origin_of_pos hr⟩ = 0)
    (hcontract :
      ∀ x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ‖g x - g y‖ ≤ (1 / 2 : ℝ) * ‖(x : EuclideanSpace ℝ (Fin n)) - (y : EuclideanSpace ℝ (Fin n))‖) :
    Function.Injective
        (fun x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r =>
          (x : EuclideanSpace ℝ (Fin n)) + g x) ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆
        Set.range
          (fun x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r =>
            (x : EuclideanSpace ℝ (Fin n)) + g x) := by
  let E := EuclideanSpace ℝ (Fin n)
  constructor
  · intro x y hxy
    have hsub :
        ((x : E) - (y : E)) = g y - g x := by
      have hsub' :
          ((x : E) + g x) - ((y : E) + g x) = ((y : E) + g y) - ((y : E) + g x) := by
        simpa using congrArg (fun z : E => z - ((y : E) + g x)) hxy
      calc
        ((x : E) - (y : E)) = ((x : E) + g x) - ((y : E) + g x) := by
          abel_nf
        _ = ((y : E) + g y) - ((y : E) + g x) := hsub'
        _ = g y - g x := by
          abel_nf
    have hle :
        ‖(x : E) - (y : E)‖ ≤ (1 / 2 : ℝ) * ‖(x : E) - (y : E)‖ := by
      calc
        ‖(x : E) - (y : E)‖ = ‖g y - g x‖ := by simpa [hsub]
        _ = ‖g x - g y‖ := by simpa [norm_sub_rev]
        _ ≤ (1 / 2 : ℝ) * ‖(x : E) - (y : E)‖ := hcontract x y
    have hnorm_zero : ‖(x : E) - (y : E)‖ = 0 := by
      nlinarith [norm_nonneg ((x : E) - (y : E)), hle]
    have hxy_val : (x : E) = (y : E) := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
    exact Subtype.ext (by simpa using hxy_val)
  · intro y hy
    have hy_norm : ‖y‖ < r / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    let ρ : ℝ := (2 * ‖y‖ + r) / 2
    have htwo_y_lt_r : 2 * ‖y‖ < r := by
      nlinarith [hy_norm]
    have hρ_lt_r : ρ < r := by
      dsimp [ρ]
      nlinarith [htwo_y_lt_r]
    have hρ_nonneg : 0 ≤ ρ := by
      dsimp [ρ]
      nlinarith [norm_nonneg y, hr]
    have htwo_y_le_ρ : 2 * ‖y‖ ≤ ρ := by
      dsimp [ρ]
      nlinarith [htwo_y_lt_r]
    have hy_le_half_ρ : ‖y‖ ≤ ρ / 2 := by
      nlinarith [htwo_y_le_ρ]
    have hclosed_to_open :
        ∀ x : Metric.closedBall (0 : E) ρ, (x : E) ∈ Metric.ball (0 : E) r := by
      intro x
      have hx_closed_dist : dist (x : E) (0 : E) ≤ ρ := x.property
      have hx_norm_eq_dist : ‖(x : E)‖ = dist (x : E) (0 : E) := by
        simpa using
          (dist_eq_norm (a := (x : E)) (b := (0 : E))).symm
      have hx_closed : ‖(x : E)‖ ≤ ρ := by
        rw [hx_norm_eq_dist]
        exact hx_closed_dist
      have hx_open : ‖(x : E)‖ < r := by
        nlinarith [hx_closed, hρ_lt_r]
      have hx_dist_eq_norm : dist (x : E) (0 : E) = ‖(x : E)‖ := by
        simpa using
          (dist_eq_norm (a := (x : E)) (b := (0 : E)))
      have hx_open_dist : dist (x : E) (0 : E) < r := by
        rw [hx_dist_eq_norm]
        exact hx_open
      simpa [Metric.mem_ball] using hx_open_dist
    let toBall : Metric.closedBall (0 : E) ρ → Metric.ball (0 : E) r :=
      fun x => ⟨x, hclosed_to_open x⟩
    let zeroBall : Metric.ball (0 : E) r := ⟨0, origin_mem_ball_origin_of_pos hr⟩
    have hg_norm_bound :
        ∀ x : Metric.closedBall (0 : E) ρ,
          ‖g (toBall x)‖ ≤ (1 / 2 : ℝ) * ‖(x : E)‖ := by
      intro x
      simpa [zeroBall, hzero] using hcontract (toBall x) zeroBall
    have haffine_mem_closedBall :
        ∀ x : Metric.closedBall (0 : E) ρ,
          y - g (toBall x) ∈ Metric.closedBall (0 : E) ρ := by
      intro x
      have hx_closed_dist : dist (x : E) (0 : E) ≤ ρ := x.property
      have hx_norm_eq_dist : ‖(x : E)‖ = dist (x : E) (0 : E) := by
        simpa using
          (dist_eq_norm (a := (x : E)) (b := (0 : E))).symm
      have hx_closed : ‖(x : E)‖ ≤ ρ := by
        rw [hx_norm_eq_dist]
        exact hx_closed_dist
      have hgx : ‖g (toBall x)‖ ≤ (1 / 2 : ℝ) * ‖(x : E)‖ := hg_norm_bound x
      have hgx_half_ρ : ‖g (toBall x)‖ ≤ ρ / 2 := by
        nlinarith [hgx, hx_closed]
      have hnorm_le : ‖y - g (toBall x)‖ ≤ ρ := by
        have hsum : ‖y‖ + ‖g (toBall x)‖ ≤ ρ := by
          nlinarith [hy_le_half_ρ, hgx_half_ρ]
        exact le_trans (norm_sub_le y (g (toBall x))) hsum
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le
    let T : Metric.closedBall (0 : E) ρ → Metric.closedBall (0 : E) ρ :=
      fun x => ⟨y - g (toBall x), haffine_mem_closedBall x⟩
    have hT_contraction :
        ∀ x z : Metric.closedBall (0 : E) ρ,
          dist (T x) (T z) ≤ (1 / 2 : ℝ) * dist x z := by
      intro x z
      have hdist_eq :
          dist (T x) (T z) = ‖g (toBall x) - g (toBall z)‖ := by
        change ‖(y - g (toBall x)) - (y - g (toBall z))‖ = ‖g (toBall x) - g (toBall z)‖
        have hsub :
            (y - g (toBall x)) - (y - g (toBall z)) = g (toBall z) - g (toBall x) := by
          abel_nf
        rw [hsub]
        simpa [norm_sub_rev]
      calc
        dist (T x) (T z) = ‖g (toBall x) - g (toBall z)‖ := hdist_eq
        _ ≤ (1 / 2 : ℝ) * dist x z := by
          simpa [toBall, dist_eq_norm] using hcontract (toBall x) (toBall z)
    have hT_strict :
        ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
          ∀ x z : Metric.closedBall (0 : E) ρ, dist (T x) (T z) ≤ c * dist x z := by
      refine ⟨(1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
      intro x z
      exact hT_contraction x z
    have hclosedBall_nonempty : Nonempty (Metric.closedBall (0 : E) ρ) := by
      refine ⟨⟨0, ?_⟩⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_nonneg
    have hfixed_unique :
        ∃! x : Metric.closedBall (0 : E) ρ, IsFixedPoint T x := by
      exact
        (contraction_mapping_theorem_6_7 T hT_strict).2 hclosedBall_nonempty
          (inferInstance : CompleteSpace (Metric.closedBall (0 : E) ρ))
    rcases hfixed_unique with ⟨xfix, hxfix, -⟩
    have hxfix_val : (T xfix : E) = (xfix : E) := by
      exact congrArg Subtype.val hxfix
    have hxfix_eq : y - g (toBall xfix) = (xfix : E) := by
      simpa [T] using hxfix_val
    have hy_eq : y = (xfix : E) + g (toBall xfix) := by
      calc
        y = (y - g (toBall xfix)) + g (toBall xfix) := by
          simp [sub_eq_add_neg, add_assoc]
        _ = (xfix : E) + g (toBall xfix) := by
          rw [hxfix_eq]
    refine ⟨toBall xfix, ?_⟩
    calc
      ((toBall xfix : Metric.ball (0 : E) r) : E) + g (toBall xfix) = (xfix : E) + g (toBall xfix) := by
        rfl
      _ = y := hy_eq.symm


end Section06
end Chap06
