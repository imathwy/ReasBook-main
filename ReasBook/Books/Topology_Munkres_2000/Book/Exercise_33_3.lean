module

public import Topology_Munkres_2000.Book.Definition_33_1.FunctionalSeparation
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

open Set

universe u

namespace Metric

/-- The normalized-distance function associated to two subsets of a pseudometric space. -/
noncomputable def urysohn {X : Type u} [PseudoMetricSpace X] (A B : Set X) (x : X) : ℝ :=
  infDist x A / (infDist x A + infDist x B)

/-- Helper for Exercise 33.3: a point in a set disjoint from a nonempty closed set has
strictly positive infimum distance from the closed set. -/
lemma infDist_pos_of_mem_of_disjoint {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hneA : A.Nonempty) (hAB : Disjoint A B) {x : X} (hx : x ∈ B) :
    0 < infDist x A := by
  -- Disjointness places `x` outside `A`, where closedness characterizes positive distance.
  apply (hA.notMem_iff_infDist_pos hneA).1
  exact hAB.notMem_of_mem_right hx

/-- Helper for Exercise 33.3: the sum of the distances to two disjoint nonempty closed
sets is everywhere strictly positive. -/
lemma urysohnDenominator_pos {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) (x : X) : 0 < infDist x A + infDist x B := by
  -- Split according to membership in `A`; one of the two distances is then positive.
  by_cases hx : x ∈ A
  · exact add_pos_of_nonneg_of_pos infDist_nonneg
      (infDist_pos_of_mem_of_disjoint hB hneB hAB.symm hx)
  · exact add_pos_of_pos_of_nonneg ((hA.notMem_iff_infDist_pos hneA).1 hx) infDist_nonneg

/-- Helper for Exercise 33.3: the normalized-distance function of two disjoint nonempty closed
subsets of a pseudometric space is continuous. -/
theorem continuous_urysohn {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) : Continuous (urysohn A B) := by
  -- Divide the two continuous distance expressions using denominator positivity.
  unfold urysohn
  exact
    (continuous_infDist_pt A).div
      ((continuous_infDist_pt A).add (continuous_infDist_pt B))
      (fun x ↦ ne_of_gt (urysohnDenominator_pos hA hB hneA hneB hAB x))

/-- Helper for Exercise 33.3: the normalized-distance function vanishes on its first subset. -/
theorem urysohn_eq_zero {X : Type u} [PseudoMetricSpace X] (A B : Set X) :
    EqOn (urysohn A B) 0 A := by
  -- On `A`, the numerator is zero, so the normalized quotient vanishes.
  intro x hx
  simp only [urysohn, infDist_zero_of_mem hx, zero_div, Pi.zero_apply]

/-- Helper for Exercise 33.3: the normalized-distance function equals one on the second of two
disjoint subsets when the first is nonempty and closed. -/
theorem urysohn_eq_one {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hneA : A.Nonempty) (hAB : Disjoint A B) :
    EqOn (urysohn A B) 1 B := by
  -- On `B`, its distance vanishes while disjointness keeps the numerator nonzero.
  intro x hx
  have hdistA : infDist x A ≠ 0 :=
    ne_of_gt (infDist_pos_of_mem_of_disjoint hA hneA hAB hx)
  simp only [urysohn, infDist_zero_of_mem hx, add_zero]
  exact div_self hdistA

/-- Helper for Exercise 33.3: the normalized-distance function takes its values in the unit
interval. -/
theorem urysohn_mem_Icc {X : Type u} [PseudoMetricSpace X] (A B : Set X) (x : X) :
    urysohn A B x ∈ Icc (0 : ℝ) 1 := by
  -- Nonnegativity gives the lower bound, and the numerator is at most the denominator.
  constructor
  · exact div_nonneg infDist_nonneg (add_nonneg infDist_nonneg infDist_nonneg)
  · exact div_le_one_of_le₀ (le_add_of_nonneg_right infDist_nonneg)
      (add_nonneg infDist_nonneg infDist_nonneg)

/-- Helper for Exercise 33.3: the continuous map to the unit interval given by the
normalized-distance formula. -/
@[expose]
noncomputable def urysohnMap {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) : C(X, Icc (0 : ℝ) 1) where
  toFun x := ⟨urysohn A B x, urysohn_mem_Icc A B x⟩
  continuous_toFun := (continuous_urysohn hA hB hneA hneB hAB).subtype_mk _

/-- Helper for Exercise 33.3: the underlying real value of `urysohnMap` is the
normalized-distance formula. -/
@[simp]
theorem coe_urysohnMap_apply {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) (x : X) :
    (urysohnMap hA hB hneA hneB hAB x : ℝ) = urysohn A B x := rfl

/-- Exercise 33.3: Disjoint nonempty closed subsets of a pseudometric space are functionally
separated by the normalized-distance map. -/
theorem functionallySeparated {X : Type u} [PseudoMetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hAB : Disjoint A B) : FunctionallySeparated A B := by
  -- Package the continuous real-valued formula through the public separation criterion.
  let f : C(X, ℝ) := ⟨urysohn A B, continuous_urysohn hA hB hneA hneB hAB⟩
  apply FunctionallySeparated.of_continuousMap_real f
  · exact urysohn_eq_zero A B
  · exact urysohn_eq_one hA hneA hAB
  · exact urysohn_mem_Icc A B

end Metric
