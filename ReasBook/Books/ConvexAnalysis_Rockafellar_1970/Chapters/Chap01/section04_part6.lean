/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xuran Sun, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5

open Matrix

section Chap01
section Section04

/-- Defintion 4.8.1: For a set `C ⊆ ℝ^n`, the indicator function `δ(· | C)` is
`0` on `C` and `+∞` outside `C`. -/
noncomputable def indicatorFunction {n : Nat} (C : Set (Fin n → Real)) :
    (Fin n → Real) → EReal := by
  classical
  exact fun x => if x ∈ C then (0 : EReal) else (⊤ : EReal)

/-- The indicator function is finite exactly on the set. -/
lemma indicatorFunction_lt_top_iff_mem {n : Nat} {C : Set (Fin n → Real)} {x : Fin n → Real} :
    indicatorFunction C x < (⊤ : EReal) ↔ x ∈ C := by
  classical
  by_cases hx : x ∈ C
  · simp [indicatorFunction, hx]
  · simp [indicatorFunction, hx]

/-- The effective domain of the indicator function is the original set. -/
lemma effectiveDomain_indicatorFunction_eq {n : Nat} (C : Set (Fin n → Real)) :
    effectiveDomain Set.univ (indicatorFunction C) = C := by
  classical
  ext x; simp [effectiveDomain_eq, indicatorFunction_lt_top_iff_mem]

/-- The indicator function of a convex set is convex. -/
lemma convexFunction_indicator_of_convex {n : Nat} {C : Set (Fin n → Real)}
    (hC : Convex ℝ C) : ConvexFunction (indicatorFunction C) := by
  classical
  have hconv : ConvexOn ℝ C (fun _ : Fin n → Real => (0 : Real)) :=
    convexOn_const (c := (0 : Real)) hC
  have hconvOn :
      ConvexFunctionOn Set.univ (fun x : Fin n → Real =>
        if x ∈ C then ((0 : Real) : EReal) else (⊤ : EReal)) :=
    convexFunctionOn_univ_if_top (C := C) (g := fun _ : Fin n → Real => (0 : Real)) hconv
  simpa [ConvexFunction, indicatorFunction] using hconvOn

/-- Remark 4.8.1: The epigraph of the indicator function is a half-cylinder with
cross-section `C`. Clearly `C` is a convex set iff `δ(· | C)` is a convex
function on `ℝ^n`. -/
lemma convex_iff_convexFunction_indicatorFunction {n : Nat} (C : Set (Fin n → Real)) :
    Convex ℝ C ↔ ConvexFunction (indicatorFunction C) := by
  constructor
  · intro hC
    exact convexFunction_indicator_of_convex (C := C) hC
  · intro hconv
    have hconvOn : ConvexFunctionOn Set.univ (indicatorFunction C) := by
      simpa [ConvexFunction] using hconv
    have hdomconv : Convex ℝ (effectiveDomain Set.univ (indicatorFunction C)) :=
      effectiveDomain_convex (S := Set.univ) (f := indicatorFunction C) hconvOn
    have hdom : effectiveDomain Set.univ (indicatorFunction C) = C :=
      effectiveDomain_indicatorFunction_eq (C := C)
    simpa [hdom] using hdomconv

/-- Defintion 4.8.2: The support function `delta*(· | C)` of a convex set `C` in `R^n`
is defined by `delta*(x | C) = sup {dotProduct x y | y ∈ C}`. -/
noncomputable def supportFunction {n : Nat} (C : Set (Fin n → Real)) :
    (Fin n → Real) → ℝ :=
  fun x => sSup {r : ℝ | ∃ y ∈ C, r = dotProduct x y}

/-- Defintion 4.8.2: The gauge `gamma(· | C)` is defined by
`gamma(x | C) = inf {lambda >= 0 | x ∈ lambda C}`, for `C ≠ ∅`. -/
noncomputable def gaugeFunction {n : Nat} (C : Set (Fin n → Real)) :
    (Fin n → Real) → ℝ :=
  fun x => sInf {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y}

/-- Defintion 4.8.3: The (Euclidean) distance function `d(·, C)` is defined by
`d(x, C) = inf { |x - y| | y ∈ C }`. -/
noncomputable def distanceFunction {n : Nat} (C : Set (Fin n → Real)) :
    (Fin n → Real) → ℝ :=
  fun x => Metric.infDist x C

end Section04
end Chap01
