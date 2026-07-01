/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part6

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise

/-- Text 15.0.14: A metric on `ℝⁿ` is a function `ρ : ℝⁿ × ℝⁿ → ℝ` such that:
(1) `ρ(x, y) > 0` if `x ≠ y`, and `ρ(x, y) = 0` if `x = y`;
(2) `ρ(x, y) = ρ(y, x)` for all `x, y`;
(3) `ρ(x, z) ≤ ρ(x, y) + ρ(y, z)` for all `x, y, z`.

The quantity `ρ(x, y)` is interpreted as the distance between `x` and `y`.

In this development, we use `Fin n → ℝ` for `ℝⁿ`. The usual mathlib notion of a metric space is
`MetricSpace`, and `IsMetricFun ρ` records the book axioms for the distance function `ρ`. -/
def IsMetricFun {n : ℕ} (ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x y, x ≠ y → 0 < ρ x y) ∧
    (∀ x, ρ x x = 0) ∧
      (∀ x y, ρ x y = ρ y x) ∧ ∀ x y z, ρ x z ≤ ρ x y + ρ y z

/-- A metric function vanishes only on the diagonal. -/
lemma eq_of_IsMetricFun_eq_zero {n : ℕ} {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hρ : IsMetricFun ρ) {x y : Fin n → ℝ} (hxy : ρ x y = 0) : x = y := by
  classical
  rcases hρ with ⟨hpos, -, -, -⟩
  by_contra hne
  have hpos' : (0 : ℝ) < ρ x y := hpos x y hne
  simp [hxy] at hpos'

/-- Build a metric space structure from a metric function. -/
lemma exists_metricSpace_of_IsMetricFun {n : ℕ}
    (ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (hρ : IsMetricFun ρ) :
    ∃ ms : MetricSpace (Fin n → ℝ), ms.dist = ρ := by
  classical
  rcases hρ with ⟨hpos, hdiag, hsymm, htri⟩
  refine ⟨{ dist := ρ
            dist_self := hdiag
            dist_comm := hsymm
            dist_triangle := htri
            eq_of_dist_eq_zero := ?_ }, rfl⟩
  intro x y hxy
  exact eq_of_IsMetricFun_eq_zero (ρ := ρ) ⟨hpos, hdiag, hsymm, htri⟩ hxy

/-- A metric space with distance `ρ` satisfies the metric-function axioms. -/
lemma isMetricFun_of_exists_metricSpace {n : ℕ}
    (ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hρ : ∃ ms : MetricSpace (Fin n → ℝ), ms.dist = ρ) : IsMetricFun ρ := by
  rcases hρ with ⟨ms, hdist⟩
  letI : MetricSpace (Fin n → ℝ) := ms
  letI : PseudoMetricSpace (Fin n → ℝ) := ms.toPseudoMetricSpace
  have hdist' : dist = ρ := by
    simpa using hdist
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [← hdist']
    exact (dist_pos).2 hxy
  · intro x
    rw [← hdist']
    exact dist_self x
  · intro x y
    rw [← hdist']
    exact dist_comm x y
  · intro x y z
    rw [← hdist']
    exact dist_triangle x y z

theorem isMetricFun_iff_exists_metricSpace {n : ℕ} (ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    IsMetricFun ρ ↔ ∃ ms : MetricSpace (Fin n → ℝ), ms.dist = ρ := by
  constructor
  · intro hρ
    exact exists_metricSpace_of_IsMetricFun (ρ := ρ) hρ
  · intro hρ
    exact isMetricFun_of_exists_metricSpace (ρ := ρ) hρ

/-- Text 15.0.15: An extreme example of a metric on `ℝⁿ` is the function
`ρ(x, y) = 0` if `x = y` and `ρ(x, y) = 1` if `x ≠ y` (the discrete metric).

This metric has no relation to the algebraic structure of `ℝⁿ`. -/
noncomputable def discreteMetricFun {n : ℕ} : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := by
  classical
  exact fun x y => if x = y then 0 else 1

theorem discreteMetricFun_isMetricFun {n : ℕ} : IsMetricFun (discreteMetricFun (n := n)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    simp [discreteMetricFun, hxy]
  · intro x
    simp [discreteMetricFun]
  · intro x y
    by_cases hxy : x = y <;> simp [discreteMetricFun, hxy, eq_comm]
  · intro x y z
    by_cases hxy : x = y
    · by_cases hyz : y = z
      · subst hxy; subst hyz; simp [discreteMetricFun]
      · subst hxy; simp [discreteMetricFun, hyz]
    · by_cases hyz : y = z
      · subst hyz; simp [discreteMetricFun, hxy]
      · by_cases hxz : x = z
        · subst hxz
          simp [discreteMetricFun, hxy, hyz]
        · simp [discreteMetricFun, hxy, hyz, hxz]

/-- Text 15.0.16: A metric `ρ` on `ℝⁿ` is called a Minkowski metric if it satisfies the metric
axioms and:

- Translation invariance: `ρ (x + z) (y + z) = ρ x y` for all `x, y, z`.
- Segment homogeneity: `ρ x ((1 - λ) • x + λ • y) = λ * ρ x y` for all `x, y` and `λ ∈ [0, 1]`. -/
def IsMinkowskiMetricFun {n : ℕ} (ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  IsMetricFun ρ ∧
    (∀ x y z, ρ (x + z) (y + z) = ρ x y) ∧
      ∀ x y (r : ℝ),
        r ∈ Set.Icc (0 : ℝ) 1 → ρ x ((1 - r) • x + r • y) = r * ρ x y

/-- A real-valued function `k : ℝⁿ → ℝ` is a norm if it is nonnegative, vanishes only at `0`,
satisfies the triangle inequality, and is absolutely homogeneous: `k (r • x) = |r| * k x`. -/
def IsNormFun {n : ℕ} (k : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ k x) ∧
    (∀ x, k x = 0 ↔ x = 0) ∧ (∀ x y, k (x + y) ≤ k x + k y) ∧
      ∀ x (r : ℝ), k (r • x) = |r| * k x

/-- Given a norm function `k`, define the associated distance function `ρ x y := k (x - y)`. -/
def normFunToMinkowskiMetricFun {n : ℕ} (k : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  fun x y => k (x - y)

/-- Given a Minkowski metric `ρ`, define the associated norm function `k x := ρ x 0`. -/
def minkowskiMetricFunToNormFun {n : ℕ} (ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => ρ x 0

/-- Displacement to a convex combination is a scalar multiple of the difference. -/
lemma sub_segment_eq_smul_sub {n : ℕ} (x y : Fin n → ℝ) (r : ℝ) :
    x - ((1 - r) • x + r • y) = r • (x - y) := by
  ext i
  simp
  ring

/-- A norm induces a Minkowski metric via `ρ x y = k (x - y)`. -/
lemma isMinkowskiMetricFun_normFunToMinkowskiMetricFun {n : ℕ} {k : (Fin n → ℝ) → ℝ}
    (hk : IsNormFun k) :
    IsMinkowskiMetricFun (normFunToMinkowskiMetricFun (n := n) k) := by
  rcases hk with ⟨hk_nonneg, hk_zero, hk_triangle, hk_hom⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y hxy
      have hne : x - y ≠ 0 := by
        intro h
        apply hxy
        exact sub_eq_zero.mp h
      have hne' : k (x - y) ≠ 0 := by
        intro h
        have : x - y = 0 := (hk_zero (x - y)).1 h
        exact hne this
      have hle : 0 ≤ k (x - y) := hk_nonneg (x - y)
      have hlt : 0 < k (x - y) := lt_of_le_of_ne hle (Ne.symm hne')
      simpa [normFunToMinkowskiMetricFun] using hlt
    · intro x
      have hzero : k (x - x) = 0 := (hk_zero (x - x)).2 (sub_self x)
      simpa [normFunToMinkowskiMetricFun] using hzero
    · intro x y
      have hxy : x - y = (-1 : ℝ) • (y - x) := by
        ext i
        simp
      calc
        normFunToMinkowskiMetricFun (n := n) k x y = k (x - y) := rfl
        _ = k ((-1 : ℝ) • (y - x)) := by
          rw [hxy]
        _ = |(-1 : ℝ)| * k (y - x) := hk_hom (y - x) (-1)
        _ = k (y - x) := by simp
        _ = normFunToMinkowskiMetricFun (n := n) k y x := rfl
    · intro x y z
      have htri := hk_triangle (x - y) (y - z)
      have hsub : x - z = (x - y) + (y - z) :=
        (sub_add_sub_cancel x y z).symm
      have htri' : k (x - z) ≤ k (x - y) + k (y - z) := by
        rw [hsub]
        exact htri
      simpa [normFunToMinkowskiMetricFun] using htri'
  · intro x y z
    simp [normFunToMinkowskiMetricFun, add_sub_add_right_eq_sub]
  · intro x y r hr
    have hsub : x - ((1 - r) • x + r • y) = r • (x - y) :=
      sub_segment_eq_smul_sub x y r
    have hr0 : 0 ≤ r := hr.1
    calc
      normFunToMinkowskiMetricFun (n := n) k x ((1 - r) • x + r • y)
          = k (x - ((1 - r) • x + r • y)) := rfl
      _ = k (r • (x - y)) := by simp [hsub]
      _ = |r| * k (x - y) := hk_hom (x - y) r
      _ = r * k (x - y) := by simp [abs_of_nonneg hr0]
      _ = r * normFunToMinkowskiMetricFun (n := n) k x y := rfl

/-- For a Minkowski metric, the induced norm is homogeneous on `[0,1]`. -/
lemma minkowskiMetricFunToNormFun_hom_Icc {n : ℕ}
    {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hρ : IsMinkowskiMetricFun ρ) :
    ∀ x r, r ∈ Set.Icc (0 : ℝ) 1 →
      minkowskiMetricFunToNormFun (n := n) ρ (r • x) =
        r * minkowskiMetricFunToNormFun (n := n) ρ x := by
  rcases hρ with ⟨hmetric, _htrans, hseg⟩
  rcases hmetric with ⟨_hpos, _hdiag, hsymm, _htri⟩
  intro x r hr
  have hseg' : ρ 0 (r • x) = r * ρ 0 x := by
    simpa using hseg 0 x r hr
  calc
    minkowskiMetricFunToNormFun (n := n) ρ (r • x) = ρ (r • x) 0 := rfl
    _ = ρ 0 (r • x) := by simpa using (hsymm (r • x) 0)
    _ = r * ρ 0 x := hseg'
    _ = r * ρ x 0 := by simpa using congrArg (fun t => r * t) (hsymm 0 x)
    _ = r * minkowskiMetricFunToNormFun (n := n) ρ x := rfl

/-- The norm induced by a Minkowski metric is even. -/
lemma minkowskiMetricFunToNormFun_neg {n : ℕ}
    {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hρ : IsMinkowskiMetricFun ρ) :
    ∀ x,
      minkowskiMetricFunToNormFun (n := n) ρ (-x) =
        minkowskiMetricFunToNormFun (n := n) ρ x := by
  rcases hρ with ⟨hmetric, htrans, _hseg⟩
  rcases hmetric with ⟨_hpos, _hdiag, hsymm, _htri⟩
  intro x
  have htrans' : ρ 0 x = ρ (-x) 0 := by
    simpa using (htrans (-x) 0 x)
  have hsymm' : ρ 0 x = ρ x 0 := hsymm 0 x
  calc
    minkowskiMetricFunToNormFun (n := n) ρ (-x) = ρ (-x) 0 := rfl
    _ = ρ 0 x := by simpa using htrans'.symm
    _ = ρ x 0 := by simpa using hsymm'
    _ = minkowskiMetricFunToNormFun (n := n) ρ x := rfl

/-- The norm induced by a Minkowski metric is homogeneous for nonnegative scalars. -/
lemma minkowskiMetricFunToNormFun_hom_nonneg {n : ℕ}
    {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hρ : IsMinkowskiMetricFun ρ) :
    ∀ x r, 0 ≤ r →
      minkowskiMetricFunToNormFun (n := n) ρ (r • x) =
        r * minkowskiMetricFunToNormFun (n := n) ρ x := by
  classical
  intro x r hr
  by_cases hle : r ≤ 1
  · exact minkowskiMetricFunToNormFun_hom_Icc (n := n) (ρ := ρ) hρ x r ⟨hr, hle⟩
  · have hrgt : 1 < r := lt_of_not_ge hle
    have hrpos : 0 < r := lt_trans zero_lt_one hrgt
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hIcc : (1 / r) ∈ Set.Icc (0 : ℝ) 1 := by
      have hnonneg : 0 ≤ (1 / r : ℝ) := (one_div_nonneg).2 (le_of_lt hrpos)
      have hle' : (1 / r : ℝ) ≤ 1 :=
        (div_le_one (a := (1 : ℝ)) (b := r) hrpos).2 (le_of_lt hrgt)
      exact ⟨hnonneg, hle'⟩
    have hseg' :
        minkowskiMetricFunToNormFun (n := n) ρ ((1 / r) • (r • x)) =
          (1 / r) * minkowskiMetricFunToNormFun (n := n) ρ (r • x) :=
      minkowskiMetricFunToNormFun_hom_Icc (n := n) (ρ := ρ) hρ (r • x) (1 / r) hIcc
    have hseg'' :
        minkowskiMetricFunToNormFun (n := n) ρ x =
          (1 / r) * minkowskiMetricFunToNormFun (n := n) ρ (r • x) := by
      simpa [smul_smul, one_div, hrne] using hseg'
    have hmul' :
        r * minkowskiMetricFunToNormFun (n := n) ρ x =
          minkowskiMetricFunToNormFun (n := n) ρ (r • x) := by
      have hmul :
          r * minkowskiMetricFunToNormFun (n := n) ρ x =
            r * ((1 / r) * minkowskiMetricFunToNormFun (n := n) ρ (r • x)) := by
        simpa using congrArg (fun t => r * t) hseg''
      simpa [one_div, mul_assoc, hrne] using hmul
    exact hmul'.symm

/-- A Minkowski metric induces a norm via `k x = ρ x 0`. -/
lemma isNormFun_minkowskiMetricFunToNormFun {n : ℕ}
    {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hρ : IsMinkowskiMetricFun ρ) :
    IsNormFun (minkowskiMetricFunToNormFun (n := n) ρ) := by
  classical
  rcases hρ with ⟨hmetric, htrans, hseg⟩
  rcases hmetric with ⟨hpos, hdiag, hsymm, htri⟩
  have hmetric' : IsMetricFun ρ := ⟨hpos, hdiag, hsymm, htri⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx0 : x = 0
    · subst hx0
      simp [minkowskiMetricFunToNormFun, hdiag 0]
    · have hpos' : 0 < ρ x 0 := hpos x 0 (by simpa using hx0)
      exact le_of_lt hpos'
  · intro x
    constructor
    · intro hx
      by_contra hx0
      have hpos' : 0 < ρ x 0 := hpos x 0 (by simpa using hx0)
      have hzero : ρ x 0 = 0 := by simpa [minkowskiMetricFunToNormFun] using hx
      linarith
    · intro hx0
      subst hx0
      simpa [minkowskiMetricFunToNormFun] using hdiag 0
  · intro x z
    have htri' : ρ (x + z) 0 ≤ ρ (x + z) z + ρ z 0 := htri (x + z) z 0
    have htrans' : ρ (x + z) z = ρ x 0 := by
      simpa using htrans x 0 z
    have htri'' : ρ (x + z) 0 ≤ ρ x 0 + ρ z 0 := by
      simpa [htrans'] using htri'
    simpa [minkowskiMetricFunToNormFun] using htri''
  · intro x r
    by_cases hr : 0 ≤ r
    · have hhom :=
        minkowskiMetricFunToNormFun_hom_nonneg (n := n) (ρ := ρ)
          ⟨hmetric', htrans, hseg⟩ x r hr
      simpa [abs_of_nonneg hr] using hhom
    · have hrneg : r < 0 := lt_of_not_ge hr
      have hhom :=
        minkowskiMetricFunToNormFun_hom_nonneg (n := n) (ρ := ρ)
          ⟨hmetric', htrans, hseg⟩ x (-r) (by linarith)
      have hneg_vec : -((-r) • x) = r • x := by
        ext i
        simp
      have hneg :
          minkowskiMetricFunToNormFun (n := n) ρ (r • x) =
            minkowskiMetricFunToNormFun (n := n) ρ ((-r) • x) := by
        have hsymm' :=
          minkowskiMetricFunToNormFun_neg (n := n) (ρ := ρ) ⟨hmetric', htrans, hseg⟩
            ((-r) • x)
        simpa [hneg_vec] using hsymm'
      calc
        minkowskiMetricFunToNormFun (n := n) ρ (r • x) =
            minkowskiMetricFunToNormFun (n := n) ρ ((-r) • x) := hneg
        _ = (-r) * minkowskiMetricFunToNormFun (n := n) ρ x := hhom
        _ = |r| * minkowskiMetricFunToNormFun (n := n) ρ x := by
          simp [abs_of_neg hrneg]

/-- Translation invariance pins down a Minkowski metric by its values at the origin. -/
lemma minkowskiMetricFun_eq_normFunToMinkowskiMetricFun_minkowskiMetricFunToNormFun {n : ℕ}
    {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (htrans : ∀ x y z, ρ (x + z) (y + z) = ρ x y) :
    ∀ x y,
      ρ x y =
        normFunToMinkowskiMetricFun (n := n) (minkowskiMetricFunToNormFun (n := n) ρ) x y := by
  intro x y
  have htrans' : ρ (x - y) 0 = ρ x y := by
    simpa [sub_eq_add_neg] using htrans x y (-y)
  calc
    ρ x y = ρ (x - y) 0 := by simpa using htrans'.symm
    _ = normFunToMinkowskiMetricFun (n := n) (minkowskiMetricFunToNormFun (n := n) ρ) x y :=
      rfl

/-- Text 15.0.17: There is a one-to-one correspondence between Minkowski metrics and norms: if `k`
is a norm then `ρ x y := k (x - y)` is a Minkowski metric, and conversely every Minkowski metric
`ρ` arises uniquely in this way from the norm `k x := ρ x 0`. -/
noncomputable def normFunEquivMinkowskiMetricFun {n : ℕ} :
    {k : (Fin n → ℝ) → ℝ // IsNormFun k} ≃
      {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ // IsMinkowskiMetricFun ρ} := by
  classical
  refine
    { toFun := fun k =>
        ⟨normFunToMinkowskiMetricFun (n := n) k.1, by
          exact isMinkowskiMetricFun_normFunToMinkowskiMetricFun (n := n) (k := k.1) k.2⟩
      invFun := fun ρ =>
        ⟨minkowskiMetricFunToNormFun (n := n) ρ.1, by
          exact isNormFun_minkowskiMetricFunToNormFun (n := n) (ρ := ρ.1) ρ.2⟩
      left_inv := by
        intro k
        ext x
        simp [minkowskiMetricFunToNormFun, normFunToMinkowskiMetricFun]
      right_inv := by
        intro ρ
        ext x y
        have htrans : ∀ x y z, ρ.1 (x + z) (y + z) = ρ.1 x y := ρ.2.2.1
        exact
          (minkowskiMetricFun_eq_normFunToMinkowskiMetricFun_minkowskiMetricFunToNormFun
              (n := n) (ρ := ρ.1) htrans x y).symm }

/-- The gauge of a symmetric closed bounded convex set with `0` in its interior is a norm. -/
lemma isNormFun_gaugeFunction_of_symmClosedBoundedConvex_zeroInterior {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC_symm : ∀ x, x ∈ C ↔ -x ∈ C) (hC_closed : IsClosed C)
    (hC_bdd : Bornology.IsBounded C) (hC_conv : Convex ℝ C)
    (hC0 : (0 : Fin n → ℝ) ∈ interior C) : IsNormFun (gaugeFunction C) := by
  classical
  have hC_symm' : ∀ x, x ∈ C → -x ∈ C := by
    intro x hx
    exact (hC_symm x).1 hx
  have hkgauge :
      IsNormGauge (fun x => (gaugeFunction C x : EReal)) :=
    gaugeFunctionEReal_isNormGauge_of_symmClosedBoundedConvex_zeroInterior
      (C := C) hC_closed hC_conv hC_bdd hC0 hC_symm'
  have hGauge : IsGauge (fun x => (gaugeFunction C x : EReal)) := hkgauge.1
  have hpos : ∀ x, x ≠ 0 → (0 : EReal) < (gaugeFunction C x : EReal) := hkgauge.2.2.2
  have hnonneg : ∀ x, 0 ≤ (gaugeFunction C x : EReal) := hGauge.2.1
  have hzero : (gaugeFunction C (0 : Fin n → ℝ) : EReal) = 0 := hGauge.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have hnonneg' : (0 : EReal) ≤ (gaugeFunction C x : EReal) := hnonneg x
    exact (EReal.coe_le_coe_iff).1 (by simpa using hnonneg')
  · intro x
    constructor
    · intro hx
      by_contra hx0
      have hpos' : (0 : EReal) < (gaugeFunction C x : EReal) := hpos x hx0
      simp [hx] at hpos'
    · intro hx0
      subst hx0
      have hzero' : (gaugeFunction C (0 : Fin n → ℝ) : EReal) = 0 := hzero
      exact_mod_cast hzero'
  · intro x y
    have hle :
        (gaugeFunction C (x + y) : EReal) ≤
          (gaugeFunction C x : EReal) + (gaugeFunction C y : EReal) :=
      IsGauge.add_le (k := fun z => (gaugeFunction C z : EReal)) hGauge x y
    have hle' :
        (gaugeFunction C (x + y) : EReal) ≤
          ((gaugeFunction C x + gaugeFunction C y : ℝ) : EReal) := by
      simpa [EReal.coe_add, add_comm, add_left_comm, add_assoc] using hle
    exact (EReal.coe_le_coe_iff).1 hle'
  · intro x r
    have hhom' :
        (gaugeFunction C (r • x) : EReal) =
          ((|r| : ℝ) : EReal) * (gaugeFunction C x : EReal) :=
      IsNormGauge.smul_eq_abs hkgauge x r
    have hhom'' :
        (gaugeFunction C (r • x) : EReal) =
          ((|r| * gaugeFunction C x : ℝ) : EReal) := by
      simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hhom'
    exact_mod_cast hhom''

/-- The gauge of a closed convex set with `0` in its interior has unit sublevel set `C`. -/
lemma gaugeFunction_unitBall_eq {n : ℕ} {C : Set (Fin n → ℝ)} (hC_closed : IsClosed C)
    (hC_conv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ interior C) :
    {x : Fin n → ℝ | gaugeFunction C x ≤ (1 : ℝ)} = C := by
  have hC0mem : (0 : Fin n → ℝ) ∈ C := interior_subset hC0
  have hCabs :
      ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C :=
    absorbing_of_zero_mem_interior (C := C) hC_conv hC0
  have hset :
      C = {x : Fin n → ℝ | (gaugeFunction C x : EReal) ≤ (1 : EReal)} :=
    set_eq_gaugeFunction_sublevel_one (n := n) (D := C) hC_closed hC_conv hC0mem hCabs
  ext x; constructor
  · intro hx
    have hx' : (gaugeFunction C x : EReal) ≤ (1 : EReal) := (EReal.coe_le_coe_iff).2 hx
    rw [hset]
    exact hx'
  · intro hx
    have hx' := hx
    rw [hset] at hx'
    have hx'' : (gaugeFunction C x : EReal) ≤ (1 : EReal) := by
      simpa using hx'
    exact (EReal.coe_le_coe_iff).1 hx''

/-- Metric balls from a norm are translates of scaled unit balls. -/
lemma ball_eq_image_add_smul_of_normFun_unitBall {n : ℕ} {k : (Fin n → ℝ) → ℝ}
    {C : Set (Fin n → ℝ)} (hk : IsNormFun k) (hC : {x : Fin n → ℝ | k x ≤ 1} = C) :
    ∀ x : Fin n → ℝ, ∀ ε : ℝ, 0 < ε →
      {y | normFunToMinkowskiMetricFun (n := n) k x y ≤ ε} = (fun c => x + ε • c) '' C := by
  classical
  rcases hk with ⟨_hk_nonneg, _hk_zero, _hk_triangle, hk_hom⟩
  have hCmem : ∀ c, c ∈ C ↔ k c ≤ 1 := by
    intro c
    constructor
    · intro hc
      have hc' : c ∈ {x : Fin n → ℝ | k x ≤ 1} := by simpa [hC] using hc
      simpa using hc'
    · intro hc
      have hc' : c ∈ {x : Fin n → ℝ | k x ≤ 1} := by simpa using hc
      simpa [hC] using hc'
  intro x ε hε
  ext y; constructor
  · intro hy
    have hxy : x - y = (-1 : ℝ) • (y - x) := by
      ext i
      simp
    have hy' : k (y - x) ≤ ε := by
      have hsymm' : k (x - y) = k (y - x) := by
        calc
          k (x - y) = k ((-1 : ℝ) • (y - x)) := by rw [hxy]
          _ = |(-1 : ℝ)| * k (y - x) := hk_hom (y - x) (-1)
          _ = k (y - x) := by simp
      simpa [normFunToMinkowskiMetricFun, hsymm'] using hy
    have hεne : ε ≠ 0 := ne_of_gt hε
    set c : Fin n → ℝ := (1 / ε) • (y - x)
    have hc_le : k c ≤ 1 := by
      have hnonneg : 0 ≤ (1 / ε : ℝ) := one_div_nonneg.mpr (le_of_lt hε)
      have hkc : k c = (1 / ε) * k (y - x) := by
        calc
          k c = |(1 / ε : ℝ)| * k (y - x) := by
            simpa [c] using hk_hom (y - x) (1 / ε)
          _ = (1 / ε) * k (y - x) := by
            have habs : |(1 / ε : ℝ)| = (1 / ε : ℝ) := abs_of_nonneg hnonneg
            rw [habs]
      have hmul : (1 / ε) * k (y - x) ≤ (1 / ε) * ε :=
        mul_le_mul_of_nonneg_left hy' hnonneg
      have hmul' : (1 / ε) * k (y - x) ≤ 1 := by
        have h1 : (ε : ℝ)⁻¹ * ε = 1 := inv_mul_cancel₀ hεne
        simpa [one_div, h1] using hmul
      simpa [hkc] using hmul'
    have hcC : c ∈ C := (hCmem c).2 hc_le
    have hscale : ε • c = y - x := by
      calc
        ε • c = ε • ((1 / ε) • (y - x)) := rfl
        _ = (ε * (1 / ε)) • (y - x) := by simp [smul_smul]
        _ = (1 : ℝ) • (y - x) := by field_simp [hεne]
        _ = y - x := by simp
    have hyx : y = x + ε • c := by
      calc
        y = x + (y - x) := by abel
        _ = x + ε • c := by simp [hscale]
    exact ⟨c, hcC, hyx.symm⟩
  · rintro ⟨c, hcC, rfl⟩
    have hc_le : k c ≤ 1 := (hCmem c).1 hcC
    have hsub : x - (x + ε • c) = (-ε) • c := by
      ext i
      simp
    have hεnonneg : 0 ≤ ε := le_of_lt hε
    calc
      normFunToMinkowskiMetricFun (n := n) k x (x + ε • c) = k (x - (x + ε • c)) := rfl
      _ = k ((-ε) • c) := by simp [hsub]
      _ = |(-ε)| * k c := hk_hom c (-ε)
      _ = |ε| * k c := by simp
      _ = ε * k c := by simp [abs_of_pos hε]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hc_le hεnonneg
      _ = ε := by ring

/-- The induced norm of a Minkowski metric with prescribed balls is the gauge of `C`. -/
lemma minkowskiMetricFunToNormFun_eq_gaugeFunction_of_ball_property {n : ℕ}
    {C : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hρ : IsMinkowskiMetricFun ρ)
    (hball : ∀ ε : ℝ, 0 < ε → {y | ρ 0 y ≤ ε} = (fun c => ε • c) '' C) :
    ∀ x, minkowskiMetricFunToNormFun (n := n) ρ x = gaugeFunction C x := by
  classical
  rcases hρ with ⟨hmetric, _htrans, _hseg⟩
  rcases hmetric with ⟨hpos, hdiag, hsymm, _htri⟩
  have hC0 : (0 : Fin n → ℝ) ∈ C := by
    have hball1 := hball 1 (by norm_num)
    have hmem0 : (0 : Fin n → ℝ) ∈ {y | ρ 0 y ≤ (1 : ℝ)} := by
      have h0 : ρ 0 (0 : Fin n → ℝ) = 0 := hdiag 0
      simp [h0]
    have hmem0' : (0 : Fin n → ℝ) ∈ (fun c => (1 : ℝ) • c) '' C := by
      simpa [hball1] using hmem0
    rcases hmem0' with ⟨c, hcC, hc0⟩
    have hc0' : c = (0 : Fin n → ℝ) := by
      simpa using hc0
    simpa [hc0'] using hcC
  intro x
  let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y}
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hS_nonempty : S.Nonempty := by
    have hnonneg : 0 ≤ ρ 0 x := by
      by_cases hx : x = 0
      · subst hx
        simp [hdiag 0]
      · exact le_of_lt (hpos 0 x (by simpa [eq_comm] using hx))
    have hpos' : 0 < ρ 0 x + 1 := by linarith
    have hxmem : x ∈ {y | ρ 0 y ≤ ρ 0 x + 1} := by
      change ρ 0 x ≤ ρ 0 x + 1
      linarith
    have hxmem' : x ∈ (fun c => (ρ 0 x + 1) • c) '' C := by
      simpa [hball (ρ 0 x + 1) hpos'] using hxmem
    rcases hxmem' with ⟨y, hyC, hxy⟩
    refine ⟨ρ 0 x + 1, ?_, y, hyC, ?_⟩
    · linarith
    · simpa using hxy.symm
  have hle : gaugeFunction C x ≤ ρ 0 x := by
    have hnonneg : 0 ≤ ρ 0 x := by
      by_cases hx : x = 0
      · subst hx
        simp [hdiag 0]
      · exact le_of_lt (hpos 0 x (by simpa [eq_comm] using hx))
    have hmem : ρ 0 x ∈ S := by
      by_cases hx : x = 0
      · subst hx
        refine ⟨hnonneg, 0, hC0, ?_⟩
        simp
      · have hpos' : 0 < ρ 0 x := hpos 0 x (by simpa [eq_comm] using hx)
        have hxmem : x ∈ {y | ρ 0 y ≤ ρ 0 x} := by
          change ρ 0 x ≤ ρ 0 x
          exact le_rfl
        have hxmem' : x ∈ (fun c => (ρ 0 x) • c) '' C := by
          simpa [hball (ρ 0 x) hpos'] using hxmem
        rcases hxmem' with ⟨y, hyC, hxy⟩
        exact ⟨hnonneg, y, hyC, by simpa using hxy.symm⟩
    have hle' : sInf S ≤ ρ 0 x := csInf_le hS_bdd hmem
    simpa [gaugeFunction, S] using hle'
  have hge : ρ 0 x ≤ gaugeFunction C x := by
    have hbound : ∀ r ∈ S, ρ 0 x ≤ r := by
      intro r hr
      rcases hr with ⟨hr0, y, hyC, hxy⟩
      by_cases hrpos : r = 0
      · subst hrpos
        have hx0 : x = 0 := by simpa using hxy
        subst hx0
        simp [hdiag 0]
      · have hrpos' : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrpos)
        have hxmem : x ∈ (fun c => r • c) '' C := ⟨y, hyC, by simpa using hxy.symm⟩
        have hxmem' : x ∈ {y | ρ 0 y ≤ r} := by
          simpa [hball r hrpos'] using hxmem
        exact hxmem'
    have hge' : ρ 0 x ≤ sInf S := le_csInf hS_nonempty hbound
    simpa [gaugeFunction, S] using hge'
  have hEq : ρ 0 x = gaugeFunction C x := le_antisymm hge hle
  calc
    minkowskiMetricFunToNormFun (n := n) ρ x = ρ x 0 := rfl
    _ = ρ 0 x := by simpa using hsymm x 0
    _ = gaugeFunction C x := hEq

/-- Text 15.0.18: If `C` is a symmetric closed bounded convex set such that `0 ∈ interior C`, then
there is a unique Minkowski metric `ρ` such that the `ρ`-ball of radius `ε > 0` around `x` is
`x + ε C`, i.e.
`{y | ρ x y ≤ ε} = {x + ε • c | c ∈ C}`. -/
theorem existsUnique_minkowskiMetricFun_ball_eq_image_add_smul {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_symm : ∀ x, x ∈ C ↔ -x ∈ C) (hC_closed : IsClosed C) (hC_bdd : Bornology.IsBounded C)
    (hC_conv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ interior C) :
    ∃! ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ,
      IsMinkowskiMetricFun ρ ∧
        ∀ x : Fin n → ℝ,
          ∀ ε : ℝ, 0 < ε → {y | ρ x y ≤ ε} = (fun c => x + ε • c) '' C := by
  classical
  have hk :
      IsNormFun (gaugeFunction C) :=
    isNormFun_gaugeFunction_of_symmClosedBoundedConvex_zeroInterior
      (n := n) (C := C) hC_symm hC_closed hC_bdd hC_conv hC0
  let ρ0 : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    normFunToMinkowskiMetricFun (n := n) (gaugeFunction C)
  refine ⟨ρ0, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact isMinkowskiMetricFun_normFunToMinkowskiMetricFun (n := n) (k := gaugeFunction C) hk
    · intro x ε hε
      have hunit :
          {x : Fin n → ℝ | gaugeFunction C x ≤ (1 : ℝ)} = C :=
        gaugeFunction_unitBall_eq (n := n) (C := C) hC_closed hC_conv hC0
      simpa [ρ0] using
        (ball_eq_image_add_smul_of_normFun_unitBall (n := n) (k := gaugeFunction C) (C := C) hk
          hunit x ε hε)
  · intro ρ hρ
    rcases hρ with ⟨hρ_mink, hρ_ball⟩
    have hball0 : ∀ ε : ℝ, 0 < ε → {y | ρ 0 y ≤ ε} = (fun c => ε • c) '' C := by
      intro ε hε
      simpa using (hρ_ball 0 ε hε)
    have hnorm_eq :
        ∀ x, minkowskiMetricFunToNormFun (n := n) ρ x = gaugeFunction C x :=
      minkowskiMetricFunToNormFun_eq_gaugeFunction_of_ball_property
        (n := n) (C := C) (ρ := ρ) hρ_mink hball0
    have htrans : ∀ x y z, ρ (x + z) (y + z) = ρ x y := hρ_mink.2.1
    have hnorm_fun : minkowskiMetricFunToNormFun (n := n) ρ = gaugeFunction C := by
      funext x
      exact hnorm_eq x
    ext x y
    calc
      ρ x y =
          normFunToMinkowskiMetricFun (n := n)
            (minkowskiMetricFunToNormFun (n := n) ρ) x y :=
        minkowskiMetricFun_eq_normFunToMinkowskiMetricFun_minkowskiMetricFunToNormFun
          (n := n) (ρ := ρ) htrans x y
      _ = normFunToMinkowskiMetricFun (n := n) (gaugeFunction C) x y := by
        simp [hnorm_fun]
      _ = ρ0 x y := by simp [ρ0]

/-- A distance function `d : α → α → ℝ` defines a notion of "open set" by the usual metric-ball
criterion: `s` is open if for every `x ∈ s` there exists `ε > 0` such that `d x y < ε` implies
`y ∈ s`. -/
def IsOpenOfDistFun {α : Type*} (d : α → α → ℝ) (s : Set α) : Prop :=
  ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ y, d x y < ε → y ∈ s

def IsClosedOfDistFun {α : Type*} (d : α → α → ℝ) (s : Set α) : Prop :=
  IsOpenOfDistFun d sᶜ

/-- A sequence `u : ℕ → α` is Cauchy with respect to `d` if for every `ε > 0` there exists `N`
such that `d (u m) (u n) < ε` for all `m,n ≥ N`. -/
def CauchySeqOfDistFun {α : Type*} (d : α → α → ℝ) (u : ℕ → α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → d (u m) (u n) < ε

/-- Euclidean distance on `ℝⁿ` (modeled as `Fin n → ℝ`), defined by
`d(x,y) = ‖x - y‖₂ = sqrt (dotProduct (x - y) (x - y))`.

We use a `pi`-prefixed name to avoid clashing with mathlib's `euclideanDist`. -/
noncomputable def piEuclideanDist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct (x - y) (x - y))


end Section15
end Chap03
