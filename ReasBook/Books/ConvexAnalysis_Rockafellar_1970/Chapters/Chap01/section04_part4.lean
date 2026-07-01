/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xuran Sun, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part3

open Matrix
open scoped BigOperators
open scoped Topology

section Chap01
section Section04
open scoped BigOperators

/-- First derivative of the coordinate product along a line at `0`. -/
lemma negGeomMean_prod_deriv_at0 {n : Nat} {x z : Fin n → Real} (hx : ∀ i, x i ≠ 0) :
    let P : ℝ → ℝ := fun t => Finset.univ.prod (fun i => x i + t * z i)
    deriv P 0 = (Finset.univ.prod (fun i => x i)) * Finset.univ.sum (fun i => z i / x i) := by
  classical
  dsimp
  have hderiv_linear : ∀ i, deriv (fun t => x i + t * z i) 0 = z i := by
    intro i
    calc
      deriv (fun t => x i + t * z i) 0 =
          deriv (fun t => t * z i) 0 := by
            simp
      _ = z i := by
            simp
  have hdiff :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ (fun t => x i + t * z i) 0 := by
    intro i hi
    simp
  have hderiv :
      deriv (fun t => Finset.univ.prod (fun i => x i + t * z i)) 0 =
        ∑ i, (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j)) * z i := by
    simpa [smul_eq_mul, hderiv_linear, Finset.prod_fn] using
      (deriv_finset_prod (u := (Finset.univ : Finset (Fin n)))
        (f := fun i t => x i + t * z i) (x := 0) hdiff)
  have hprod_erase :
      ∀ i, (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j)) =
        (Finset.univ.prod (fun j => x j)) / x i := by
    intro i
    have hx_i : x i ≠ 0 := hx i
    have hmul :
        x i * (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j)) =
          Finset.univ.prod (fun j => x j) := by
      simpa using
        (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
          (f := fun j => x j) (a := i) (h := Finset.mem_univ i))
    field_simp [hx_i]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    deriv (fun t => Finset.univ.prod (fun i => x i + t * z i)) 0 =
        ∑ i, (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j)) * z i := hderiv
    _ = ∑ i, ((Finset.univ.prod (fun j => x j)) / x i) * z i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hprod_erase i]
    _ = ∑ i, (Finset.univ.prod (fun j => x j)) * (z i / x i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hstep :
              (Finset.univ.prod (fun j => x j) / x i) * z i =
                (Finset.univ.prod (fun j => x j) * z i) / x i := by
            simpa using
              (div_mul_eq_mul_div₀ (Finset.univ.prod (fun j => x j)) (z i) (x i))
          calc
            (Finset.univ.prod (fun j => x j) / x i) * z i =
                (Finset.univ.prod (fun j => x j) * z i) / x i := hstep
            _ = (Finset.univ.prod (fun j => x j)) * (z i / x i) := by
                  simp [mul_div_assoc]
    _ = (Finset.univ.prod (fun j => x j)) * Finset.univ.sum (fun i => z i / x i) := by
          simp [Finset.mul_sum]

/-- Second derivative of the coordinate product along a line at `0`. -/
lemma negGeomMean_prod_second_deriv_at0 {n : Nat} {x z : Fin n → Real} (hx : ∀ i, x i ≠ 0) :
    let P : ℝ → ℝ := fun t => Finset.univ.prod (fun i => x i + t * z i)
    deriv (deriv P) 0 =
      (Finset.univ.prod (fun i => x i)) *
        ((Finset.univ.sum (fun i => z i / x i)) ^ 2 -
          Finset.univ.sum (fun i => (z i / x i) ^ 2)) := by
  classical
  dsimp
  set u : Fin n → Real := fun i => z i / x i
  have hderiv_t :
      (fun t => deriv (fun s => Finset.univ.prod (fun i => x i + s * z i)) t) =
        fun t =>
          ∑ i, (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i := by
    funext t
    have hdiff :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          DifferentiableAt ℝ (fun s => x i + s * z i) t := by
      intro i hi
      simp
    simpa [smul_eq_mul, Finset.prod_fn] using
      (deriv_finset_prod (u := (Finset.univ : Finset (Fin n)))
        (f := fun i s => x i + s * z i) (x := t) hdiff)
  have hderiv_prod :
      ∀ i,
        deriv (fun t => Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) 0 =
          Finset.sum (s := (Finset.univ.erase i)) (fun j =>
            (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j) := by
    intro i
    have hdiff :
        ∀ j ∈ (Finset.univ.erase i),
          DifferentiableAt ℝ (fun t => x j + t * z j) 0 := by
      intro j hj
      simp
    simpa [smul_eq_mul, Finset.prod_fn] using
      (deriv_finset_prod (u := (Finset.univ.erase i))
        (f := fun j t => x j + t * z j) (x := 0) hdiff)
  have hdiff_sum :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ
          (fun t =>
            (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i) 0 := by
    intro i hi
    have hdiff_prod :
        DifferentiableAt ℝ
          (fun t => Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) 0 := by
      simpa [Finset.prod_fn] using
        (DifferentiableAt.finset_prod (u := (Finset.univ.erase i))
          (f := fun j t => x j + t * z j) (x := 0) (by
            intro j hj
            simp
          ))
    simpa using hdiff_prod.mul_const (z i)
  have hderiv2 :
      deriv (deriv (fun t => Finset.univ.prod (fun i => x i + t * z i))) 0 =
        ∑ i, deriv (fun t =>
          (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i) 0 := by
    simpa [hderiv_t, Finset.sum_fn] using
      (deriv_sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun i t =>
          (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i)
        (x := 0) hdiff_sum)
  have hderiv2' :
      deriv (deriv (fun t => Finset.univ.prod (fun i => x i + t * z i))) 0 =
        ∑ i,
          (deriv
              (fun t =>
                Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) 0) *
            z i := by
    refine hderiv2.trans ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp
  have hderiv2'' :
      deriv (deriv (fun t => Finset.univ.prod (fun i => x i + t * z i))) 0 =
        ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
          (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j * z i)) := by
    calc
      deriv (deriv (fun t => Finset.univ.prod (fun i => x i + t * z i))) 0 =
          ∑ i,
            (deriv
                (fun t =>
                  Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) 0) *
              z i := hderiv2'
      _ =
          ∑ i,
            (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
                (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j)) *
              z i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hderiv_prod i]
      _ =
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
            (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j * z i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (Finset.sum_mul (s := (Finset.univ.erase i))
                  (f := fun j =>
                    (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j)
                  (a := z i))
  have hrewrite :
      ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
        (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j * z i)) =
        ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
          (Finset.univ.prod (fun k => x k)) * (z i / x i) * (z j / x j))) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hprod :
        (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) =
          (Finset.univ.prod (fun k => x k)) / x i / x j :=
      prod_erase_erase_eq_div (x := x) (hx := hx) (i := i) (j := j) hj
    calc
      (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j * z i =
          ((Finset.univ.prod (fun k => x k)) / x i / x j) * z j * z i := by
            simp [hprod]
      _ = (Finset.univ.prod (fun k => x k)) * (z i / x i) * (z j / x j) := by
            simp [div_eq_mul_inv]
            ring_nf
  have hfactor :
      ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
        (Finset.univ.prod (fun k => x k)) * (z i / x i) * (z j / x j))) =
        (Finset.univ.prod (fun k => x k)) *
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := by
    have hrewrite' :
        ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
          (Finset.univ.prod (fun k => x k)) * (z i / x i) * (z j / x j))) =
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
            (Finset.univ.prod (fun k => x k)) * u i * u j)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [u, mul_comm, mul_left_comm]
    have hfactor' :
        (Finset.univ.prod (fun k => x k)) *
            ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
            (Finset.univ.prod (fun k => x k)) * u i * u j)) := by
      have houter :
          (Finset.univ.prod (fun k => x k)) *
              ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
            ∑ i, (Finset.univ.prod (fun k => x k)) *
              (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := by
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun i => Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j))
            (a := Finset.univ.prod (fun k => x k)))
      have hinner :
          ∀ i,
            (Finset.univ.prod (fun k => x k)) *
                (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
              Finset.sum (s := (Finset.univ.erase i)) (fun j =>
                (Finset.univ.prod (fun k => x k)) * u i * u j) := by
        intro i
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (Finset.mul_sum (s := (Finset.univ.erase i)) (f := fun j => u i * u j)
            (a := Finset.univ.prod (fun k => x k)))
      calc
        (Finset.univ.prod (fun k => x k)) *
            ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
            ∑ i, (Finset.univ.prod (fun k => x k)) *
              (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := houter
        _ =
            ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
              (Finset.univ.prod (fun k => x k)) * u i * u j)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hinner i
    calc
      ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
          (Finset.univ.prod (fun k => x k)) * (z i / x i) * (z j / x j))) =
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
            (Finset.univ.prod (fun k => x k)) * u i * u j)) := hrewrite'
      _ = (Finset.univ.prod (fun k => x k)) *
            ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := by
          simpa using hfactor'.symm
  have hsum :
      ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
        (Finset.univ.sum u) ^ 2 - Finset.univ.sum (fun i => (u i) ^ 2) :=
    sum_erase_mul_sum_eq_sum_sq_sub_sum_sq (u := u)
  calc
    deriv (deriv (fun t => Finset.univ.prod (fun i => x i + t * z i))) 0 =
        ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
          (Finset.prod (s := ((Finset.univ.erase i).erase j)) (fun k => x k)) * z j * z i)) :=
          hderiv2''
    _ =
        ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j =>
          (Finset.univ.prod (fun k => x k)) * (z i / x i) * (z j / x j))) := hrewrite
    _ =
        (Finset.univ.prod (fun k => x k)) *
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := hfactor
    _ =
        (Finset.univ.prod (fun i => x i)) *
          ((Finset.univ.sum u) ^ 2 - Finset.univ.sum (fun i => (u i) ^ 2)) := by
          rw [hsum]
    _ = (Finset.univ.prod (fun i => x i)) *
          ((Finset.univ.sum (fun i => z i / x i)) ^ 2 -
            Finset.univ.sum (fun i => (z i / x i) ^ 2)) := by
          simp [u]

/-- The negative geometric mean is continuous on the nonnegative orthant. -/
lemma continuousOn_negGeomMean_nonneg {n : Nat} :
    ContinuousOn (fun x : Fin n → Real =>
      -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))))
      {x | ∀ i, 0 ≤ x i} := by
  classical
  have hprod :
      ContinuousOn (fun x : Fin n → Real => Finset.univ.prod (fun i => x i))
        {x | ∀ i, 0 ≤ x i} :=
    (contDiffOn_prod_coord (C := {x | ∀ i, 0 ≤ x i})).continuousOn
  have hpow_nonneg : 0 ≤ (1 / (n : Real)) := by
    have hn : 0 ≤ (n : Real) := by exact_mod_cast (Nat.zero_le n)
    exact div_nonneg (by norm_num) hn
  have hpow :
      ContinuousOn (fun x : Fin n → Real =>
        (Finset.univ.prod (fun i => x i)) ^ (1 / (n : Real)))
        {x | ∀ i, 0 ≤ x i} :=
    ContinuousOn.rpow_const (p := (1 / (n : Real))) hprod (by
      intro x hx
      exact Or.inr hpow_nonneg)
  simpa using hpow.neg

/-- The line product is nonzero near `0` when the base point is positive. -/
lemma prod_line_ne_zero_eventually {n : Nat} {x z : Fin n → Real} (hx : ∀ i, 0 < x i) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (Finset.univ.prod (fun i => x i + t * z i)) ≠ 0 := by
  classical
  have hpos_each : ∀ i : Fin n, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < x i + t * z i := by
    intro i
    have hcont : ContinuousAt (fun t : ℝ => x i + t * z i) 0 := by
      simpa using (continuousAt_const.add (continuousAt_id.mul_const (z i)))
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (x i + 0 * z i) := by
      simpa using (Ioi_mem_nhds (hx i))
    exact hcont.tendsto.eventually hmem
  have hpos_all : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < x i + t * z i :=
    (Filter.eventually_all).2 hpos_each
  refine hpos_all.mono ?_
  intro t ht
  have hprod_pos : 0 < Finset.univ.prod (fun i => x i + t * z i) := by
    refine Finset.prod_pos ?_
    intro i hi
    exact ht i
  exact ne_of_gt hprod_pos

/-- The derivative of the line product is differentiable at `0`. -/
lemma deriv_line_prod_differentiable_at0 {n : Nat} {x z : Fin n → Real} :
    DifferentiableAt ℝ
      (fun t => deriv (fun s => Finset.univ.prod (fun i => x i + s * z i)) t) 0 := by
  classical
  have hderiv :
      (fun t => deriv (fun s => Finset.univ.prod (fun i => x i + s * z i)) t) =
        fun t =>
          ∑ i, (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i := by
    funext t
    have hdiff :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          DifferentiableAt ℝ (fun s => x i + s * z i) t := by
      intro i hi
      simp
    simpa [smul_eq_mul, Finset.prod_fn] using
      (deriv_finset_prod (u := (Finset.univ : Finset (Fin n)))
        (f := fun i s => x i + s * z i) (x := t) hdiff)
  have hdiff_term :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ
          (fun t =>
            (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i) 0 := by
    intro i hi
    have hdiff_prod :
        DifferentiableAt ℝ
          (fun t => Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) 0 := by
      simpa [Finset.prod_fn] using
        (DifferentiableAt.finset_prod (u := (Finset.univ.erase i))
          (f := fun j t => x j + t * z j) (x := 0) (by
            intro j hj
            simp
          ))
    simpa using hdiff_prod.mul_const (z i)
  have hdiff_sum :
      DifferentiableAt ℝ (fun t =>
        Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun i =>
          (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i)) 0 := by
    have hdiff_sum' :
        DifferentiableAt ℝ
          (∑ i, fun t =>
            (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i) 0 := by
      refine (DifferentiableAt.sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun i t =>
          (Finset.prod (s := (Finset.univ.erase i)) (fun j => x j + t * z j)) * z i) (x := 0) ?_)
      intro i hi
      exact hdiff_term i hi
    simpa [Finset.sum_fn] using hdiff_sum'
  simpa [hderiv] using hdiff_sum

/-- Second derivative of `t ↦ (P t)^a` at `0` under a local nonzero hypothesis. -/
lemma line_rpow_second_deriv_at0 {P : ℝ → ℝ} {a : ℝ}
    (hP0 : P 0 ≠ 0)
    (hP_diff : ∀ᶠ t in 𝓝 0, DifferentiableAt ℝ P t)
    (hP_near : ∀ᶠ t in 𝓝 0, P t ≠ 0)
    (hP0_diff : DifferentiableAt ℝ P 0)
    (hP' : DifferentiableAt ℝ (deriv P) 0) :
    deriv (deriv (fun t => (P t) ^ a)) 0 =
      a * (a - 1) * (P 0) ^ (a - 1 - 1) * (deriv P 0) ^ 2 +
        a * (P 0) ^ (a - 1) * deriv (deriv P) 0 := by
  have hEq :
      (fun t => deriv (fun s => (P s) ^ a) t) =ᶠ[𝓝 0]
        fun t => deriv P t * a * (P t) ^ (a - 1) := by
    refine (hP_diff.and hP_near).mono ?_
    intro t ht
    have hdiff : DifferentiableAt ℝ P t := ht.1
    have hne : P t ≠ 0 := ht.2
    simpa using
      (deriv_rpow_const (f := P) (x := t) (p := a) hdiff (Or.inl hne))
  have hderiv_eq :
      deriv (fun t => deriv (fun s => (P s) ^ a) t) 0 =
        deriv (fun t => deriv P t * a * (P t) ^ (a - 1)) 0 :=
    Filter.EventuallyEq.deriv_eq hEq
  have hdiff_rpow_a1 : DifferentiableAt ℝ (fun t => (P t) ^ (a - 1)) 0 :=
    hP0_diff.rpow_const (Or.inl hP0)
  have hderiv_rpow_a1 :
      deriv (fun t => (P t) ^ (a - 1)) 0 =
        deriv P 0 * (a - 1) * (P 0) ^ (a - 1 - 1) := by
    simpa using
      (deriv_rpow_const (f := P) (x := 0) (p := a - 1) hP0_diff (Or.inl hP0))
  have hdiff_mul :
      DifferentiableAt ℝ (fun t => deriv P t * (P t) ^ (a - 1)) 0 :=
    hP'.mul hdiff_rpow_a1
  have hderiv_mul :
      deriv (fun t => deriv P t * (P t) ^ (a - 1)) 0 =
        deriv (deriv P) 0 * (P 0) ^ (a - 1) +
          deriv P 0 * deriv (fun t => (P t) ^ (a - 1)) 0 := by
    simpa using
      (deriv_mul (c := fun t => deriv P t) (d := fun t => (P t) ^ (a - 1))
        (x := 0) hP' hdiff_rpow_a1)
  have hderiv_const :
      deriv (fun t => deriv P t * a * (P t) ^ (a - 1)) 0 =
        a * deriv (fun t => deriv P t * (P t) ^ (a - 1)) 0 := by
    have hderiv_const' :
        deriv (fun t => a * (deriv P t * (P t) ^ (a - 1))) 0 =
          a * deriv (fun t => deriv P t * (P t) ^ (a - 1)) 0 :=
      deriv_const_mul (c := a) (d := fun t => deriv P t * (P t) ^ (a - 1)) (x := 0) hdiff_mul
    simp [mul_comm, mul_assoc, hderiv_const']
  calc
    deriv (deriv (fun t => (P t) ^ a)) 0
        = deriv (fun t => deriv P t * a * (P t) ^ (a - 1)) 0 := hderiv_eq
    _ = a * (deriv (deriv P) 0 * (P 0) ^ (a - 1) +
            deriv P 0 * deriv (fun t => (P t) ^ (a - 1)) 0) := by
          simp [hderiv_const, hderiv_mul]
    _ = a * (a - 1) * (P 0) ^ (a - 1 - 1) * (deriv P 0) ^ 2 +
          a * (P 0) ^ (a - 1) * deriv (deriv P) 0 := by
          simp [hderiv_rpow_a1, pow_two, mul_comm, mul_left_comm, mul_assoc]
          ring

/-- Second derivative of the negative geometric mean along a line. -/
lemma negGeomMean_line_second_deriv {n : Nat} (hn : n ≠ 0) {x z : Fin n → Real}
    (hx : ∀ i, 0 < x i) :
    let g : (Fin n → Real) → Real :=
      fun x => -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))
    deriv (deriv (fun t : ℝ => g (x + t • z))) 0 =
      (1 / (n : Real)) ^ 2 * g x *
        ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
  classical
  let g : (Fin n → Real) → Real :=
    fun x => -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))
  let P : ℝ → ℝ := fun t => Finset.univ.prod (fun i => x i + t * z i)
  have hx_ne : ∀ i, x i ≠ 0 := fun i => ne_of_gt (hx i)
  have hP0 : P 0 ≠ 0 := by
    simpa [P] using (prod_ne_zero_of_pos (x := x) hx)
  have hP_diff : ∀ᶠ t in 𝓝 0, DifferentiableAt ℝ P t := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have hdiff :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          DifferentiableAt ℝ (fun s => x i + s * z i) t := by
      intro i hi
      simp
    simpa [P, Finset.prod_fn] using
      (DifferentiableAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
        (f := fun i s => x i + s * z i) (x := t) hdiff)
  have hP_near : ∀ᶠ t in 𝓝 0, P t ≠ 0 := by
    simpa [P] using (prod_line_ne_zero_eventually (x := x) (z := z) hx)
  have hP0_diff : DifferentiableAt ℝ P 0 := by
    have hdiff :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          DifferentiableAt ℝ (fun s => x i + s * z i) 0 := by
      intro i hi
      simp
    simpa [P, Finset.prod_fn] using
      (DifferentiableAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
        (f := fun i s => x i + s * z i) (x := 0) hdiff)
  have hP' : DifferentiableAt ℝ (deriv P) 0 := by
    simpa [P] using (deriv_line_prod_differentiable_at0 (x := x) (z := z))
  have hline_rpow :
      deriv (deriv (fun t => (P t) ^ (1 / (n : Real)))) 0 =
        (1 / (n : Real)) * ((1 / (n : Real)) - 1) *
              (P 0) ^ ((1 / (n : Real)) - 1 - 1) *
              (deriv P 0) ^ 2 +
          (1 / (n : Real)) * (P 0) ^ ((1 / (n : Real)) - 1) * deriv (deriv P) 0 := by
    simpa using
      (line_rpow_second_deriv_at0 (P := P) (a := (1 / (n : Real))) hP0 hP_diff hP_near hP0_diff hP')
  have hneg :
      deriv (deriv (fun t => -(P t) ^ (1 / (n : Real)))) 0 =
        - deriv (deriv (fun t => (P t) ^ (1 / (n : Real)))) 0 := by
    calc
      deriv (deriv (fun t => -(P t) ^ (1 / (n : Real)))) 0 =
          deriv (fun t => - deriv (fun s => (P s) ^ (1 / (n : Real))) t) 0 := by
            simp [deriv.fun_neg']
      _ = - deriv (deriv (fun t => (P t) ^ (1 / (n : Real)))) 0 := by
            simp
  have hderiv_P :
      deriv P 0 =
        (Finset.univ.prod (fun i => x i)) * Finset.univ.sum (fun i => z i / x i) := by
    simpa [P] using (negGeomMean_prod_deriv_at0 (x := x) (z := z) hx_ne)
  have hderiv2_P :
      deriv (deriv P) 0 =
        (Finset.univ.prod (fun i => x i)) *
          ((Finset.univ.sum (fun i => z i / x i)) ^ 2 -
            Finset.univ.sum (fun i => (z i / x i) ^ 2)) := by
    simpa [P] using (negGeomMean_prod_second_deriv_at0 (x := x) (z := z) hx_ne)
  have hP0_eq : P 0 = Finset.univ.prod (fun i => x i) := by
    simp [P]
  have hn' : (n : Real) ≠ 0 := by exact_mod_cast hn
  have hcalc :
      deriv (deriv (fun t : ℝ => g (x + t • z))) 0 =
        (1 / (n : Real)) ^ 2 * g x *
          ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
    calc
      deriv (deriv (fun t : ℝ => g (x + t • z))) 0
          = deriv (deriv (fun t => -(P t) ^ (1 / (n : Real)))) 0 := by
              simp [g, P, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      _ = - deriv (deriv (fun t => (P t) ^ (1 / (n : Real)))) 0 := hneg
      _ =
          - ((1 / (n : Real)) * ((1 / (n : Real)) - 1) *
                (P 0) ^ ((1 / (n : Real)) - 1 - 1) * (deriv P 0) ^ 2 +
              (1 / (n : Real)) * (P 0) ^ ((1 / (n : Real)) - 1) * deriv (deriv P) 0) := by
          rw [hline_rpow]
      _ =
          (1 / (n : Real)) ^ 2 * g x *
            ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
          set a : ℝ := 1 / (n : ℝ) with ha
          set A : ℝ := ∏ i, x i with hA
          set S : ℝ := ∑ i, z i / x i with hS
          set Q : ℝ := ∑ i, (z i / x i) ^ 2 with hQ
          have hA_ne : A ≠ 0 := by
            simpa [hA, hP0_eq] using hP0
          have hA_pow2 : A ^ (a - 1 - 1) * A ^ 2 = A ^ a := by
            have h := (Real.rpow_add_natCast (x := A) (hx := hA_ne) (y := a - 1 - 1) (n := 2))
            calc
              A ^ (a - 1 - 1) * A ^ 2 = A ^ (a - 1 - 1 + 2) := by
                simpa using h.symm
              _ = A ^ a := by ring_nf
          have hA_pow1 : A ^ (a - 1) * A = A ^ a := by
            have h := (Real.rpow_add_natCast (x := A) (hx := hA_ne) (y := a - 1) (n := 1))
            calc
              A ^ (a - 1) * A = A ^ (a - 1 + 1) := by
                simpa using h.symm
              _ = A ^ a := by ring_nf
          simp [g, hP0_eq, hderiv_P, hderiv2_P, pow_two, ← ha, ← hA]
          have hA_pow1' : A * A ^ (-1 + a) = A ^ a := by
            have h' : -1 + a = a - 1 := by ring_nf
            calc
              A * A ^ (-1 + a) = A ^ (-1 + a) * A := by ac_rfl
              _ = A ^ (a - 1) * A := by simp [h']
              _ = A ^ a := hA_pow1
          have hA_pow2' : A ^ 2 * A ^ (-2 + a) = A ^ a := by
            have h' : -2 + a = a - 1 - 1 := by ring_nf
            calc
              A ^ 2 * A ^ (-2 + a) = A ^ (-2 + a) * A ^ 2 := by ac_rfl
              _ = A ^ (a - 1 - 1) * A ^ 2 := by simp [h']
              _ = A ^ a := hA_pow2
          have hA_pow1S : A * A ^ (-1 + a) * S ^ 2 = A ^ a * S ^ 2 := by
            calc
              A * A ^ (-1 + a) * S ^ 2 = (A * A ^ (-1 + a)) * S ^ 2 := by ac_rfl
              _ = A ^ a * S ^ 2 := by simp [hA_pow1']
          have hA_pow1Q : A * A ^ (-1 + a) * Q = A ^ a * Q := by
            calc
              A * A ^ (-1 + a) * Q = (A * A ^ (-1 + a)) * Q := by ac_rfl
              _ = A ^ a * Q := by simp [hA_pow1']
          have hA_pow2a : A ^ 2 * a * S ^ 2 * A ^ (-2 + a) = a * S ^ 2 * A ^ a := by
            calc
              A ^ 2 * a * S ^ 2 * A ^ (-2 + a) = a * S ^ 2 * (A ^ 2 * A ^ (-2 + a)) := by
                ac_rfl
              _ = a * S ^ 2 * A ^ a := by simp [hA_pow2']
          have hA_pow2b : A ^ 2 * S ^ 2 * A ^ (-2 + a) = S ^ 2 * A ^ a := by
            calc
              A ^ 2 * S ^ 2 * A ^ (-2 + a) = S ^ 2 * (A ^ 2 * A ^ (-2 + a)) := by ac_rfl
              _ = S ^ 2 * A ^ a := by simp [hA_pow2']
          have hA_pow1T : A ^ (a - 1) * (A * (S * S - Q)) = A ^ a * (S * S - Q) := by
            calc
              A ^ (a - 1) * (A * (S * S - Q)) = (A ^ (a - 1) * A) * (S * S - Q) := by
                ac_rfl
              _ = A ^ a * (S * S - Q) := by simp [hA_pow1]
          have hA_pow2T : A ^ (a - 1 - 1) * (A * S * (A * S)) = A ^ a * (S * S) := by
            calc
              A ^ (a - 1 - 1) * (A * S * (A * S)) =
                  (A ^ (a - 1 - 1) * (A * A)) * (S * S) := by ac_rfl
              _ = (A ^ (a - 1 - 1) * A ^ 2) * (S * S) := by simp [pow_two]
              _ = A ^ a * (S * S) := by
                simp [hA_pow2]
          have hA_pow1Ta :
              a * A ^ (a - 1) * (A * (S * S - Q)) = a * A ^ a * (S * S - Q) := by
            calc
              a * A ^ (a - 1) * (A * (S * S - Q)) =
                  a * (A ^ (a - 1) * (A * (S * S - Q))) := by ac_rfl
              _ = a * (A ^ a * (S * S - Q)) := by simp [hA_pow1T]
              _ = a * A ^ a * (S * S - Q) := by ac_rfl
          have hA_pow2Ta :
              a * (a - 1) * A ^ (a - 1 - 1) * (A * S * (A * S)) =
                a * (a - 1) * A ^ a * (S * S) := by
            calc
              a * (a - 1) * A ^ (a - 1 - 1) * (A * S * (A * S)) =
                  a * (a - 1) * (A ^ (a - 1 - 1) * (A * S * (A * S))) := by
                    ac_rfl
              _ = a * (a - 1) * (A ^ a * (S * S)) := by simp [hA_pow2T]
              _ = a * (a - 1) * A ^ a * (S * S) := by ac_rfl
          simp [hA_pow1Ta, hA_pow2Ta]
          simp [ha, mul_assoc, mul_comm, mul_left_comm]
          ring_nf
          field_simp [hn']
  simpa [g] using hcalc

/-- The Hessian quadratic form for the negative geometric mean. -/
lemma negGeomMean_hessian_quadratic_form {n : Nat} (hn : n ≠ 0) {x z : Fin n → Real}
    (hx : ∀ i, 0 < x i) :
    star z ⬝ᵥ
        (hessianMatrix (fun x : Fin n → Real =>
          -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) x *ᵥ z) =
      (1 / (n : Real)) ^ 2 *
        (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) *
        ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
  classical
  let g : (Fin n → Real) → Real :=
    fun x => -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))
  have hline :
      deriv (deriv (fun t : ℝ => g (x + t • z))) 0 =
        (1 / (n : Real)) ^ 2 * g x *
          ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
    simpa [g] using (negGeomMean_line_second_deriv (n := n) hn (x := x) (z := z) hx)
  have hquad :
      deriv (deriv (fun t : ℝ => g (x + t • z))) 0 =
        star z ⬝ᵥ (hessianMatrix g x *ᵥ z) := by
    have hopen : IsOpen {x : Fin n → Real | ∀ i, 0 < x i} := isOpen_posOrthant
    have hcont :
        ContDiffOn ℝ 2 g {x : Fin n → Real | ∀ i, 0 < x i} := by
      simpa [g] using (contDiffOn_negGeomMean_pos (n := n))
    have hxC : x + (0 : ℝ) • z ∈ {x : Fin n → Real | ∀ i, 0 < x i} := by
      simpa using hx
    simpa [g] using
      (line_second_deriv_eq_quadratic_form (hopen := hopen) (hcont := hcont)
        (y := x) (z := z) (t := 0) hxC)
  calc
    star z ⬝ᵥ
        (hessianMatrix (fun x : Fin n → Real =>
          -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) x *ᵥ z)
        = deriv (deriv (fun t : ℝ => g (x + t • z))) 0 := by
            simpa [g] using hquad.symm
    _ = (1 / (n : Real)) ^ 2 * g x *
          ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := hline
    _ = (1 / (n : Real)) ^ 2 *
          (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) *
          ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
          simp [g]

/-- Nonnegativity of the quadratic form for the negative geometric mean. -/
lemma negGeomMean_quadratic_form_nonneg {n : Nat} {x z : Fin n → Real}
    (hx : ∀ i, 0 < x i) :
    0 ≤ (1 / (n : Real)) ^ 2 *
        (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) *
        ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
  classical
  set u : Fin n → Real := fun i => z i / x i
  have hsum_le :
      (Finset.univ.sum u) ^ 2 ≤ (n : Real) * Finset.univ.sum (fun i => (u i) ^ 2) :=
    sum_sq_le_n_mul_sum_sq u
  have hbracket :
      (Finset.univ.sum u) ^ 2 - (n : Real) * Finset.univ.sum (fun i => (u i) ^ 2) ≤ 0 := by
    linarith
  have hprod_pos : 0 < Finset.univ.prod (fun i => x i) := by
    refine Finset.prod_pos ?_
    intro i hi
    exact hx i
  have hpos : 0 ≤ (Finset.univ.prod (fun i => x i)) ^ (1 / (n : Real)) := by
    exact le_of_lt (Real.rpow_pos_of_pos hprod_pos (1 / (n : Real)))
  have hg : (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) ≤ 0 := by
    simpa using (neg_nonpos.mpr hpos)
  have hnonneg : 0 ≤ (1 / (n : Real)) ^ 2 := by
    simp
  have hmul : 0 ≤
      (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) *
        ((Finset.univ.sum u) ^ 2 - (n : Real) * Finset.univ.sum (fun i => (u i) ^ 2)) := by
    exact mul_nonneg_of_nonpos_of_nonpos hg hbracket
  have hmul' :
      0 ≤ (1 / (n : Real)) ^ 2 *
        ((-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) *
          ((Finset.univ.sum u) ^ 2 - (n : Real) * Finset.univ.sum (fun i => (u i) ^ 2))) := by
    exact mul_nonneg hnonneg hmul
  simpa [u, mul_assoc] using hmul'

/-- The Hessian of the negative geometric mean is positive semidefinite on the positive orthant. -/
lemma negGeomMean_hessian_posSemidef {n : Nat} (hn : n ≠ 0) :
    ∀ x, (∀ i, 0 < x i) →
      Matrix.PosSemidef
        (hessianMatrix (fun x : Fin n → Real =>
          -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) x) := by
  intro x hx
  classical
  let g : (Fin n → Real) → Real :=
    fun x => -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))
  refine (posSemidef_iff_real (M := hessianMatrix g x)).2 ?_
  refine ⟨?hsymm, ?hquad⟩
  · have hopen : IsOpen {x : Fin n → Real | ∀ i, 0 < x i} := isOpen_posOrthant
    have hcont :
        ContDiffOn ℝ 2 g {x : Fin n → Real | ∀ i, 0 < x i} := by
      simpa [g] using (contDiffOn_negGeomMean_pos (n := n))
    simpa [g] using (hessian_symm (hopen := hopen) (hcont := hcont) (x := x) hx)
  · intro z
    have hquad_form :
        z ⬝ᵥ (hessianMatrix g x *ᵥ z) =
          (1 / (n : Real)) ^ 2 * g x *
            ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
      have hquad' :=
        negGeomMean_hessian_quadratic_form (n := n) hn (x := x) (z := z) hx
      simpa [g] using hquad'
    have hnonneg :
        0 ≤ (1 / (n : Real)) ^ 2 * g x *
          ((∑ i, z i / x i) ^ 2 - (n : Real) * ∑ i, (z i / x i) ^ 2) := by
      simpa [g] using (negGeomMean_quadratic_form_nonneg (x := x) (z := z) hx)
    simpa [hquad_form] using hnonneg

/-- Convexity of the negative geometric mean on the positive orthant. -/
lemma convexOn_negGeomMean_pos {n : Nat} (hn : n ≠ 0) :
    ConvexOn ℝ {x | ∀ i, 0 < x i}
      (fun x : Fin n → Real =>
        -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) := by
  have hC : Convex ℝ {x : Fin n → Real | ∀ i, 0 < x i} := convex_posOrthant
  have hopen : IsOpen {x : Fin n → Real | ∀ i, 0 < x i} := isOpen_posOrthant
  have hcont :
      ContDiffOn ℝ 2 (fun x : Fin n → Real =>
        -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))))
        {x : Fin n → Real | ∀ i, 0 < x i} := contDiffOn_negGeomMean_pos
  refine convexOn_of_hessian_posSemidef (hC := hC) (hopen := hopen)
    (hcont := hcont) ?_
  intro x hx
  exact negGeomMean_hessian_posSemidef (n := n) hn x hx

end Section04
end Chap01
