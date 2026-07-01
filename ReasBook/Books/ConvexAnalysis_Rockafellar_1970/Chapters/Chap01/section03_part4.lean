/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section03_part3

open scoped BigOperators
open scoped Pointwise

section Chap01
section Section03

/-- Membership in the cone at scale `1` is exactly membership in the base set. -/
lemma coneSet_mem_one_iff {n : ℕ} (C : Set (Fin n → Real)) (x : Fin n → Real) :
    (1, x) ∈ {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C} ↔ x ∈ C := by
  simp [Set.mem_setOf_eq, zero_le_one]

/-- Text 3.6.12: For sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`,
`K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`, and
`K = { (λ, x) | (λ, x) ∈ K1, (λ, x) ∈ K2 }`. Then
`(1, x) ∈ K` iff `x ∈ C1 ∩ C2`. -/
theorem coneSet_intersection_iff {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (x : Fin n → Real) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) := K1 ∩ K2
      (1, x) ∈ K ↔ x ∈ C1 ∩ C2) := by
  -- Unfold the definitions and simplify.
  simp

/-- Text 3.6.13: For convex sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`,
`K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`, and
`K = { (λ, x) | (λ, x) ∈ K1, (λ, x) ∈ K2 }`. Then `K` is convex. -/
theorem convex_coneSet_intersection {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) := K1 ∩ K2
      Convex Real K) := by
  dsimp
  have hK1 : Convex Real {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1} := by
    simpa using (convex_coneSet_of_convex (hC := hC1))
  have hK2 : Convex Real {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2} := by
    simpa using (convex_coneSet_of_convex (hC := hC2))
  simpa using hK1.inter hK2

/-- The hyperplane `{(1, x)}` in `ℝ × ℝ^n` is convex. -/
lemma convex_H_hyperplane_one {n : ℕ} :
    Convex Real {p : Real × (Fin n → Real) | p.1 = 1} := by
  intro x hx y hy a b ha hb hab
  simp [Set.mem_setOf_eq] at hx hy ⊢
  calc
    (a • x + b • y).1 = a * x.1 + b * y.1 := by simp
    _ = a + b := by simp [hx, hy]
    _ = 1 := by simpa using hab

/-- The inverse addition is the projection of `K ∩ H` to the second coordinate. -/
lemma inverseAddition_eq_snd_image_K_inter_H {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real,
            p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
      let H : Set (Real × (Fin n → Real)) := {p | p.1 = 1}
      (C1 # C2) =
        (LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real)) '' (K ∩ H)) := by
  classical
  let K1 : Set (Real × (Fin n → Real)) := {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
  let K2 : Set (Real × (Fin n → Real)) := {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
  let K : Set (Real × (Fin n → Real)) :=
    {p |
      ∃ r1 r2 : Real,
        p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
  let H : Set (Real × (Fin n → Real)) := {p | p.1 = 1}
  have h :
      (C1 # C2) =
        (LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real)) '' (K ∩ H) := by
    ext x
    constructor
    · intro hx
      have hK : (1, x) ∈ K := by
        have hK' :
            (let K1 : Set (Real × (Fin n → Real)) :=
                {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
              let K2 : Set (Real × (Fin n → Real)) :=
                {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
              let K : Set (Real × (Fin n → Real)) :=
                {p |
                  ∃ r1 r2 : Real,
                    p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
              (1, x) ∈ K) :=
          (coneSet_inverseAddition_iff (C1 := C1) (C2 := C2) (x := x) hC1 hC2).2 hx
        simpa [K1, K2, K] using hK'
      refine (Set.mem_image
        (f := (LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real)))
        (s := K ∩ H) (y := x)).2 ?_
      refine ⟨(1, x), ?_, ?_⟩
      · exact ⟨hK, by simp [H]⟩
      · simp
    · intro hx
      rcases (Set.mem_image
        (f := (LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real)))
        (s := K ∩ H) (y := x)).1 hx with ⟨p, hp, rfl⟩
      rcases p with ⟨r, y⟩
      have hr : r = 1 := by
        simpa [H] using hp.2
      have hK : (1, y) ∈ K := by
        simpa [hr] using hp.1
      have hK' :
          (let K1 : Set (Real × (Fin n → Real)) :=
              {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
            let K2 : Set (Real × (Fin n → Real)) :=
              {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
            let K : Set (Real × (Fin n → Real)) :=
              {p |
                ∃ r1 r2 : Real,
                  p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
            (1, y) ∈ K) := by
        simpa [K1, K2, K] using hK
      have hy :
          y ∈ C1 # C2 :=
        (coneSet_inverseAddition_iff (C1 := C1) (C2 := C2) (x := y) hC1 hC2).1 hK'
      simpa using hy
  simpa [K1, K2, K, H] using h

/-- The intersection of the cone-set `K` with the hyperplane `H` is convex. -/
lemma convex_K_inter_H {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real,
            p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
      let H : Set (Real × (Fin n → Real)) := {p | p.1 = 1}
      Convex Real (K ∩ H)) := by
  let K1 : Set (Real × (Fin n → Real)) := {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
  let K2 : Set (Real × (Fin n → Real)) := {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
  let K : Set (Real × (Fin n → Real)) :=
    {p |
      ∃ r1 r2 : Real,
        p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
  let H : Set (Real × (Fin n → Real)) := {p | p.1 = 1}
  have hK : Convex Real K := by
    simpa [K1, K2, K] using
      (convex_coneSet_inverseAddition (C1 := C1) (C2 := C2) hC1 hC2)
  have hH : Convex Real H := by
    simpa [H] using (convex_H_hyperplane_one (n := n))
  have hKH : Convex Real (K ∩ H) := hK.inter hH
  simpa [K1, K2, K, H] using hKH

/-- Theorem 3.7: If `C1` and `C2` are convex sets in `ℝ^n`, then their inverse sum
`C1 # C2` is convex. -/
theorem convex_inverseAddition {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real (C1 # C2) := by
  classical
  let K1 : Set (Real × (Fin n → Real)) := {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
  let K2 : Set (Real × (Fin n → Real)) := {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
  let K : Set (Real × (Fin n → Real)) :=
    {p |
      ∃ r1 r2 : Real,
        p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
  let H : Set (Real × (Fin n → Real)) := {p | p.1 = 1}
  have hKH : Convex Real (K ∩ H) := by
    simpa [K1, K2, K, H] using (convex_K_inter_H (C1 := C1) (C2 := C2) hC1 hC2)
  have himage :
      Convex Real
        ((LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real)) '' (K ∩ H)) :=
    hKH.linear_image (LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real))
  have hEq :
      (C1 # C2) =
        (LinearMap.snd (R := Real) (M := Real) (M₂ := Fin n → Real)) '' (K ∩ H) := by
    simpa [K1, K2, K, H] using
      (inverseAddition_eq_snd_image_K_inter_H (C1 := C1) (C2 := C2) hC1 hC2)
  simpa [hEq] using himage

end Section03
end Chap01
