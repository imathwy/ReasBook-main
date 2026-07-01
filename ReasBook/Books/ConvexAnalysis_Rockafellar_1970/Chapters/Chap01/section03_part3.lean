/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section03_part2

open scoped BigOperators
open scoped Pointwise

section Chap01
section Section03

/- Text 3.6.10: For convex sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`,
`K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`, and
`K = { (λ, x) | ∃ λ1 λ2 x1 x2, λ = λ1 + λ2, x = x1 + x2,
  (λ1, x1) ∈ K1, (λ2, x2) ∈ K2 }`.
Then `(1, x) ∈ K` iff `x ∈ conv(C1 ∪ C2)`. -/
/-- Membership in the cone-sum set is equivalent to an explicit convex combination. -/
lemma coneSet_sum_iff_exists_convex_combo {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (x : Fin n → Real) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real, ∃ x1 x2 : Fin n → Real,
            p.1 = r1 + r2 ∧ p.2 = x1 + x2 ∧
              (r1, x1) ∈ K1 ∧ (r2, x2) ∈ K2}
      (1, x) ∈ K) ↔
      ∃ r1 r2 : Real, ∃ c1 c2 : Fin n → Real,
        0 ≤ r1 ∧ 0 ≤ r2 ∧ r1 + r2 = 1 ∧ c1 ∈ C1 ∧ c2 ∈ C2 ∧
          x = r1 • c1 + r2 • c2 := by
  dsimp
  constructor
  · rintro ⟨r1, r2, x1, x2, hsum, hx, hx1, hx2⟩
    rcases hx1 with ⟨hr1, hx1⟩
    rcases hx2 with ⟨hr2, hx2⟩
    rcases (Set.mem_smul_set.mp hx1) with ⟨c1, hc1, rfl⟩
    rcases (Set.mem_smul_set.mp hx2) with ⟨c2, hc2, rfl⟩
    refine ⟨r1, r2, c1, c2, hr1, hr2, hsum.symm, hc1, hc2, ?_⟩
    exact hx
  · rintro ⟨r1, r2, c1, c2, hr1, hr2, hsum, hc1, hc2, hx⟩
    refine ⟨r1, r2, r1 • c1, r2 • c2, hsum.symm, ?_, ?_, ?_⟩
    · exact hx
    · exact ⟨hr1, Set.smul_mem_smul_set hc1⟩
    · exact ⟨hr2, Set.smul_mem_smul_set hc2⟩

/-- Membership in the cone-sum set is equivalent to membership in the convex join. -/
lemma coneSet_sum_iff_mem_convexJoin {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (x : Fin n → Real) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real, ∃ x1 x2 : Fin n → Real,
            p.1 = r1 + r2 ∧ p.2 = x1 + x2 ∧
              (r1, x1) ∈ K1 ∧ (r2, x2) ∈ K2}
      (1, x) ∈ K) ↔ x ∈ convexJoin Real C1 C2 := by
  constructor
  · intro hx
    rcases (coneSet_sum_iff_exists_convex_combo (C1 := C1) (C2 := C2) (x := x)).1 hx with
      ⟨r1, r2, c1, c2, hr1, hr2, hsum, hc1, hc2, hxcomb⟩
    refine (mem_convexJoin (𝕜 := Real) (s := C1) (t := C2) (x := x)).2 ?_
    refine ⟨c1, hc1, c2, hc2, ?_⟩
    exact ⟨r1, r2, hr1, hr2, hsum, hxcomb.symm⟩
  · intro hx
    rcases (mem_convexJoin (𝕜 := Real) (s := C1) (t := C2) (x := x)).1 hx with
      ⟨c1, hc1, c2, hc2, hxseg⟩
    rcases hxseg with ⟨r1, r2, hr1, hr2, hsum, hxcomb⟩
    refine (coneSet_sum_iff_exists_convex_combo (C1 := C1) (C2 := C2) (x := x)).2 ?_
    exact ⟨r1, r2, c1, c2, hr1, hr2, hsum, hc1, hc2, hxcomb.symm⟩

theorem coneSet_sum_iff_convexHull_union {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2)
    (hC1ne : C1.Nonempty) (hC2ne : C2.Nonempty) (x : Fin n → Real) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real, ∃ x1 x2 : Fin n → Real,
            p.1 = r1 + r2 ∧ p.2 = x1 + x2 ∧
              (r1, x1) ∈ K1 ∧ (r2, x2) ∈ K2}
      (1, x) ∈ K ↔ x ∈ convexHull Real (C1 ∪ C2)) := by
  have hjoin :
      (let K1 : Set (Real × (Fin n → Real)) :=
          {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
        let K2 : Set (Real × (Fin n → Real)) :=
          {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
        let K : Set (Real × (Fin n → Real)) :=
          {p |
            ∃ r1 r2 : Real, ∃ x1 x2 : Fin n → Real,
              p.1 = r1 + r2 ∧ p.2 = x1 + x2 ∧
                (r1, x1) ∈ K1 ∧ (r2, x2) ∈ K2}
        (1, x) ∈ K ↔ x ∈ convexJoin Real C1 C2) :=
    coneSet_sum_iff_mem_convexJoin (C1 := C1) (C2 := C2) (x := x)
  have hconv : convexHull Real (C1 ∪ C2) = convexJoin Real C1 C2 :=
    hC1.convexHull_union hC2 hC1ne hC2ne
  simpa [hconv] using hjoin

/-- Text 3.6.11: For convex sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`,
`K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`, and
`K = { (λ, x) | ∃ λ1 λ2 x1 x2, λ = λ1 + λ2, x = x1 + x2,
  (λ1, x1) ∈ K1, (λ2, x2) ∈ K2 }`.
Then `K` is convex. -/
theorem convex_coneSet_sum {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real, ∃ x1 x2 : Fin n → Real,
            p.1 = r1 + r2 ∧ p.2 = x1 + x2 ∧
              (r1, x1) ∈ K1 ∧ (r2, x2) ∈ K2}
      Convex Real K) := by
  dsimp
  have hK1 : Convex Real {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1} := by
    simpa using (convex_coneSet_of_convex (hC := hC1))
  have hK2 : Convex Real {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2} := by
    simpa using (convex_coneSet_of_convex (hC := hC2))
  have hK :
      {p : Real × (Fin n → Real) |
        ∃ r1 r2 : Real,
          p.1 = r1 + r2 ∧
            ∃ x1 x2 : Fin n → Real,
              p.2 = x1 + x2 ∧ (0 ≤ r1 ∧ x1 ∈ r1 • C1) ∧ 0 ≤ r2 ∧ x2 ∈ r2 • C2} =
        {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1} +
          {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2} := by
    ext p
    constructor
    · rintro ⟨r1, r2, hsum, x1, x2, hxsum, h1, hr2, h2⟩
      refine (Set.mem_add).2 ?_
      refine ⟨(r1, x1), h1, (r2, x2), ⟨hr2, h2⟩, ?_⟩
      ext <;> simp [hsum, hxsum]
    · intro hp
      rcases (Set.mem_add).1 hp with ⟨p1, hp1, p2, hp2, hsum⟩
      rcases p1 with ⟨r1, x1⟩
      rcases p2 with ⟨r2, x2⟩
      rcases hp1 with ⟨hr1, hx1⟩
      rcases hp2 with ⟨hr2, hx2⟩
      have hsum1 : p.1 = r1 + r2 := by
        have : r1 + r2 = p.1 := by
          simpa using (congrArg Prod.fst hsum)
        exact this.symm
      have hsum2 : p.2 = x1 + x2 := by
        have : x1 + x2 = p.2 := by
          simpa using (congrArg Prod.snd hsum)
        exact this.symm
      exact ⟨r1, r2, hsum1, x1, x2, hsum2, ⟨hr1, hx1⟩, hr2, hx2⟩
  simpa [hK] using (Convex.add (s := {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1})
    (t := {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}) hK1 hK2)

end Section03
end Chap01
