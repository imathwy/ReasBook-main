/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section02_part1

open scoped BigOperators
open scoped Pointwise

section Chap01
section Section03

/-- Translation by adding on the right equals translation by adding on the left. -/
lemma image_add_right_eq_image_add_left {n : ℕ} (C : Set (Fin n → Real))
    (a : Fin n → Real) :
    Set.image (fun x => x + a) C = Set.image (fun x => a + x) C := by
  ext y
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> refine ⟨x, hx, ?_⟩ <;>
    simp [add_comm]

/-- Theorem 3.0.1: If `C` is a convex set in `Real^n`, then `C + a` is convex
for any `a` in `Real^n`. -/
theorem convex_translate {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) (a : Fin n → Real) :
    Convex Real (Set.image (fun x => x + a) C) := by
  simpa [image_add_right_eq_image_add_left (C:=C) (a:=a)] using hC.translate a

/-- Theorem 3.0.2: If `C` is a convex set in `Real^n`, then `r C = {r x | x ∈ C}`
is convex for any `r ∈ Real`. -/
theorem convex_smul_image {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) (r : Real) :
    Convex Real (Set.image (fun x => r • x) C) := by
  simpa using (hC.smul r)

/-- Theorem 3.1: If `C1` and `C2` are convex sets in `Real^n`, then their sum
`C1 + C2 = {x1 + x2 | x1 ∈ C1, x2 ∈ C2}` is convex. -/
theorem convex_add {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real (C1 + C2) := by
  simpa using hC1.add hC2

/-- The upper set `{x | ∃ x1 ∈ C1, x1 ≤ x}` lies in `C1 + {x | 0 ≤ x}`. -/
lemma upper_set_subset_add_nonneg {n : ℕ} {C1 : Set (Fin n → Real)} :
    {x : Fin n → Real | ∃ x1 ∈ C1, x1 ≤ x} ⊆
      C1 + Set.Ici (0 : Fin n → Real) := by
  intro x hx
  rcases hx with ⟨x1, hx1, hxle⟩
  refine (Set.mem_add).2 ?_
  refine ⟨x1, hx1, x - x1, ?_, ?_⟩
  · exact sub_nonneg.mpr hxle
  · simp

/-- A pointwise nonnegative orthant is a convex set. -/
lemma convex_nonneg_orthant {n : ℕ} :
    Convex Real (Set.Ici (0 : Fin n → Real)) := by
  simpa using (convex_Ici (0 : Fin n → Real))

/-- The sum with the nonnegative orthant lies in the upper set. -/
lemma add_nonneg_subset_upper_set {n : ℕ} {C1 : Set (Fin n → Real)} :
    C1 + Set.Ici (0 : Fin n → Real) ⊆
      {x : Fin n → Real | ∃ x1 ∈ C1, x1 ≤ x} := by
  intro x hx
  rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
  refine ⟨x1, hx1, ?_⟩
  intro i
  have h := add_le_add_left (hx2 i) (x1 i)
  simpa using h

/-- Text 3.1.1: If `C1` is a convex set in `R^n`, then the set
`{x | ∃ x1 ∈ C1, x1 ≤ x}` is also convex, where `≤` is understood componentwise. -/
theorem convex_upper_set_of_le {n : ℕ} {C1 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) :
    Convex Real {x : Fin n → Real | ∃ x1 ∈ C1, x1 ≤ x} := by
  have hsubset : {x : Fin n → Real | ∃ x1 ∈ C1, x1 ≤ x} =
      C1 + Set.Ici (0 : Fin n → Real) := by
    ext x
    constructor
    · exact (upper_set_subset_add_nonneg (C1 := C1) (a := x))
    · exact (add_nonneg_subset_upper_set (C1 := C1) (a := x))
  have hC2 : Convex Real (Set.Ici (0 : Fin n → Real)) :=
    convex_nonneg_orthant (n := n)
  simpa [hsubset] using (convex_add (hC1 := hC1) (hC2 := hC2))

/-- Unpack the inclusion `r • K ⊆ K` into pointwise closure under scaling. -/
lemma smul_mem_of_smul_subset {n : ℕ} {K : Set (Fin n → Real)}
    (hK : ∀ {r : Real}, 0 < r → r • K ⊆ K) {r : Real} (hr : 0 < r)
    {x : Fin n → Real} (hx : x ∈ K) : r • x ∈ K := by
  exact hK hr (Set.smul_mem_smul_set (a := r) (s := K) hx)

/-- Unpack the inclusion `K + K ⊆ K` into pointwise closure under addition. -/
lemma add_mem_of_add_subset {n : ℕ} {K : Set (Fin n → Real)}
    (hK : K + K ⊆ K) {x y : Fin n → Real} (hx : x ∈ K) (hy : y ∈ K) :
    x + y ∈ K := by
  apply hK
  exact (Set.mem_add).2 ⟨x, hx, y, hy, rfl⟩

/-- Text 3.1.2: A set `K` is a convex cone iff for every `λ > 0` we have
`λ • K ⊆ K`, and `K + K ⊆ K`. -/
theorem convexCone_iff_smul_subset_add_subset {n : ℕ} (K : Set (Fin n → Real)) :
    (∃ C : ConvexCone Real (Fin n → Real), (C : Set (Fin n → Real)) = K) ↔
      (∀ {r : Real}, 0 < r → r • K ⊆ K) ∧ K + K ⊆ K := by
  constructor
  · rintro ⟨C, rfl⟩
    constructor
    · intro r hr x hx
      rcases (Set.mem_smul_set.mp hx) with ⟨y, hy, rfl⟩
      exact C.smul_mem hr hy
    · intro x hx
      rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
      exact C.add_mem hx1 hx2
  · rintro ⟨hsmul, hadd⟩
    refine ⟨ConvexCone.mk K ?_ ?_, rfl⟩
    · intro r hr x hx
      exact smul_mem_of_smul_subset (K := K) hsmul hr hx
    · intro x hx y hy
      exact add_mem_of_add_subset (K := K) hadd hx hy

/-- A finite Minkowski sum of convex sets is convex. -/
lemma convex_sum_finset_set {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Set (Fin n → Real)) (hA : ∀ i ∈ s, Convex Real (A i)) :
    Convex Real (s.sum A) := by
  classical
  revert hA
  refine Finset.induction_on s ?h0 ?hstep
  · intro hA
    simpa using (convex_zero (𝕜 := Real) (E := Fin n → Real))
  · intro a s ha hs hAas
    have hconv_a : Convex Real (A a) := hAas a (by simp [ha])
    have hconv_s : Convex Real (s.sum A) :=
      hs (by intro i hi; exact hAas i (by simp [hi]))
    simpa [Finset.sum_insert, ha] using
      (convex_add (hC1 := hconv_a) (hC2 := hconv_s))

/-- Text 3.1.3: If `C1, ..., Cm` are convex sets, then the linear combination
`C = lambda_1 • C1 + ... + lambda_m • Cm` is convex. -/
theorem convex_linear_combination {n m : ℕ} (C : Fin m → Set (Fin n → Real))
    (w : Fin m → Real) (hC : ∀ i, Convex Real (C i)) :
    Convex Real (∑ i, w i • C i) := by
  classical
  have hA : ∀ i ∈ (Finset.univ : Finset (Fin m)), Convex Real (w i • C i) := by
    intro i hi
    simpa using (hC i).smul (w i)
  simpa using
    (convex_sum_finset_set (n := n) (s := Finset.univ)
      (A := fun i => w i • C i) hA)

/-- Text 3.1.4: A set `C = lambda_1 • C1 + ... + lambda_m • Cm` is called a convex
combination of `C1, ..., Cm` when `lambda_i ≥ 0` for all `i` and
`lambda_1 + ... + lambda_m = 1`. -/
def IsConvexCombinationSet {n m : ℕ} (C : Set (Fin n → Real))
    (C' : Fin m → Set (Fin n → Real)) (w : Fin m → Real) : Prop :=
  C = ∑ i, w i • C' i ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = (1 : Real)

/-- A Minkowski sum point lies in a translate of the second set. -/
lemma minkowski_sum_subset_iUnion_translate {n : ℕ} (C1 C2 : Set (Fin n → Real)) :
    C1 + C2 ⊆ ⋃ x1 ∈ C1, (fun x2 => x1 + x2) '' C2 := by
  intro x hx
  rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨x1, ?_⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨hx1, ?_⟩
  exact ⟨x2, hx2, rfl⟩

/-- A point in a translate union lies in the Minkowski sum. -/
lemma iUnion_translate_subset_minkowski_sum {n : ℕ} (C1 C2 : Set (Fin n → Real)) :
    (⋃ x1 ∈ C1, (fun x2 => x1 + x2) '' C2) ⊆ C1 + C2 := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨x1, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hx1, hx⟩
  rcases hx with ⟨x2, hx2, rfl⟩
  exact (Set.mem_add).2 ⟨x1, hx1, x2, hx2, rfl⟩

/-- Text 3.1.5: For sets `C1, C2 ⊆ ℝ^n`, the Minkowski sum satisfies
`C1 + C2 = ⋃ x1 ∈ C1, (x1 + C2)`, where `x1 + C2 = {x1 + x2 | x2 ∈ C2}` is the
translate of `C2` by the vector `x1`. -/
theorem minkowski_sum_eq_iUnion_translate {n : ℕ} (C1 C2 : Set (Fin n → Real)) :
    C1 + C2 = ⋃ x1 ∈ C1, (fun x2 => x1 + x2) '' C2 := by
  refine subset_antisymm ?_ ?_
  · exact minkowski_sum_subset_iUnion_translate C1 C2
  · exact iUnion_translate_subset_minkowski_sum C1 C2

/-- Minkowski sum is commutative. -/
lemma minkowski_sum_comm {n : ℕ} (C1 C2 : Set (Fin n → Real)) :
    C1 + C2 = C2 + C1 := by
  ext x
  constructor
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
    exact (Set.mem_add).2 ⟨x2, hx2, x1, hx1, by simp [add_comm]⟩
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x2, hx2, x1, hx1, rfl⟩
    exact (Set.mem_add).2 ⟨x1, hx1, x2, hx2, by simp [add_comm]⟩

/-- Minkowski sum is associative. -/
lemma minkowski_sum_assoc {n : ℕ} (C1 C2 C3 : Set (Fin n → Real)) :
    (C1 + C2) + C3 = C1 + (C2 + C3) := by
  ext x
  constructor
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x12, hx12, x3, hx3, rfl⟩
    rcases (Set.mem_add).1 hx12 with ⟨x1, hx1, x2, hx2, rfl⟩
    refine (Set.mem_add).2 ⟨x1, hx1, x2 + x3, ?_, ?_⟩
    · exact (Set.mem_add).2 ⟨x2, hx2, x3, hx3, rfl⟩
    · simp [add_assoc]
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x1, hx1, x23, hx23, rfl⟩
    rcases (Set.mem_add).1 hx23 with ⟨x2, hx2, x3, hx3, rfl⟩
    refine (Set.mem_add).2 ⟨x1 + x2, ?_, x3, hx3, ?_⟩
    · exact (Set.mem_add).2 ⟨x1, hx1, x2, hx2, rfl⟩
    · simp [add_assoc]

/-- Scalar multiplication on sets is associative. -/
lemma smul_smul_set {n : ℕ} (C : Set (Fin n → Real)) (r1 r2 : Real) :
    r1 • (r2 • C) = (r1 * r2) • C := by
  ext x
  constructor
  · intro hx
    rcases (Set.mem_smul_set.mp hx) with ⟨y, hy, rfl⟩
    rcases (Set.mem_smul_set.mp hy) with ⟨z, hz, rfl⟩
    exact (Set.mem_smul_set.mpr ⟨z, hz, by simp [smul_smul]⟩)
  · intro hx
    rcases (Set.mem_smul_set.mp hx) with ⟨z, hz, rfl⟩
    refine (Set.mem_smul_set.mpr ?_)
    refine ⟨r2 • z, Set.smul_mem_smul_set (a := r2) (s := C) hz, ?_⟩
    simp [smul_smul]

/-- Scalar multiplication distributes over Minkowski sums. -/
lemma smul_add_set {n : ℕ} (C1 C2 : Set (Fin n → Real)) (r : Real) :
    r • (C1 + C2) = r • C1 + r • C2 := by
  ext x
  constructor
  · intro hx
    rcases (Set.mem_smul_set.mp hx) with ⟨y, hy, rfl⟩
    rcases (Set.mem_add).1 hy with ⟨x1, hx1, x2, hx2, rfl⟩
    refine (Set.mem_add).2 ?_
    refine ⟨r • x1, Set.smul_mem_smul_set (a := r) (s := C1) hx1,
      r • x2, Set.smul_mem_smul_set (a := r) (s := C2) hx2, ?_⟩
    simp [smul_add]
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨y1, hy1, y2, hy2, rfl⟩
    rcases (Set.mem_smul_set.mp hy1) with ⟨x1, hx1, rfl⟩
    rcases (Set.mem_smul_set.mp hy2) with ⟨x2, hx2, rfl⟩
    refine (Set.mem_smul_set.mpr ?_)
    refine ⟨x1 + x2, (Set.mem_add).2 ⟨x1, hx1, x2, hx2, rfl⟩, ?_⟩
    simp [smul_add]

/-- The easy inclusion of a scaled set into a Minkowski sum of scaled sets. -/
lemma smul_set_subset_add_smul_set {n : ℕ} (C : Set (Fin n → Real)) (r1 r2 : Real) :
    (r1 + r2) • C ⊆ r1 • C + r2 • C := by
  intro x hx
  rcases (Set.mem_smul_set.mp hx) with ⟨y, hy, rfl⟩
  refine (Set.mem_add).2 ?_
  refine ⟨r1 • y, Set.smul_mem_smul_set (a := r1) (s := C) hy,
    r2 • y, Set.smul_mem_smul_set (a := r2) (s := C) hy, ?_⟩
  simp [add_smul]

/-- Convexity gives closure under binary convex combinations inside `C`. -/
lemma convex_combo_subset {n : ℕ} {C : Set (Fin n → Real)} (hC : Convex Real C)
    {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • C + b • C ⊆ C := by
  intro x hx
  rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
  rcases (Set.mem_smul_set.mp hx1) with ⟨y1, hy1, rfl⟩
  rcases (Set.mem_smul_set.mp hx2) with ⟨y2, hy2, rfl⟩
  exact hC hy1 hy2 ha hb hab

/-- Scale a convex combination back to a Minkowski sum of scaled sets. -/
lemma add_smul_subset_smul_of_pos {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) {r1 r2 : Real} (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hpos : 0 < r1 + r2) :
    r1 • C + r2 • C ⊆ (r1 + r2) • C := by
  intro x hx
  rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
  rcases (Set.mem_smul_set.mp hx1) with ⟨y1, hy1, rfl⟩
  rcases (Set.mem_smul_set.mp hx2) with ⟨y2, hy2, rfl⟩
  set a : Real := r1 / (r1 + r2)
  set b : Real := r2 / (r1 + r2)
  have hsum : r1 + r2 ≠ 0 := ne_of_gt hpos
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hr1 (le_of_lt hpos)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg hr2 (le_of_lt hpos)
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hsum]
  have hmem : a • y1 + b • y2 ∈ C := hC hy1 hy2 ha hb hab
  refine (Set.mem_smul_set.mpr ?_)
  refine ⟨a • y1 + b • y2, hmem, ?_⟩
  calc
    (r1 + r2) • (a • y1 + b • y2)
        = (r1 + r2) • (a • y1) + (r1 + r2) • (b • y2) := by
            simp [smul_add]
    _ = ((r1 + r2) * a) • y1 + ((r1 + r2) * b) • y2 := by
            simp [smul_smul]
    _ = r1 • y1 + r2 • y2 := by
            have hmul1 : (r1 + r2) * a = r1 := by
              dsimp [a]
              field_simp [hsum]
            have hmul2 : (r1 + r2) * b = r2 := by
              dsimp [b]
              field_simp [hsum]
            simp [hmul1, hmul2]

/-- Text 3.1.6: For sets `C1, C2, C3` in `ℝ^n` and real numbers `λ1, λ2, λ`, the
Minkowski sum is commutative and associative, scalar multiplication is
associative, and scalar multiplication distributes over sums:
`C1 + C2 = C2 + C1`, `(C1 + C2) + C3 = C1 + (C2 + C3)`,
`λ1(λ2 C) = (λ1 λ2) C`, and `λ(C1 + C2) = λ C1 + λ C2`. -/
theorem minkowski_sum_smul_properties {n : ℕ} (C1 C2 C3 C : Set (Fin n → Real))
    (r1 r2 r : Real) :
    C1 + C2 = C2 + C1 ∧
      (C1 + C2) + C3 = C1 + (C2 + C3) ∧
        r1 • (r2 • C) = (r1 * r2) • C ∧
          r • (C1 + C2) = r • C1 + r • C2 := by
  refine ⟨minkowski_sum_comm (C1 := C1) (C2 := C2), ?_⟩
  refine ⟨minkowski_sum_assoc (C1 := C1) (C2 := C2) (C3 := C3), ?_⟩
  refine ⟨smul_smul_set (C := C) (r1 := r1) (r2 := r2), ?_⟩
  exact smul_add_set (C1 := C1) (C2 := C2) (r := r)

/-- Theorem 3.2: If `C` is a convex set in `Real^n` and `λ1 ≥ 0`, `λ2 ≥ 0`, then
`(λ1 + λ2) • C = λ1 • C + λ2 • C`. -/
theorem convex_smul_add_eq {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) {r1 r2 : Real} (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) :
    (r1 + r2) • C = r1 • C + r2 • C := by
  refine Set.Subset.antisymm ?hsubset1 ?hsubset2
  · exact smul_set_subset_add_smul_set (C := C) r1 r2
  · by_cases hsum : r1 + r2 = 0
    · have hr1' : r1 = 0 := by linarith
      have hr2' : r2 = 0 := by linarith
      subst hr1' hr2'
      intro x hx
      rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
      rcases (Set.mem_smul_set.mp hx1) with ⟨y1, hy1, rfl⟩
      rcases (Set.mem_smul_set.mp hx2) with ⟨y2, hy2, rfl⟩
      exact (Set.mem_smul_set.mpr ⟨y1, hy1, by simp⟩)
    · have hpos : 0 < r1 + r2 := by
        have hnonneg : 0 ≤ r1 + r2 := add_nonneg hr1 hr2
        exact lt_of_le_of_ne hnonneg (by symm; exact hsum)
      exact add_smul_subset_smul_of_pos (hC := hC) (hr1 := hr1) (hr2 := hr2) hpos

/-- Text 3.2.1: For a convex set `C ⊆ ℝ^n` and any `λ` with `1 ≥ λ ≥ 0`,
it holds that `C = λ • C + (1 - λ) • C`. -/
theorem convex_eq_smul_add_smul_self {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) {r : Real} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    C = r • C + (1 - r) • C := by
  have hnonneg : 0 ≤ 1 - r := by
    linarith
  have hsum : r + (1 - r) = (1 : Real) := by
    ring
  have hsmul :
      (1 : Real) • C = r • C + (1 - r) • C := by
    simpa [hsum] using
      (convex_smul_add_eq (hC := hC) (r1 := r) (r2 := 1 - r) hr0 hnonneg)
  simpa using hsmul

/-- Text 3.2.2: For a convex set `C ⊆ ℝ^n`, it holds that `C + C = 2C`. -/
theorem convex_add_eq_two_smul {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) :
    C + C = (2 : Real) • C := by
  have h : (2 : Real) • C = C + C := by
    simpa [one_smul, one_add_one_eq_two] using
      (convex_smul_add_eq (hC := hC) (r1 := (1 : Real)) (r2 := (1 : Real))
        (hr1 := zero_le_one) (hr2 := zero_le_one))
  exact h.symm

/-- Text 3.2.3: For a convex set `C ⊆ ℝ^n`, it holds that `C + C + C = 3C`. -/
theorem convex_add_eq_three_smul {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) :
    C + C + C = (3 : Real) • C := by
  calc
    C + C + C = (C + C) + C := by rfl
    _ = (2 : Real) • C + C := by
      simp [convex_add_eq_two_smul hC]
    _ = (2 : Real) • C + (1 : Real) • C := by
      simp [one_smul]
    _ = ((2 : Real) + (1 : Real)) • C := by
      symm
      exact
        (convex_smul_add_eq (hC := hC) (r1 := (2 : Real)) (r2 := (1 : Real))
          (by norm_num) (by norm_num))
    _ = (3 : Real) • C := by norm_num

/-- Membership in a finite Minkowski sum of scaled sets is equivalent to a pointwise witness. -/
lemma mem_sum_smul_set_iff_exists_points {n m : ℕ} (C : Fin m → Set (Fin n → Real))
    (w : Fin m → Real) (x : Fin n → Real) :
    x ∈ ∑ i, w i • C i ↔
      ∃ z : Fin m → Fin n → Real, (∀ i, z i ∈ C i) ∧ x = ∑ i, w i • z i := by
  classical
  have h :
      ∀ (s : Finset (Fin m)) (x : Fin n → Real),
        x ∈ Finset.sum s (fun i => w i • C i) ↔
          ∃ z : Fin m → Fin n → Real,
            (∀ i ∈ s, z i ∈ C i) ∧ x = Finset.sum s (fun i => w i • z i) := by
    intro s
    refine Finset.induction_on s ?h0 ?hstep
    · intro x
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro i hi
          cases hi
        · simp [hx0]
      · rintro ⟨z, hz, hx⟩
        have hx0 : x = 0 := by simpa using hx
        simp [hx0]
    · intro a s ha hs x
      constructor
      · intro hx
        have hx' :
            x ∈ w a • C a + Finset.sum s (fun i => w i • C i) := by
          simpa [Finset.sum_insert, ha] using hx
        rcases (Set.mem_add).1 hx' with ⟨x1, hx1, x2, hx2, rfl⟩
        rcases (Set.mem_smul_set.mp hx1) with ⟨y1, hy1, rfl⟩
        rcases (hs x2).1 hx2 with ⟨z, hz, hsum⟩
        let z' : Fin m → Fin n → Real := fun i => if i = a then y1 else z i
        refine ⟨z', ?_, ?_⟩
        · intro i hi
          by_cases hia : i = a
          · subst hia
            simpa [z'] using hy1
          · have hi' : i ∈ s := by
              rcases (Finset.mem_insert.mp hi) with hia' | hi'
              · exact (hia hia').elim
              · exact hi'
            have hz' : z i ∈ C i := hz i hi'
            simpa [z', hia] using hz'
        · have hsum' :
            Finset.sum s (fun i => w i • z' i) =
              Finset.sum s (fun i => w i • z i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hia : i ≠ a := by
              intro hia'
              exact ha (hia' ▸ hi)
            simp [z', hia]
          calc
            w a • y1 + x2 = w a • z' a + Finset.sum s (fun i => w i • z i) := by
              simp [z', hsum]
            _ = w a • z' a + Finset.sum s (fun i => w i • z' i) := by
              simp [hsum']
            _ = Finset.sum (insert a s) (fun i => w i • z' i) := by
              simp [Finset.sum_insert, ha]
      · rintro ⟨z, hz, hx⟩
        have hz_s : ∀ i ∈ s, z i ∈ C i := by
          intro i hi
          exact hz i (by simp [hi])
        have hx2 :
            Finset.sum s (fun i => w i • z i) ∈
              Finset.sum s (fun i => w i • C i) := by
          exact (hs (Finset.sum s (fun i => w i • z i))).2 ⟨z, hz_s, rfl⟩
        have hx1 : w a • z a ∈ w a • C a := by
          exact Set.smul_mem_smul_set (a := w a) (s := C a) (hz a (by simp))
        have hxsum : x = w a • z a + Finset.sum s (fun i => w i • z i) := by
          calc
            x = Finset.sum (insert a s) (fun i => w i • z i) := hx
            _ = w a • z a + Finset.sum s (fun i => w i • z i) := by
              simp [Finset.sum_insert, ha]
        have hxmem :
            x ∈ w a • C a + Finset.sum s (fun i => w i • C i) := by
          refine (Set.mem_add).2 ?_
          refine ⟨w a • z a, hx1, Finset.sum s (fun i => w i • z i), hx2, ?_⟩
          exact hxsum.symm
        simpa [Finset.sum_insert, ha] using hxmem
  simpa using (h (Finset.univ : Finset (Fin m)) x)

/-- Choose indices witnessing membership in a union of sets. -/
lemma choose_index_family_of_mem_iUnion {n m : ℕ} {I : Type*} {C : I → Set (Fin n → Real)}
    {x : Fin m → Fin n → Real} (hx : ∀ i, x i ∈ ⋃ j, C j) :
    ∃ f : Fin m → I, ∀ i, x i ∈ C (f i) := by
  classical
  refine ⟨fun i => Classical.choose (Set.mem_iUnion.1 (hx i)), ?_⟩
  intro i
  have h := Classical.choose_spec (Set.mem_iUnion.1 (hx i))
  simpa using h

/-- Theorem 3.3: If `{C_i | i ∈ I}` is a collection of nonempty convex sets in `ℝ^n`
and `C` is the convex hull of their union, then `C` is the union of all finite
convex combinations `∑ i, λ_i C_i`, where the coefficients are nonnegative,
only finitely many are nonzero, and they sum to `1`. -/
theorem convexHull_iUnion_eq_setOf_finite_convexCombinations {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → Real)) (_hCne : ∀ i, (C i).Nonempty)
    (_hCconv : ∀ i, Convex Real (C i)) :
    convexHull Real (⋃ i, C i) =
      {x : Fin n → Real |
        ∃ m : ℕ, ∃ f : Fin m → I, ∃ w : Fin m → Real,
          (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ x ∈ ∑ i, w i • C (f i)} := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_convexHull_iff_exists_fin_isConvexCombination n (⋃ i, C i) x).1 hx with
      ⟨m, y, hyS, hcomb⟩
    rcases hcomb with ⟨w, hw0, hw1, hxsum⟩
    obtain ⟨f, hf⟩ := choose_index_family_of_mem_iUnion (C := C) (x := y) hyS
    refine ⟨m, f, w, hw0, hw1, ?_⟩
    exact (mem_sum_smul_set_iff_exists_points (C := fun i => C (f i)) (w := w) (x := x)).2
      ⟨y, hf, hxsum⟩
  · rintro ⟨m, f, w, hw0, hw1, hxmem⟩
    rcases (mem_sum_smul_set_iff_exists_points (C := fun i => C (f i)) (w := w) (x := x)).1
        hxmem with ⟨y, hyC, hxsum⟩
    have hyS : ∀ i, y i ∈ ⋃ j, C j := by
      intro i
      exact Set.mem_iUnion.2 ⟨f i, hyC i⟩
    refine (mem_convexHull_iff_exists_fin_isConvexCombination n (⋃ i, C i) x).2 ?_
    refine ⟨m, y, hyS, ?_⟩
    exact ⟨w, hw0, hw1, hxsum⟩

/-- Text 3.4.0: Given a linear transformation `A` from `ℝ^n` to `ℝ^m`, the image of
`C ⊆ ℝ^n` under `A` is `AC = {A x | x ∈ C}`. -/
def linearImage {n m : ℕ} (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (C : Set (Fin n → Real)) : Set (Fin m → Real) :=
  A '' C

/-- Text 3.4.0: Given a linear transformation `A` from `ℝ^n` to `ℝ^m`, the inverse
image of `D ⊆ ℝ^m` under `A` is `A⁻¹ D = {x | A x ∈ D}`. -/
def linearPreimage {n m : ℕ} (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (D : Set (Fin m → Real)) : Set (Fin n → Real) :=
  A ⁻¹' D

/-- Linear images of convex sets are convex. -/
lemma convex_linearImage {n m : ℕ}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) {C : Set (Fin n → Real)}
    (hC : Convex Real C) : Convex Real (linearImage A C) := by
  simpa [linearImage] using (hC.linear_image A)

/-- Linear preimages of convex sets are convex. -/
lemma convex_linearPreimage {n m : ℕ}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) {D : Set (Fin m → Real)}
    (hD : Convex Real D) : Convex Real (linearPreimage A D) := by
  simpa [linearPreimage] using (hD.linear_preimage A)

/-- Theorem 3.4: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. Then
`A C` is a convex set in `ℝ^m` for every convex set `C` in `ℝ^n`, and `A⁻¹ D`
is a convex set in `ℝ^n` for every convex set `D` in `ℝ^m`. -/
theorem convex_linearImage_and_preimage {n m : ℕ}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    (∀ {C : Set (Fin n → Real)}, Convex Real C → Convex Real (linearImage A C)) ∧
      (∀ {D : Set (Fin m → Real)}, Convex Real D → Convex Real (linearPreimage A D)) := by
  constructor
  · intro C hC
    exact convex_linearImage (A := A) hC
  · intro D hD
    exact convex_linearPreimage (A := A) hD

/-- Corollary 3.4.1: The orthogonal projection of a convex set `C` on a subspace `L`
is another convex set. -/
theorem convex_orthogonalProjection {n : ℕ}
    (L : Submodule Real (EuclideanSpace Real (Fin n)))
    [Submodule.HasOrthogonalProjection L] {C : Set (EuclideanSpace Real (Fin n))}
    (hC : Convex Real C) :
    Convex Real ((Submodule.starProjection (𝕜 := Real)
      (E := EuclideanSpace Real (Fin n)) L) '' C) := by
  simpa using (hC.linear_image
    ((Submodule.starProjection (𝕜 := Real)
      (E := EuclideanSpace Real (Fin n)) L).toLinearMap))

/-- Translating the nonnegative orthant yields the upper set `≥ a`. -/
lemma translate_nonneg_orthant_eq_ge {m : ℕ} (a : Fin m → Real) :
    Set.image (fun u => u + a) {u : Fin m → Real | 0 ≤ u} =
      {y : Fin m → Real | y ≥ a} := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    intro i
    exact le_add_of_nonneg_left (hu i)
  · intro hy
    refine ⟨y - a, ?_, ?_⟩
    · intro i
      exact sub_nonneg.mpr (hy i)
    · funext i
      simp

/-- The preimage of the translated nonnegative orthant is a pointwise inequality. -/
lemma linearPreimage_translate_nonneg_orthant_eq_ge {m n : ℕ}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) (a : Fin m → Real) :
    linearPreimage A (Set.image (fun u => u + a) {u : Fin m → Real | 0 ≤ u}) =
      {x : Fin n → Real | A x ≥ a} := by
  ext x
  simp [linearPreimage, translate_nonneg_orthant_eq_ge (a := a)]

/-- The image of the nonnegative orthant is characterized by existence. -/
lemma linearImage_nonneg_orthant_eq_exists {m n : ℕ}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    linearImage A {x : Fin n → Real | 0 ≤ x} =
      {y : Fin m → Real | ∃ x, 0 ≤ x ∧ A x = y} := by
  ext y
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, hx, rfl⟩
  · exact ⟨x, hx, rfl⟩

/-- Text 3.4.2: Let `A ∈ ℝ^{m×n}`. Define the nonnegative orthants
`K = {u ∈ ℝ^m | u ≥ 0}` and `C = {x ∈ ℝ^n | x ≥ 0}` and for `a ∈ ℝ^m` set
`D = K + a = {u + a | u ∈ K} = {y ∈ ℝ^m | y ≥ a}`. Then the preimage
`A⁻¹ D` equals `{x ∈ ℝ^n | A x ≥ a}` and the image `A C` equals
`{y ∈ ℝ^m | ∃ x ∈ ℝ^n_+, A x = y}`. -/
theorem linearImage_preimage_nonneg_orthant {m n : ℕ}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) (a : Fin m → Real) :
    (let K : Set (Fin m → Real) := {u | 0 ≤ u}
     let C : Set (Fin n → Real) := {x | 0 ≤ x}
     let D : Set (Fin m → Real) := Set.image (fun u => u + a) K
     D = {y | y ≥ a} ∧
       linearPreimage A D = {x | A x ≥ a} ∧
       linearImage A C = {y | ∃ x, 0 ≤ x ∧ A x = y}) := by
  dsimp
  refine ⟨translate_nonneg_orthant_eq_ge (a := a), ?_⟩
  refine ⟨linearPreimage_translate_nonneg_orthant_eq_ge (A := A) (a := a), ?_⟩
  exact linearImage_nonneg_orthant_eq_exists (A := A)

/-- Theorem 3.5: For convex sets `C ⊆ ℝ^m` and `D ⊆ ℝ^n`, the direct-sum set
`C ⊕ D = {x = (y, z) | y ∈ C, z ∈ D}` is a convex set in `ℝ^{m+n}`. -/
theorem convex_prod {m n : ℕ} {C : Set (Fin m → Real)} {D : Set (Fin n → Real)}
    (hC : Convex Real C) (hD : Convex Real D) :
    Convex Real (Set.prod C D) := by
  simpa using hC.prod hD

/-- Text 3.5.1: Let `C` and `D` be convex sets in `ℝ^m` and `ℝ^n`. Then
`C ⊕ D = {x = (y, z) | y ∈ C, z ∈ D}` is called the direct sum of `C` and `D`. -/
def directSumSet {m n : ℕ} (C : Set (Fin m → Real)) (D : Set (Fin n → Real)) :
    Set ((Fin m → Real) × (Fin n → Real)) :=
  Set.prod C D

/-- Text 3.5.2: The direct sum of two convex sets is convex. -/
theorem convex_directSumSet {m n : ℕ} {C : Set (Fin m → Real)} {D : Set (Fin n → Real)}
    (hC : Convex Real C) (hD : Convex Real D) :
    Convex Real (directSumSet C D) := by
  simpa [directSumSet] using (convex_prod (hC := hC) (hD := hD))

/-- Unique decomposition forces elements of `(C - C) ∩ (D - D)` to be zero. -/
lemma unique_decomp_imp_intersection_subset_zero {n : ℕ} {C D : Set (Fin n → Real)}
    (huniq : ∀ x ∈ C + D, ∃! yz : (Fin n → Real) × (Fin n → Real),
      yz.1 ∈ C ∧ yz.2 ∈ D ∧ x = yz.1 + yz.2) :
    ∀ v, v ∈ (C - C) ∩ (D - D) → v = 0 := by
  intro v hv
  rcases hv with ⟨hvC, hvD⟩
  rcases (Set.mem_sub).1 hvC with ⟨c1, hc1, c2, hc2, rfl⟩
  rcases (Set.mem_sub).1 hvD with ⟨d1, hd1, d2, hd2, h_eq⟩
  have hx : c2 + d1 = c1 + d2 := by
    have hx' : d1 + c2 = c1 + d2 :=
      (sub_eq_sub_iff_add_eq_add).1 h_eq
    simpa [add_comm] using hx'
  have hx_mem : c2 + d1 ∈ C + D :=
    (Set.mem_add).2 ⟨c2, hc2, d1, hd1, rfl⟩
  rcases huniq (c2 + d1) hx_mem with ⟨yz, hyz, hyz_unique⟩
  have hcd : (c2, d1) = yz := by
    apply hyz_unique
    exact ⟨hc2, hd1, rfl⟩
  have hcd' : (c1, d2) = yz := by
    apply hyz_unique
    exact ⟨hc1, hd2, hx⟩
  have hpair : (c2, d1) = (c1, d2) := by
    calc
      (c2, d1) = yz := hcd
      _ = (c1, d2) := hcd'.symm
  have hc_eq : c1 = c2 := by
    exact (congrArg Prod.fst hpair).symm
  simp [hc_eq]

/-- If `C` and `D` are nonempty, then `0 ∈ (C - C) ∩ (D - D)`. -/
lemma zero_mem_intersection_of_nonempty {n : ℕ} {C D : Set (Fin n → Real)}
    (hC : C.Nonempty) (hD : D.Nonempty) :
    (0 : Fin n → Real) ∈ (C - C) ∩ (D - D) := by
  rcases hC with ⟨c, hc⟩
  rcases hD with ⟨d, hd⟩
  refine ⟨?_, ?_⟩
  · exact (Set.mem_sub).2 ⟨c, hc, c, hc, by simp⟩
  · exact (Set.mem_sub).2 ⟨d, hd, d, hd, by simp⟩

/-- Intersection criterion implies uniqueness of decompositions in `C + D`. -/
lemma intersection_eq_zero_imp_unique_decomp {n : ℕ} {C D : Set (Fin n → Real)}
    (hinter : (C - C) ∩ (D - D) = ({0} : Set (Fin n → Real))) :
    ∀ x ∈ C + D, ∃! yz : (Fin n → Real) × (Fin n → Real),
      yz.1 ∈ C ∧ yz.2 ∈ D ∧ x = yz.1 + yz.2 := by
  intro x hx
  rcases (Set.mem_add).1 hx with ⟨y, hy, z, hz, rfl⟩
  refine ⟨(y, z), ⟨hy, hz, rfl⟩, ?_⟩
  intro yz hyz
  rcases hyz with ⟨hyz1, hyz2, hyz_eq⟩
  have hsub : y - yz.1 = yz.2 - z := by
    apply (sub_eq_sub_iff_add_eq_add).2
    simpa [add_comm] using hyz_eq
  have hyC : y - yz.1 ∈ C - C :=
    (Set.mem_sub).2 ⟨y, hy, yz.1, hyz1, rfl⟩
  have hyD : y - yz.1 ∈ D - D := by
    have : yz.2 - z ∈ D - D :=
      (Set.mem_sub).2 ⟨yz.2, hyz2, z, hz, rfl⟩
    simpa [hsub] using this
  have hmem : y - yz.1 ∈ (C - C) ∩ (D - D) := ⟨hyC, hyD⟩
  have hzero : y - yz.1 = 0 := by
    have : y - yz.1 ∈ ({0} : Set (Fin n → Real)) := by
      simpa [hinter] using hmem
    simpa using this
  have hy_eq : y = yz.1 := sub_eq_zero.mp hzero
  have hz_eq : yz.2 = z := by
    have hz0 : yz.2 - z = 0 := by
      simpa [hzero] using hsub.symm
    exact sub_eq_zero.mp hz0
  ext <;> simp [hy_eq.symm, hz_eq]

/-- Text 3.5.3: For sets `C, D ⊆ ℝ^n`, the following are equivalent:
(1) (Unique decomposition) Every `x ∈ C + D` can be written in a unique way as
`x = y + z` with `(y, z) ∈ C × D`.
(2) (Intersection criterion) `(C - C) ∩ (D - D) = {0}`. -/
theorem unique_decomposition_iff_intersection_sub {n : ℕ}
    (C D : Set (Fin n → Real)) (hC : C.Nonempty) (hD : D.Nonempty) :
    (∀ x ∈ C + D, ∃! yz : (Fin n → Real) × (Fin n → Real),
      yz.1 ∈ C ∧ yz.2 ∈ D ∧ x = yz.1 + yz.2) ↔
      (C - C) ∩ (D - D) = ({0} : Set (Fin n → Real)) := by
  constructor
  · intro huniq
    ext v
    constructor
    · intro hv
      have hv0 :=
        unique_decomp_imp_intersection_subset_zero (C := C) (D := D) huniq v hv
      simp [Set.mem_singleton_iff, hv0]
    · intro hv
      have hv0 : v = 0 := by
        simpa [Set.mem_singleton_iff] using hv
      have h0mem :
          (0 : Fin n → Real) ∈ (C - C) ∩ (D - D) :=
        zero_mem_intersection_of_nonempty (C := C) (D := D) hC hD
      simpa [hv0] using h0mem
  · intro hinter
    exact intersection_eq_zero_imp_unique_decomp (C := C) (D := D) hinter

/-- Text 3.5.4: If `C ⊆ ℝ^n` is convex, then `C - C` is a convex set. -/
theorem convex_sub_self {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) :
    Convex Real (C - C) := by
  simpa using hC.sub hC

/-- Push a scalar factor through membership in a scaled set. -/
lemma coneSet_smul_mem {n : ℕ} {C : Set (Fin n → Real)} {r a : Real}
    {x : Fin n → Real} (hx : x ∈ r • C) : a • x ∈ (a * r) • C := by
  rcases (Set.mem_smul_set.mp hx) with ⟨y, hy, rfl⟩
  exact (Set.mem_smul_set.mpr ⟨y, hy, by simp [smul_smul]⟩)

/-- Convexity combines elements of scaled sets into a larger scaled set. -/
lemma coneSet_combo_mem {n : ℕ} {C : Set (Fin n → Real)} (hC : Convex Real C)
    {r1 r2 a b : Real} {x1 x2 : Fin n → Real}
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hx1 : x1 ∈ r1 • C) (hx2 : x2 ∈ r2 • C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x1 + b • x2 ∈ (a * r1 + b * r2) • C := by
  have hx1' : a • x1 ∈ (a * r1) • C :=
    coneSet_smul_mem (a := a) (r := r1) hx1
  have hx2' : b • x2 ∈ (b * r2) • C :=
    coneSet_smul_mem (a := b) (r := r2) hx2
  have hsum :
      a • x1 + b • x2 ∈ (a * r1) • C + (b * r2) • C :=
    (Set.mem_add).2 ⟨a • x1, hx1', b • x2, hx2', rfl⟩
  have hconv :
      (a * r1 + b * r2) • C = (a * r1) • C + (b * r2) • C := by
    have hnonneg1 : 0 ≤ a * r1 := mul_nonneg ha hr1
    have hnonneg2 : 0 ≤ b * r2 := mul_nonneg hb hr2
    simpa using
      (convex_smul_add_eq (hC := hC) (r1 := a * r1) (r2 := b * r2)
        hnonneg1 hnonneg2)
  simpa [hconv] using hsum

/-- Text 3.5.5: For a convex set `C ⊆ ℝ^n`, the set
`K_C = { (λ, x) ∈ ℝ × ℝ^n | λ ≥ 0, x ∈ λ C }` is convex. -/
theorem convex_coneSet_of_convex {n : ℕ} {C : Set (Fin n → Real)}
    (hC : Convex Real C) :
    Convex Real {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C} := by
  intro p hp q hq a b ha hb hab
  rcases p with ⟨r1, x1⟩
  rcases q with ⟨r2, x2⟩
  rcases hp with ⟨hr1, hx1⟩
  rcases hq with ⟨hr2, hx2⟩
  have hnonneg : 0 ≤ a * r1 + b * r2 :=
    add_nonneg (mul_nonneg ha hr1) (mul_nonneg hb hr2)
  have hmem :
      a • x1 + b • x2 ∈ (a * r1 + b * r2) • C :=
    coneSet_combo_mem (hC := hC) (hr1 := hr1) (hr2 := hr2)
      (hx1 := hx1) (hx2 := hx2) (ha := ha) (hb := hb)
  refine ⟨?_, ?_⟩
  · simpa using hnonneg
  · simpa using hmem

/-- Linear combinations distribute over coordinatewise additions in `ℝ^p`. -/
lemma smul_add_smul_add_eq {p : ℕ} {a b : Real}
    (z1 z1' z2 z2' : Fin p → Real) :
    (a • z1 + b • z1') + (a • z2 + b • z2') =
      a • (z1 + z2) + b • (z1' + z2') := by
  ext i
  simp [Pi.add_apply, Pi.smul_apply]
  ring

/-- Theorem 3.6: Let `C1` and `C2` be convex sets in `ℝ^{m+p}`. Let `C` be the
set of vectors `x = (y, z)` with `y ∈ ℝ^m` and `z ∈ ℝ^p` such that there exist
`z1` and `z2` with `(y, z1) ∈ C1`, `(y, z2) ∈ C2`, and `z1 + z2 = z`. Then `C`
is a convex set in `ℝ^{m+p}`. -/
theorem convex_fiberwise_add {m p : ℕ}
    {C1 C2 : Set ((Fin m → Real) × (Fin p → Real))}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real
      {x : (Fin m → Real) × (Fin p → Real) |
        ∃ z1 z2 : Fin p → Real,
          (x.1, z1) ∈ C1 ∧ (x.1, z2) ∈ C2 ∧ z1 + z2 = x.2} := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨z1, z2, hx1, hx2, hxsum⟩
  rcases hy with ⟨z1', z2', hy1, hy2, hysum⟩
  refine ⟨a • z1 + b • z1', a • z2 + b • z2', ?_, ?_, ?_⟩
  · have hcombo : a • (x.1, z1) + b • (y.1, z1') ∈ C1 :=
      hC1 hx1 hy1 ha hb hab
    simpa using hcombo
  · have hcombo : a • (x.1, z2) + b • (y.1, z2') ∈ C2 :=
      hC2 hx2 hy2 ha hb hab
    simpa using hcombo
  · calc
      (a • z1 + b • z1') + (a • z2 + b • z2') =
          a • (z1 + z2) + b • (z1' + z2') :=
        smul_add_smul_add_eq (z1 := z1) (z1' := z1') (z2 := z2) (z2' := z2')
      _ = a • x.2 + b • y.2 := by
        simp [hxsum, hysum]
      _ = (a • x + b • y).2 := by
        simp

/-- Text 3.6.1: Define the inverse addition `C1 # C2` by
`⋃₀ {S | ∃ λ1 λ2, 0 ≤ λ1, 0 ≤ λ2, λ1 + λ2 = 1, S = (λ1 • C1) ∩ (λ2 • C2)}`,
equivalently as `⋃₀ { (1 - λ) • C1 ∩ λ • C2 | 0 ≤ λ ∧ λ ≤ 1 }`. -/
def inverseAddition {n : ℕ} (C1 C2 : Set (Fin n → Real)) : Set (Fin n → Real) :=
  ⋃₀ {S : Set (Fin n → Real) |
    ∃ r1 r2 : Real, 0 ≤ r1 ∧ 0 ≤ r2 ∧ r1 + r2 = 1 ∧
      S = (r1 • C1) ∩ (r2 • C2)}

notation:70 C1 " # " C2 => inverseAddition C1 C2

/-- Text 3.6.2: Let `C1` and `C2` be convex sets in `ℝ^{m+p}`. Let `C` be the set
of vectors `x = (y, z)` with `y ∈ ℝ^m` and `z ∈ ℝ^p` such that there exist
`y1` and `y2` with `(y1, z) ∈ C1`, `(y2, z) ∈ C2`, and `y1 + y2 = y`. Then `C`
is a convex set in `ℝ^{m+p}`. -/
theorem convex_fiberwise_add_left {m p : ℕ}
    {C1 C2 : Set ((Fin m → Real) × (Fin p → Real))}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real
      {x : (Fin m → Real) × (Fin p → Real) |
        ∃ y1 y2 : Fin m → Real,
          (y1, x.2) ∈ C1 ∧ (y2, x.2) ∈ C2 ∧ y1 + y2 = x.1} := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨y1, y2, hx1, hx2, hxsum⟩
  rcases hy with ⟨y1', y2', hy1, hy2, hysum⟩
  refine ⟨a • y1 + b • y1', a • y2 + b • y2', ?_, ?_, ?_⟩
  · have hcombo : a • (y1, x.2) + b • (y1', y.2) ∈ C1 :=
      hC1 hx1 hy1 ha hb hab
    simpa using hcombo
  · have hcombo : a • (y2, x.2) + b • (y2', y.2) ∈ C2 :=
      hC2 hx2 hy2 ha hb hab
    simpa using hcombo
  · calc
      (a • y1 + b • y1') + (a • y2 + b • y2') =
          a • (y1 + y2) + b • (y1' + y2') :=
        smul_add_smul_add_eq (z1 := y1) (z1' := y1') (z2 := y2) (z2' := y2')
      _ = a • x.1 + b • y.1 := by
        simp [hxsum, hysum]
      _ = (a • x + b • y).1 := by
        simp

/- Text 3.6.3: Let `C1` and `C2` be convex sets in `ℝ^{m+p}`. Let `C` be the set
of vectors `x = (y, z)` with `y ∈ ℝ^m` and `z ∈ ℝ^p` such that there exist
`y1, y2, z1, z2` with `(y1, z1) ∈ C1`, `(y2, z2) ∈ C2`, `y1 + y2 = y`, and
`z1 + z2 = z`. Then `C` is a convex set in `ℝ^{m+p}`. -/
/-- Membership in the componentwise-sum set is equivalent to membership in the
Minkowski sum in the product space. -/
lemma mem_add_prod_iff {m p : ℕ}
    {C1 C2 : Set ((Fin m → Real) × (Fin p → Real))}
    {x : (Fin m → Real) × (Fin p → Real)} :
    x ∈ {x : (Fin m → Real) × (Fin p → Real) |
        ∃ y1 y2 : Fin m → Real, ∃ z1 z2 : Fin p → Real,
          (y1, z1) ∈ C1 ∧ (y2, z2) ∈ C2 ∧ y1 + y2 = x.1 ∧ z1 + z2 = x.2} ↔
      x ∈ C1 + C2 := by
  constructor
  · intro hx
    rcases hx with ⟨y1, y2, z1, z2, hy1, hy2, hy, hz⟩
    refine (Set.mem_add).2 ?_
    refine ⟨(y1, z1), hy1, (y2, z2), hy2, ?_⟩
    ext <;> simp [hy, hz]
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
    refine ⟨x1.1, x2.1, x1.2, x2.2, ?_, ?_, ?_, ?_⟩
    · simpa using hx1
    · simpa using hx2
    · rfl
    · rfl

theorem convex_add_prod {m p : ℕ}
    {C1 C2 : Set ((Fin m → Real) × (Fin p → Real))}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real
      {x : (Fin m → Real) × (Fin p → Real) |
        ∃ y1 y2 : Fin m → Real, ∃ z1 z2 : Fin p → Real,
          (y1, z1) ∈ C1 ∧ (y2, z2) ∈ C2 ∧ y1 + y2 = x.1 ∧ z1 + z2 = x.2} := by
  have hset :
      {x : (Fin m → Real) × (Fin p → Real) |
        ∃ y1 y2 : Fin m → Real, ∃ z1 z2 : Fin p → Real,
          (y1, z1) ∈ C1 ∧ (y2, z2) ∈ C2 ∧ y1 + y2 = x.1 ∧ z1 + z2 = x.2} =
        C1 + C2 := by
    ext x
    simpa using (mem_add_prod_iff (C1 := C1) (C2 := C2) (x := x))
  exact hset.symm ▸ (hC1.add hC2)

/-- Text 3.6.4: If `C1` and `C2` are convex sets in `ℝ^n`, then `C1 ∩ C2`
is convex. -/
theorem convex_intersection {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real (C1 ∩ C2) := by
  exact hC1.inter hC2

/-- Text 3.6.5: Let `C1` and `C2` be convex sets in `ℝ^{m+p}`. Let `C` be the set
of vectors `x = (y, z)` with `y ∈ ℝ^m` and `z ∈ ℝ^p` such that `(y, z) ∈ C1` and
`(y, z) ∈ C2`. Then `C` is a convex set in `ℝ^{m+p}`. -/
theorem convex_intersection_prod {m p : ℕ}
    {C1 C2 : Set ((Fin m → Real) × (Fin p → Real))}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real (C1 ∩ C2) := by
  exact hC1.inter hC2

/-- Membership in the cone set at `λ = 1` reduces to membership in the base set. -/
lemma mem_coneSet_one_iff {n : ℕ} {C : Set (Fin n → Real)} {x : Fin n → Real} :
    ((1 : Real), x) ∈ {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C} ↔
      x ∈ C := by
  constructor
  · rintro ⟨_, hx⟩
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, hyx⟩
    have hy' : y = x := by
      simpa using hyx
    simpa [hy'] using hy
  · intro hx
    refine ⟨by simp, ?_⟩
    exact Set.mem_smul_set.mpr ⟨x, hx, by simp⟩

/-- Unfolding the cone sum at `λ = 1` yields a decomposition into `C1` and `C2`. -/
lemma mem_K_iff_exists_add {n : ℕ} {C1 C2 : Set (Fin n → Real)} {x : Fin n → Real} :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ x1 x2 : Fin n → Real,
            p.2 = x1 + x2 ∧ (p.1, x1) ∈ K1 ∧ (p.1, x2) ∈ K2}
      (1, x) ∈ K) ↔
      ∃ x1 x2 : Fin n → Real, x = x1 + x2 ∧ x1 ∈ C1 ∧ x2 ∈ C2 := by
  dsimp
  constructor
  · rintro ⟨x1, x2, hxsum, hx1, hx2⟩
    refine ⟨x1, x2, ?_, ?_, ?_⟩
    · simpa using hxsum
    · exact (mem_coneSet_one_iff (C := C1) (x := x1)).1 hx1
    · exact (mem_coneSet_one_iff (C := C2) (x := x2)).1 hx2
  · rintro ⟨x1, x2, hxsum, hx1, hx2⟩
    refine ⟨x1, x2, ?_, ?_, ?_⟩
    · simpa using hxsum
    · exact (mem_coneSet_one_iff (C := C1) (x := x1)).2 hx1
    · exact (mem_coneSet_one_iff (C := C2) (x := x2)).2 hx2

/-- Text 3.6.6: For convex sets `C1` and `C2` in `ℝ^n`, define
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`, `K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`,
and `K = { (λ, x) | ∃ x1 x2, x = x1 + x2 ∧ (λ, x1) ∈ K1 ∧ (λ, x2) ∈ K2 }`.
Then `(1, x) ∈ K` iff `x ∈ C1 + C2`. -/
theorem coneSet_add_iff {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (x : Fin n → Real) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ x1 x2 : Fin n → Real,
            p.2 = x1 + x2 ∧ (p.1, x1) ∈ K1 ∧ (p.1, x2) ∈ K2}
      (1, x) ∈ K ↔ x ∈ C1 + C2) := by
  constructor
  · intro hx
    have hx' :=
      (mem_K_iff_exists_add (C1 := C1) (C2 := C2) (x := x)).1 hx
    rcases hx' with ⟨x1, x2, hxsum, hx1, hx2⟩
    exact (Set.mem_add).2 ⟨x1, hx1, x2, hx2, by simpa using hxsum.symm⟩
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, hsum⟩
    have hx' : ∃ x1 x2 : Fin n → Real, x = x1 + x2 ∧ x1 ∈ C1 ∧ x2 ∈ C2 :=
      ⟨x1, x2, hsum.symm, hx1, hx2⟩
    exact (mem_K_iff_exists_add (C1 := C1) (C2 := C2) (x := x)).2 hx'

end Section03
end Chap01
