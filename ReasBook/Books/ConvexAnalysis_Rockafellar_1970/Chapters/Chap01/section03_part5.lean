/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section03_part4

open scoped BigOperators
open scoped Pointwise

section Chap01
section Section03

/-- A convex cone containing `0` is closed under nonnegative scaling. -/
lemma cone_smul_mem_of_nonneg {n : ℕ} (K : ConvexCone Real (Fin n → Real))
    (h0 : (0 : Fin n → Real) ∈ K) {r : Real} (hr : 0 ≤ r)
    {x : Fin n → Real} (hx : x ∈ K) : r • x ∈ K := by
  by_cases hr0 : r = 0
  · subst hr0
    simpa using h0
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    exact K.smul_mem hrpos hx

/-- For convex cones containing `0`, the convex join equals the Minkowski sum. -/
lemma convexJoin_eq_add_of_cones {n : ℕ}
    (K1 K2 : ConvexCone Real (Fin n → Real))
    (h0K1 : (0 : Fin n → Real) ∈ K1) (h0K2 : (0 : Fin n → Real) ∈ K2) :
    convexJoin Real (K1 : Set (Fin n → Real)) (K2 : Set (Fin n → Real)) =
      (K1 : Set (Fin n → Real)) + (K2 : Set (Fin n → Real)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_convexJoin (𝕜 := Real) (s := (K1 : Set (Fin n → Real)))
        (t := (K2 : Set (Fin n → Real))) (x := x)).1 hx with
      ⟨x1, hx1, x2, hx2, hxseg⟩
    rcases hxseg with ⟨a, b, ha, hb, -, hcomb⟩
    have hx1' : a • x1 ∈ (K1 : Set (Fin n → Real)) :=
      cone_smul_mem_of_nonneg K1 h0K1 ha hx1
    have hx2' : b • x2 ∈ (K2 : Set (Fin n → Real)) :=
      cone_smul_mem_of_nonneg K2 h0K2 hb hx2
    refine (Set.mem_add).2 ?_
    refine ⟨a • x1, hx1', b • x2, hx2', ?_⟩
    exact hcomb
  · intro hx
    rcases (Set.mem_add).1 hx with ⟨x1, hx1, x2, hx2, rfl⟩
    refine (mem_convexJoin (𝕜 := Real) (s := (K1 : Set (Fin n → Real)))
        (t := (K2 : Set (Fin n → Real))) (x := x1 + x2)).2 ?_
    have h2nonneg : (0 : Real) ≤ (2 : Real) := by norm_num
    have hx1' : (2 : Real) • x1 ∈ (K1 : Set (Fin n → Real)) :=
      cone_smul_mem_of_nonneg K1 h0K1 h2nonneg hx1
    have hx2' : (2 : Real) • x2 ∈ (K2 : Set (Fin n → Real)) :=
      cone_smul_mem_of_nonneg K2 h0K2 h2nonneg hx2
    refine ⟨2 • x1, hx1', 2 • x2, hx2', ?_⟩
    refine ⟨(1 / 2 : Real), (1 / 2 : Real), ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · ext i
      simp

/-- For convex cones containing `0`, inverse addition equals intersection. -/
lemma inverseAddition_eq_inter_of_cones {n : ℕ}
    (K1 K2 : ConvexCone Real (Fin n → Real))
    (h0K1 : (0 : Fin n → Real) ∈ K1) (h0K2 : (0 : Fin n → Real) ∈ K2) :
    ((K1 : Set (Fin n → Real)) # (K2 : Set (Fin n → Real))) =
      (K1 : Set (Fin n → Real)) ∩ (K2 : Set (Fin n → Real)) := by
  ext x
  constructor
  · intro hx
    rcases (Set.mem_sUnion).1 hx with ⟨S, hS, hxS⟩
    rcases hS with ⟨r1, r2, hr1, hr2, _, rfl⟩
    rcases hxS with ⟨hx1, hx2⟩
    rcases (Set.mem_smul_set).1 hx1 with ⟨y1, hy1, hy1eq⟩
    rcases (Set.mem_smul_set).1 hx2 with ⟨y2, hy2, hy2eq⟩
    have hy1' : r1 • y1 ∈ (K1 : Set (Fin n → Real)) :=
      cone_smul_mem_of_nonneg K1 h0K1 hr1 hy1
    have hy2' : r2 • y2 ∈ (K2 : Set (Fin n → Real)) :=
      cone_smul_mem_of_nonneg K2 h0K2 hr2 hy2
    have hxK1 : x ∈ (K1 : Set (Fin n → Real)) := by
      simpa [hy1eq] using hy1'
    have hxK2 : x ∈ (K2 : Set (Fin n → Real)) := by
      simpa [hy2eq] using hy2'
    exact ⟨hxK1, hxK2⟩
  · rintro ⟨hx1, hx2⟩
    refine (Set.mem_sUnion).2 ?_
    refine ⟨((1 / 2 : Real) • (K1 : Set (Fin n → Real))) ∩
        ((1 / 2 : Real) • (K2 : Set (Fin n → Real))), ?_, ?_⟩
    · refine ⟨(1 / 2 : Real), (1 / 2 : Real), ?_, ?_, ?_, rfl⟩
      · norm_num
      · norm_num
      · norm_num
    · refine ⟨?_, ?_⟩
      · have hx1' : (2 : Real) • x ∈ (K1 : Set (Fin n → Real)) :=
          cone_smul_mem_of_nonneg K1 h0K1 (by norm_num) hx1
        refine (Set.mem_smul_set).2 ?_
        refine ⟨2 • x, hx1', ?_⟩
        ext i
        simp [Pi.smul_apply]
      · have hx2' : (2 : Real) • x ∈ (K2 : Set (Fin n → Real)) :=
          cone_smul_mem_of_nonneg K2 h0K2 (by norm_num) hx2
        refine (Set.mem_smul_set).2 ?_
        refine ⟨2 • x, hx2', ?_⟩
        ext i
        simp [Pi.smul_apply]

/-- Theorem 3.8: If `K1` and `K2` are convex cones containing the origin, then
`K1 + K2 = conv(K1 ∪ K2)` and `K1 # K2 = K1 ∩ K2`. -/
theorem convexCone_add_eq_convexHull_union_and_inverseAddition_eq_inter {n : ℕ}
    (K1 K2 : ConvexCone Real (Fin n → Real))
    (h0K1 : (0 : Fin n → Real) ∈ K1) (h0K2 : (0 : Fin n → Real) ∈ K2) :
    ((K1 : Set (Fin n → Real)) + (K2 : Set (Fin n → Real)) =
        convexHull Real ((K1 : Set (Fin n → Real)) ∪ (K2 : Set (Fin n → Real)))) ∧
    (((K1 : Set (Fin n → Real)) # (K2 : Set (Fin n → Real))) =
        ((K1 : Set (Fin n → Real)) ∩ (K2 : Set (Fin n → Real)))) := by
  have hK1ne : (K1 : Set (Fin n → Real)).Nonempty := ⟨0, h0K1⟩
  have hK2ne : (K2 : Set (Fin n → Real)).Nonempty := ⟨0, h0K2⟩
  have hconvHull :
      convexHull Real ((K1 : Set (Fin n → Real)) ∪ (K2 : Set (Fin n → Real))) =
        convexJoin Real (K1 : Set (Fin n → Real)) (K2 : Set (Fin n → Real)) :=
    (K1.convex).convexHull_union (K2.convex) hK1ne hK2ne
  have hjoin :
      convexJoin Real (K1 : Set (Fin n → Real)) (K2 : Set (Fin n → Real)) =
        (K1 : Set (Fin n → Real)) + (K2 : Set (Fin n → Real)) :=
    convexJoin_eq_add_of_cones (K1 := K1) (K2 := K2) h0K1 h0K2
  refine ⟨?_, ?_⟩
  · calc
      (K1 : Set (Fin n → Real)) + (K2 : Set (Fin n → Real)) =
          convexJoin Real (K1 : Set (Fin n → Real)) (K2 : Set (Fin n → Real)) := by
            simpa using hjoin.symm
      _ = convexHull Real ((K1 : Set (Fin n → Real)) ∪ (K2 : Set (Fin n → Real))) := by
            simpa using hconvHull.symm
  · simpa using
      (inverseAddition_eq_inter_of_cones (K1 := K1) (K2 := K2) h0K1 h0K2)

/-- Text 3.8.1: The umbra of `C` with respect to `S`, for disjoint subsets
`C, S ⊆ ℝ^n`, is the set `⋂ x ∈ S, ⋃ λ ≥ 1, ((1 - λ) • x) + λ • C`. -/
def umbra {n : ℕ} (C S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  ⋂ x ∈ S, ⋃ r ≥ (1 : Real), ({(1 - r) • x} : Set (Fin n → Real)) + (r • C)

/-- Text 3.8.2: The penumbra of `C` with respect to `S`, for disjoint subsets
`C, S ⊆ ℝ^n`, is the set `⋃ x ∈ S, ⋃ λ ≥ 1, ((1 - λ) • x) + λ • C`. -/
def penumbra {n : ℕ} (C S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  ⋃ x ∈ S, ⋃ r ≥ (1 : Real), ({(1 - r) • x} : Set (Fin n → Real)) + (r • C)

/-- Membership in a slice of the umbra can be written with explicit witnesses. -/
lemma mem_umbra_slice_iff {n : ℕ} {C : Set (Fin n → Real)} {x u : Fin n → Real} :
    u ∈ ⋃ r ≥ (1 : Real), ({(1 - r) • x} : Set (Fin n → Real)) + (r • C) ↔
      ∃ r ≥ (1 : Real), ∃ c ∈ C, u = (1 - r) • x + r • c := by
  constructor
  · intro hu
    rcases Set.mem_iUnion.1 hu with ⟨r, hu⟩
    rcases Set.mem_iUnion.1 hu with ⟨hr, hu⟩
    rcases Set.mem_add.1 hu with ⟨a, ha, b, hb, hsum⟩
    have ha' : a = (1 - r) • x := by simpa using ha
    rcases Set.mem_smul_set.1 hb with ⟨c, hc, rfl⟩
    refine ⟨r, hr, c, hc, ?_⟩
    simpa [ha'] using hsum.symm
  · rintro ⟨r, hr, c, hc, hEq⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨r, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨hr, ?_⟩
    refine Set.mem_add.2 ?_
    refine ⟨(1 - r) • x, by simp, r • c, ?_, ?_⟩
    · exact (Set.mem_smul_set).2 ⟨c, hc, rfl⟩
    · simpa using hEq.symm

/-- Each umbra slice is convex when `C` is convex. -/
lemma convex_umbra_slice {n : ℕ} {C : Set (Fin n → Real)} (hC : Convex Real C)
    (x : Fin n → Real) :
    Convex Real (⋃ r ≥ (1 : Real), ({(1 - r) • x} : Set (Fin n → Real)) + (r • C)) := by
  classical
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  rcases (mem_umbra_slice_iff (C := C) (x := x) (u := u)).1 hu with
    ⟨r1, hr1, c1, hc1, rfl⟩
  rcases (mem_umbra_slice_iff (C := C) (x := x) (u := v)).1 hv with
    ⟨r2, hr2, c2, hc2, rfl⟩
  set r : Real := a * r1 + b * r2 with hrdef
  have hr : (1 : Real) ≤ r := by
    nlinarith [ha, hb, hr1, hr2, hab, hrdef]
  have hrpos : 0 < r := by linarith
  have hrne : r ≠ 0 := by linarith
  set c : Fin n → Real := (a * r1 / r) • c1 + (b * r2 / r) • c2 with hcdef
  have hc : c ∈ C := by
    have ha' : 0 ≤ a * r1 / r := by
      have hnonneg : 0 ≤ a * r1 := by nlinarith [ha, hr1]
      exact div_nonneg hnonneg (le_of_lt hrpos)
    have hb' : 0 ≤ b * r2 / r := by
      have hnonneg : 0 ≤ b * r2 := by nlinarith [hb, hr2]
      exact div_nonneg hnonneg (le_of_lt hrpos)
    have hsum : a * r1 / r + b * r2 / r = (1 : Real) := by
      calc
        a * r1 / r + b * r2 / r = (a * r1 + b * r2) / r := by
          symm
          exact add_div (a * r1) (b * r2) r
        _ = r / r := by simp [hrdef]
        _ = (1 : Real) := by simp [hrne]
    exact hC hc1 hc2 ha' hb' hsum
  have hmul1 : r * (a * r1 / r) = a * r1 := by
    field_simp [hrne]
  have hmul2 : r * (b * r2 / r) = b * r2 := by
    field_simp [hrne]
  have hrc : r • c = (a * r1) • c1 + (b * r2) • c2 := by
    calc
      r • c = r • ((a * r1 / r) • c1 + (b * r2 / r) • c2) := by simp [hcdef]
      _ = r • ((a * r1 / r) • c1) + r • ((b * r2 / r) • c2) := by
          simp
      _ = (r * (a * r1 / r)) • c1 + (r * (b * r2 / r)) • c2 := by
          simp [mul_smul]
      _ = (a * r1) • c1 + (b * r2) • c2 := by
          simp [hmul1, hmul2]
  have hcomb :
      a • ((1 - r1) • x + r1 • c1) + b • ((1 - r2) • x + r2 • c2)
        = (1 - r) • x + (a * r1) • c1 + (b * r2) • c2 := by
    ext i
    have hab' : a = 1 - b := by linarith [hab]
    simp [hrdef, hab']
    ring_nf
  apply (mem_umbra_slice_iff (C := C) (x := x)
      (u := a • ((1 - r1) • x + r1 • c1) + b • ((1 - r2) • x + r2 • c2))).2
  refine ⟨r, hr, c, hc, ?_⟩
  calc
    a • ((1 - r1) • x + r1 • c1) + b • ((1 - r2) • x + r2 • c2)
        = (1 - r) • x + (a * r1) • c1 + (b * r2) • c2 := hcomb
    _ = (1 - r) • x + ((a * r1) • c1 + (b * r2) • c2) := by
        simp [add_assoc]
    _ = (1 - r) • x + r • c := by
        rw [← hrc]

/-- Text 3.8.3: The umbra is convex if `C` is convex. -/
theorem convex_umbra_of_convex {n : ℕ} {C S : Set (Fin n → Real)}
    (hC : Convex Real C) :
    Convex Real (umbra C S) := by
  classical
  refine convex_iInter ?_
  intro x
  refine convex_iInter ?_
  intro hx
  simpa using (convex_umbra_slice (C := C) (x := x) hC)

/-- Text 3.8.4: The penumbra is convex if both `S` and `C` are convex. -/
theorem convex_penumbra_of_convex {n : ℕ} {C S : Set (Fin n → Real)}
    (hC : Convex Real C) (hS : Convex Real S) :
    Convex Real (penumbra C S) := by
  classical
  by_cases hSnonempty : S.Nonempty
  · rw [convex_iff_add_mem]
    intro u hu v hv a b ha hb hab
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith [hab]
      simpa [hb1] using hv
    by_cases hb0 : b = 0
    · subst hb0
      have ha1 : a = 1 := by linarith [hab]
      simpa [ha1] using hu
    rcases Set.mem_iUnion.1 hu with ⟨x1, hu⟩
    rcases Set.mem_iUnion.1 hu with ⟨hx1, hu⟩
    rcases (mem_umbra_slice_iff (C := C) (x := x1) (u := u)).1 hu with
      ⟨r1, hr1, c1, hc1, huEq⟩
    rcases Set.mem_iUnion.1 hv with ⟨x2, hv⟩
    rcases Set.mem_iUnion.1 hv with ⟨hx2, hv⟩
    rcases (mem_umbra_slice_iff (C := C) (x := x2) (u := v)).1 hv with
      ⟨r2, hr2, c2, hc2, hvEq⟩
    set r : Real := a * r1 + b * r2 with hrdef
    have hr : (1 : Real) ≤ r := by
      nlinarith [ha, hb, hr1, hr2, hab, hrdef]
    have hrpos : 0 < r := by linarith [hr]
    have hrne : r ≠ 0 := by linarith [hrpos]
    set c : Fin n → Real := (a * r1 / r) • c1 + (b * r2 / r) • c2 with hcdef
    have hc : c ∈ C := by
      have ha' : 0 ≤ a * r1 / r := by
        have hnonneg : 0 ≤ a * r1 := by nlinarith [ha, hr1]
        exact div_nonneg hnonneg (le_of_lt hrpos)
      have hb' : 0 ≤ b * r2 / r := by
        have hnonneg : 0 ≤ b * r2 := by nlinarith [hb, hr2]
        exact div_nonneg hnonneg (le_of_lt hrpos)
      have hsum : a * r1 / r + b * r2 / r = (1 : Real) := by
        calc
          a * r1 / r + b * r2 / r = (a * r1 + b * r2) / r := by
            symm
            exact add_div (a * r1) (b * r2) r
          _ = r / r := by simp [hrdef]
          _ = (1 : Real) := by simp [hrne]
      exact hC hc1 hc2 ha' hb' hsum
    by_cases hrone : r = 1
    · rcases hSnonempty with ⟨x0, hx0⟩
      have hsumzero : a * (r1 - 1) + b * (r2 - 1) = 0 := by
        nlinarith [hrdef, hrone, hab]
      have hterm1 : a * (r1 - 1) = 0 := by
        have hnonneg1 : 0 ≤ a * (r1 - 1) := by nlinarith [ha, hr1]
        have hnonneg2 : 0 ≤ b * (r2 - 1) := by nlinarith [hb, hr2]
        nlinarith [hsumzero, hnonneg1, hnonneg2]
      have hterm2 : b * (r2 - 1) = 0 := by
        have hnonneg1 : 0 ≤ a * (r1 - 1) := by nlinarith [ha, hr1]
        have hnonneg2 : 0 ≤ b * (r2 - 1) := by nlinarith [hb, hr2]
        nlinarith [hsumzero, hnonneg1, hnonneg2]
      have hr1eq : r1 = 1 := by
        rcases mul_eq_zero.1 hterm1 with hzero | hzero
        · exact (ha0 hzero).elim
        · linarith
      have hr2eq : r2 = 1 := by
        rcases mul_eq_zero.1 hterm2 with hzero | hzero
        · exact (hb0 hzero).elim
        · linarith
      have hwC : a • u + b • v ∈ C := by
        have hwC' : a • c1 + b • c2 ∈ C := hC hc1 hc2 ha hb hab
        have huc : u = c1 := by simp [huEq, hr1eq]
        have hvc : v = c2 := by simp [hvEq, hr2eq]
        convert hwC' using 1
        simp [huc, hvc]
      refine Set.mem_iUnion.2 ?_
      refine ⟨x0, ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨hx0, ?_⟩
      refine (mem_umbra_slice_iff (C := C) (x := x0) (u := a • u + b • v)).2 ?_
      refine ⟨1, by linarith, a • u + b • v, hwC, ?_⟩
      simp
    · have hrne' : r - 1 ≠ 0 := by
        intro h
        apply hrone
        exact sub_eq_zero.mp h
      have hrlt : 1 < r := lt_of_le_of_ne hr (Ne.symm hrone)
      have hrpos' : 0 < r - 1 := by linarith [hrlt]
      set x : Fin n → Real :=
          (a * (r1 - 1) / (r - 1)) • x1 + (b * (r2 - 1) / (r - 1)) • x2 with hxdef
      have hax : 0 ≤ a * (r1 - 1) / (r - 1) := by
        have hnonneg : 0 ≤ a * (r1 - 1) := by nlinarith [ha, hr1]
        exact div_nonneg hnonneg (le_of_lt hrpos')
      have hbx : 0 ≤ b * (r2 - 1) / (r - 1) := by
        have hnonneg : 0 ≤ b * (r2 - 1) := by nlinarith [hb, hr2]
        exact div_nonneg hnonneg (le_of_lt hrpos')
      have hsumx : a * (r1 - 1) / (r - 1) + b * (r2 - 1) / (r - 1) = (1 : Real) := by
        have hrdiff : r - 1 = a * (r1 - 1) + b * (r2 - 1) := by
          nlinarith [hrdef, hab]
        calc
          a * (r1 - 1) / (r - 1) + b * (r2 - 1) / (r - 1) =
              (a * (r1 - 1) + b * (r2 - 1)) / (r - 1) := by
                symm
                exact add_div (a * (r1 - 1)) (b * (r2 - 1)) (r - 1)
          _ = (r - 1) / (r - 1) := by simp [hrdiff]
          _ = (1 : Real) := by simp [hrne']
      have hx : x ∈ S := by
        have hx' :
            (a * (r1 - 1) / (r - 1)) • x1 + (b * (r2 - 1) / (r - 1)) • x2 ∈ S :=
          hS hx1 hx2 hax hbx hsumx
        convert hx' using 1
      have hmul1 : r * (a * r1 / r) = a * r1 := by
        field_simp [hrne]
      have hmul2 : r * (b * r2 / r) = b * r2 := by
        field_simp [hrne]
      have hrc : r • c = (a * r1) • c1 + (b * r2) • c2 := by
        calc
          r • c = r • ((a * r1 / r) • c1 + (b * r2 / r) • c2) := by simp [hcdef]
          _ = r • ((a * r1 / r) • c1) + r • ((b * r2 / r) • c2) := by
              simp
          _ = (r * (a * r1 / r)) • c1 + (r * (b * r2 / r)) • c2 := by
              simp [mul_smul]
          _ = (a * r1) • c1 + (b * r2) • c2 := by
              simp [hmul1, hmul2]
      have hmulx1 :
          (1 - r) * (a * (r1 - 1) / (r - 1)) = a * (1 - r1) := by
        calc
          (1 - r) * (a * (r1 - 1) / (r - 1)) =
              - (r - 1) * (a * (r1 - 1) / (r - 1)) := by ring
          _ = - (a * (r1 - 1)) := by field_simp [hrne']
          _ = a * (1 - r1) := by ring
      have hmulx2 :
          (1 - r) * (b * (r2 - 1) / (r - 1)) = b * (1 - r2) := by
        calc
          (1 - r) * (b * (r2 - 1) / (r - 1)) =
              - (r - 1) * (b * (r2 - 1) / (r - 1)) := by ring
          _ = - (b * (r2 - 1)) := by field_simp [hrne']
          _ = b * (1 - r2) := by ring
      have hxr : (1 - r) • x = (a * (1 - r1)) • x1 + (b * (1 - r2)) • x2 := by
        calc
          (1 - r) • x =
              (1 - r) • ((a * (r1 - 1) / (r - 1)) • x1 +
                (b * (r2 - 1) / (r - 1)) • x2) := by simp [hxdef]
          _ = (1 - r) • ((a * (r1 - 1) / (r - 1)) • x1) +
                (1 - r) • ((b * (r2 - 1) / (r - 1)) • x2) := by
              simp
          _ = ((1 - r) * (a * (r1 - 1) / (r - 1))) • x1 +
                ((1 - r) * (b * (r2 - 1) / (r - 1))) • x2 := by
              simp [mul_smul]
          _ = (a * (1 - r1)) • x1 + (b * (1 - r2)) • x2 := by
              simp [hmulx1, hmulx2]
      have hcomb :
          a • u + b • v =
            (a * (1 - r1)) • x1 + (b * (1 - r2)) • x2 +
            (a * r1) • c1 + (b * r2) • c2 := by
        ext i
        simp [huEq, hvEq]
        ring
      have hw : a • u + b • v = (1 - r) • x + r • c := by
        calc
          a • u + b • v =
              (a * (1 - r1)) • x1 + (b * (1 - r2)) • x2 +
              (a * r1) • c1 + (b * r2) • c2 := hcomb
          _ = (1 - r) • x + r • c := by
              simp [hxr, hrc, add_assoc, add_left_comm, add_comm]
      refine Set.mem_iUnion.2 ?_
      refine ⟨x, ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨hx, ?_⟩
      refine (mem_umbra_slice_iff (C := C) (x := x) (u := a • u + b • v)).2 ?_
      refine ⟨r, hr, c, hc, ?_⟩
      simp [hw]
  · have hSempty : S = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hSnonempty
    subst hSempty
    simpa [penumbra] using (convex_empty : Convex Real (∅ : Set (Fin n → Real)))

end Section03
end Chap01
