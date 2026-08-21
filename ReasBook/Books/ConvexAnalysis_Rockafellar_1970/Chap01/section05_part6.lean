/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part5

section Chap01
section Section05

/-- Coordinate projections are convex on `ℝ^n`. -/
lemma convexFunctionOn_coord {n : Nat} (j : Fin n) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (x j : EReal)) := by
  refine (convexFunctionOn_iff_segment_inequality
    (C := (Set.univ : Set (Fin n → Real))) (f := fun x => (x j : EReal))
    (hC := convex_univ) ?_).2 ?_
  · intro x hx
    exact EReal.coe_ne_bot (x j)
  · intro x hx y hy t ht0 ht1
    have hleft :
        ((1 - t) • x + t • y) j = (1 - t) * x j + t * y j := by
      simp [smul_eq_mul]
    have hright :
        ((1 - t : Real) : EReal) * (x j : EReal) + ((t : Real) : EReal) * (y j : EReal) =
          (( (1 - t) * x j + t * y j : Real) : EReal) := by
      calc
        ((1 - t : Real) : EReal) * (x j : EReal) + ((t : Real) : EReal) * (y j : EReal) =
            (( (1 - t) * x j : Real) : EReal) + (( t * y j : Real) : EReal) := by
              rfl
        _ = (( (1 - t) * x j + t * y j : Real) : EReal) := by
              simp [EReal.coe_add]
    calc
      (fun x => (x j : EReal)) ((1 - t) • x + t • y) =
          (( (1 - t) * x j + t * y j : Real) : EReal) := by
            simp [hleft]
      _ ≤ ((1 - t : Real) : EReal) * (x j : EReal) + ((t : Real) : EReal) * (y j : EReal) := by
            simp

/-- Text 5.5.0.1: The function `f` which assigns to each `x = (xi_1, ..., xi_n)` the
greatest of the components `xi_j` of `x` is convex. -/
lemma convexFunctionOn_maxComponent {n : Nat} :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => iSup (fun j : Fin n => (x j : EReal))) := by
  refine convexFunctionOn_iSup (f := fun j x => (x j : EReal)) ?_
  intro j
  simpa using (convexFunctionOn_coord (n := n) (j := j))

/-- Pulling out a positive scalar from a finite supremum in `EReal`. -/
lemma iSup_mul_of_pos {n : Nat} (a : Fin n → EReal) {t : Real} (ht : 0 < t) :
    (⨆ j, (t : EReal) * a j) = (t : EReal) * ⨆ j, a j := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro j
    have hj : a j ≤ ⨆ j, a j := le_iSup (fun j => a j) j
    exact ereal_mul_le_mul_of_pos_left_general (t := t) ht hj
  · have htinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hleinv :
        (⨆ j, (t⁻¹ : EReal) * ((t : EReal) * a j)) ≤
          (t⁻¹ : EReal) * ⨆ j, (t : EReal) * a j := by
      refine iSup_le ?_
      intro j
      have hj :
          (t : EReal) * a j ≤
            ⨆ j, (t : EReal) * a j :=
        le_iSup (fun j => (t : EReal) * a j) j
      exact ereal_mul_le_mul_of_pos_left_general (t := t⁻¹) htinv hj
    have hle0 :
        (⨆ j, a j) ≤
          ⨆ j, (t⁻¹ : EReal) * ((t : EReal) * a j) := by
      refine iSup_le ?_
      intro j
      have hcancel :
          a j = (t⁻¹ : EReal) * ((t : EReal) * a j) := by
        symm
        calc
          (t⁻¹ : EReal) * ((t : EReal) * a j)
              = (t : EReal) * ((t⁻¹ : EReal) * a j) := by
                  simp [mul_left_comm]
          _ = a j := by
                  simpa [mul_assoc] using
                    (ereal_mul_inv_smul (t := t) ht (x := a j))
      calc
        a j = (t⁻¹ : EReal) * ((t : EReal) * a j) := hcancel
        _ ≤ ⨆ j, (t⁻¹ : EReal) * ((t : EReal) * a j) := by
              exact le_iSup (fun j => (t⁻¹ : EReal) * ((t : EReal) * a j)) j
    have hle' :
        (⨆ j, a j) ≤
          (t⁻¹ : EReal) * ⨆ j, (t : EReal) * a j :=
      le_trans hle0 hleinv
    have hmul := ereal_mul_le_mul_of_pos_left_general (t := t) ht hle'
    simpa [ereal_mul_inv_smul (t := t) ht (x := ⨆ j, (t : EReal) * a j)] using hmul

/-- Rewrite the max-component after scaling as `EReal` multiplication. -/
lemma maxComponent_smul_rewrite {n : Nat} (x : Fin n → Real) (t : Real) :
    (⨆ j, ((t • x) j : EReal)) = ⨆ j, (t : EReal) * (x j : EReal) := by
  classical
  refine iSup_congr ?_
  intro j
  simp [smul_eq_mul, EReal.coe_mul]

/-- Text 5.5.0.2: The function `f` which assigns to each `x = (xi_1, ..., xi_n)` the
greatest of the components `xi_j` of `x` is positively homogeneous. -/
lemma positivelyHomogeneous_maxComponent {n : Nat} :
    PositivelyHomogeneous
      (fun x : Fin n → Real => iSup (fun j : Fin n => (x j : EReal))) := by
  intro x t ht
  calc
    (⨆ j, ((t • x) j : EReal)) = ⨆ j, (t : EReal) * (x j : EReal) :=
      maxComponent_smul_rewrite (x := x) (t := t)
    _ = (t : EReal) * ⨆ j, (x j : EReal) :=
      iSup_mul_of_pos (a := fun j => (x j : EReal)) (t := t) ht

/-- Components of a vector form a bounded-above set. -/
lemma bddAbove_components {n : Nat} (x : Fin n → ℝ) :
    BddAbove { r : ℝ | ∃ j : Fin n, r = x j } := by
  classical
  simpa [Set.range, eq_comm] using (Set.finite_range x).bddAbove

/-- The standard basis vector lies in the simplex. -/
lemma simplex_stdBasis_mem {n : Nat} (j : Fin n) :
    (∀ i, 0 ≤ ((Pi.single j (1 : ℝ)) : Fin n → ℝ) i) ∧
    (Finset.univ.sum (fun i => ((Pi.single j (1 : ℝ)) : Fin n → ℝ) i) = 1) := by
  classical
  refine And.intro ?_ ?_
  · intro i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · have hsum :
        Finset.univ.sum (fun i : Fin n => ((Pi.single j (1 : ℝ)) : Fin n → ℝ) i) =
          ((Pi.single j (1 : ℝ)) : Fin n → ℝ) j := by
      refine
        Finset.sum_eq_single (s := Finset.univ) (a := j)
          (f := fun i : Fin n => ((Pi.single j (1 : ℝ)) : Fin n → ℝ) i) ?_ ?_
      · intro b hb hbj
        simp [Pi.single_eq_of_ne hbj]
      · intro h
        exact (False.elim (h (Finset.mem_univ j)))
    simp [hsum]

/-- A convex combination of components is bounded by their supremum. -/
lemma dotProduct_le_sSup_components_of_simplex {n : Nat} (x y : Fin n → ℝ)
    (hy0 : ∀ j, 0 ≤ y j) (hysum : Finset.univ.sum (fun j => y j) = 1) :
    dotProduct x y ≤ sSup { r : ℝ | ∃ j : Fin n, r = x j } := by
  classical
  let Sx : Set ℝ := { r : ℝ | ∃ j : Fin n, r = x j }
  have hbd : BddAbove Sx := bddAbove_components (x := x)
  have hxle : ∀ j, x j ≤ sSup Sx := by
    intro j
    exact le_csSup hbd ⟨j, rfl⟩
  have hsum_le :
      Finset.univ.sum (fun j => x j * y j) ≤
        Finset.univ.sum (fun j => sSup Sx * y j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_right (hxle j) (hy0 j)
  have hsum_eq :
      Finset.univ.sum (fun j => sSup Sx * y j) =
        sSup Sx * Finset.univ.sum (fun j => y j) := by
    simpa using
      (Finset.mul_sum (s := Finset.univ) (f := fun j => y j) (a := sSup Sx)).symm
  calc
    dotProduct x y = Finset.univ.sum (fun j => x j * y j) := by
      simp [dotProduct]
    _ ≤ Finset.univ.sum (fun j => sSup Sx * y j) := hsum_le
    _ = sSup Sx * Finset.univ.sum (fun j => y j) := hsum_eq
    _ = sSup Sx := by simp [hysum]

/-- Each component is bounded by the support function of the simplex. -/
lemma component_le_supportFunction_simplex {n : Nat} (x : Fin n → ℝ) (j : Fin n) :
    x j ≤
      supportFunction
        { y : Fin n → Real |
          (∀ j, 0 ≤ y j) ∧ (Finset.univ.sum (fun j => y j) = 1) } x := by
  classical
  let C : Set (Fin n → ℝ) :=
    { y : Fin n → ℝ |
      (∀ j, 0 ≤ y j) ∧ (Finset.univ.sum (fun j => y j) = 1) }
  have hbd :
      BddAbove { r : ℝ | ∃ y ∈ C, r = dotProduct x y } := by
    refine ⟨sSup { r : ℝ | ∃ j : Fin n, r = x j }, ?_⟩
    intro r hr
    rcases hr with ⟨y, hyC, rfl⟩
    rcases hyC with ⟨hy0, hysum⟩
    exact dotProduct_le_sSup_components_of_simplex (x := x) (y := y) hy0 hysum
  have hmem : x j ∈ { r : ℝ | ∃ y ∈ C, r = dotProduct x y } := by
    have hCmem : ((Pi.single j (1 : ℝ)) : Fin n → ℝ) ∈ C := by
      simp [C, simplex_stdBasis_mem]
    refine ⟨(Pi.single j (1 : ℝ)), hCmem, ?_⟩
    simp
  exact le_csSup hbd hmem

/-- Text 5.5.0.3: The function `f` which assigns to each `x = (xi_1, ..., xi_n)` the
greatest of the components `xi_j` of `x` is the support function of the simplex
`C = { y = (eta_1, ..., eta_n) | eta_j ≥ 0, eta_1 + ... + eta_n = 1 }`. -/
lemma supportFunction_simplex_eq_maxComponent {n : Nat} :
    let C : Set (Fin n → Real) :=
      { y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (Finset.univ.sum (fun j => y j) = 1) }
    supportFunction C = fun x => sSup { r : ℝ | ∃ j : Fin n, r = x j } := by
  classical
  cases n with
  | zero =>
      funext x
      simp [supportFunction]
  | succ n =>
      funext x
      let C : Set (Fin (Nat.succ n) → Real) :=
        { y : Fin (Nat.succ n) → Real |
          (∀ j, 0 ≤ y j) ∧ (Finset.univ.sum (fun j => y j) = 1) }
      let Sx : Set ℝ := { r : ℝ | ∃ j : Fin (Nat.succ n), r = x j }
      have hle : supportFunction C x ≤ sSup Sx := by
        have hCne : C.Nonempty := by
          refine ⟨(Pi.single (0 : Fin (Nat.succ n)) (1 : ℝ)), ?_⟩
          simpa [C] using (simplex_stdBasis_mem (j := (0 : Fin (Nat.succ n))))
        have hne : Set.Nonempty { r : ℝ | ∃ y ∈ C, r = dotProduct x y } := by
          rcases hCne with ⟨y, hyC⟩
          exact ⟨dotProduct x y, ⟨y, hyC, rfl⟩⟩
        refine csSup_le hne ?_
        intro r hr
        rcases hr with ⟨y, hyC, rfl⟩
        rcases hyC with ⟨hy0, hysum⟩
        simpa [Sx] using
          (dotProduct_le_sSup_components_of_simplex (x := x) (y := y) hy0 hysum)
      have hge : sSup Sx ≤ supportFunction C x := by
        have hneSx : Sx.Nonempty := by
          refine ⟨x (0 : Fin (Nat.succ n)), ⟨(0 : Fin (Nat.succ n)), rfl⟩⟩
        refine csSup_le hneSx ?_
        intro r hr
        rcases hr with ⟨j, rfl⟩
        simpa [C] using (component_le_supportFunction_simplex (x := x) (j := j))
      exact le_antisymm hle hge

/-- Absolute values of components form a bounded-above set. -/
lemma bddAbove_abs_components {n : Nat} (x : Fin n → ℝ) :
    BddAbove { r : ℝ | ∃ j : Fin n, r = |x j| } := by
  simpa using (bddAbove_components (x := fun j => |x j|))

/-- Componentwise absolute value bound for convex combinations. -/
lemma abs_component_le_convexCombo {n : Nat} (x y : Fin n → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Fin n) :
    |((a • x + b • y) j)| ≤ a * |x j| + b * |y j| := by
  have h1 : |a * x j| = a * |x j| := by
    calc
      |a * x j| = |a| * |x j| := by
        simp
      _ = a * |x j| := by simp [abs_of_nonneg ha]
  have h2 : |b * y j| = b * |y j| := by
    calc
      |b * y j| = |b| * |y j| := by
        simp
      _ = b * |y j| := by simp [abs_of_nonneg hb]
  calc
    |((a • x + b • y) j)| = |a * x j + b * y j| := by
      simp [smul_eq_mul]
    _ ≤ |a * x j| + |b * y j| := by
      simpa using (abs_add_le (a * x j) (b * y j))
    _ = a * |x j| + b * |y j| := by
      simp [h1, h2]

/-- The set of absolute component values is nonempty in positive dimension. -/
lemma abs_components_nonempty_succ {n : Nat} (x : Fin (Nat.succ n) → ℝ) :
    Set.Nonempty { r : ℝ | ∃ j : Fin (Nat.succ n), r = |x j| } := by
  refine ⟨|x (0 : Fin (Nat.succ n))|, ?_⟩
  exact ⟨0, rfl⟩

/-- Dot product bound for vectors in the l1-ball. -/
lemma dotProduct_le_sSup_abs_components_of_l1Ball {n : Nat} (x y : Fin n → ℝ)
    (hy : Finset.univ.sum (fun j => |y j|) ≤ 1) :
    dotProduct x y ≤ sSup { r : ℝ | ∃ j : Fin n, r = |x j| } := by
  classical
  let Sx : Set ℝ := { r : ℝ | ∃ j : Fin n, r = |x j| }
  have hbd : BddAbove Sx := bddAbove_abs_components (x := x)
  have hsum_le_abs :
      Finset.univ.sum (fun j => x j * y j) ≤
        Finset.univ.sum (fun j => |x j| * |y j|) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have : x j * y j ≤ |x j * y j| := le_abs_self (x j * y j)
    calc
      x j * y j ≤ |x j * y j| := this
      _ = |x j| * |y j| := by simp [abs_mul]
  have hxle : ∀ j, |x j| ≤ sSup Sx := by
    intro j
    exact le_csSup hbd ⟨j, rfl⟩
  have hsum_le :
      Finset.univ.sum (fun j => |x j| * |y j|) ≤
        Finset.univ.sum (fun j => sSup Sx * |y j|) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_right (hxle j) (abs_nonneg (y j))
  have hsum_eq :
      Finset.univ.sum (fun j => sSup Sx * |y j|) =
        sSup Sx * Finset.univ.sum (fun j => |y j|) := by
    simpa using
      (Finset.mul_sum (s := Finset.univ) (f := fun j => |y j|) (a := sSup Sx)).symm
  have hnonneg : 0 ≤ sSup Sx := by
    by_cases hne : Sx.Nonempty
    · rcases hne with ⟨r, ⟨j, rfl⟩⟩
      have : 0 ≤ |x j| := abs_nonneg (x j)
      exact le_trans this (le_csSup hbd ⟨j, rfl⟩)
    · have hSx : Sx = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
      simp [hSx]
  calc
    dotProduct x y = Finset.univ.sum (fun j => x j * y j) := by
      simp [dotProduct]
    _ ≤ Finset.univ.sum (fun j => |x j| * |y j|) := hsum_le_abs
    _ ≤ Finset.univ.sum (fun j => sSup Sx * |y j|) := hsum_le
    _ = sSup Sx * Finset.univ.sum (fun j => |y j|) := hsum_eq
    _ ≤ sSup Sx * 1 := by
      exact mul_le_mul_of_nonneg_left hy hnonneg
    _ = sSup Sx := by simp

/-- A single-coordinate vector with bounded absolute value lies in the l1-ball. -/
lemma l1Ball_single_mem {n : Nat} (j : Fin n) (s : ℝ) (hs : |s| ≤ 1) :
    (Pi.single j s : Fin n → ℝ) ∈
      { y : Fin n → ℝ | Finset.univ.sum (fun i => |y i|) ≤ 1 } := by
  classical
  have hsum :
      Finset.univ.sum (fun i : Fin n => |((Pi.single j s) : Fin n → ℝ) i|) =
        |((Pi.single j s) : Fin n → ℝ) j| := by
    refine
      Finset.sum_eq_single (s := Finset.univ) (a := j)
        (f := fun i : Fin n => |((Pi.single j s) : Fin n → ℝ) i|) ?_ ?_
    · intro b hb hbj
      simp [Pi.single_eq_of_ne hbj]
    · intro h
      exact (False.elim (h (Finset.mem_univ j)))
  simpa [hsum] using hs

/-- Each absolute component is bounded by the support function of the l1-ball. -/
lemma abs_component_le_supportFunction_l1Ball {n : Nat} (x : Fin n → ℝ) (j : Fin n) :
    |x j| ≤
      supportFunction
        { y : Fin n → Real | Finset.univ.sum (fun j => |y j|) ≤ 1 } x := by
  classical
  let D : Set (Fin n → ℝ) :=
    { y : Fin n → ℝ | Finset.univ.sum (fun j => |y j|) ≤ 1 }
  let Sx : Set ℝ := { r : ℝ | ∃ j : Fin n, r = |x j| }
  have hbd :
      BddAbove { r : ℝ | ∃ y ∈ D, r = dotProduct x y } := by
    refine ⟨sSup Sx, ?_⟩
    intro r hr
    rcases hr with ⟨y, hyD, rfl⟩
    have hyD' : Finset.univ.sum (fun j => |y j|) ≤ 1 := by
      simpa [D] using hyD
    simpa [Sx] using
      (dotProduct_le_sSup_abs_components_of_l1Ball (x := x) (y := y) (hy := hyD'))
  let s : ℝ := if 0 ≤ x j then 1 else -1
  let y : Fin n → ℝ := Pi.single j s
  have hyD : y ∈ D := by
    have hs : |s| ≤ 1 := by
      by_cases h : 0 ≤ x j
      · simp [s, h]
      · simp [s, h]
    simpa [D, y] using (l1Ball_single_mem (j := j) (s := s) hs)
  have hmem : |x j| ∈ { r : ℝ | ∃ y ∈ D, r = dotProduct x y } := by
    refine ⟨y, hyD, ?_⟩
    by_cases h : 0 ≤ x j
    · simp [y, s, h, abs_of_nonneg h]
    · have hneg : x j < 0 := lt_of_not_ge h
      simp [y, s, h, abs_of_neg hneg]
  exact le_csSup hbd hmem

/-- Text 5.5.0.4: The function `k(x) = max { |xi_j| | j = 1, ..., n }` is convex in `ℝ^n`. -/
lemma convexOn_maxAbsComponent {n : Nat} :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real))
      (fun x => sSup { r : ℝ | ∃ j : Fin n, r = |x j| }) := by
  classical
  cases n with
  | zero =>
      have hfun :
          (fun x : Fin 0 → ℝ => sSup { r : ℝ | ∃ j : Fin 0, r = |x j| }) =
            fun _ => (0 : ℝ) := by
        funext x
        simp
      simpa [hfun] using
        (convexOn_const (s := (Set.univ : Set (Fin 0 → Real)))
          (c := (0 : ℝ)) convex_univ)
  | succ n =>
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      let Sxy : Set ℝ := { r : ℝ | ∃ j : Fin (Nat.succ n), r = |(a • x + b • y) j| }
      let Sx : Set ℝ := { r : ℝ | ∃ j : Fin (Nat.succ n), r = |x j| }
      let Sy : Set ℝ := { r : ℝ | ∃ j : Fin (Nat.succ n), r = |y j| }
      have hbdx : BddAbove Sx := bddAbove_abs_components (x := x)
      have hbdy : BddAbove Sy := bddAbove_abs_components (x := y)
      have hne : Sxy.Nonempty := abs_components_nonempty_succ (x := a • x + b • y)
      have hle : sSup Sxy ≤ a * sSup Sx + b * sSup Sy := by
        refine csSup_le hne ?_
        intro r hr
        rcases hr with ⟨j, rfl⟩
        have hxj : |x j| ≤ sSup Sx := le_csSup hbdx ⟨j, rfl⟩
        have hyj : |y j| ≤ sSup Sy := le_csSup hbdy ⟨j, rfl⟩
        have hcomb :
            |((a • x + b • y) j)| ≤ a * |x j| + b * |y j| :=
          abs_component_le_convexCombo (x := x) (y := y) (a := a) (b := b) ha hb j
        have hmulx : a * |x j| ≤ a * sSup Sx :=
          mul_le_mul_of_nonneg_left hxj ha
        have hmuly : b * |y j| ≤ b * sSup Sy :=
          mul_le_mul_of_nonneg_left hyj hb
        exact le_trans hcomb (add_le_add hmulx hmuly)
      simpa [Sxy, Sx, Sy] using hle

/-- Text 5.5.0.5: The function `k(x) = max { |xi_j| | j = 1, ..., n }` is the support
function of the convex set `D = { y = (eta_1, ..., eta_n) | |eta_1| + ... + |eta_n| ≤ 1 }`. -/
lemma supportFunction_l1Ball_eq_maxAbsComponent {n : Nat} :
    let D : Set (Fin n → Real) :=
      { y : Fin n → Real | Finset.univ.sum (fun j => |y j|) ≤ 1 }
    supportFunction D = fun x => sSup { r : ℝ | ∃ j : Fin n, r = |x j| } := by
  classical
  cases n with
  | zero =>
      funext x
      simp [supportFunction]
  | succ n =>
      funext x
      let D : Set (Fin (Nat.succ n) → ℝ) :=
        { y : Fin (Nat.succ n) → ℝ | Finset.univ.sum (fun j => |y j|) ≤ 1 }
      let Sx : Set ℝ := { r : ℝ | ∃ j : Fin (Nat.succ n), r = |x j| }
      have hle : supportFunction D x ≤ sSup Sx := by
        have hDne : D.Nonempty := by
          refine ⟨0, ?_⟩
          simp [D]
        have hne : Set.Nonempty { r : ℝ | ∃ y ∈ D, r = dotProduct x y } := by
          rcases hDne with ⟨y, hyD⟩
          exact ⟨dotProduct x y, ⟨y, hyD, rfl⟩⟩
        refine csSup_le hne ?_
        intro r hr
        rcases hr with ⟨y, hyD, rfl⟩
        have hyD' : Finset.univ.sum (fun j => |y j|) ≤ 1 := by
          simpa [D] using hyD
        simpa [Sx] using
          (dotProduct_le_sSup_abs_components_of_l1Ball (x := x) (y := y) (hy := hyD'))
      have hge : sSup Sx ≤ supportFunction D x := by
        have hneSx : Sx.Nonempty := abs_components_nonempty_succ (x := x)
        refine csSup_le hneSx ?_
        intro r hr
        rcases hr with ⟨j, rfl⟩
        simpa [D] using (abs_component_le_supportFunction_l1Ball (x := x) (j := j))
      exact le_antisymm hle hge

/-- Membership in the cube is equivalent to an absolute-value bound. -/
lemma cube_mem_iff_abs_le_one {n : Nat} {x : Fin n → ℝ} :
    (x ∈ { x : Fin n → ℝ | ∀ j, -1 ≤ x j ∧ x j ≤ 1 }) ↔ ∀ j, |x j| ≤ 1 := by
  constructor
  · intro hx j
    exact abs_le.2 (hx j)
  · intro hx j
    exact abs_le.1 (hx j)

/-- If all components of `x` are bounded by `t > 0`, then `x` lies in the scaled cube. -/
lemma mem_scaling_cube_of_abs_le {n : Nat} {x : Fin n → ℝ} {t : ℝ}
    (ht : 0 < t) (hxt : ∀ j, |x j| ≤ t) :
    x ∈ (fun y => t • y) '' { x : Fin n → ℝ | ∀ j, -1 ≤ x j ∧ x j ≤ 1 } := by
  let u : Fin n → ℝ := (t⁻¹) • x
  refine ⟨u, ?_, ?_⟩
  · have hu : ∀ j, |u j| ≤ (1 : ℝ) := by
      intro j
      have ht0 : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht)
      have hmul : t⁻¹ * |x j| ≤ t⁻¹ * t := by
        exact mul_le_mul_of_nonneg_left (hxt j) ht0
      have hmul' : t⁻¹ * t = (1 : ℝ) := by
        have htne : t ≠ 0 := ne_of_gt ht
        simpa using (inv_mul_cancel₀ htne)
      have h1 : |u j| = t⁻¹ * |x j| := by
        simp [u, smul_eq_mul, abs_mul, abs_of_nonneg ht0]
      simpa [h1, hmul'] using hmul
    exact (cube_mem_iff_abs_le_one).2 hu
  · have htne : t ≠ 0 := ne_of_gt ht
    simp [u, smul_smul, htne]

/-- Membership in a scaled cube bounds each component in absolute value. -/
lemma abs_le_of_mem_scaling_cube {n : Nat} {x : Fin n → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ (fun y => t • y) '' { x : Fin n → ℝ | ∀ j, -1 ≤ x j ∧ x j ≤ 1 }) :
    ∀ j, |x j| ≤ t := by
  rcases hx with ⟨u, huE, rfl⟩
  have hu : ∀ j, |u j| ≤ (1 : ℝ) := (cube_mem_iff_abs_le_one).1 huE
  intro j
  have hmul : |t * u j| = t * |u j| := by
    simp [abs_mul, abs_of_nonneg ht]
  have hle : t * |u j| ≤ t * 1 := by
    exact mul_le_mul_of_nonneg_left (hu j) ht
  calc
    |(t • u) j| = |t * u j| := by simp [smul_eq_mul]
    _ = t * |u j| := hmul
    _ ≤ t * 1 := hle
    _ = t := by simp

/-- Text 5.5.0.6: The function `k(x) = max { |xi_j| | j = 1, ..., n }` is the gauge of the
`n`-dimensional cube `E = { x = (xi_1, ..., xi_n) | -1 ≤ xi_j ≤ 1, j = 1, ..., n }`. -/
lemma gaugeOfCube_eq_maxAbsComponent {n : Nat} :
    let E : Set (Fin n → Real) :=
      { x : Fin n → Real | ∀ j, -1 ≤ x j ∧ x j ≤ 1 }
    gaugeOfConvexSet E = fun x => sSup { r : ℝ | ∃ j : Fin n, r = |x j| } := by
  classical
  cases n with
  | zero =>
      funext x
      have hx : x = 0 := by
        apply Subsingleton.elim _ _
      subst hx
      let E : Set (Fin 0 → ℝ) :=
        { x : Fin 0 → ℝ | ∀ j, -1 ≤ x j ∧ x j ≤ 1 }
      let A : Set ℝ :=
        { r : ℝ | 0 ≤ r ∧ (0 : Fin 0 → ℝ) ∈ (fun y => r • y) '' E }
      have h0E : (0 : Fin 0 → ℝ) ∈ E := by
        simp [E]
      have hAeq : A = Set.Ici (0 : ℝ) := by
        ext r
        constructor
        · intro hr
          exact hr.1
        · intro hr
          have hmem : (0 : Fin 0 → ℝ) ∈ (fun y => r • y) '' E := by
            refine ⟨0, h0E, ?_⟩
            simp
          exact ⟨hr, hmem⟩
      have hAinf : sInf A = (0 : ℝ) := by
        simp [hAeq]
      have hGauge : gaugeOfConvexSet E 0 = 0 := by
        dsimp [gaugeOfConvexSet]
        simpa [A] using hAinf
      have hSup :
          sSup { r : ℝ | ∃ j : Fin 0, r = |(0 : Fin 0 → ℝ) j| } = (0 : ℝ) := by
        simp
      rw [hSup]
      exact hGauge
  | succ n =>
      funext x
      let E : Set (Fin (Nat.succ n) → ℝ) :=
        { x : Fin (Nat.succ n) → ℝ | ∀ j, -1 ≤ x j ∧ x j ≤ 1 }
      let Sx : Set ℝ := { r : ℝ | ∃ j : Fin (Nat.succ n), r = |x j| }
      let A : Set ℝ := { r : ℝ | 0 ≤ r ∧ x ∈ (fun y => r • y) '' E }
      let t : ℝ := sSup Sx
      have hbd : BddAbove Sx := bddAbove_abs_components (x := x)
      have hneSx : Sx.Nonempty := abs_components_nonempty_succ (x := x)
      have hxt : ∀ j, |x j| ≤ t := by
        intro j
        exact le_csSup hbd ⟨j, rfl⟩
      have hnonneg : 0 ≤ t := by
        rcases hneSx with ⟨r, ⟨j, rfl⟩⟩
        have : 0 ≤ |x j| := abs_nonneg (x j)
        exact le_trans this (le_csSup hbd ⟨j, rfl⟩)
      have htmem : t ∈ A := by
        refine ⟨hnonneg, ?_⟩
        by_cases ht0 : t = 0
        · have hx0 : x = 0 := by
            funext j
            have h0 : |x j| ≤ (0 : ℝ) := by
              simpa [ht0] using hxt j
            have h0' : |x j| = (0 : ℝ) := le_antisymm h0 (abs_nonneg _)
            exact abs_eq_zero.mp h0'
          subst hx0
          have h0E : (0 : Fin (Nat.succ n) → ℝ) ∈ E := by
            simp [E]
          refine ⟨0, h0E, ?_⟩
          simp [ht0]
        · have htpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm ht0)
          exact mem_scaling_cube_of_abs_le (x := x) (t := t) htpos hxt
      have hAbdd : BddBelow A := by
        refine ⟨0, ?_⟩
        intro r hr
        exact hr.1
      have hle : sInf A ≤ t := csInf_le hAbdd htmem
      have hAne : A.Nonempty := ⟨t, htmem⟩
      have hge : t ≤ sInf A := by
        refine le_csInf hAne ?_
        intro r hr
        have habs : ∀ j, |x j| ≤ r :=
          abs_le_of_mem_scaling_cube (t := r) hr.1 hr.2
        refine csSup_le hneSx ?_
        intro s hs
        rcases hs with ⟨j, rfl⟩
        exact habs j
      have hst : sInf A = t := le_antisymm hle hge
      have hGauge : gaugeOfConvexSet E x = t := by
        simpa [gaugeOfConvexSet, A, t] using hst
      simpa [Sx, t] using hGauge

/-- Text 5.5.1: For a function `g`, define `f x = inf { μ | (x, μ) ∈ conv (epi g) }`.
Then `f` is called the convex hull of `g`, and is denoted `f = conv(g)`. -/
noncomputable def convexHullFunction {n : Nat} (g : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal :=
  fun x =>
    sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
      (x, μ) ∈
        convexHull Real (epigraph (S := (Set.univ : Set (Fin n → Real))) g) })

/-- The convex hull of an epigraph is convex. -/
lemma convex_convexHull_epigraph {n : Nat} (g : (Fin n → Real) → EReal) :
    Convex ℝ (convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g)) := by
  simpa using
    (convex_convexHull (𝕜 := ℝ)
      (s := epigraph (S := (Set.univ : Set (Fin n → Real))) g))

/-- Rewrite the convex hull function as an `EReal` inf-section. -/
lemma convexHullFunction_eq_inf_section {n : Nat} (g : (Fin n → Real) → EReal) :
    convexHullFunction g =
      fun x =>
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (x, μ) ∈ convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) }) := by
  rfl

/-- Text 5.5.2: If `f = conv(g)` is the convex hull of `g`, then `f` is a convex function. -/
theorem convexFunctionOn_convexHullFunction {n : Nat} (g : (Fin n → Real) → EReal) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (convexHullFunction g) := by
  classical
  simpa [convexHullFunction_eq_inf_section] using
    (convexOn_inf_section_of_convex
      (F := convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g))
      (convex_convexHull_epigraph (g := g)))

/-- If `h ≤ g`, then `epi g ⊆ epi h`. -/
lemma epigraph_subset_epigraph_of_le {n : Nat} {h g : (Fin n → Real) → EReal}
    (h_le_g : h ≤ g) :
    epigraph (S := (Set.univ : Set (Fin n → Real))) g ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) h := by
  intro p hp
  rcases p with ⟨x, μ⟩
  have hgp : g x ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := g)).1 hp
  have hhp : h x ≤ (μ : EReal) := le_trans (h_le_g x) hgp
  exact (mem_epigraph_univ_iff (f := h)).2 hhp

/-- Convex hull of `epi g` lies in `epi h` when `h` is convex and `h ≤ g`. -/
lemma convexHull_epigraph_subset_of_convex {n : Nat} {h g : (Fin n → Real) → EReal}
    (hh : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h)
    (h_le_g : h ≤ g) :
    convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) h := by
  have hsubset :
      epigraph (S := (Set.univ : Set (Fin n → Real))) g ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) h :=
    epigraph_subset_epigraph_of_le (h := h) (g := g) h_le_g
  have hconv :
      Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) h) :=
    convex_epigraph_of_convexFunctionOn (f := h) hh
  exact convexHull_min hsubset hconv

/-- Inclusion in an epigraph gives a pointwise lower bound on the inf-section. -/
lemma le_inf_section_of_subset_epigraph {n : Nat} {h : (Fin n → Real) → EReal}
    {F : Set ((Fin n → Real) × Real)}
    (hF : F ⊆ epigraph (S := (Set.univ : Set (Fin n → Real))) h) :
    h ≤ fun x =>
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F }) := by
  intro x
  refine le_sInf ?_
  intro z hz
  rcases hz with ⟨μ, hμ, rfl⟩
  have hxmem :
      (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) h := hF hμ
  exact (mem_epigraph_univ_iff (f := h)).1 hxmem

/-- Text 5.5.3: `f = conv(g)` is the greatest convex function majorized by `g`. -/
theorem convexHullFunction_greatest_convex_minorant {n : Nat} (g : (Fin n → Real) → EReal) :
    let f := convexHullFunction g;
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f ∧
      f ≤ g ∧
      ∀ h : (Fin n → Real) → EReal,
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        h ≤ g →
        h ≤ f := by
  classical
  set f := convexHullFunction g
  refine And.intro ?_ ?_
  · simpa [f] using convexFunctionOn_convexHullFunction (g := g)
  refine And.intro ?_ ?_
  · have hsubset :
        epigraph (S := (Set.univ : Set (Fin n → Real))) g ⊆
          convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
      simpa using
        (subset_convexHull (𝕜 := ℝ)
          (s := epigraph (S := (Set.univ : Set (Fin n → Real))) g))
    have hle :
        (fun x =>
          sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (x, μ) ∈ convexHull ℝ
              (epigraph (S := (Set.univ : Set (Fin n → Real))) g) })) ≤ g :=
      le_of_epigraph_subset_inf_section (h := g)
        (F := convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g)) hsubset
    intro x
    simpa [f, convexHullFunction_eq_inf_section] using hle x
  intro h hh h_le_g
  have hsubset :
      convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) h :=
    convexHull_epigraph_subset_of_convex (h := h) (g := g) hh h_le_g
  have hle :
      h ≤ fun x =>
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (x, μ) ∈ convexHull ℝ
            (epigraph (S := (Set.univ : Set (Fin n → Real))) g) }) :=
    le_inf_section_of_subset_epigraph (h := h)
      (F := convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g)) hsubset
  simpa [f, convexHullFunction_eq_inf_section] using hle

/-- The first projection of a finite sum of pairs is the sum of first projections. -/
lemma fst_sum {ι : Type*} {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (s : Finset ι) (f : ι → α × β) :
    (s.sum f).1 = s.sum (fun i => (f i).1) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [ha, hs, Prod.fst_add]

/-- The second projection of a finite sum of pairs is the sum of second projections. -/
lemma snd_sum {ι : Type*} {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (s : Finset ι) (f : ι → α × β) :
    (s.sum f).2 = s.sum (fun i => (f i).2) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [ha, hs, Prod.snd_add]

/-- Membership in the convex hull of an epigraph is a finite convex combination. -/
lemma mem_convexHull_epigraph_iff_fin_combo {n : Nat} {g : (Fin n → Real) → EReal}
    {x : Fin n → Real} {μ : Real} :
    (x, μ) ∈ convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) ↔
      ∃ (m : Nat) (lam : Fin m → Real) (x' : Fin m → (Fin n → Real))
        (μ' : Fin m → Real),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        (Finset.univ.sum (fun i => lam i * μ' i) = μ) ∧
        (∀ i, g (x' i) ≤ (μ' i : EReal)) := by
  classical
  constructor
  · intro hx
    rcases
        (mem_convexHull_iff_exists_fintype (R := Real)
            (s := epigraph (S := (Set.univ : Set (Fin n → Real))) g) (x := (x, μ))).1 hx with
      ⟨ι, _inst, w, z, hw0, hw1, hz, hsum⟩
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    refine
      ⟨Fintype.card ι, (fun i => w (e.symm i)), (fun i => (z (e.symm i)).1),
        (fun i => (z (e.symm i)).2), ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hw0 (e.symm i)
    · have hsum' : (∑ i, w (e.symm i)) = ∑ i, w i := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i))
      simpa [hsum'] using hw1
    · have hsum_fst : (∑ i, w i • (z i).1) = x := by
        have h := congrArg Prod.fst hsum
        have h' :
            Finset.univ.sum (fun i => (w i • z i).1) = x := by
          simpa [fst_sum (s := Finset.univ) (f := fun i => w i • z i)] using h
        simpa using h'
      have hsum' : (∑ i, w (e.symm i) • (z (e.symm i)).1) = ∑ i, w i • (z i).1 := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i • (z i).1))
      simpa [hsum'] using hsum_fst
    · have hsum_snd : (∑ i, w i • (z i).2) = μ := by
        have h := congrArg Prod.snd hsum
        have h' :
            Finset.univ.sum (fun i => (w i • z i).2) = μ := by
          simpa [snd_sum (s := Finset.univ) (f := fun i => w i • z i)] using h
        simpa [smul_eq_mul] using h'
      have hsum' :
          (∑ i, w (e.symm i) * (z (e.symm i)).2) = ∑ i, w i * (z i).2 := by
        simpa using (Equiv.sum_comp e.symm (fun i => w i • (z i).2))
      have hsum_snd' : (∑ i, w i * (z i).2) = μ := by
        simpa [smul_eq_mul] using hsum_snd
      simpa [hsum'] using hsum_snd'
    · intro i
      have hz' :
          z (e.symm i) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) g := hz (e.symm i)
      exact (mem_epigraph_univ_iff (f := g)).1 hz'
  · rintro ⟨m, lam, x', μ', h0, hsum1, hsumx, hsumμ, hle⟩
    refine
      mem_convexHull_of_exists_fintype
        (s := epigraph (S := (Set.univ : Set (Fin n → Real))) g) (x := (x, μ))
        (w := lam) (z := fun i => (x' i, μ' i)) ?_ ?_ ?_ ?_
    · intro i
      exact h0 i
    · simpa using hsum1
    · intro i
      exact (mem_epigraph_univ_iff (f := g)).2 (hle i)
    · apply Prod.ext
      · have hsum_fst :
            (Finset.univ.sum (fun i => (lam i • x' i, lam i * μ' i))).1 =
              Finset.univ.sum (fun i => lam i • x' i) := by
          simp [fst_sum (s := Finset.univ)
            (f := fun i => (lam i • x' i, lam i * μ' i))]
        simpa [hsum_fst] using hsumx
      · have hsum_snd :
            (Finset.univ.sum (fun i => (lam i • x' i, lam i * μ' i))).2 =
              Finset.univ.sum (fun i => lam i * μ' i) := by
          simp [snd_sum (s := Finset.univ)
            (f := fun i => (lam i • x' i, lam i * μ' i))]
        have hsumμ' : Finset.univ.sum (fun i => lam i * μ' i) = μ := by
          simpa [smul_eq_mul] using hsumμ
        simp [hsum_snd, hsumμ']

/-- Compare finite `EReal` sums using pointwise bounds and nonnegative weights. -/
lemma sum_ereal_mul_le_sum_of_le {n m : Nat} {g : (Fin n → Real) → EReal}
    (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)) (μ' : Fin m → Real)
    (h0 : ∀ i, 0 ≤ lam i) (hμ : ∀ i, g (x' i) ≤ (μ' i : EReal)) :
    Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) ≤
      Finset.univ.sum (fun i => ((lam i : Real) : EReal) * (μ' i : EReal)) := by
  classical
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hli : lam i = 0
  · simp [hli]
  · have hpos : 0 < lam i := lt_of_le_of_ne (h0 i) (Ne.symm hli)
    exact ereal_mul_le_mul_of_pos_left_general (t := lam i) hpos (hμ i)

/-- Coercion from `ℝ` to `EReal` commutes with finite sums. -/
lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (s.sum (fun i => (f i : EReal))) = ((s.sum f : ℝ) : EReal) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [ha, hs, EReal.coe_add]

/-- A finite sum of `EReal` terms is not `⊥` if each term is not `⊥`. -/
lemma sum_ne_bot_of_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (h : ∀ i ∈ s, f i ≠ ⊥) : s.sum f ≠ ⊥ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a s ha hs h
    have ha' : f a ≠ ⊥ := h a (by simp [ha])
    have hs' : s.sum f ≠ ⊥ := hs (by
      intro i hi
      exact h i (by simp [hi]))
    have hne : f a + s.sum f ≠ ⊥ := (EReal.add_ne_bot_iff).2 ⟨ha', hs'⟩
    simpa [ha] using hne

end Section05
end Chap01
