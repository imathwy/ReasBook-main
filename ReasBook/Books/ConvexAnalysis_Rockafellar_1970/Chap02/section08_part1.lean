/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part1

noncomputable section
open scoped RealInnerProductSpace
open scoped Pointwise Topology

section Chap02
section Section08

/-- Definition 8.0.1. Let `C` be a nonempty convex set in `ℝ^n`. The set `C` recedes in the
direction of a nonzero vector `y` if `x + λ • y ∈ C` for all `x ∈ C` and all `λ ≥ 0`. -/
def Set.RecedesInDirection {n : Nat} (C : Set (EuclideanSpace Real (Fin n)))
    (y : EuclideanSpace Real (Fin n)) : Prop :=
  y ≠ 0 ∧ ∀ ⦃x⦄, x ∈ C → ∀ ⦃t : Real⦄, 0 ≤ t → x + t • y ∈ C

/-- Definition 8.0.2. Let `C` be a non-empty convex set. The recession cone of `C`
is the set `0^+ C = { y | x + λ • y ∈ C` for all `x ∈ C` and all `λ ≥ 0` }. -/
def Set.recessionCone {E : Type*} [AddCommGroup E] [Module Real E] (C : Set E) : Set E :=
  { y | ∀ ⦃x⦄, x ∈ C → ∀ ⦃t : Real⦄, 0 ≤ t → x + t • y ∈ C }

/-- Definition 8.0.3. Let `C` be a non-empty convex set in `R^n`. A direction `D` of `R^n`
is called a direction of recession of `C` if `C` recedes in the direction `D`. -/
def Set.IsDirectionOfRecession {n : Nat} (C : Set (EuclideanSpace Real (Fin n)))
    (D : EuclideanSpace Real (Fin n)) : Prop :=
  Set.RecedesInDirection C D

/-- If `C` is closed under translation by `y`, then all integer translates stay in `C`. -/
lemma add_mem_of_add_mem_nat_smul {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)} (hadd : ∀ x ∈ C, x + y ∈ C) :
    ∀ {x} (_hx : x ∈ C) (m : ℕ), x + (m : ℝ) • y ∈ C := by
  intro x _hx m
  induction m generalizing x with
  | zero =>
      simpa using _hx
  | succ m ih =>
      have hx0 : x ∈ C := _hx
      have hx' : x + (m : ℝ) • y ∈ C := ih hx0
      have hy : x + (m : ℝ) • y + y ∈ C := hadd (x := x + (m : ℝ) • y) hx'
      simpa [Nat.cast_add, add_smul, one_smul, add_assoc] using hy

/-- If `C` is convex and `C + y ⊆ C`, then `y` lies in the recession cone. -/
lemma mem_recessionCone_of_add_mem {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hconv : Convex Real C) {y : EuclideanSpace Real (Fin n)}
    (hadd : ∀ x ∈ C, x + y ∈ C) : y ∈ Set.recessionCone C := by
  intro x hx t ht
  by_cases hzero : t = 0
  · simpa [hzero] using hx
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    obtain ⟨m, hm⟩ := exists_nat_ge t
    have hxmy : x + (m : ℝ) • y ∈ C := add_mem_of_add_mem_nat_smul (C := C) hadd hx m
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le htpos hm
    have hdivnonneg : 0 ≤ t / (m : ℝ) := div_nonneg ht (le_of_lt hmpos)
    have hdivle : t / (m : ℝ) ≤ (1 : ℝ) :=
      (div_le_one (a := t) (b := (m : ℝ)) hmpos).2 hm
    have hxmem :
        x + (t / (m : ℝ)) • ((m : ℝ) • y) ∈ C :=
      hconv.add_smul_mem hx hxmy ⟨hdivnonneg, hdivle⟩
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hmul : (t / (m : ℝ)) * (m : ℝ) = t := by
      calc
        (t / (m : ℝ)) * (m : ℝ) = t * (m : ℝ) / (m : ℝ) := by
          simp [div_mul_eq_mul_div]
        _ = t := by
          simpa [mul_comm] using (mul_div_cancel_left₀ (b := t) (a := (m : ℝ)) hm0)
    simpa [smul_smul, hmul] using hxmem

/-- Characterization of the recession cone via unit translation. -/
lemma recessionCone_eq_add_mem {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hconv : Convex Real C) :
    Set.recessionCone C = { y | ∀ x ∈ C, x + y ∈ C } := by
  ext y
  constructor
  · intro hy x hx
    have hy' := hy hx (t := (1 : ℝ)) (by exact zero_le_one)
    simpa using hy'
  · intro hy
    exact mem_recessionCone_of_add_mem (C := C) hconv hy

/-- The recession cone of a convex set is convex. -/
lemma recessionCone_convex {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hconv : Convex Real C) : Convex Real (Set.recessionCone C) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab x hx t ht
  have hx₁ : x + t • y₁ ∈ C := hy₁ hx ht
  have hx₂ : x + t • y₂ ∈ C := hy₂ hx ht
  have hcomb :
      a • (x + t • y₁) + b • (x + t • y₂) =
        x + t • (a • y₁ + b • y₂) := by
    ext i
    simp [smul_add, smul_smul, add_comm, add_left_comm, add_assoc, mul_comm, mul_assoc]
    calc
      a * x.ofLp i + b * x.ofLp i = (a + b) * x.ofLp i := by ring
      _ = x.ofLp i := by simp [hab]
  have hmem :
      a • (x + t • y₁) + b • (x + t • y₂) ∈ C :=
    hconv hx₁ hx₂ ha hb hab
  exact hcomb.symm ▸ hmem

/-- Positive scaling preserves membership in the recession cone. -/
lemma recessionCone_smul_pos {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)} (hy : y ∈ Set.recessionCone C) {t : Real} (ht : 0 < t) :
    t • y ∈ Set.recessionCone C := by
  intro x hx s hs
  have hst : 0 ≤ s * t := mul_nonneg hs (le_of_lt ht)
  have hmem := hy hx hst
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hmem

/-- Theorem 8.1. Let `C` be a non-empty convex set. The recession cone `0^+ C` is a convex cone
containing the origin, and it equals the set of vectors `y` such that `C + y ⊆ C`. -/
theorem recessionCone_convexCone_and_eq {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (_hC : C.Nonempty) (hconv : Convex Real C) :
    Convex Real (Set.recessionCone C) ∧
      (∀ y ∈ Set.recessionCone C, ∀ t : Real, 0 < t → t • y ∈ Set.recessionCone C) ∧
      (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C ∧
      Set.recessionCone C = { y | ∀ x ∈ C, x + y ∈ C } := by
  have hconvex : Convex Real (Set.recessionCone C) := recessionCone_convex (C := C) hconv
  have hsmul :
      ∀ y ∈ Set.recessionCone C, ∀ t : Real, 0 < t → t • y ∈ Set.recessionCone C := by
    intro y hy t ht
    exact recessionCone_smul_pos (C := C) hy ht
  have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
    intro x hx t ht
    simpa using hx
  have heq :
      Set.recessionCone C = { y | ∀ x ∈ C, x + y ∈ C } :=
    recessionCone_eq_add_mem (C := C) hconv
  exact ⟨hconvex, hsmul, hzero, heq⟩

/-- A direction vector of an affine subspace belongs to its recession cone. -/
lemma direction_subset_recessionCone_affineSubspace {n : Nat}
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    {y : EuclideanSpace Real (Fin n)} (hy : y ∈ M.direction) :
    y ∈ Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) := by
  intro x hx t _ht
  have hty : t • y ∈ M.direction := M.direction.smul_mem t hy
  have hmem : t • y +ᵥ x ∈ M :=
    AffineSubspace.vadd_mem_of_mem_direction (s := M) hty hx
  simpa [vadd_eq_add, add_comm] using hmem

/-- Any vector in the recession cone of a nonempty affine subspace lies in its direction. -/
lemma recessionCone_subset_direction_affineSubspace {n : Nat}
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    (hM : (M : Set (EuclideanSpace Real (Fin n))).Nonempty)
    {y : EuclideanSpace Real (Fin n)}
    (hy : y ∈ Set.recessionCone (M : Set (EuclideanSpace Real (Fin n)))) :
    y ∈ M.direction := by
  rcases hM with ⟨x0, hx0⟩
  have hx0y : x0 + y ∈ M := by
    have h := hy (x := x0) hx0 (t := (1 : Real)) (by exact zero_le_one)
    simpa using h
  have hdir : (x0 + y) -ᵥ x0 ∈ M.direction :=
    AffineSubspace.vsub_mem_direction (s := M) hx0y hx0
  simpa [vsub_eq_sub] using hdir

/-- Corollary 8.1.1. If `M ⊆ ℝ^n` is a non-empty affine set and `L` is the linear subspace
parallel to `M`, then `0^+ M = L`. -/
theorem recessionCone_affineSubspace_eq_direction {n : Nat}
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    (hM : (M : Set (EuclideanSpace Real (Fin n))).Nonempty)
    (L : Submodule Real (EuclideanSpace Real (Fin n)))
    (hL : L = M.direction) :
    Set.recessionCone (M : Set (EuclideanSpace Real (Fin n))) =
      (L : Set (EuclideanSpace Real (Fin n))) := by
  subst hL
  ext y
  constructor
  · intro hy
    exact recessionCone_subset_direction_affineSubspace (M := M) hM hy
  · intro hy
    exact direction_subset_recessionCone_affineSubspace (M := M) hy

/-- Inner product with a translated point splits into a sum. -/
lemma inner_add_smul_eq {n : Nat} (x y b : EuclideanSpace Real (Fin n)) (t : ℝ) :
    ⟪x + t • y, b⟫ = ⟪x, b⟫ + t * ⟪y, b⟫ := by
  simp [inner_add_left, inner_smul_left]

/-- If a linear function is bounded below on `t ≥ 0`, its slope is nonnegative. -/
lemma nonneg_of_forall_add_smul_ge {a b c : ℝ} (h : ∀ t ≥ 0, a + t * b ≥ c) : 0 ≤ b := by
  by_contra hb
  have hb' : b < 0 := lt_of_not_ge hb
  have h0 : a ≥ c := by
    have h0' := h 0 (by linarith)
    simpa using h0'
  set t : ℝ := (a - c) / (-b) + 1
  have hbpos : 0 < -b := by linarith
  have ht_nonneg : 0 ≤ t := by
    have hdiff : 0 ≤ a - c := by linarith
    have hdiv : 0 ≤ (a - c) / (-b) := div_nonneg hdiff (le_of_lt hbpos)
    have hsum : 0 ≤ (a - c) / (-b) + 1 := by linarith
    simpa [t] using hsum
  have hineq : a + t * b ≥ c := h t ht_nonneg
  have hbne : b ≠ 0 := ne_of_lt hb'
  have hdiv : b / (-b) = -1 := by
    calc
      b / (-b) = -(b / b) := by simp [div_neg_eq_neg_div]
      _ = -1 := by simp [hbne]
  have hval : a + t * b = c + b := by
    have :
        a + ((a - c) / (-b) + 1) * b = c + b := by
      calc
        a + ((a - c) / (-b) + 1) * b
            = a + (a - c) / (-b) * b + b := by ring
        _ = a + (a - c) * b / (-b) + b := by
              simpa using (div_mul_eq_mul_div (a - c) (-b) b)
        _ = a + (a - c) * (b / (-b)) + b := by
              simpa using (mul_div_assoc (a - c) b (-b))
        _ = a + (a - c) * (-1) + b := by simp [hdiv]
        _ = c + b := by ring
    simpa [t] using this
  have hcontr : c + b ≥ c := by simpa [hval] using hineq
  have hb_nonneg : 0 ≤ b := by linarith
  exact (not_le_of_gt hb') hb_nonneg

/-- Vectors in the recession cone of a nonempty intersection of half-spaces have
nonnegative inner products with the defining normals. -/
lemma recessionCone_subset_inner_ge_zero {n : Nat} {ι : Type*} (I : Set ι)
    (b : ι → EuclideanSpace Real (Fin n)) (β : ι → Real)
    (hC :
      ({x : EuclideanSpace Real (Fin n) | ∀ i, i ∈ I → ⟪x, b i⟫ ≥ β i} : Set _).Nonempty)
    {y : EuclideanSpace Real (Fin n)}
    (hy :
      y ∈ Set.recessionCone
        ({x : EuclideanSpace Real (Fin n) | ∀ i, i ∈ I → ⟪x, b i⟫ ≥ β i} : Set _)) :
    ∀ i, i ∈ I → ⟪y, b i⟫ ≥ 0 := by
  rcases hC with ⟨x0, hx0⟩
  intro i hi
  have hineq : ∀ t ≥ 0, ⟪x0, b i⟫ + t * ⟪y, b i⟫ ≥ β i := by
    intro t ht
    have hxmem :
        x0 + t • y ∈
          ({x : EuclideanSpace Real (Fin n) | ∀ i, i ∈ I → ⟪x, b i⟫ ≥ β i} : Set _) :=
      hy (x := x0) hx0 (t := t) ht
    have hbi : ⟪x0 + t • y, b i⟫ ≥ β i := hxmem i hi
    simpa [inner_add_smul_eq] using hbi
  exact nonneg_of_forall_add_smul_ge hineq

/-- The recession cone of a closed set is closed. -/
lemma recessionCone_isClosed_of_closed {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hC : IsClosed C) : IsClosed (Set.recessionCone C) := by
  classical
  have hclosed_aux :
      ∀ (x : EuclideanSpace Real (Fin n)) (t : ℝ),
        IsClosed {y : EuclideanSpace Real (Fin n) | x + t • y ∈ C} := by
    intro x t
    have hcont : Continuous fun y : EuclideanSpace Real (Fin n) => x + t • y := by
      simpa using (continuous_const.add (continuous_const.smul continuous_id))
    simpa [Set.preimage] using hC.preimage hcont
  have hrepr :
      Set.recessionCone C =
        ⋂ x, ⋂ (hx : x ∈ C), ⋂ (t : ℝ), ⋂ (ht : 0 ≤ t),
          {y : EuclideanSpace Real (Fin n) | x + t • y ∈ C} := by
    ext y
    constructor
    · intro hy
      refine Set.mem_iInter.2 ?_
      intro x
      refine Set.mem_iInter.2 ?_
      intro hx
      refine Set.mem_iInter.2 ?_
      intro t
      refine Set.mem_iInter.2 ?_
      intro ht
      exact hy hx ht
    · intro hy x hx t ht
      have hy' :
          y ∈ {y : EuclideanSpace Real (Fin n) | x + t • y ∈ C} :=
        (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hy x) hx) t) ht)
      simpa using hy'
  have hclosed :
      IsClosed
        (⋂ x, ⋂ (hx : x ∈ C), ⋂ (t : ℝ), ⋂ (ht : 0 ≤ t),
          {y : EuclideanSpace Real (Fin n) | x + t • y ∈ C}) := by
    refine isClosed_iInter ?_
    intro x
    refine isClosed_iInter ?_
    intro hx
    refine isClosed_iInter ?_
    intro t
    refine isClosed_iInter ?_
    intro ht
    exact hclosed_aux x t
  simpa [hrepr] using hclosed

/-- Corollary 8.1.2. Let `C = {x ∈ ℝ^n | ⟪x, b_i⟫ ≥ β_i, ∀ i ∈ I}` be nonempty. Then
`0^+ C = {y ∈ ℝ^n | ⟪y, b_i⟫ ≥ 0, ∀ i ∈ I}`. -/
theorem recessionCone_eq_inner_ge_zero {n : Nat} {ι : Type*} (I : Set ι)
    (b : ι → EuclideanSpace Real (Fin n)) (β : ι → Real)
    (hC :
      ({x : EuclideanSpace Real (Fin n) | ∀ i, i ∈ I → ⟪x, b i⟫ ≥ β i} : Set _).Nonempty) :
    Set.recessionCone
        ({x : EuclideanSpace Real (Fin n) | ∀ i, i ∈ I → ⟪x, b i⟫ ≥ β i} : Set _) =
      {y : EuclideanSpace Real (Fin n) | ∀ i, i ∈ I → ⟪y, b i⟫ ≥ 0} := by
  ext y
  constructor
  · intro hy
    exact recessionCone_subset_inner_ge_zero (I := I) (b := b) (β := β) hC hy
  · intro hy x hx t ht i hi
    have hx_i : ⟪x, b i⟫ ≥ β i := hx i hi
    have hy_i : ⟪y, b i⟫ ≥ 0 := hy i hi
    have hsum : ⟪x, b i⟫ + t * ⟪y, b i⟫ ≥ β i := by
      have hnonneg : 0 ≤ t * ⟪y, b i⟫ := mul_nonneg ht hy_i
      linarith
    simpa [inner_add_smul_eq] using hsum

/-- Elements of the recession cone give limits with decreasing coefficients. -/
lemma recessionCone_subset_seq_limits {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) {y : EuclideanSpace Real (Fin n)} (hy : y ∈ Set.recessionCone C) :
    ∃ (x : ℕ → EuclideanSpace Real (Fin n)) (r : ℕ → ℝ),
      (∀ n, x n ∈ C) ∧ Antitone r ∧ Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) ∧
        Filter.Tendsto (fun n => r n • x n) Filter.atTop (𝓝 y) := by
  rcases hCne with ⟨x0, hx0⟩
  refine ⟨(fun n => x0 + ((n : ℝ) + 1) • y), (fun n => 1 / ((n : ℝ) + 1)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have hnonneg : 0 ≤ (n : ℝ) + 1 := by linarith
    exact hy (x := x0) hx0 (t := (n : ℝ) + 1) hnonneg
  · intro m n hmn
    dsimp
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hle' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    exact one_div_le_one_div_of_le hpos hle
  · simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))
  · have hcont_smul : Continuous fun t : ℝ => t • x0 := by
      continuity
    have hsmul :
        Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x0) Filter.atTop (𝓝 (0 : _)) :=
      (by
        simpa using
          (hcont_smul.continuousAt.tendsto.comp
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))))
    have hcont_add : Continuous fun z : EuclideanSpace Real (Fin n) => z + y := by
      continuity
    have hlim :
        Filter.Tendsto
            (fun n : ℕ => (1 / ((n : ℝ) + 1)) • x0 + y) Filter.atTop (𝓝 y) := by
      simpa using (hcont_add.continuousAt.tendsto.comp hsmul)
    have hform :
        (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (x0 + ((n : ℝ) + 1) • y)) =
          fun n : ℕ => (1 / ((n : ℝ) + 1)) • x0 + y := by
      funext n
      have hne : (n : ℝ) + 1 ≠ 0 := by linarith
      calc
        (1 / ((n : ℝ) + 1)) • (x0 + ((n : ℝ) + 1) • y)
            = (1 / ((n : ℝ) + 1)) • x0 +
                (1 / ((n : ℝ) + 1)) • (((n : ℝ) + 1) • y) := by
                  simp [smul_add]
        _ = (1 / ((n : ℝ) + 1)) • x0 + y := by
              simp [smul_smul, hne]
    refine hlim.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro n
    exact (congrArg (fun f => f n) hform).symm

/-- If a point in `closure K` has positive first coordinate, then it lies in `K`. -/
lemma mem_K_of_mem_closure_K_first_pos {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex Real C) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, v ∈ closure K → 0 < first v → v ∈ K := by
  classical
  intro coords first tail S K v hv hpos
  have hmem : ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
    simpa [coords, first, tail, S, K] using (mem_K_iff_first_tail (n := n) (C := C) hCconv)
  rcases (mem_closure_iff_seq_limit).1 hv with ⟨vseq, hvseqK, hvseqtendsto⟩
  have hcont_first : Continuous first := by
    simpa [first] using
      (continuous_apply 0).comp
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).continuous
  have hcont_tail : Continuous tail := by
    have hcont_coords : Continuous coords :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).continuous
    have hcont_pi :
        Continuous fun v : EuclideanSpace Real (Fin (1 + n)) =>
          fun i => coords v (Fin.natAdd 1 i) := by
      refine continuous_pi ?_
      intro i
      simpa using (continuous_apply (Fin.natAdd 1 i)).comp hcont_coords
    simpa [tail] using
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.continuous.comp hcont_pi
  have hfirst_tendsto :
      Filter.Tendsto (fun k => first (vseq k)) Filter.atTop (𝓝 (first v)) :=
    (hcont_first.tendsto v).comp hvseqtendsto
  have htail_tendsto :
      Filter.Tendsto (fun k => tail (vseq k)) Filter.atTop (𝓝 (tail v)) :=
    (hcont_tail.tendsto v).comp hvseqtendsto
  have hx_exists :
      ∀ k, ∃ x, x ∈ C ∧ first (vseq k) • x = tail (vseq k) := by
    intro k
    rcases (hmem (vseq k)).1 (hvseqK k) with ⟨_, hx⟩
    exact hx
  choose x hxC hxeq using hx_exists
  have hxeq' : ∀ k, x k = (first (vseq k))⁻¹ • tail (vseq k) := by
    intro k
    have hposk : 0 < first (vseq k) := (hmem (vseq k)).1 (hvseqK k) |>.1
    have hne : (first (vseq k) : ℝ) ≠ 0 := ne_of_gt hposk
    have hmul : (first (vseq k))⁻¹ * first (vseq k) = (1 : ℝ) := by
      field_simp [hne]
    calc
      x k = (1 : ℝ) • x k := by simp
      _ = ((first (vseq k))⁻¹ * first (vseq k)) • x k := by simp [hmul]
      _ = (first (vseq k))⁻¹ • (first (vseq k) • x k) := by
        simp [smul_smul]
      _ = (first (vseq k))⁻¹ • tail (vseq k) := by
        simp [hxeq k]
  have hx_tendsto :
      Filter.Tendsto (fun k => x k) Filter.atTop (𝓝 ((first v)⁻¹ • tail v)) := by
    have hfirst_ne : (first v : ℝ) ≠ 0 := ne_of_gt hpos
    have hfirst_inv_tendsto :
        Filter.Tendsto (fun k => (first (vseq k))⁻¹) Filter.atTop (𝓝 ((first v)⁻¹)) :=
      (tendsto_inv₀ (x := first v) hfirst_ne).comp hfirst_tendsto
    have hsmul :
        Filter.Tendsto (fun k => (first (vseq k))⁻¹ • tail (vseq k)) Filter.atTop
          (𝓝 ((first v)⁻¹ • tail v)) :=
      hfirst_inv_tendsto.smul htail_tendsto
    simpa [hxeq'] using hsmul
  have hxlimit : (first v)⁻¹ • tail v ∈ C := by
    refine hCclosed.mem_of_tendsto hx_tendsto ?_
    exact Filter.Eventually.of_forall hxC
  have htail_mem : tail v ∈ (first v) • C := by
    refine ⟨(first v)⁻¹ • tail v, hxlimit, ?_⟩
    have hne : (first v : ℝ) ≠ 0 := ne_of_gt hpos
    have hmul : (first v : ℝ) * (first v)⁻¹ = 1 := by
      field_simp [hne]
    calc
      first v • ((first v)⁻¹ • tail v) =
          ((first v) * (first v)⁻¹) • tail v := by
            simp [smul_smul]
      _ = tail v := by simp [hmul]
  exact (hmem v).2 ⟨hpos, htail_mem⟩

/-- Points in `closure K` with zero first coordinate yield recession directions. -/
lemma tail_mem_recessionCone_of_mem_closure_K_first_zero {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex Real C) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, v ∈ closure K → first v = 0 → tail v ∈ Set.recessionCone C := by
  classical
  intro coords first tail S K v hv hzero
  rcases (mem_closure_iff_seq_limit).1 hv with ⟨vseq, hvseqK, hvseqtendsto⟩
  have hmem : ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
    simpa [coords, first, tail, S, K] using (mem_K_iff_first_tail (n := n) (C := C) hCconv)
  have hcont_first : Continuous first := by
    simpa [first] using
      (continuous_apply 0).comp
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).continuous
  have hcont_tail : Continuous tail := by
    have hcont_coords : Continuous coords :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).continuous
    have hcont_pi :
        Continuous fun v : EuclideanSpace Real (Fin (1 + n)) =>
          fun i => coords v (Fin.natAdd 1 i) := by
      refine continuous_pi ?_
      intro i
      simpa using (continuous_apply (Fin.natAdd 1 i)).comp hcont_coords
    simpa [tail] using
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.continuous.comp hcont_pi
  have hfirst_tendsto :
      Filter.Tendsto (fun k => first (vseq k)) Filter.atTop (𝓝 (first v)) :=
    (hcont_first.tendsto v).comp hvseqtendsto
  have htail_tendsto :
      Filter.Tendsto (fun k => tail (vseq k)) Filter.atTop (𝓝 (tail v)) :=
    (hcont_tail.tendsto v).comp hvseqtendsto
  intro x hx t ht
  by_cases ht0 : t = 0
  · subst ht0
    simpa using hx
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let y0 : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => 1)
  let append :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
        EuclideanSpace Real (Fin (1 + n)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
    fun x => append y0 x
  have hy0 : (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y0) 0 = 1 := by
    simp [y0]
  have hfirst_tail_lift :
      first (lift x) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y0) 0 ∧
        tail (lift x) = x := by
    simpa [lift, coords, first, tail, append] using
      (first_tail_append (n := n) (y := y0) (z := x))
  have hfirst_lift : first (lift x) = 1 := by
    simpa [hy0] using hfirst_tail_lift.1
  have hfirst_lift' : (lift x).ofLp 0 = 1 := by
    simpa [first, coords] using hfirst_lift
  have htail_lift : tail (lift x) = x := hfirst_tail_lift.2
  have hlift_mem : lift x ∈ K := by
    have hs : lift x ∈ S := by
      refine ⟨hfirst_lift, ?_⟩
      simpa [htail_lift] using hx
    have hsubset : S ⊆ K := by
      simpa [K] using (ConvexCone.subset_hull (R := Real) (s := S))
    exact hsubset hs
  let w : ℕ → EuclideanSpace Real (Fin (1 + n)) := fun k => lift x + t • vseq k
  have hw_mem : ∀ k, w k ∈ K := by
    intro k
    have hsmul : t • vseq k ∈ K := by
      have hsmul' :
          t • vseq k ∈ (ConvexCone.hull Real S : Set _) :=
        (ConvexCone.hull Real S).smul_mem htpos (by simpa [K] using hvseqK k)
      simpa [K] using hsmul'
    have hadd : lift x + t • vseq k ∈ K := by
      have hsum :
          lift x + t • vseq k ∈ (ConvexCone.hull Real S : Set _) :=
        (ConvexCone.hull Real S).add_mem (by simpa [K] using hlift_mem) (by simpa [K] using hsmul)
      simpa [K, w] using hsum
    simpa [w] using hadd
  have hfirst_w : ∀ k, first (w k) = 1 + t * first (vseq k) := by
    intro k
    simp [w, first, coords, hfirst_lift', add_comm]
  have htail_w : ∀ k, tail (w k) = x + t • tail (vseq k) := by
    intro k
    have htail_add :
        tail (lift x + t • vseq k) = tail (lift x) + t • tail (vseq k) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext i
      simp [tail, coords]
    simpa [w, htail_lift] using htail_add
  have hfirst_w_tendsto :
      Filter.Tendsto (fun k => first (w k)) Filter.atTop (𝓝 (1 + t * first v)) := by
    have hcont : Continuous fun r : ℝ => 1 + t * r := by
      simpa using (continuous_const.add (continuous_const.mul continuous_id))
    simpa [hfirst_w] using (hcont.tendsto (first v)).comp hfirst_tendsto
  have htail_w_tendsto :
      Filter.Tendsto (fun k => tail (w k)) Filter.atTop (𝓝 (x + t • tail v)) := by
    have hcont : Continuous fun z : EuclideanSpace Real (Fin n) => x + t • z := by
      simpa using (continuous_const.add (continuous_const.smul continuous_id))
    simpa [htail_w] using (hcont.tendsto (tail v)).comp htail_tendsto
  have hfirst_w_tendsto' :
      Filter.Tendsto (fun k => first (w k)) Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa [hzero] using hfirst_w_tendsto
  have hc_exists :
      ∀ k, ∃ c, c ∈ C ∧ first (w k) • c = tail (w k) := by
    intro k
    rcases (hmem (w k)).1 (hw_mem k) with ⟨_, hc⟩
    exact hc
  choose c hcC hceq using hc_exists
  have hceq' : ∀ k, c k = (first (w k))⁻¹ • tail (w k) := by
    intro k
    have hposk : 0 < first (w k) := (hmem (w k)).1 (hw_mem k) |>.1
    have hne : (first (w k) : ℝ) ≠ 0 := ne_of_gt hposk
    have hmul : (first (w k))⁻¹ * first (w k) = (1 : ℝ) := by
      field_simp [hne]
    calc
      c k = (1 : ℝ) • c k := by simp
      _ = ((first (w k))⁻¹ * first (w k)) • c k := by simp [hmul]
      _ = (first (w k))⁻¹ • (first (w k) • c k) := by
        simp [smul_smul]
      _ = (first (w k))⁻¹ • tail (w k) := by
        simp [hceq k]
  have hc_tendsto :
      Filter.Tendsto (fun k => c k) Filter.atTop (𝓝 (x + t • tail v)) := by
    have hfirst_inv_tendsto :
        Filter.Tendsto (fun k => (first (w k))⁻¹) Filter.atTop (𝓝 (1 : ℝ)) :=
      (by
        simpa using (tendsto_inv₀ (x := (1 : ℝ)) one_ne_zero).comp hfirst_w_tendsto')
    have hsmul :
        Filter.Tendsto (fun k => (first (w k))⁻¹ • tail (w k)) Filter.atTop
          (𝓝 ((1 : ℝ) • (x + t • tail v))) :=
      hfirst_inv_tendsto.smul htail_w_tendsto
    simpa [hceq', one_smul] using hsmul
  have hxlimit : x + t • tail v ∈ C := by
    refine hCclosed.mem_of_tendsto hc_tendsto ?_
    exact Filter.Eventually.of_forall hcC
  simpa using hxlimit

/-- The closure of `K` adds precisely the recession directions at `first = 0`. -/
lemma closure_cone_eq_union_recession {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    closure K = K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C} := by
  classical
  intro coords first tail S K
  have hmem : ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
    simpa [coords, first, tail, S, K] using (mem_K_iff_first_tail (n := n) (C := C) hCconv)
  have hpos_mem :
      ∀ v, v ∈ closure K → 0 < first v → v ∈ K := by
    simpa [coords, first, tail, S, K] using
      (mem_K_of_mem_closure_K_first_pos (n := n) (C := C) hCclosed hCconv)
  have htail_mem :
      ∀ v, v ∈ closure K → first v = 0 → tail v ∈ Set.recessionCone C := by
    simpa [coords, first, tail, S, K] using
      (tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n) (C := C) hCclosed hCconv)
  ext v
  constructor
  · intro hv
    have hsubset : K ⊆ {v | 0 ≤ first v} := by
      intro v hvK
      exact le_of_lt ((hmem v).1 hvK).1
    have hclosed_half : IsClosed {v | 0 ≤ first v} := by
      have hcont : Continuous first := by
        simpa [first] using
          (continuous_apply 0).comp
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).continuous
      simpa [Set.preimage] using (isClosed_Ici.preimage hcont)
    have hnonneg : 0 ≤ first v := (closure_minimal hsubset hclosed_half) hv
    have hpos_or_eq : 0 < first v ∨ first v = 0 := by
      rcases lt_or_eq_of_le hnonneg with hpos | hzero
      · exact Or.inl hpos
      · exact Or.inr hzero.symm
    cases hpos_or_eq with
    | inl hpos =>
        left
        exact hpos_mem v hv hpos
    | inr hzero =>
        right
        exact ⟨hzero, htail_mem v hv hzero⟩
  · intro hv
    rcases hv with hvK | hvrec
    · exact subset_closure hvK
    · rcases hvrec with ⟨hzero, hy⟩
      rcases hCne with ⟨x0, hx0⟩
      let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
      let xseq : ℕ → EuclideanSpace Real (Fin n) := fun n => x0 + ((n : ℝ) + 1) • tail v
      let zseq : ℕ → EuclideanSpace Real (Fin n) := fun n => r n • xseq n
      let yseq : ℕ → EuclideanSpace Real (Fin 1) :=
        fun n => (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r n)
      let append :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
            EuclideanSpace Real (Fin (1 + n)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
            ((Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
      let vseq : ℕ → EuclideanSpace Real (Fin (1 + n)) := fun n => append (yseq n) (zseq n)
      have hxseq : ∀ n, xseq n ∈ C := by
        intro n
        have hnonneg : 0 ≤ (n : ℝ) + 1 := by linarith
        exact hy (x := x0) hx0 (t := (n : ℝ) + 1) hnonneg
      have hrpos : ∀ n, 0 < r n := by
        intro n
        have hpos : 0 < (n : ℝ) + 1 := by linarith
        simpa [r] using (one_div_pos.2 hpos)
      have hfirst_tail_vseq :
          ∀ k, first (vseq k) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) (yseq k)) 0 ∧
            tail (vseq k) = zseq k := by
        intro k
        simpa [vseq, coords, first, tail, append] using
          (first_tail_append (n := n) (y := yseq k) (z := zseq k))
      have hfirst_vseq : ∀ n, first (vseq n) = r n := by
        intro n
        have := (hfirst_tail_vseq n).1
        simpa [yseq] using this
      have htail_vseq : ∀ n, tail (vseq n) = zseq n := by
        intro n
        exact (hfirst_tail_vseq n).2
      have hvseqK : ∀ n, vseq n ∈ K := by
        intro n
        have htail_mem : tail (vseq n) ∈ (first (vseq n)) • C := by
          refine ⟨xseq n, hxseq n, ?_⟩
          simp [htail_vseq n, hfirst_vseq n, zseq]
        exact (hmem (vseq n)).2 ⟨by simpa [hfirst_vseq n] using hrpos n, htail_mem⟩
      have hr_tendsto : Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [r, one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))
      have hyseq_tendsto :
          Filter.Tendsto yseq Filter.atTop
            (𝓝 ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))) := by
        have hcont :
            Continuous fun r : ℝ =>
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r) := by
          have hcont_pi : Continuous fun r : ℝ => (fun _ : Fin 1 => r) := by
            refine continuous_pi ?_
            intro _
            simpa using (continuous_id : Continuous fun r : ℝ => r)
          simpa using
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.continuous.comp hcont_pi
        simpa [yseq] using (hcont.tendsto (0 : ℝ)).comp hr_tendsto
      have hzseq_tendsto :
          Filter.Tendsto zseq Filter.atTop (𝓝 (tail v)) := by
        have hcont_smul : Continuous fun t : ℝ => t • x0 := by
          simpa using (continuous_id.smul continuous_const)
        have hsmul :
            Filter.Tendsto (fun n : ℕ => r n • x0) Filter.atTop (𝓝 (0 : _)) :=
          (by
            simpa using (hcont_smul.continuousAt.tendsto.comp hr_tendsto))
        have hcont_add : Continuous fun z : EuclideanSpace Real (Fin n) => z + tail v := by
          simpa using
            (continuous_id.add (continuous_const :
              Continuous fun _ : EuclideanSpace Real (Fin n) => tail v))
        have hlim :
            Filter.Tendsto (fun n : ℕ => r n • x0 + tail v) Filter.atTop (𝓝 (tail v)) := by
          simpa using (hcont_add.continuousAt.tendsto.comp hsmul)
        have hform :
            (fun n : ℕ => r n • xseq n) = fun n : ℕ => r n • x0 + tail v := by
          funext n
          have hne : (n : ℝ) + 1 ≠ 0 := by linarith
          have hmul : r n * ((n : ℝ) + 1) = (1 : ℝ) := by
            simp [r, hne, div_eq_mul_inv]
          calc
            r n • xseq n = r n • (x0 + ((n : ℝ) + 1) • tail v) := rfl
            _ = r n • x0 + r n • (((n : ℝ) + 1) • tail v) := by
              simp [smul_add]
            _ = r n • x0 + tail v := by
              simp [smul_smul, hmul]
        simpa [zseq, hform] using hlim
      have hcont_append :
          Continuous fun p :
              EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n) =>
            append p.1 p.2 := by
        have hcont_pair :
            Continuous fun p :
                EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n) =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) p.1,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) p.2) := by
          exact
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).continuous.comp continuous_fst).prodMk
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous.comp continuous_snd)
        have hcont_append' :
            Continuous fun p :
                EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n) =>
              (Fin.appendIsometry 1 n)
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) p.1,
                 (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) p.2) := by
          exact (Fin.appendIsometry 1 n).continuous.comp hcont_pair
        simpa [append] using
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm.continuous.comp hcont_append'
      have hpair_tendsto :
          Filter.Tendsto (fun n : ℕ => (yseq n, zseq n)) Filter.atTop
            (𝓝 ( (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)),
                  tail v )) := by
        simpa using (hyseq_tendsto.prodMk_nhds hzseq_tendsto)
      have hvseq_tendsto :
          Filter.Tendsto vseq Filter.atTop
            (𝓝 (append
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
              (tail v))) := by
        simpa [vseq] using (hcont_append.tendsto _).comp hpair_tendsto
      have hfirst_tail_v0 :
          first (append
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
            (tail v)) =
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))) 0 ∧
            tail (append
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
              (tail v)) = tail v := by
        simpa [coords, first, tail, append] using
          (first_tail_append (n := n)
            (y := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
            (z := tail v))
      have hv_eq :
          v =
            append ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
              (tail v) := by
        have hfirst_zero :
            first (append
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
              (tail v)) = 0 := by
          simpa using hfirst_tail_v0.1
        have hfirst_eq :
            first v =
              first (append
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
                (tail v)) := by
          calc
            first v = 0 := hzero
            _ =
                first (append
                  ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
                  (tail v)) := by
                simpa using hfirst_zero.symm
        have htail_eq :
            tail v =
              tail (append
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
                (tail v)) := by
          simpa using hfirst_tail_v0.2.symm
        have heq :
            ∀ u w, first u = first w → tail u = tail w → u = w := by
          simpa [coords, first, tail] using (eq_of_first_tail_eq (n := n))
        exact heq v _ hfirst_eq htail_eq
      refine (mem_closure_iff_seq_limit).2 ?_
      refine ⟨vseq, hvseqK, ?_⟩
      rw [hv_eq]
      exact hvseq_tendsto

/-- Reverse inclusion for the sequence characterization of the recession cone. -/
lemma seq_limits_subset_recessionCone {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) {y : EuclideanSpace Real (Fin n)}
    (hy :
      ∃ (x : ℕ → EuclideanSpace Real (Fin n)) (r : ℕ → ℝ),
        (∀ n, x n ∈ C) ∧ Antitone r ∧ Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) ∧
          Filter.Tendsto (fun n => r n • x n) Filter.atTop (𝓝 y)) :
    y ∈ Set.recessionCone C := by
  rcases hy with ⟨x, r, hxC, hr_antitone, hr_tendsto, hrx_tendsto⟩
  have hnonneg : ∀ n, 0 ≤ r n := by
    intro n
    by_contra hneg
    have hneg' : r n < 0 := lt_of_not_ge hneg
    have hlim_lower := (tendsto_order.1 hr_tendsto).1
    have hnegn : r n / 2 < 0 := by linarith
    rcases (Filter.eventually_atTop.1 (hlim_lower (r n / 2) hnegn)) with ⟨N, hN⟩
    have hle : r (max N n) ≤ r n := hr_antitone (by exact le_max_right _ _)
    have hgt : r n / 2 < r (max N n) := hN _ (by exact le_max_left _ _)
    have hlt1 : r n / 2 < r n := lt_of_lt_of_le hgt hle
    have hlt2 : r n < r n / 2 := by linarith
    exact (lt_asymm hlt1 hlt2)
  by_cases hzero : ∃ n, r n = 0
  · rcases hzero with ⟨n0, hn0⟩
    have hzero_eventually : ∀ᶠ n in Filter.atTop, r n = 0 := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨n0, ?_⟩
      intro m hm
      have hle : r m ≤ r n0 := hr_antitone hm
      have hle' : r m ≤ 0 := by simpa [hn0] using hle
      have hge : 0 ≤ r m := hnonneg m
      exact le_antisymm hle' hge
    have hzero_smul :
        (fun n => r n • x n) =ᶠ[Filter.atTop] fun _ => (0 : EuclideanSpace Real (Fin n)) := by
      refine hzero_eventually.mono ?_
      intro n hn
      simp [hn]
    have hy0 :
        y = (0 : EuclideanSpace Real (Fin n)) := by
      have hlim0 :
          Filter.Tendsto (fun _ : ℕ => (0 : EuclideanSpace Real (Fin n)))
            Filter.atTop (𝓝 (0 : EuclideanSpace Real (Fin n))) := tendsto_const_nhds
      exact tendsto_nhds_unique_of_eventuallyEq hrx_tendsto hlim0 hzero_smul
    subst hy0
    have hzero_mem :
        (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
      exact (recessionCone_convexCone_and_eq (C := C) hCne hCconv).2.2.1
    simpa using hzero_mem
  · have hpos : ∀ n, 0 < r n := by
      intro n
      have hne : r n ≠ 0 := by
        intro hzero'
        exact hzero ⟨n, hzero'⟩
      exact lt_of_le_of_ne (hnonneg n) hne.symm
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    let yseq : ℕ → EuclideanSpace Real (Fin 1) :=
      fun n => (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r n)
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let vseq : ℕ → EuclideanSpace Real (Fin (1 + n)) :=
      fun n => append (yseq n) (r n • x n)
    have hmem : ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
      simpa [coords, first, tail, S, K] using (mem_K_iff_first_tail (n := n) (C := C) hCconv)
    have hfirst_tail_vseq :
        ∀ k, first (vseq k) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) (yseq k)) 0 ∧
          tail (vseq k) = r k • x k := by
      intro k
      simpa [vseq, coords, first, tail, append] using
        (first_tail_append (n := n) (y := yseq k) (z := r k • x k))
    have hfirst_vseq : ∀ n, first (vseq n) = r n := by
      intro n
      have := (hfirst_tail_vseq n).1
      simpa [yseq] using this
    have htail_vseq : ∀ n, tail (vseq n) = r n • x n := by
      intro n
      exact (hfirst_tail_vseq n).2
    have hvseqK : ∀ n, vseq n ∈ K := by
      intro n
      have htail_mem : tail (vseq n) ∈ (first (vseq n)) • C := by
        refine ⟨x n, hxC n, ?_⟩
        simp [htail_vseq n, hfirst_vseq n]
      exact (hmem (vseq n)).2 ⟨by simpa [hfirst_vseq n] using hpos n, htail_mem⟩
    have hcont_append :
        Continuous fun p :
            EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n) =>
          append p.1 p.2 := by
      have hcont_pair :
          Continuous fun p :
              EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n) =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) p.1,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) p.2) := by
        exact
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).continuous.comp continuous_fst).prodMk
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous.comp continuous_snd)
      have hcont_append' :
          Continuous fun p :
              EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n) =>
            (Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) p.1,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) p.2) := by
        exact (Fin.appendIsometry 1 n).continuous.comp hcont_pair
      simpa [append] using
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm.continuous.comp hcont_append'
    have hyseq_tendsto :
        Filter.Tendsto yseq Filter.atTop
          (𝓝 ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))) := by
      have hcont :
          Continuous fun r : ℝ =>
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r) := by
        have hcont_pi : Continuous fun r : ℝ => (fun _ : Fin 1 => r) := by
          refine continuous_pi ?_
          intro _
          simpa using (continuous_id : Continuous fun r : ℝ => r)
        simpa using
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.continuous.comp hcont_pi
      simpa [yseq] using (hcont.tendsto (0 : ℝ)).comp hr_tendsto
    have hpair_tendsto :
        Filter.Tendsto (fun n : ℕ => (yseq n, r n • x n)) Filter.atTop
          (𝓝 ( (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)),
                y )) := by
      exact hyseq_tendsto.prodMk_nhds hrx_tendsto
    have hvseq_tendsto :
        Filter.Tendsto vseq Filter.atTop
          (𝓝 (append
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
            y)) := by
      simpa [vseq] using (hcont_append.tendsto _).comp hpair_tendsto
    have hfirst_tail_v0 :
        first (append
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))) y) =
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))) 0 ∧
          tail (append
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))) y) = y := by
      simpa [coords, first, tail, append] using
        (first_tail_append (n := n)
          (y := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))
          (z := y))
    have hzero_first :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ)))) 0 = 0 := by
      simp
    have hfirst_zero :
        first (append
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))) y) = 0 := by
      simpa [hzero_first] using hfirst_tail_v0.1
    have htail_v0 :
        tail (append
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))) y) = y :=
      hfirst_tail_v0.2
    have hmem_closure :
        append ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))) y ∈
          closure K := by
      refine (mem_closure_iff_seq_limit).2 ?_
      refine ⟨vseq, hvseqK, hvseq_tendsto⟩
    have hrec :
        tail (append
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))) y) ∈
          Set.recessionCone C := by
      have htail_mem :
          ∀ v, v ∈ closure K → first v = 0 → tail v ∈ Set.recessionCone C := by
        simpa [coords, first, tail, S, K] using
          (tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n) (C := C)
            hCclosed hCconv)
      exact htail_mem _ hmem_closure hfirst_zero
    have hy_mem : y ∈ Set.recessionCone C := by
      have htail_v0' :
          tail (append (WithLp.toLp 2 fun x => 0) y) = y := by
        simpa using htail_v0
      simpa [htail_v0'] using hrec
    simpa using hy_mem

end Section08
end Chap02
