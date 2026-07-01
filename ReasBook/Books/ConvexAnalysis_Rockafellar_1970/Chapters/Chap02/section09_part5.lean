/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part4

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- The infimal convolution family is the linear-map infimum for the block sum. -/
lemma infimalConvolutionFamily_eq_Ah {n m : Nat}
    (f : Fin m → (Fin n → Real) → EReal) :
    let e := blockEquivFun (n := n) (m := m)
    let A := (sumLinearMapFun (n := n) (m := m)).comp e.toLinearMap
    let h : (Fin (m * n) → Real) → EReal :=
      fun x => Finset.univ.sum (fun i => f i ((e x) i))
    let Ah : (Fin n → Real) → EReal :=
      fun y => sInf { z : EReal | ∃ x : Fin (m * n) → Real, A x = y ∧ z = h x }
    Ah = infimalConvolutionFamily f := by
  classical
  intro e A h Ah
  funext y
  have hset :
      { z : EReal | ∃ x : Fin (m * n) → Real, A x = y ∧ z = h x } =
        { z : EReal |
          ∃ x' : Fin m → (Fin n → Real),
            Finset.univ.sum (fun i => x' i) = y ∧
              z = Finset.univ.sum (fun i => f i (x' i)) } := by
    ext z
    constructor
    · rintro ⟨x, hxA, rfl⟩
      refine ⟨e x, ?_, ?_⟩
      · simpa [A, sumLinearMapFun] using hxA
      · simp [h]
    · rintro ⟨x', hsum, rfl⟩
      refine ⟨e.symm x', ?_, ?_⟩
      · simpa [A, sumLinearMapFun] using hsum
      · simp [h]
  simp [infimalConvolutionFamily, Ah, hset]

/-- The `h0_plus` kernel condition for the block sum follows from the corollary hypothesis. -/
lemma hA_from_hzero {n m : Nat}
    {f0_plus : Fin m → (Fin n → Real) → EReal}
    (hzero :
      ∀ z : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => f0_plus i (z i)) ≤ (0 : EReal)) →
        (Finset.univ.sum (fun i => f0_plus i (-(z i))) > (0 : EReal)) →
        (Finset.univ.sum (fun i => z i) ≠ (0 : Fin n → Real))) :
    let e := blockEquivFun (n := n) (m := m)
    let A := (sumLinearMapFun (n := n) (m := m)).comp e.toLinearMap
    let h0_plus : (Fin (m * n) → Real) → EReal :=
      fun x => Finset.univ.sum (fun i => f0_plus i ((e x) i))
    ∀ z : Fin (m * n) → Real,
      h0_plus z ≤ (0 : EReal) →
      h0_plus (-z) > (0 : EReal) → A z ≠ 0 := by
  classical
  intro e A h0_plus z hzle hzgt
  have hzle' :
      Finset.univ.sum (fun i => f0_plus i ((e z) i)) ≤ (0 : EReal) := by
    simpa [h0_plus] using hzle
  have hzgt' :
      Finset.univ.sum (fun i => f0_plus i (-(e z i))) > (0 : EReal) := by
    have hzgt'' :
        Finset.univ.sum (fun i => f0_plus i ((e (-z)) i)) > (0 : EReal) := by
      simpa [h0_plus] using hzgt
    have hneg : e (-z) = - e z := by
      simp
    simpa [hneg] using hzgt''
  have hsum_ne :
      Finset.univ.sum (fun i => (e z) i) ≠ (0 : Fin n → Real) :=
    hzero (e z) hzle' hzgt'
  have hAz : A z = Finset.univ.sum (fun i => (e z) i) := by
    simp [A, sumLinearMapFun]
  intro hAz0
  apply hsum_ne
  simpa [hAz] using hAz0

/-- Linear map sending `(xᵢ, μᵢ)` to `(xᵢ, ∑ μᵢ)`. -/
noncomputable def sumMuLinearMap {n m : Nat} :
    (Fin m → (Fin n → Real) × Real) →ₗ[Real] (Fin m → (Fin n → Real)) × Real :=
  { toFun := fun x => (fun i => (x i).1, Finset.univ.sum (fun i => (x i).2))
    map_add' := by
      intro x y
      ext i <;> simp [Finset.sum_add_distrib]
    map_smul' := by
      intro r x
      ext i
      · simp
      · have h :=
          (Finset.mul_sum (s := Finset.univ) (f := fun i => (x i).2) (a := r))
        simpa using h.symm }

/-- Recession cone of a nonempty product set is the product of recession cones. -/
lemma recessionCone_pi_eq_pi_recessionCone {m : Nat} {E : Type*} [AddCommGroup E] [Module Real E]
    (C : Fin m → Set E) (hC : ∀ i, (C i).Nonempty) :
    Set.recessionCone (Set.pi Set.univ C) =
      Set.pi Set.univ (fun i => Set.recessionCone (C i)) := by
  classical
  choose x0 hx0 using hC
  ext y
  constructor
  · intro hy
    refine (Set.mem_pi).2 ?_
    intro i hi x hx t ht
    let x' : Fin m → E := fun j => if hji : j = i then x else x0 j
    have hx' : x' ∈ Set.pi Set.univ C := by
      refine (Set.mem_pi).2 ?_
      intro j hj
      by_cases hji : j = i
      · simpa [x', hji] using hx
      · simpa [x', hji] using hx0 j
    have hmem := hy hx' ht
    have hmem' : (x' i + t • y i) ∈ C i := by
      have := (Set.mem_pi).1 hmem i (by simp)
      simpa [x'] using this
    simpa [x'] using hmem'
  · intro hy x hx t ht
    refine (Set.mem_pi).2 ?_
    intro i hi
    have hx' : x i ∈ C i := (Set.mem_pi).1 hx i (by simp)
    have hy' : y i ∈ Set.recessionCone (C i) := (Set.mem_pi).1 hy i (by simp)
    exact hy' hx' ht

/-- Sum of real coefficients coerced to `EReal` is the coercion of the real sum. -/
lemma sum_coe_ereal {α : Type*} (s : Finset α) (f : α → Real) :
    s.sum (fun i => (f i : EReal)) = ((s.sum f : Real) : EReal) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [ha, hs, EReal.coe_add]

/-- A finite sum of `EReal` terms is not `⊥` if none of the terms is `⊥`. -/
lemma sum_ne_bot_of_ne_bot' {α : Type*} (s : Finset α) (β : α → EReal)
    (h : ∀ i ∈ s, β i ≠ (⊥ : EReal)) : s.sum β ≠ (⊥ : EReal) := by
  simpa using (sum_ne_bot_of_ne_bot (s := s) (f := β) h)

/-- A finite sum is `⊤` if one term is `⊤` and none are `⊥`. -/
lemma sum_eq_top_of_eq_top {α : Type*} (s : Finset α) (β : α → EReal)
    (i0 : α) (hi0 : i0 ∈ s) (htop : β i0 = (⊤ : EReal))
    (hbot : ∀ i ∈ s, β i ≠ (⊥ : EReal)) :
    s.sum β = (⊤ : EReal) := by
  classical
  have hsum :
      s.sum β = β i0 + (s.erase i0).sum β := by
    symm
    simpa using (Finset.add_sum_erase (s := s) (f := β) (a := i0) hi0)
  have hsum_ne_bot :
      (s.erase i0).sum β ≠ (⊥ : EReal) := by
    refine sum_ne_bot_of_ne_bot' (s := s.erase i0) (β := β) ?_
    intro i hi
    exact hbot i (Finset.mem_erase.mp hi).2
  have htop_sum : β i0 + (s.erase i0).sum β = (⊤ : EReal) := by
    simpa [htop] using
      (EReal.top_add_of_ne_bot (x := (s.erase i0).sum β) hsum_ne_bot)
  simpa [hsum] using htop_sum

/-- Split a real upper bound on an `EReal` sum into componentwise real bounds. -/
lemma split_real_sum_of_le {m : Nat} (hm : 0 < m) {β : Fin m → EReal} {α : Real}
    (hbot : ∀ i, β i ≠ (⊥ : EReal))
    (hβ : (Finset.univ.sum (fun i => β i)) ≤ (α : EReal)) :
    ∃ a : Fin m → Real,
      (∀ i, β i ≤ (a i : EReal)) ∧
      (Finset.univ.sum (fun i => a i) = α) := by
  classical
  have hnot_top : ∀ i, β i ≠ (⊤ : EReal) := by
    intro i htop
    have hsum_ne_bot :
        (Finset.univ.erase i).sum (fun j => β j) ≠ (⊥ : EReal) := by
      refine sum_ne_bot_of_ne_bot' (s := Finset.univ.erase i) (β := fun j => β j) ?_
      intro j hj
      exact hbot j
    have hsum_top : (Finset.univ.sum (fun j => β j)) = (⊤ : EReal) := by
      calc
        Finset.univ.sum (fun j => β j) =
            β i + (Finset.univ.erase i).sum (fun j => β j) := by
          symm
          simpa using
            (Finset.add_sum_erase (s := Finset.univ) (f := fun j => β j) (a := i) (by simp))
        _ = ⊤ := by
          simpa [htop] using
            (EReal.top_add_of_ne_bot
              (x := (Finset.univ.erase i).sum (fun j => β j)) hsum_ne_bot)
    have hβ' := hβ
    rw [hsum_top] at hβ'
    exact (not_top_le_coe α) hβ'
  let b : Fin m → Real := fun i => (β i).toReal
  have hβ_eq : ∀ i, β i = (b i : EReal) := by
    intro i
    simpa [b] using (EReal.coe_toReal (hnot_top i) (hbot i)).symm
  have hsum_eq :
      (Finset.univ.sum (fun i => β i)) = ((Finset.univ.sum (fun i => b i)) : EReal) := by
    calc
      Finset.univ.sum (fun i => β i) =
          Finset.univ.sum (fun i => (b i : EReal)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [hβ_eq i]
      _ = ((Finset.univ.sum (fun i => b i)) : EReal) := by
        simp [sum_coe_ereal]
  have hsum_le : (Finset.univ.sum (fun i => b i)) ≤ α := by
    have hsum_le'' :
        (Finset.univ.sum (fun i => (b i : EReal))) ≤ (α : EReal) := by
      have hβ' := hβ
      rw [hsum_eq] at hβ'
      exact hβ'
    have hsum_le''' := hsum_le''
    rw [sum_coe_ereal (s := Finset.univ) (f := fun i => b i)] at hsum_le'''
    exact (EReal.coe_le_coe_iff).1 hsum_le'''
  let i0 : Fin m := ⟨0, hm⟩
  let a : Fin m → Real :=
    fun i => if h : i = i0 then b i + (α - Finset.univ.sum (fun j => b j)) else b i
  have hsum_a : Finset.univ.sum (fun i => a i) = α := by
    have hsum_a' :
        Finset.univ.sum (fun i => a i) =
          a i0 + (Finset.univ.erase i0).sum (fun i => a i) := by
      symm
      exact
        (Finset.add_sum_erase (s := Finset.univ) (f := fun i => a i) (a := i0) (by simp))
    have hsum_erase :
        (Finset.univ.erase i0).sum (fun i => a i) =
          (Finset.univ.erase i0).sum (fun i => b i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
      simp [a, hne]
    have hsum_b :
        Finset.univ.sum (fun i => b i) =
          b i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
      symm
      exact
        (Finset.add_sum_erase (s := Finset.univ) (f := fun i => b i) (a := i0) (by simp))
    calc
      Finset.univ.sum (fun i => a i) =
          a i0 + (Finset.univ.erase i0).sum (fun i => a i) := hsum_a'
      _ = a i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
        simp [hsum_erase]
      _ = (b i0 + (α - Finset.univ.sum (fun j => b j))) +
            (Finset.univ.erase i0).sum (fun i => b i) := by
        simp [a]
      _ = (b i0 + (Finset.univ.erase i0).sum (fun i => b i)) +
            (α - Finset.univ.sum (fun j => b j)) := by
        ring
      _ = (Finset.univ.sum (fun i => b i)) +
            (α - Finset.univ.sum (fun j => b j)) := by
        rw [hsum_b]
      _ = α := by
        linarith
  refine ⟨a, ?_, hsum_a⟩
  intro i
  by_cases h : i = i0
  · subst h
    have hle : b i0 ≤ b i0 + (α - Finset.univ.sum (fun j => b j)) := by
      linarith
    have hle' :
        ((b i0) : EReal) ≤ ((b i0 + (α - Finset.univ.sum (fun j => b j))) : Real) := by
      exact (EReal.coe_le_coe_iff).2 hle
    have hβi0 : β i0 = (b i0 : EReal) := hβ_eq i0
    simpa [a, hβi0] using hle'
  · have hle : β i ≤ (b i : EReal) := EReal.le_coe_toReal (hnot_top i)
    simpa [a, h] using hle

/-- A strict inequality on a finite `EReal` sum is equivalent to the strict real inequality. -/
lemma g0_plus_gt_toReal_sum {m : Nat} {β : Fin m → EReal} {α : Real}
    (hnot_top : ∀ i, β i ≠ (⊤ : EReal))
    (hnot_bot : ∀ i, β i ≠ (⊥ : EReal)) :
    (Finset.univ.sum (fun i => β i) > (α : EReal)) ↔
      (Finset.univ.sum (fun i => (β i).toReal) > α) := by
  classical
  let b : Fin m → Real := fun i => (β i).toReal
  have hβ_eq : ∀ i, β i = (b i : EReal) := by
    intro i
    simpa [b] using (EReal.coe_toReal (hnot_top i) (hnot_bot i)).symm
  have hsum_eq :
      (Finset.univ.sum (fun i => β i)) = ((Finset.univ.sum (fun i => b i)) : EReal) := by
    calc
      Finset.univ.sum (fun i => β i) =
          Finset.univ.sum (fun i => (b i : EReal)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [hβ_eq i]
      _ = ((Finset.univ.sum (fun i => b i)) : EReal) := by
        simp [sum_coe_ereal]
  constructor
  · intro hgt
    have hgt' : (α : EReal) < (Finset.univ.sum (fun i => β i)) := by
      simpa [gt_iff_lt] using hgt
    have hgt'' :
        (α : EReal) < ((Finset.univ.sum (fun i => b i)) : EReal) := by
      have hgt'' := hgt'
      rw [hsum_eq] at hgt''
      exact hgt''
    have hgt_real : α < Finset.univ.sum (fun i => b i) := by
      have hgt''' := hgt''
      rw [sum_coe_ereal (s := Finset.univ) (f := fun i => b i)] at hgt'''
      exact (EReal.coe_lt_coe_iff).1 hgt'''
    simpa [gt_iff_lt] using hgt_real
  · intro hgt
    have hgt_real : α < Finset.univ.sum (fun i => b i) := by
      simpa [gt_iff_lt] using hgt
    have hgt' :
        (α : EReal) < Finset.univ.sum (fun i => (b i : EReal)) := by
      simpa [sum_coe_ereal] using (EReal.coe_lt_coe_iff).2 hgt_real
    have hgt'' : (α : EReal) < (Finset.univ.sum (fun i => β i)) := by
      have hgt'' := hgt'
      rw [hsum_eq.symm] at hgt''
      exact hgt''
    simpa [gt_iff_lt] using hgt''

/-- Split a strict inequality for a real sum by lowering one component. -/
lemma split_real_sum_of_gt {m : Nat} (hm : 0 < m) {r : Fin m → Real} {α : Real} :
    (Finset.univ.sum (fun i => r i) > α) →
      ∃ i0 : Fin m,
        ∃ a : Fin m → Real,
          a i0 < r i0 ∧
          (∀ i ≠ i0, a i = r i) ∧
          (Finset.univ.sum (fun i => a i) = α) := by
  classical
  intro hgt
  let i0 : Fin m := ⟨0, hm⟩
  let a : Fin m → Real :=
    fun i => if h : i = i0 then α - (Finset.univ.erase i0).sum (fun j => r j) else r i
  refine ⟨i0, a, ?_, ?_, ?_⟩
  · have hsum :
        Finset.univ.sum (fun i => r i) =
          r i0 + (Finset.univ.erase i0).sum (fun j => r j) := by
      symm
      exact
        (Finset.add_sum_erase (s := Finset.univ) (f := fun i => r i) (a := i0) (by simp))
    have hlt : α - (Finset.univ.erase i0).sum (fun j => r j) < r i0 := by
      have : α < r i0 + (Finset.univ.erase i0).sum (fun j => r j) := by
        linarith [hsum, hgt]
      linarith
    simpa [a] using hlt
  · intro i hi
    have hne : i ≠ i0 := by
      exact hi
    simp [a, hne]
  · have hsum_a :
        Finset.univ.sum (fun i => a i) =
          a i0 + (Finset.univ.erase i0).sum (fun i => a i) := by
      symm
      exact
        (Finset.add_sum_erase (s := Finset.univ) (f := fun i => a i) (a := i0) (by simp))
    have hsum_erase :
        (Finset.univ.erase i0).sum (fun i => a i) =
          (Finset.univ.erase i0).sum (fun i => r i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
      simp [a, hne]
    calc
      Finset.univ.sum (fun i => a i) =
          a i0 + (Finset.univ.erase i0).sum (fun i => a i) := hsum_a
      _ = a i0 + (Finset.univ.erase i0).sum (fun i => r i) := by
        simp [hsum_erase]
      _ = (α - (Finset.univ.erase i0).sum (fun j => r j)) +
            (Finset.univ.erase i0).sum (fun i => r i) := by
        simp [a]
      _ = α := by
        linarith

/-- Split a strict sum inequality into strictly lower components with the same total. -/
lemma split_real_sum_of_gt_strict_all {m : Nat} (hm : 0 < m) {r : Fin m → Real} {α : Real}
    (hgt : Finset.univ.sum (fun i => r i) > α) :
    ∃ a : Fin m → Real, (∀ i, a i < r i) ∧ Finset.univ.sum (fun i => a i) = α := by
  classical
  set gap : Real := Finset.univ.sum (fun i => r i) - α
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hmpos : (0 : Real) < (m : Real) := by
    exact_mod_cast hm
  set ε : Real := gap / ((m : Real) + 1)
  have hεpos : 0 < ε := by
    have hdenom : 0 < (m : Real) + 1 := by linarith
    exact div_pos hgap hdenom
  let r' : Fin m → Real := fun i => r i - ε
  have hsum_r' :
      Finset.univ.sum (fun i => r' i) =
        Finset.univ.sum (fun i => r i) - (m : Real) * ε := by
    simp [r', sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_const]
  have hmul_lt : (m : Real) * ε < gap := by
    have hdenom : 0 < (m : Real) + 1 := by linarith
    have hdiv_lt_one : (m : Real) / ((m : Real) + 1) < (1 : Real) := by
      have hm_lt : (m : Real) < (m : Real) + 1 := by linarith
      exact (div_lt_one hdenom).2 hm_lt
    have hmul :
        (m : Real) * ε = gap * ((m : Real) / ((m : Real) + 1)) := by
      dsimp [ε]
      calc
        (m : Real) * (gap / ((m : Real) + 1)) =
            (m : Real) * gap / ((m : Real) + 1) := by
              simp [mul_div_assoc]
        _ = gap * (m : Real) / ((m : Real) + 1) := by
              simp [mul_comm]
        _ = gap * ((m : Real) / ((m : Real) + 1)) := by
              simp [mul_div_assoc]
    have hmul_lt' : gap * ((m : Real) / ((m : Real) + 1)) < gap * 1 := by
      exact (mul_lt_mul_of_pos_left hdiv_lt_one hgap)
    simpa [hmul] using hmul_lt'
  have hsum_r'_gt : Finset.univ.sum (fun i => r' i) > α := by
    dsimp [gap] at hmul_lt
    linarith [hsum_r', hmul_lt]
  rcases split_real_sum_of_gt (m := m) (hm := hm) (r := r') (α := α) hsum_r'_gt with
    ⟨i0, a, ha_lt, ha_eq, ha_sum⟩
  refine ⟨a, ?_, ha_sum⟩
  intro i
  by_cases h : i = i0
  · have hlt : a i < r' i := by
      simpa [h] using ha_lt
    have hlt' : r' i < r i := by
      dsimp [r']
      linarith [hεpos]
    exact lt_of_lt_of_le hlt (le_of_lt hlt')
  · have hEq : a i = r' i := ha_eq i h
    have hlt : r' i < r i := by
      dsimp [r']
      linarith [hεpos]
    simpa [hEq] using hlt

/-- A witness for failing recession membership in an epigraph. -/
lemma not_mem_recessionCone_epigraph_witness {n : Nat}
    {f : (Fin n → Real) → EReal} {v : Fin n → Real} {a : Real}
    (hnot :
      (v, a) ∉ Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f)) :
    ∃ x μ t,
      0 ≤ t ∧
        f (x + t • v) > ((μ + t * a : Real) : EReal) ∧
          f x ≤ (μ : EReal) := by
  classical
  have hnot' :
      ¬ (∀ x ∈ epigraph (Set.univ : Set (Fin n → Real)) f, ∀ t : Real, 0 ≤ t →
        x + t • (v, a) ∈ epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [Set.recessionCone] using hnot
  classical
  push_neg at hnot'
  rcases hnot' with ⟨x, hx, t, ht, hnotmem⟩
  rcases x with ⟨x, μ⟩
  have hxle : f x ≤ (μ : EReal) :=
    (mem_epigraph_univ_iff (f := f)).1 hx
  have hnotmem' :
      (x + t • v, μ + t * a) ∉ epigraph (Set.univ : Set (Fin n → Real)) f := by
    simpa using hnotmem
  have hnotle : ¬ f (x + t • v) ≤ ((μ + t * a : Real) : EReal) := by
    intro hle
    exact hnotmem' ((mem_epigraph_univ_iff (f := f)).2 hle)
  refine ⟨x, μ, t, ht, ?_, hxle⟩
  exact lt_of_not_ge hnotle

/-- Epigraph nonemptiness from recession-epigraph equality and non-bottomness. -/
lemma nonempty_epigraph_of_hrec {n m : Nat}
    {f f0_plus : Fin m → (Fin n → Real) → EReal}
    (hnotbot0 : ∀ i : Fin m, ∀ x, f0_plus i x ≠ (⊥ : EReal))
    (hrec_i :
      ∀ i : Fin m,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i)) :
    ∀ i : Fin m, Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
  intro i
  by_contra hne
  have hempty :
      epigraph (Set.univ : Set (Fin n → Real)) (f i) = ∅ :=
    (Set.not_nonempty_iff_eq_empty).1 hne
  have hrec_univ :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
        (Set.univ : Set ((Fin n → Real) × Real)) := by
    ext p
    simp [Set.recessionCone, hempty]
  have hEpi_univ :
      epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i) =
        (Set.univ : Set ((Fin n → Real) × Real)) := by
    simpa [hrec_univ] using (hrec_i i).symm
  have hbot : f0_plus i (0 : Fin n → Real) = (⊥ : EReal) := by
    have hlt : ∀ y : Real, f0_plus i (0 : Fin n → Real) < (y : EReal) := by
      intro y
      have hle :
          f0_plus i (0 : Fin n → Real) ≤ ((y - 1) : EReal) := by
        have hmem :
            ((0 : Fin n → Real), (y - 1)) ∈
              epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i) := by
          simp [hEpi_univ]
        exact (mem_epigraph_univ_iff (f := f0_plus i)).1 hmem
      have hlt' : ((y - 1 : Real) : EReal) < (y : EReal) := by
        exact (EReal.coe_lt_coe_iff).2 (by linarith)
      exact lt_of_le_of_lt hle hlt'
    exact (EReal.eq_bot_iff_forall_lt _).2 hlt
  exact (hnotbot0 i (0 : Fin n → Real)) hbot

/-- A fixed-step translation in a convex set yields a recession direction. -/
lemma mem_recessionCone_of_add_mem_fixed_t {E : Type*} [AddCommGroup E] [Module Real E]
    {C : Set E} (hconv : Convex Real C) {v : E} {t : Real} (ht : 0 < t)
    (hadd : ∀ x ∈ C, x + t • v ∈ C) : v ∈ Set.recessionCone C := by
  have hmem_t : t • v ∈ Set.recessionCone C := by
    intro x hx s hs
    by_cases hzero : s = 0
    · simpa [hzero] using hx
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
      have hnat :
          ∀ {x} (hx : x ∈ C) (m : ℕ), x + (m : ℝ) • (t • v) ∈ C := by
        intro x hx m
        induction m generalizing x with
        | zero =>
            simpa using hx
        | succ m ih =>
            have hx' : x + (m : ℝ) • (t • v) ∈ C := ih hx
            have hy :
                x + (m : ℝ) • (t • v) + t • v ∈ C :=
              hadd (x := x + (m : ℝ) • (t • v)) hx'
            simpa [Nat.cast_add, add_smul, one_smul, add_assoc] using hy
      obtain ⟨m, hm⟩ := exists_nat_ge s
      have hxmy : x + (m : ℝ) • (t • v) ∈ C := hnat hx m
      have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hspos hm
      have hdivnonneg : 0 ≤ s / (m : ℝ) := div_nonneg hs (le_of_lt hmpos)
      have hdivle : s / (m : ℝ) ≤ (1 : ℝ) :=
        (div_le_one (a := s) (b := (m : ℝ)) hmpos).2 hm
      have hxmem :
          x + (s / (m : ℝ)) • ((m : ℝ) • (t • v)) ∈ C :=
        hconv.add_smul_mem hx hxmy ⟨hdivnonneg, hdivle⟩
      have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      have hmul : (s / (m : ℝ)) * (m : ℝ) = s := by
        calc
          (s / (m : ℝ)) * (m : ℝ) = s * (m : ℝ) / (m : ℝ) := by
            simp [div_mul_eq_mul_div]
          _ = s := by
            simpa [mul_comm] using (mul_div_cancel_left₀ (b := s) (a := (m : ℝ)) hm0)
      have hmul' : (s / (m : ℝ)) * (m * t) = s * t := by
        calc
          (s / (m : ℝ)) * (m * t) = ((s / (m : ℝ)) * (m : ℝ)) * t := by
            ring
          _ = s * t := by simp [hmul]
      simpa [smul_smul, hmul'] using hxmem
  intro x hx s hs
  have hs' : 0 ≤ s / t := by
    exact div_nonneg hs (le_of_lt ht)
  have hmem := hmem_t (x := x) hx (t := s / t) hs'
  have hmul : (s / t) * t = s := by
    field_simp [ne_of_gt ht]
  simpa [smul_smul, hmul, mul_comm, mul_left_comm, mul_assoc] using hmem

/-- Approximate a recession slope at a fixed time with slack. -/
lemma recCone_tight_approx_at_t {n : Nat}
    {f f0_plus : (Fin n → Real) → EReal}
    (hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) =
        epigraph (Set.univ : Set (Fin n → Real)) f0_plus)
    (hconv : Convex Real (epigraph (Set.univ : Set (Fin n → Real)) f))
    {v : Fin n → Real} {a : Real} (ha : ((a : Real) : EReal) < f0_plus v)
    {t : Real} (ht : 0 < t) {ε : Real} (hε : 0 < ε) :
    ∃ x : Fin n → Real, ∃ μ : Real, f x ≤ (μ : EReal) ∧
      ((μ + t * a - ε : Real) : EReal) ≤ f (x + t • v) := by
  classical
  set a' : Real := a - ε / t
  have hlt_a' : a' < a := by
    have hεt : 0 < ε / t := by
      exact div_pos hε ht
    dsimp [a']
    linarith
  have hlt_a'ereal : ((a' : Real) : EReal) < (a : EReal) :=
    (EReal.coe_lt_coe_iff).2 hlt_a'
  have ha' : ((a' : Real) : EReal) < f0_plus v := lt_trans hlt_a'ereal ha
  have hnot_mem :
      (v, a') ∉ Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    intro hmem
    have hmem' :
        (v, a') ∈ epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
      simpa [hrec] using hmem
    have hle :
        f0_plus v ≤ (a' : EReal) :=
      (mem_epigraph_univ_iff (f := f0_plus)).1 hmem'
    exact (not_lt_of_ge hle) ha'
  have hnot_all :
      ¬ ∀ x ∈ epigraph (Set.univ : Set (Fin n → Real)) f,
        x + t • (v, a') ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
    intro hforall
    have hmem :
        (v, a') ∈ Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) := by
      exact
        mem_recessionCone_of_add_mem_fixed_t
          (C := epigraph (Set.univ : Set (Fin n → Real)) f) hconv (v := (v, a')) (t := t) ht
          hforall
    exact hnot_mem hmem
  classical
  push_neg at hnot_all
  rcases hnot_all with ⟨x, hx, hnotmem⟩
  rcases x with ⟨x, μ⟩
  have hxle : f x ≤ (μ : EReal) :=
    (mem_epigraph_univ_iff (f := f)).1 hx
  have hnotmem' :
      (x + t • v, μ + t * a') ∉ epigraph (Set.univ : Set (Fin n → Real)) f := by
    exact hnotmem
  have hnotle : ¬ f (x + t • v) ≤ ((μ + t * a' : Real) : EReal) := by
    intro hle
    exact hnotmem' ((mem_epigraph_univ_iff (f := f)).2 hle)
  have hlt : f (x + t • v) > ((μ + t * a' : Real) : EReal) :=
    lt_of_not_ge hnotle
  have hcalc' : t * a' = t * a - ε := by
    dsimp [a']
    calc
      t * (a - ε / t) = t * a - t * (ε / t) := by ring
      _ = t * a - ε := by
        have hmul : t * (ε / t) = ε := by
          field_simp [ne_of_gt ht]
        simp [hmul]
  have hcalc : μ + t * a - ε = μ + t * a' := by
    linarith [hcalc']
  refine ⟨x, μ, hxle, ?_⟩
  have hle : ((μ + t * a' : Real) : EReal) ≤ f (x + t • v) := le_of_lt hlt
  simpa [hcalc] using hle

/-- A strict gap at one component plus slack bounds on the others yields a strict sum. -/
lemma strict_sum_from_one_component_with_slack {m : Nat} {β b ε : Fin m → Real} {i0 : Fin m}
    (hgt : β i0 > b i0)
    (hslack : ∀ i ≠ i0, β i ≥ b i - ε i)
    (hε : (Finset.univ.erase i0).sum (fun i => ε i) < β i0 - b i0) :
    Finset.univ.sum (fun i => β i) > Finset.univ.sum (fun i => b i) := by
  classical
  have hsum_beta :
      Finset.univ.sum (fun i => β i) =
        β i0 + (Finset.univ.erase i0).sum (fun i => β i) := by
    symm
    exact
      (Finset.add_sum_erase (s := Finset.univ) (f := fun i => β i) (a := i0) (by simp))
  have hsum_b :
      Finset.univ.sum (fun i => b i) =
        b i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
    symm
    exact
      (Finset.add_sum_erase (s := Finset.univ) (f := fun i => b i) (a := i0) (by simp))
  have hsum_rest :
      (Finset.univ.erase i0).sum (fun i => b i - ε i) ≤
        (Finset.univ.erase i0).sum (fun i => β i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    exact hslack i hne
  have hsum_rest' :
      (Finset.univ.erase i0).sum (fun i => β i) ≥
        (Finset.univ.erase i0).sum (fun i => b i) -
          (Finset.univ.erase i0).sum (fun i => ε i) := by
    have hsum_sub :
        (Finset.univ.erase i0).sum (fun i => b i - ε i) =
          (Finset.univ.erase i0).sum (fun i => b i) -
            (Finset.univ.erase i0).sum (fun i => ε i) := by
      simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have hsum_le :
        (Finset.univ.erase i0).sum (fun i => b i) -
            (Finset.univ.erase i0).sum (fun i => ε i) ≤
          (Finset.univ.erase i0).sum (fun i => β i) := by
      simpa [hsum_sub] using hsum_rest
    exact hsum_le
  have hsum_beta_ge :
      β i0 + (Finset.univ.erase i0).sum (fun i => b i) -
          (Finset.univ.erase i0).sum (fun i => ε i) ≤
        Finset.univ.sum (fun i => β i) := by
    have hsum_rest'' := add_le_add_left hsum_rest' (β i0)
    have hsum_rest''' :
        β i0 + (Finset.univ.erase i0).sum (fun i => b i) -
            (Finset.univ.erase i0).sum (fun i => ε i) ≤
          β i0 + (Finset.univ.erase i0).sum (fun i => β i) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum_rest''
    simpa [← hsum_beta] using hsum_rest'''
  have hgap : β i0 - b i0 > (Finset.univ.erase i0).sum (fun i => ε i) := by
    have hgt' : 0 < β i0 - b i0 := by
      linarith [hgt]
    linarith [hε, hgt']
  have hsum_gt :
      Finset.univ.sum (fun i => β i) >
        b i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
    have :
        β i0 + (Finset.univ.erase i0).sum (fun i => b i) -
            (Finset.univ.erase i0).sum (fun i => ε i) >
          b i0 + (Finset.univ.erase i0).sum (fun i => b i) := by
      linarith
    have hlt :
        b i0 + (Finset.univ.erase i0).sum (fun i => b i) <
          β i0 + (Finset.univ.erase i0).sum (fun i => b i) -
            (Finset.univ.erase i0).sum (fun i => ε i) := by
      simpa [gt_iff_lt] using this
    exact lt_of_lt_of_le hlt hsum_beta_ge
  calc
    Finset.univ.sum (fun i => β i) >
        b i0 + (Finset.univ.erase i0).sum (fun i => b i) := hsum_gt
    _ = Finset.univ.sum (fun i => b i) := by
      exact hsum_b.symm

/-- A strict gap with slack on `EReal` components yields a strict sum inequality. -/
lemma ereal_strict_sum_from_one_component_with_slack {m : Nat} {β : Fin m → EReal}
    {b ε : Fin m → Real} {i0 : Fin m}
    (hnot_top : ∀ i, β i ≠ (⊤ : EReal)) (hnot_bot : ∀ i, β i ≠ (⊥ : EReal))
    (hgt : β i0 > (b i0 : EReal))
    (hslack : ∀ i ≠ i0, β i ≥ ((b i - ε i : Real) : EReal))
    (hε : (Finset.univ.erase i0).sum (fun i => ε i) < (β i0).toReal - b i0) :
    Finset.univ.sum (fun i => β i) > (Finset.univ.sum (fun i => b i) : EReal) := by
  classical
  let rb : Fin m → Real := fun i => (β i).toReal
  have hβ_eq : ∀ i, β i = (rb i : EReal) := by
    intro i
    simpa [rb] using (EReal.coe_toReal (hnot_top i) (hnot_bot i)).symm
  have hgt_real : rb i0 > b i0 := by
    have hgt' : (rb i0 : EReal) > (b i0 : EReal) := by
      simpa [hβ_eq i0] using hgt
    exact (EReal.coe_lt_coe_iff).1 hgt'
  have hslack_real : ∀ i ≠ i0, rb i ≥ b i - ε i := by
    intro i hi
    have hle' : (rb i : EReal) ≥ ((b i - ε i : Real) : EReal) := by
      simpa [hβ_eq i] using hslack i hi
    exact (EReal.coe_le_coe_iff).1 hle'
  have hsum_real :
      Finset.univ.sum (fun i => rb i) > Finset.univ.sum (fun i => b i) :=
    strict_sum_from_one_component_with_slack (β := rb) (b := b) (ε := ε) (i0 := i0)
      hgt_real hslack_real hε
  have hsum_ereal :
      Finset.univ.sum (fun i => (rb i : EReal)) >
        Finset.univ.sum (fun i => (b i : EReal)) := by
    have hsum_real' :
        Finset.univ.sum (fun i => b i) < Finset.univ.sum (fun i => rb i) := by
      simpa [gt_iff_lt] using hsum_real
    have hsum_ereal' :
        Finset.univ.sum (fun i => (b i : EReal)) <
          Finset.univ.sum (fun i => (rb i : EReal)) := by
      simpa [sum_coe_ereal] using (EReal.coe_lt_coe_iff).2 hsum_real'
    simpa [gt_iff_lt] using hsum_ereal'
  have hsum_eq :
      Finset.univ.sum (fun i => β i) =
        Finset.univ.sum (fun i => (rb i : EReal)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [hβ_eq i]
  have hsum_b :
      (Finset.univ.sum (fun i => b i) : EReal) =
        Finset.univ.sum (fun i => (b i : EReal)) := by
    simp [sum_coe_ereal]
  simpa [hsum_eq, hsum_b] using hsum_ereal

/-- Finite-case contradiction in the `⊤` branch of `recessionCone_sum_epigraph_prod`. -/
lemma recessionCone_sum_epigraph_prod_top_contra {n m : Nat}
    {f f0_plus : Fin m → (Fin n → Real) → EReal}
    {g : (Fin m → (Fin n → Real)) → EReal}
    (hg : g = fun x => Finset.univ.sum (fun i => f i (x i)))
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal))
    (_hnotbot0 : ∀ i : Fin m, ∀ x, f0_plus i x ≠ (⊥ : EReal))
    (_hrec_i :
      ∀ i : Fin m,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i))
    {p : (Fin m → (Fin n → Real)) × Real} {i0 : Fin m}
    (_htop : f0_plus i0 (p.1 i0) = (⊤ : EReal))
    {a : Fin m → Real}
    {x0 : Fin n → Real} {μ0 t : Real}
    (hgt0 : f i0 (x0 + t • p.1 i0) > ((μ0 + t * a i0 : Real) : EReal))
    (_hx0 : f i0 x0 ≤ (μ0 : EReal))
    (ha_sum : Finset.univ.sum (fun i => a i) = p.2)
    {x : Fin m → (Fin n → Real)} {μ : Fin m → Real}
    (hxi0 : x i0 = x0) (hμi0 : μ i0 = μ0)
    (_hxle : ∀ i, f i (x i) ≤ (μ i : EReal))
    {ε : Fin m → Real}
    (hslack :
      ∀ i ≠ i0,
        ((μ i + t * a i - ε i : Real) : EReal) ≤ f i (x i + t • p.1 i))
    (hε :
      (Finset.univ.erase i0).sum (fun i => ε i) <
        (f i0 (x0 + t • p.1 i0)).toReal - (μ0 + t * a i0))
    (hmem''' :
      g (x + t • p.1) ≤ (Finset.univ.sum (fun i => μ i) + t * p.2 : EReal))
    (htopg : ¬ ∃ i, f i (x i + t • p.1 i) = (⊤ : EReal)) :
    False := by
  classical
  let β : Fin m → EReal := fun i => f i (x i + t • p.1 i)
  let b : Fin m → Real := fun i => μ i + t * a i
  have hnot_top : ∀ i, β i ≠ (⊤ : EReal) := by
    intro i htopi
    exact htopg ⟨i, by simpa [β] using htopi⟩
  have hnot_bot : ∀ i, β i ≠ (⊥ : EReal) := by
    intro i
    exact hnotbot i (x i + t • p.1 i)
  have hgt : β i0 > (b i0 : EReal) := by
    simpa [β, b, hxi0, hμi0] using hgt0
  have hslack' : ∀ i ≠ i0, β i ≥ ((b i - ε i : Real) : EReal) := by
    intro i hi
    have h := hslack i hi
    simpa [β, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hε' :
      (Finset.univ.erase i0).sum (fun i => ε i) <
        (β i0).toReal - b i0 := by
    simpa [β, b, hxi0, hμi0] using hε
  have hsum_gt :
      Finset.univ.sum (fun i => β i) > (Finset.univ.sum (fun i => b i) : EReal) :=
    ereal_strict_sum_from_one_component_with_slack (β := β) (b := b) (ε := ε) (i0 := i0)
      hnot_top hnot_bot hgt hslack' hε'
  have hsum_le :
      Finset.univ.sum (fun i => β i) ≤ (Finset.univ.sum (fun i => b i) : EReal) := by
    have hmem'''_sum := hmem'''
    simp [hg] at hmem'''_sum
    have hsum_b :
        Finset.univ.sum (fun i => b i) =
          Finset.univ.sum (fun i => μ i) + t * p.2 := by
      calc
        Finset.univ.sum (fun i => b i) =
            Finset.univ.sum (fun i => μ i + t * a i) := by rfl
        _ = Finset.univ.sum (fun i => μ i) +
              Finset.univ.sum (fun i => t * a i) := by
          simp [Finset.sum_add_distrib]
        _ = Finset.univ.sum (fun i => μ i) + t * Finset.univ.sum (fun i => a i) := by
          simp [Finset.mul_sum]
        _ = Finset.univ.sum (fun i => μ i) + t * p.2 := by
          simp [ha_sum]
    have hsum_b_ereal :
        Finset.univ.sum (fun i => (b i : EReal)) =
          (Finset.univ.sum (fun i => μ i) : EReal) + (t : EReal) * (p.2 : EReal) := by
      have hsum_b' :
          Finset.univ.sum (fun i => (b i : EReal)) =
            ((Finset.univ.sum (fun i => μ i) + t * p.2) : EReal) := by
        have hsum_b'' := congrArg (fun x : Real => (x : EReal)) hsum_b
        simpa [sum_coe_ereal] using hsum_b''
      simpa [EReal.coe_add, EReal.coe_mul, ← sum_coe_ereal] using hsum_b'
    rw [← sum_coe_ereal (s := Finset.univ) (f := fun i => μ i)] at hmem'''_sum
    rw [← hsum_b_ereal] at hmem'''_sum
    simpa [β] using hmem'''_sum
  exact (not_lt_of_ge hsum_le) hsum_gt

end Section09
end Chap02
