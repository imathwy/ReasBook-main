/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part4

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- Remove zero weights from a convex combination while preserving the point and objective. -/
lemma drop_zero_weights_preserves_convexCombination_obj {n k : Nat}
    {p : Fin k → Fin n → Real} {w : Fin k → Real} {x : Fin n → Real} {a : Fin k → Real}
    (hw : IsConvexWeights k w) (hx : x = convexCombination n k p w)
    (hzero : ∃ i, w i = 0) :
    ∃ (k' : Nat) (e : Fin k' ↪ Fin k) (w' : Fin k' → Real),
      IsConvexWeights k' w' ∧
        (∀ j, w' j ≠ 0) ∧
        x = convexCombination n k' (fun j => p (e j)) w' ∧
        (∑ j, w' j * a (e j) = ∑ i, w i * a i) ∧
        k' < k := by
  classical
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  let t : Finset (Fin k) := Finset.univ.filter (fun i => w i ≠ 0)
  let k' : Nat := t.card
  let e' : t ≃ Fin k' := t.equivFin
  let e : Fin k' ↪ Fin k :=
    { toFun := fun j => (e'.symm j).1
      inj' := by
        intro j1 j2 h
        apply e'.symm.injective
        apply Subtype.ext
        simpa using h }
  let w' : Fin k' → Real := fun j => w (e j)
  have hwnz' : ∀ j, w' j ≠ 0 := by
    intro j
    have hmem : (e'.symm j).1 ∈ t := (e'.symm j).2
    have hmem' : w (e'.symm j).1 ≠ 0 := (Finset.mem_filter.mp hmem).2
    simpa [w', e] using hmem'
  have hw'_nonneg : ∀ j, 0 ≤ w' j := by
    intro j
    simpa [w', e] using hw_nonneg (e j)
  have hsum_t :
      t.sum (fun i => w i) = ∑ i, w i := by
    have hsum_filter :=
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
        (p := fun i => w i ≠ 0) (f := fun i => w i))
    have hsum_if :
        ∑ i, (if w i ≠ 0 then w i else 0) = ∑ i, w i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : w i = 0 <;> simp [h]
    calc
      t.sum (fun i => w i) =
          ∑ i, (if w i ≠ 0 then w i else 0) := by
        simpa [t] using hsum_filter
      _ = ∑ i, w i := hsum_if
  have hsum_subtype_w :
      t.sum (fun i => w i) = ∑ i : t, w i.1 := by
    refine
      (Finset.sum_subtype (s := t) (p := fun i => i ∈ t) (f := fun i => w i) ?_)
    intro i
    simp
  have hsum_equiv_w :
      ∑ j, w' j = ∑ i : t, w i.1 := by
    simpa [w', e] using (Equiv.sum_comp e'.symm (fun i : t => w i.1))
  have hsum_w' : ∑ j, w' j = 1 := by
    calc
      ∑ j, w' j = ∑ i : t, w i.1 := hsum_equiv_w
      _ = t.sum (fun i => w i) := by symm; exact hsum_subtype_w
      _ = ∑ i, w i := hsum_t
      _ = 1 := hw_sum
  have hw' : IsConvexWeights k' w' := ⟨hw'_nonneg, hsum_w'⟩
  have hsum_t_p :
      t.sum (fun i => w i • p i) = ∑ i, w i • p i := by
    have hsum_filter :=
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
        (p := fun i => w i ≠ 0) (f := fun i => w i • p i))
    have hsum_if :
        ∑ i, (if w i ≠ 0 then w i • p i else 0) = ∑ i, w i • p i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : w i = 0 <;> simp [h, zero_smul]
    calc
      t.sum (fun i => w i • p i) =
          ∑ i, (if w i ≠ 0 then w i • p i else 0) := by
        simpa [t] using hsum_filter
      _ = ∑ i, w i • p i := hsum_if
  have hsum_subtype_p :
      t.sum (fun i => w i • p i) = ∑ i : t, w i.1 • p i.1 := by
    refine
      (Finset.sum_subtype (s := t) (p := fun i => i ∈ t) (f := fun i => w i • p i) ?_)
    intro i
    simp
  have hsum_equiv_p :
      ∑ j, w' j • p (e j) = ∑ i : t, w i.1 • p i.1 := by
    simpa [w', e] using (Equiv.sum_comp e'.symm (fun i : t => w i.1 • p i.1))
  have hx_sum : x = ∑ i, w i • p i := by
    simpa [convexCombination] using hx
  have hsum_p :
      ∑ j, w' j • p (e j) = ∑ i, w i • p i := by
    calc
      ∑ j, w' j • p (e j) = ∑ i : t, w i.1 • p i.1 := hsum_equiv_p
      _ = t.sum (fun i => w i • p i) := by symm; exact hsum_subtype_p
      _ = ∑ i, w i • p i := hsum_t_p
  have hx_comb : x = convexCombination n k' (fun j => p (e j)) w' := by
    calc
      x = ∑ i, w i • p i := hx_sum
      _ = ∑ j, w' j • p (e j) := by symm; exact hsum_p
      _ = convexCombination n k' (fun j => p (e j)) w' := by
            simp [convexCombination]
  have hsum_t_a :
      t.sum (fun i => w i * a i) = ∑ i, w i * a i := by
    have hsum_filter :=
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
        (p := fun i => w i ≠ 0) (f := fun i => w i * a i))
    have hsum_if :
        ∑ i, (if w i ≠ 0 then w i * a i else 0) = ∑ i, w i * a i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : w i = 0 <;> simp [h]
    calc
      t.sum (fun i => w i * a i) =
          ∑ i, (if w i ≠ 0 then w i * a i else 0) := by
        simpa [t] using hsum_filter
      _ = ∑ i, w i * a i := hsum_if
  have hsum_subtype_a :
      t.sum (fun i => w i * a i) = ∑ i : t, w i.1 * a i.1 := by
    refine
      (Finset.sum_subtype (s := t) (p := fun i => i ∈ t) (f := fun i => w i * a i) ?_)
    intro i
    simp
  have hsum_equiv_a :
      ∑ j, w' j * a (e j) = ∑ i : t, w i.1 * a i.1 := by
    simpa [w', e] using (Equiv.sum_comp e'.symm (fun i : t => w i.1 * a i.1))
  have hobj_eq :
      ∑ j, w' j * a (e j) = ∑ i, w i * a i := by
    calc
      ∑ j, w' j * a (e j) = ∑ i : t, w i.1 * a i.1 := hsum_equiv_a
      _ = t.sum (fun i => w i * a i) := by symm; exact hsum_subtype_a
      _ = ∑ i, w i * a i := hsum_t_a
  have hsubset : t ⊆ (Finset.univ : Finset (Fin k)) := by
    intro i hi
    simp
  have hne : t ≠ (Finset.univ : Finset (Fin k)) := by
    rcases hzero with ⟨i0, hi0⟩
    intro h_eq
    have : i0 ∈ t := by
      simp [h_eq]
    have hne' : w i0 ≠ 0 := (Finset.mem_filter.mp this).2
    exact hne' hi0
  have hssub : t ⊂ (Finset.univ : Finset (Fin k)) :=
    (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hne⟩
  have hk' : k' < k := by
    have hk' := Finset.card_lt_card hssub
    simpa [k', t] using hk'
  refine ⟨k', e, w', hw', hwnz', hx_comb, hobj_eq, hk'⟩

/-- Reduce a convex combination to an affinely independent one without increasing a linear
objective. -/
lemma exists_affineIndependent_convexCombination_obj_le {n k : Nat}
    {p : Fin k → Fin n → Real} {w : Fin k → Real} {x : Fin n → Real} {a : Fin k → Real}
    (hw : IsConvexWeights k w) (hwnz : ∀ i, w i ≠ 0)
    (hx : x = convexCombination n k p w) :
    ∃ m : Nat, m ≤ n + 1 ∧
      ∃ (e : Fin m ↪ Fin k) (w' : Fin m → Real),
        IsConvexWeights m w' ∧
          (∀ j, w' j ≠ 0) ∧
          x = convexCombination n m (fun j => p (e j)) w' ∧
          AffineIndependent ℝ (fun j => p (e j)) ∧
          (∑ j, w' j * a (e j) ≤ ∑ i, w i * a i) := by
  classical
  let P : Nat → Prop := fun k =>
    ∀ {p : Fin k → Fin n → Real} {w : Fin k → Real} {x : Fin n → Real} {a : Fin k → Real},
      IsConvexWeights k w → (∀ i, w i ≠ 0) → x = convexCombination n k p w →
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (e : Fin m ↪ Fin k) (w' : Fin m → Real),
            IsConvexWeights m w' ∧
              (∀ j, w' j ≠ 0) ∧
              x = convexCombination n m (fun j => p (e j)) w' ∧
              AffineIndependent ℝ (fun j => p (e j)) ∧
              (∑ j, w' j * a (e j) ≤ ∑ i, w i * a i)
  have hP : P k := by
    refine Nat.strong_induction_on (p := P) k ?_
    intro k ih p w x a hw hwnz hx
    by_cases hAff : AffineIndependent ℝ p
    ·
      have hm : k ≤ n + 1 := by
        simpa using (caratheodory_aux_card_le_n_add_one (n := n) (z := p) hAff)
      let e : Fin k ↪ Fin k :=
        { toFun := fun i => i
          inj' := by intro i j h; simpa using h }
      refine ⟨k, hm, e, w, hw, hwnz, ?_, hAff, ?_⟩
      · simpa [e] using hx
      ·
        simp [e]
    ·
      cases k with
      | zero =>
          rcases hw with ⟨_, hsum⟩
          simp at hsum
      | succ m =>
          have hw' : IsConvexWeights (m + 1) w := by simpa using hw
          have hx' : x = convexCombination n (m + 1) p w := hx
          have hdep : ¬ AffineIndependent ℝ p := hAff
          rcases
              convex_elim_one_point_obj_to_shorter_fin (n := n) (m := m) (p := p) (w := w)
                (x := x) (a := a) hw' hwnz hx' hdep with
            ⟨i0, w1, hw1, hx1, hw1_i0, hobj_le1⟩
          rcases
              drop_zero_weights_preserves_convexCombination_obj (p := p) (w := w1) (x := x)
                (a := a) hw1 hx1 ⟨i0, hw1_i0⟩ with
            ⟨k', e1, w2, hw2, hwnz2, hx2, hobj_eq2, hk'⟩
          have hih :=
            ih k' hk' (p := fun j => p (e1 j)) (w := w2) (x := x)
              (a := fun j => a (e1 j)) hw2 hwnz2 hx2
          rcases hih with ⟨m', hm', e2, w3, hw3, hwnz3, hx3, hAff3, hobj_le3⟩
          let e : Fin m' ↪ Fin (m + 1) :=
            { toFun := fun j => e1 (e2 j)
              inj' := by
                intro i j h
                exact e2.injective (e1.injective h) }
          refine ⟨m', hm', e, w3, hw3, hwnz3, ?_, hAff3, ?_⟩
          · simpa [e] using hx3
          ·
            have hobj_le3' :
                ∑ j, w3 j * a (e j) ≤ ∑ i, w2 i * a (e1 i) := by
              simpa [e] using hobj_le3
            have hobj_le2 : ∑ i, w2 i * a (e1 i) ≤ ∑ i, w1 i * a i := by
              exact le_of_eq hobj_eq2
            exact le_trans hobj_le3' (le_trans hobj_le2 hobj_le1)
  exact hP hw hwnz hx

/-- Reindex a finset convex-combination witness to `Fin k` with nonzero weights. -/
lemma B0_mem_to_Fin_pos_repr
    {n : Nat} {ι : Type*} {f : ι → (Fin n → Real) → EReal}
    {x : Fin n → Real} {z : EReal}
    {s : Finset ι} {lam : ι → Real} {x' : ι → Fin n → Real}
    (h0 : ∀ i, 0 ≤ lam i)
    (hsum1 : s.sum (fun i => lam i) = 1)
    (hsumx : s.sum (fun i => lam i • x' i) = x)
    (hz : z = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i))) :
    ∃ k : Nat, ∃ (idx : Fin k → ι) (p : Fin k → Fin n → Real) (w : Fin k → Real),
      IsConvexWeights k w ∧ (∀ j, w j ≠ 0) ∧ x = convexCombination n k p w ∧
      z = ∑ j, ((w j : Real) : EReal) * f (idx j) (p j) := by
  classical
  let t : Finset ι := s.filter (fun i => lam i ≠ 0)
  have hsum_t :
      t.sum (fun i => lam i) = s.sum (fun i => lam i) := by
    have hsum_filter :=
      (Finset.sum_filter (s := s) (p := fun i => lam i ≠ 0) (f := fun i => lam i))
    have hsum_if :
        s.sum (fun i => if lam i ≠ 0 then lam i else 0) =
          s.sum (fun i => lam i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : lam i = 0 <;> simp [h]
    calc
      t.sum (fun i => lam i) =
          s.sum (fun i => if lam i ≠ 0 then lam i else 0) := by
        simpa [t] using hsum_filter
      _ = s.sum (fun i => lam i) := hsum_if
  have hsum_t_x :
      t.sum (fun i => lam i • x' i) = s.sum (fun i => lam i • x' i) := by
    have hsum_filter :=
      (Finset.sum_filter (s := s) (p := fun i => lam i ≠ 0)
        (f := fun i => lam i • x' i))
    have hsum_if :
        s.sum (fun i => if lam i ≠ 0 then lam i • x' i else 0) =
          s.sum (fun i => lam i • x' i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : lam i = 0 <;> simp [h]
    calc
      t.sum (fun i => lam i • x' i) =
          s.sum (fun i => if lam i ≠ 0 then lam i • x' i else 0) := by
        simpa [t] using hsum_filter
      _ = s.sum (fun i => lam i • x' i) := hsum_if
  have hsum_t_z :
      t.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) =
        s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
    have hsum_filter :=
      (Finset.sum_filter (s := s) (p := fun i => lam i ≠ 0)
        (f := fun i => ((lam i : Real) : EReal) * f i (x' i)))
    have hsum_if :
        s.sum (fun i =>
          if lam i ≠ 0 then ((lam i : Real) : EReal) * f i (x' i) else 0) =
          s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : lam i = 0 <;> simp [h]
    calc
      t.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) =
          s.sum (fun i =>
            if lam i ≠ 0 then ((lam i : Real) : EReal) * f i (x' i) else 0) := by
        simpa [t] using hsum_filter
      _ = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := hsum_if
  let k : Nat := t.card
  let e : t ≃ Fin k := t.equivFin
  let idx : Fin k → ι := fun j => (e.symm j).1
  let p : Fin k → Fin n → Real := fun j => x' (e.symm j).1
  let w : Fin k → Real := fun j => lam (e.symm j).1
  have hwnz : ∀ j, w j ≠ 0 := by
    intro j
    have hmem : (e.symm j).1 ∈ t := (e.symm j).2
    have hmem' : lam (e.symm j).1 ≠ 0 := (Finset.mem_filter.mp hmem).2
    simpa [w] using hmem'
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    simpa [w] using h0 (e.symm j).1
  have hsum_subtype :
      t.sum (fun i => lam i) = ∑ i : t, lam i.1 := by
    refine
      (Finset.sum_subtype (s := t) (p := fun i => i ∈ t) (f := fun i => lam i) ?_)
    intro i
    simp
  have hsum_subtype_x :
      t.sum (fun i => lam i • x' i) = ∑ i : t, lam i.1 • x' i.1 := by
    refine
      (Finset.sum_subtype (s := t) (p := fun i => i ∈ t)
        (f := fun i => lam i • x' i) ?_)
    intro i
    simp
  have hsum_subtype_z :
      t.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) =
        ∑ i : t, ((lam i.1 : Real) : EReal) * f i.1 (x' i.1) := by
    refine
      (Finset.sum_subtype (s := t) (p := fun i => i ∈ t)
        (f := fun i => ((lam i : Real) : EReal) * f i (x' i)) ?_)
    intro i
    simp
  have hsum_w : ∑ j, w j = 1 := by
    have hsum_equiv :
        ∑ j, w j = ∑ i : t, lam i.1 := by
      simpa [w] using (Equiv.sum_comp e.symm (fun i : t => lam i.1))
    calc
      ∑ j, w j = ∑ i : t, lam i.1 := hsum_equiv
      _ = t.sum (fun i => lam i) := by symm; exact hsum_subtype
      _ = s.sum (fun i => lam i) := hsum_t
      _ = 1 := hsum1
  have hw : IsConvexWeights k w := ⟨hw_nonneg, hsum_w⟩
  have hx_sum : x = ∑ j, w j • p j := by
    have hsum_equiv :
        ∑ j, w j • p j = ∑ i : t, lam i.1 • x' i.1 := by
      simpa [w, p] using (Equiv.sum_comp e.symm (fun i : t => lam i.1 • x' i.1))
    have hx_t : t.sum (fun i => lam i • x' i) = x := by
      calc
        t.sum (fun i => lam i • x' i) = s.sum (fun i => lam i • x' i) := hsum_t_x
        _ = x := hsumx
    calc
      x = t.sum (fun i => lam i • x' i) := by symm; exact hx_t
      _ = ∑ i : t, lam i.1 • x' i.1 := hsum_subtype_x
      _ = ∑ j, w j • p j := by symm; exact hsum_equiv
  have hx_comb : x = convexCombination n k p w := by
    simpa [convexCombination] using hx_sum
  have hz_sum : z = ∑ j, ((w j : Real) : EReal) * f (idx j) (p j) := by
    have hsum_equiv :
        ∑ j, ((w j : Real) : EReal) * f (idx j) (p j) =
          ∑ i : t, ((lam i.1 : Real) : EReal) * f i.1 (x' i.1) := by
      simpa [w, idx, p] using
        (Equiv.sum_comp e.symm
          (fun i : t => ((lam i.1 : Real) : EReal) * f i.1 (x' i.1)))
    have hz_t : t.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) = z := by
      calc
        t.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) =
            s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := hsum_t_z
        _ = z := by simp [hz]
    calc
      z = t.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
            symm
            exact hz_t
      _ = ∑ i : t, ((lam i.1 : Real) : EReal) * f i.1 (x' i.1) := hsum_subtype_z
      _ = ∑ j, ((w j : Real) : EReal) * f (idx j) (p j) := by
            symm
            exact hsum_equiv
  refine ⟨k, idx, p, w, hw, hwnz, hx_comb, hz_sum⟩

theorem convexHullFunctionFamily_eq_sInf_affineIndependent_convexCombination_le_add_one
    {n : Nat} {ι : Type*} {f : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ∀ x : Fin n → Real,
      convexHullFunctionFamily f x =
        sInf { z : EReal |
          ∃ m : Nat, m ≤ n + 1 ∧
            ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (w : Fin m → Real),
              IsConvexWeights m w ∧
                (∀ j, w j ≠ 0) ∧
                x = convexCombination n m x' w ∧
                AffineIndependent ℝ x' ∧
                z = ∑ j, ((w j : Real) : EReal) * f (idx j) (x' j) } := by
  classical
  intro x
  by_cases hI : Nonempty ι
  ·
    classical
    let B0 : Set EReal :=
      { z : EReal |
        ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
          (∀ i, 0 ≤ lam i) ∧
          (∀ i, i ∉ s → lam i = 0) ∧
          (s.sum (fun i => lam i) = 1) ∧
          (s.sum (fun i => lam i • x' i) = x) ∧
          z = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
    let B1 : Set EReal :=
      { z : EReal |
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (w : Fin m → Real),
            IsConvexWeights m w ∧
              (∀ j, w j ≠ 0) ∧
              x = convexCombination n m x' w ∧
              AffineIndependent ℝ x' ∧
              z = ∑ j, ((w j : Real) : EReal) * f (idx j) (x' j) }
    -- Coalesce a `B1` witness to a finset witness in `B0` with no larger objective.
    have coalesce_B1_to_B0_le :
        ∀ {z}, z ∈ B1 → ∃ z0, z0 ∈ B0 ∧ z0 ≤ z := by
      intro z hz
      rcases hz with ⟨m, _hm_le, idx, x', w, hw, hwnz, hxcomb, _hAff, hz⟩
      by_cases hz_top : z = ⊤
      · obtain ⟨i0⟩ := hI
        let s : Finset ι := {i0}
        let lam : ι → Real := fun i => if i = i0 then 1 else 0
        let x'' : ι → Fin n → Real := fun _ => x
        let z0 : EReal := s.sum (fun i => ((lam i : Real) : EReal) * f i (x'' i))
        have h0 : ∀ i, 0 ≤ lam i := by
          intro i
          by_cases hi : i = i0
          · simp [lam, hi]
          · simp [lam, hi]
        have hsupport : ∀ i, i ∉ s → lam i = 0 := by
          intro i hi
          have hi' : i ≠ i0 := by
            intro hi0
            apply hi
            simp [s, hi0]
          simp [lam, hi']
        have hsum1 : s.sum (fun i => lam i) = 1 := by
          simp [s, lam]
        have hsumx : s.sum (fun i => lam i • x'' i) = x := by
          simp [s, lam, x'']
        refine ⟨z0, ?_, ?_⟩
        · exact ⟨s, lam, x'', h0, hsupport, hsum1, hsumx, rfl⟩
        · simp [hz_top]
      · have hw' : IsConvexWeights m w := hw
        rcases hw with ⟨hw_nonneg, hw_sum⟩
        let μ' : Fin m → Real := fun j => (f (idx j) (x' j)).toReal
        let μ : Real := ∑ j, w j * μ' j
        have hsum1 : Finset.univ.sum (fun j => w j) = 1 := by
          simpa using hw_sum
        have hsumx : Finset.univ.sum (fun j => w j • x' j) = x := by
          simpa [convexCombination] using hxcomb.symm
        have hsumμ : Finset.univ.sum (fun j => w j * μ' j) = μ := by
          simp [μ]
        have hnot_top : ∀ j, f (idx j) (x' j) ≠ ⊤ :=
          bdd_toReal_of_sum_ne_top (hf := hf) (hw := hw') (hwnz := hwnz)
            (hz := hz) (hz_top := hz_top)
        have hnot_bot : ∀ j, f (idx j) (x' j) ≠ ⊥ := by
          intro j
          exact (hf (idx j)).2.2 (x' j) (by simp)
        have hle : ∀ j, f (idx j) (x' j) ≤ (μ' j : EReal) := by
          intro j
          have htop : f (idx j) (x' j) ≠ ⊤ := hnot_top j
          simpa [μ'] using
            (EReal.le_coe_toReal (x := f (idx j) (x' j)) htop)
        rcases
            merge_epigraph_combo_finset (f := f) (hf := hf) (idx := idx) (lam := w) (x' := x')
              (μ' := μ') (x := x) (μ := μ) hw_nonneg hsum1 hsumx hsumμ hle with
          ⟨s, lam', x'', μ'', h0', hzero', hsum1', hsumx', hsumμ', hle'⟩
        let z0 : EReal := s.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i))
        have hz0mem : z0 ∈ B0 := by
          exact ⟨s, lam', x'', h0', hzero', hsum1', hsumx', rfl⟩
        have hsum_le :
            z0 ≤ s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          by_cases hli : lam' i = 0
          · simp [hli]
          · have hpos : 0 < lam' i := lt_of_le_of_ne (h0' i) (Ne.symm hli)
            exact ereal_mul_le_mul_of_pos_left_general (t := lam' i) hpos (hle' i)
        have hsumμE :
            s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) = (μ : EReal) := by
          have hsum' :
              s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) =
                s.sum (fun i => ((lam' i * μ'' i : Real) : EReal)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [EReal.coe_mul]
          have hsum'' :
              s.sum (fun i => ((lam' i * μ'' i : Real) : EReal)) =
                ((s.sum (fun i => lam' i * μ'' i) : ℝ) : EReal) := by
            simpa using (ereal_coe_sum (s := s) (f := fun i => lam' i * μ'' i))
          calc
            s.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal))
                = ((s.sum (fun i => lam' i * μ'' i) : ℝ) : EReal) := hsum'.trans hsum''
            _ = (μ : EReal) := by simp [hsumμ']
        have hz_eq' : z = (μ : EReal) := by
          have hsum' :
              (∑ i, ((w i : Real) : EReal) * f (idx i) (x' i)) =
                ∑ i, ((w i * μ' i : Real) : EReal) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have htop : f (idx i) (x' i) ≠ ⊤ := hnot_top i
            have hbot : f (idx i) (x' i) ≠ ⊥ := hnot_bot i
            have hcoe : (μ' i : EReal) = f (idx i) (x' i) := by
              simpa [μ'] using (EReal.coe_toReal htop hbot)
            calc
              ((w i : Real) : EReal) * f (idx i) (x' i)
                  = ((w i : Real) : EReal) * (μ' i : EReal) := by simp [hcoe]
              _ = ((w i * μ' i : Real) : EReal) := by simp [EReal.coe_mul]
          have hsum'' :
              (∑ i, ((w i * μ' i : Real) : EReal)) =
                ((∑ i, w i * μ' i : Real) : EReal) := by
            simpa using (ereal_coe_sum (s := Finset.univ) (f := fun i => w i * μ' i))
          calc
            z = ∑ i, ((w i : Real) : EReal) * f (idx i) (x' i) := hz
            _ = ((∑ i, w i * μ' i : Real) : EReal) := by exact hsum'.trans hsum''
            _ = (μ : EReal) := by simp [μ]
        have hz0_le : z0 ≤ (μ : EReal) := by
          simpa [hsumμE] using hsum_le
        refine ⟨z0, hz0mem, ?_⟩
        simpa [hz_eq'] using hz0_le
    -- Reduce a finset witness in `B0` to an affinely independent witness in `B1`.
    have B0_to_B1_exists_le :
        ∀ {z}, z ∈ B0 → ∃ z1, z1 ∈ B1 ∧ z1 ≤ z := by
      intro z hz
      by_cases hz_top : z = ⊤
      · obtain ⟨i0⟩ := hI
        let idx1 : Fin 1 → ι := fun _ => i0
        let x1 : Fin 1 → Fin n → Real := fun _ => x
        let w1 : Fin 1 → Real := fun _ => 1
        let z1 : EReal := ∑ j, ((w1 j : Real) : EReal) * f (idx1 j) (x1 j)
        have hw1 : IsConvexWeights 1 w1 := by
          refine ⟨?_, ?_⟩
          · intro j
            simp [w1]
          · simp [w1]
        have hwnz1 : ∀ j, w1 j ≠ 0 := by
          intro j
          simp [w1]
        have hx1 : x = convexCombination n 1 x1 w1 := by
          simp [convexCombination, x1, w1]
        have hAff1 : AffineIndependent ℝ x1 :=
          affineIndependent_of_subsingleton (k := ℝ) x1
        refine ⟨z1, ?_, ?_⟩
        · exact ⟨1, by simp, idx1, x1, w1, hw1, hwnz1, hx1, hAff1, rfl⟩
        · simp [hz_top]
      ·
        rcases hz with ⟨s, lam, x', h0, _hzero, hsum1, hsumx, hz_sum⟩
        rcases
            B0_mem_to_Fin_pos_repr (f := f) (x := x) (z := z) (s := s) (lam := lam)
              (x' := x') h0 hsum1 hsumx hz_sum with
          ⟨k, idx, p, w, hw, hwnz, hxcomb, hz_sum'⟩
        let a : Fin k → Real := fun i => (f (idx i) (p i)).toReal
        have hnot_top : ∀ i, f (idx i) (p i) ≠ ⊤ :=
          bdd_toReal_of_sum_ne_top (hf := hf) (hw := hw) (hwnz := hwnz)
            (hz := hz_sum') (hz_top := hz_top)
        have hnot_bot : ∀ i, f (idx i) (p i) ≠ ⊥ := by
          intro i
          exact (hf (idx i)).2.2 (p i) (by simp)
        rcases
            exists_affineIndependent_convexCombination_obj_le (p := p) (w := w) (x := x)
              (a := a) hw hwnz hxcomb with
          ⟨m, hm, e, w', hw', hwnz', hx', hAff', hobj_le⟩
        let z1 : EReal :=
          ∑ j, ((w' j : Real) : EReal) * f (idx (e j)) (p (e j))
        have hz1_mem : z1 ∈ B1 := by
          exact ⟨m, hm, (fun j => idx (e j)), (fun j => p (e j)), w', hw', hwnz',
            hx', hAff', rfl⟩
        have hcoe : ∀ i, (a i : EReal) = f (idx i) (p i) := by
          intro i
          simpa [a] using (EReal.coe_toReal (hnot_top i) (hnot_bot i))
        have hz1_coe :
            z1 = ((∑ j, w' j * a (e j) : Real) : EReal) := by
          have hsum' :
              ∑ j, ((w' j : Real) : EReal) * f (idx (e j)) (p (e j)) =
                ∑ j, ((w' j * a (e j) : Real) : EReal) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            have hcoe' : (a (e j) : EReal) = f (idx (e j)) (p (e j)) := hcoe (e j)
            calc
              ((w' j : Real) : EReal) * f (idx (e j)) (p (e j)) =
                  ((w' j : Real) : EReal) * (a (e j) : EReal) := by simp [hcoe']
              _ = ((w' j * a (e j) : Real) : EReal) := by simp [EReal.coe_mul]
          have hsum'' :
              ∑ j, ((w' j * a (e j) : Real) : EReal) =
                ((∑ j, w' j * a (e j) : Real) : EReal) := by
            simpa using
              (ereal_coe_sum (s := Finset.univ) (f := fun j => w' j * a (e j)))
          simpa [z1] using hsum'.trans hsum''
        have hz_coe : z = ((∑ i, w i * a i : Real) : EReal) := by
          have hsum' :
              ∑ i, ((w i : Real) : EReal) * f (idx i) (p i) =
                ∑ i, ((w i * a i : Real) : EReal) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            have hcoe' : (a i : EReal) = f (idx i) (p i) := hcoe i
            calc
              ((w i : Real) : EReal) * f (idx i) (p i) =
                  ((w i : Real) : EReal) * (a i : EReal) := by simp [hcoe']
              _ = ((w i * a i : Real) : EReal) := by simp [EReal.coe_mul]
          have hsum'' :
              ∑ i, ((w i * a i : Real) : EReal) =
                ((∑ i, w i * a i : Real) : EReal) := by
            simpa using (ereal_coe_sum (s := Finset.univ) (f := fun i => w i * a i))
          calc
            z = ∑ i, ((w i : Real) : EReal) * f (idx i) (p i) := hz_sum'
            _ = ((∑ i, w i * a i : Real) : EReal) := by exact hsum'.trans hsum''
        have hz1_le : z1 ≤ z := by
          have hobj_le' :
              ((∑ j, w' j * a (e j) : Real) : EReal) ≤
                ((∑ i, w i * a i : Real) : EReal) := by
            exact (EReal.coe_le_coe_iff).2 hobj_le
          simpa [hz1_coe, hz_coe] using hobj_le'
        exact ⟨z1, hz1_mem, hz1_le⟩
    have hconv :
        convexHullFunctionFamily f x = sInf B0 := by
      simpa [B0] using
        (convexHullFunctionFamily_eq_sInf_convexCombination (f := f) (hf := hf) (x := x))
    have hle : sInf B0 ≤ sInf B1 := by
      refine le_sInf ?_
      intro z hz
      rcases coalesce_B1_to_B0_le hz with ⟨z0, hz0, hz0le⟩
      exact le_trans (sInf_le hz0) hz0le
    have hge : sInf B1 ≤ sInf B0 := by
      refine le_sInf ?_
      intro z hz
      rcases B0_to_B1_exists_le hz with ⟨z1, hz1, hz1le⟩
      exact le_trans (sInf_le hz1) hz1le
    have hEq : sInf B0 = sInf B1 := le_antisymm hle hge
    calc
      convexHullFunctionFamily f x = sInf B0 := hconv
      _ = sInf B1 := hEq
  · haveI : IsEmpty ι := by
      exact not_nonempty_iff.mp hI
    let B0 : Set EReal :=
      { z : EReal |
        ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
          (∀ i, 0 ≤ lam i) ∧
          (∀ i, i ∉ s → lam i = 0) ∧
          (s.sum (fun i => lam i) = 1) ∧
          (s.sum (fun i => lam i • x' i) = x) ∧
          z = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
    let B1 : Set EReal :=
      { z : EReal |
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (w : Fin m → Real),
            IsConvexWeights m w ∧
              (∀ j, w j ≠ 0) ∧
              x = convexCombination n m x' w ∧
              AffineIndependent ℝ x' ∧
              z = ∑ j, ((w j : Real) : EReal) * f (idx j) (x' j) }
    have hB0 : B0 = (∅ : Set EReal) := by
      ext z
      constructor
      · rintro ⟨s, lam, x', -, -, hsum1, -, -⟩
        have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
        simp [hs] at hsum1
      · intro hz
        cases hz
    have hB1 : B1 = (∅ : Set EReal) := by
      ext z
      constructor
      · rintro ⟨m, _, idx, _, w, hw, _, _, _, _⟩
        have hm1 : 1 ≤ m := one_le_of_IsConvexWeights (m := m) (w := w) hw
        have hm_pos : 0 < m := lt_of_lt_of_le (by exact zero_lt_one) hm1
        let j : Fin m := ⟨0, hm_pos⟩
        exact (isEmptyElim (idx j))
      · intro hz
        cases hz
    have hconv :
        convexHullFunctionFamily f x = sInf B0 := by
      simpa [B0] using
        (convexHullFunctionFamily_eq_sInf_convexCombination (f := f) (hf := hf) (x := x))
    calc
      convexHullFunctionFamily f x = sInf B0 := hconv
      _ = ⊤ := by simp [hB0]
      _ = sInf B1 := by simp [hB1]

/-- Convexity and a finite point for `convexHullFunctionFamily` under properness. -/
lemma convexHullFunctionFamily_convex_and_exists_ne_top {n : Nat} {ι : Sort _}
    {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i))
    (hI : Nonempty ι) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (convexHullFunctionFamily fᵢ) ∧
      ∃ x, convexHullFunctionFamily fᵢ x ≠ (⊤ : EReal) := by
  classical
  rcases (convexHullFunctionFamily_greatest_convex_minorant (f := fᵢ)) with
    ⟨hconv, hle, -⟩
  rcases hI with ⟨i0⟩
  have hne_epi :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (fᵢ i0)) :=
    (hf i0).2.1
  have hne_eff :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) (fᵢ i0)) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain (S := Set.univ) (f := fᵢ i0)).1 hne_epi
  rcases hne_eff with ⟨x0, hx0⟩
  have hx0_ne_top : fᵢ i0 x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := fᵢ i0) (x := x0) hx0
  have hle0 : convexHullFunctionFamily fᵢ x0 ≤ fᵢ i0 x0 := hle i0 x0
  have hx0_g_ne_top : convexHullFunctionFamily fᵢ x0 ≠ (⊤ : EReal) := by
    intro htop
    have htop_le : (⊤ : EReal) ≤ fᵢ i0 x0 := by simpa [htop] using hle0
    have htop_eq : fᵢ i0 x0 = (⊤ : EReal) := (top_le_iff).1 htop_le
    exact hx0_ne_top htop_eq
  exact ⟨hconv, ⟨x0, hx0_g_ne_top⟩⟩

/-- Positive-scalar infimum representation for `posHomGen` of a convex hull family. -/
lemma posHomGen_convexHullFamily_eq_sInf_pos_rightScalarMultiple {n : Nat} {ι : Sort _}
    {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i))
    (hI : Nonempty ι) :
    ∀ x : Fin n → Real,
      x ≠ 0 →
        positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily fᵢ) x =
          sInf { z : EReal |
            ∃ lam : Real, 0 < lam ∧
              z = rightScalarMultiple (convexHullFunctionFamily fᵢ) lam x } := by
  intro x hx
  obtain ⟨hconv, hfinite⟩ :=
    convexHullFunctionFamily_convex_and_exists_ne_top (hf := hf) hI
  have hmain :=
    (infimumRepresentation_posHomogeneousHull (n := n)
      (h := convexHullFunctionFamily fᵢ) hconv hfinite).2
  have hmain' := hmain x (Or.inl hx)
  simpa using hmain'

/-- If the index type is empty, the convex hull family is identically `⊤`. -/
lemma convexHullFunctionFamily_eq_top_of_isEmpty {n : Nat} {ι : Type _}
    {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i))
    (hI : IsEmpty ι) :
    ∀ x : Fin n → Real, convexHullFunctionFamily fᵢ x = (⊤ : EReal) := by
  classical
  intro x
  haveI : IsEmpty ι := hI
  let B0 : Set EReal :=
    { z : EReal |
      ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • x' i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) * fᵢ i (x' i)) }
  have hB0 : B0 = (∅ : Set EReal) := by
    ext z
    constructor
    · rintro ⟨s, lam, x', -, -, hsum1, -, -⟩
      have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
      simp [hs] at hsum1
    · intro hz
      cases hz
  have hconv :
      convexHullFunctionFamily fᵢ x = sInf B0 := by
    simpa [B0] using
      (convexHullFunctionFamily_eq_sInf_convexCombination (f := fᵢ) (hf := hf) (x := x))
  simpa [hB0] using hconv

/-- In the empty-index case, the generated positively homogeneous convex function is `⊤` off zero. -/
lemma posHomGen_convexHullFamily_eq_top_of_isEmpty {n : Nat} {ι : Type _}
    {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i))
    (hI : IsEmpty ι) :
    ∀ x : Fin n → Real,
      x ≠ 0 →
        positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily fᵢ) x = (⊤ : EReal) := by
  classical
  intro x hx
  haveI : IsEmpty ι := hI
  have htop : ∀ y, convexHullFunctionFamily fᵢ y = (⊤ : EReal) :=
    convexHullFunctionFamily_eq_top_of_isEmpty (hf := hf) hI
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (convexHullFunctionFamily fᵢ) := by
    simpa using (convexHullFunctionFamily_greatest_convex_minorant (f := fᵢ)).1
  have hcone_zero :
      ∀ {p : (Fin n → Real) × Real},
        p ∈ convexConeGeneratedEpigraph (convexHullFunctionFamily fᵢ) → p = 0 := by
    intro p hp
    have hp' :=
      (mem_convexConeGeneratedEpigraph_iff
        (h := convexHullFunctionFamily fᵢ) (hh := hconv) (p := p)).1 hp
    rcases hp' with rfl | ⟨lam, hlam, hmem⟩
    · rfl
    · exfalso
      rcases hmem with ⟨q, hq, rfl⟩
      have hle :
          convexHullFunctionFamily fᵢ q.1 ≤ (q.2 : EReal) :=
        (mem_epigraph_univ_iff (f := convexHullFunctionFamily fᵢ)).1 hq
      have htop_q : convexHullFunctionFamily fᵢ q.1 = (⊤ : EReal) := htop q.1
      have htop_le : (⊤ : EReal) ≤ (q.2 : EReal) := by
        simp [htop_q] at hle
      have htop' : ((q.2 : Real) : EReal) = ⊤ := (top_le_iff).1 htop_le
      exact (EReal.coe_ne_top _ htop').elim
  have hempty :
      { μ : ℝ |
        (x, μ) ∈ convexConeGeneratedEpigraph (convexHullFunctionFamily fᵢ) } =
        (∅ : Set ℝ) := by
    ext μ
    constructor
    · intro hμ
      have hzero : (x, μ) = 0 := hcone_zero hμ
      have hx0 : x = 0 := by simpa using congrArg Prod.fst hzero
      exact (hx hx0).elim
    · intro hμ
      cases hμ
  simp [positivelyHomogeneousConvexFunctionGenerated, hempty]

/-- In the empty-index case, the witness set for Corollary 17.1.4 is empty off zero. -/
lemma cor17_1_4_rhs_empty_of_isEmpty {n : Nat} {ι : Sort _}
    {fᵢ : ι → (Fin n → Real) → EReal}
    (hI : IsEmpty ι) {x : Fin n → Real} (hx : x ≠ 0) :
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (c : Fin m → Real),
          (∀ j, 0 < c j) ∧
            x = ∑ j, c j • x' j ∧
            AffineIndependent ℝ x' ∧
            z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (x' j) } = (∅ : Set EReal) := by
  classical
  haveI : IsEmpty ι := hI
  ext z
  constructor
  · rintro ⟨m, _hm, idx, x', c, _hcpos, hxsum, _hlin, _hz⟩
    cases m with
    | zero =>
        have hx0 : x = 0 := by simpa using hxsum
        exact (hx hx0).elim
    | succ m =>
        let j : Fin (Nat.succ m) := ⟨0, Nat.succ_pos _⟩
        exact (isEmptyElim (idx j))
  · intro hz
    cases hz

/-- Multiplication by a positive real number is an order isomorphism on `EReal`. -/
noncomputable def ereal_mulPosOrderIso (t : ℝ) (ht : 0 < t) : EReal ≃o EReal where
  toFun x := (t : EReal) * x
  invFun x := ((t⁻¹ : ℝ) : EReal) * x
  left_inv x := by
    have htne : t ≠ 0 := ne_of_gt ht
    calc
      ((t⁻¹ : ℝ) : EReal) * ((t : EReal) * x) = (((t⁻¹ : ℝ) : EReal) * (t : EReal)) * x := by
        simp [mul_assoc]
      _ = ((t⁻¹ * t : ℝ) : EReal) * x := by
        simp [mul_assoc]
      _ = (1 : EReal) * x := by
        simp [inv_mul_cancel₀ (a := t) htne]
      _ = x := by simp
  right_inv x := by
    have htne : t ≠ 0 := ne_of_gt ht
    calc
      (t : EReal) * (((t⁻¹ : ℝ) : EReal) * x) = ((t : EReal) * ((t⁻¹ : ℝ) : EReal)) * x := by
        simp [mul_assoc]
      _ = ((t * t⁻¹ : ℝ) : EReal) * x := by
        simp [mul_assoc]
      _ = (1 : EReal) * x := by
        simp [mul_inv_cancel₀ (a := t) htne]
      _ = x := by simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro hab
      have ht_inv_nonneg : (0 : EReal) ≤ ((t⁻¹ : ℝ) : EReal) := by
        have : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos_of_pos ht)
        exact_mod_cast this
      have hab' := mul_le_mul_of_nonneg_left hab ht_inv_nonneg
      have htne : t ≠ 0 := ne_of_gt ht
      have hab'' :
          (((t⁻¹ : ℝ) : EReal) * (t : EReal)) * a ≤
            (((t⁻¹ : ℝ) : EReal) * (t : EReal)) * b := by
        simpa [mul_assoc] using hab'
      have hcoeff : ((t⁻¹ : ℝ) : EReal) * (t : EReal) = (1 : EReal) := by
        calc
          ((t⁻¹ : ℝ) : EReal) * (t : EReal) = ((t⁻¹ * t : ℝ) : EReal) := by
            simp
          _ = (1 : EReal) := by simp [inv_mul_cancel₀ (a := t) htne]
      simpa [hcoeff] using hab''
    · intro hab
      have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by
        have : (0 : ℝ) ≤ t := le_of_lt ht
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_left hab ht_nonneg

/-- Left multiplication by a nonnegative, non-top `EReal` distributes over finite sums. -/
lemma ereal_mul_sum {ι : Type _} (s : Finset ι) (f : ι → EReal) (a : EReal)
    (ha_nonneg : 0 ≤ a) (ha_ne_top : a ≠ ⊤) :
    a * (Finset.sum s f) = Finset.sum s (fun i => a * f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi hs
    simp [hi, hs, EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top]


end Section17
end Chap04
