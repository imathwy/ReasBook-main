/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10

section Chap01
section Section05

/-- Theorem 5.8.1: Let `f_1, ..., f_m` be proper convex functions on `ℝ^n`. Then
`f(x) = inf { max { f_1(x_1), ..., f_m(x_m) } | x_1 + ... + x_m = x }` is convex. -/
theorem convexFunctionOn_inf_iSup_of_proper {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x =>
        sInf { z : EReal |
          ∃ x' : Fin m → (Fin n → Real),
            (Finset.univ.sum (fun i => x' i) = x) ∧
              z = iSup (fun i : Fin m => f i (x' i)) }) := by
  classical
  refine
    (convexFunctionOn_univ_iff_strict_inequality (f := fun x =>
        sInf { z : EReal |
          ∃ x' : Fin m → (Fin n → Real),
            (Finset.univ.sum (fun i => x' i) = x) ∧
              z = iSup (fun i : Fin m => f i (x' i)) })).2 ?_
  intro x y α β t hfx hfy ht0 ht1
  set Sx : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = x) ∧
          z = iSup (fun i : Fin m => f i (x' i)) }
  set Sy : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = y) ∧
          z = iSup (fun i : Fin m => f i (x' i)) }
  set Sxy : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = (1 - t) • x + t • y) ∧
          z = iSup (fun i : Fin m => f i (x' i)) }
  have hneSx : Sx.Nonempty := by
    by_contra hne
    have hSx : Sx = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfx' := hfx
    simp [Sx, hSx, sInf_empty] at hfx'
  have hneSy : Sy.Nonempty := by
    by_contra hne
    have hSy : Sy = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfy' := hfy
    simp [Sy, hSy, sInf_empty] at hfy'
  rcases exists_lt_of_csInf_lt (s := Sx) hneSx (by simpa [Sx] using hfx) with
    ⟨z1, hz1Sx, hz1lt⟩
  rcases exists_lt_of_csInf_lt (s := Sy) hneSy (by simpa [Sy] using hfy) with
    ⟨z2, hz2Sy, hz2lt⟩
  rcases hz1Sx with ⟨x', hxsum, rfl⟩
  rcases hz2Sy with ⟨y', hysum, rfl⟩
  let w : Fin m → (Fin n → Real) := fun i => (1 - t) • x' i + t • y' i
  have hsum_w :
      Finset.univ.sum (fun i => w i) = (1 - t) • x + t • y := by
    calc
      Finset.univ.sum (fun i => w i) =
          (1 - t) • Finset.univ.sum (fun i => x' i) +
            t • Finset.univ.sum (fun i => y' i) := by
            simpa [w] using (sum_components_convex_combo (x' := x') (y' := y') (t := t))
      _ = (1 - t) • x + t • y := by
            simp [hxsum, hysum]
  have hfi_lt :
      ∀ i,
        f i (w i) <
          ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    intro i
    have hx_i : f i (x' i) < (α : EReal) := by
      have hle : f i (x' i) ≤ iSup (fun j : Fin m => f j (x' j)) :=
        le_iSup (fun j : Fin m => f j (x' j)) i
      exact lt_of_le_of_lt hle hz1lt
    have hy_i : f i (y' i) < (β : EReal) := by
      have hle : f i (y' i) ≤ iSup (fun j : Fin m => f j (y' j)) :=
        le_iSup (fun j : Fin m => f j (y' j)) i
      exact lt_of_le_of_lt hle hz2lt
    have hconv_i :=
      (convexFunctionOn_univ_iff_strict_inequality (f := f i)).1 (hf i).1
    simpa [w] using hconv_i (x' i) (y' i) α β t hx_i hy_i ht0 ht1
  have hsup_lt :
      iSup (fun i : Fin m => f i (w i)) <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    by_cases hm : m = 0
    · subst hm
      have hiSup :
          iSup (fun i : Fin 0 => f i (w i)) = (⊥ : EReal) := by
        simp
      have hbot' : (⊥ : EReal) < ((1 - t) * α + t * β : Real) := by
        simpa using (EReal.bot_lt_coe ((1 - t) * α + t * β))
      have hbot :
          (⊥ : EReal) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
        simpa [EReal.coe_add, EReal.coe_mul] using hbot'
      simpa [hiSup] using hbot
    · have hm' : 0 < m := Nat.pos_of_ne_zero hm
      exact iSup_lt_of_forall_lt_fin (m := m) (a := fun i => f i (w i)) (r :=
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal)) hm'
        hfi_lt
  have hmem : iSup (fun i : Fin m => f i (w i)) ∈ Sxy := by
    refine ⟨w, hsum_w, rfl⟩
  have hle : sInf Sxy ≤ iSup (fun i : Fin m => f i (w i)) := sInf_le hmem
  have hlt :
      sInf Sxy <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
    lt_of_le_of_lt hle hsup_lt
  simpa [Sxy] using hlt

end Section05
end Chap01
