/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part5

open scoped Pointwise

section Chap03
section Section11

/-- Theorem 11.5: A closed convex set `C` is the intersection of the closed half-spaces which
contain it.

In mathlib, a convenient way to express the closed half-spaces containing `C` is to quantify over
continuous linear functionals `l : StrongDual ℝ (Fin n → ℝ)` and consider the half-space
`{x | ∃ y ∈ C, l x ≤ l y}`. -/
theorem isClosed_convex_eq_iInter_halfSpaces (n : Nat) (C : Set (Fin n → Real))
    (hCconv : Convex Real C) (hCclosed : IsClosed C) :
    (⋂ l : StrongDual ℝ (Fin n → Real), {x : Fin n → Real | ∃ y ∈ C, l x ≤ l y}) = C := by
  classical
  ext a
  constructor
  · intro haInter
    by_contra haC
    have hCne : C.Nonempty := by
      rcases (Set.mem_iInter.1 haInter (0 : StrongDual ℝ (Fin n → Real))) with ⟨y, hyC, _⟩
      exact ⟨y, hyC⟩
    rcases
        exists_strongDual_strict_sep_point_of_not_mem_isClosed_convex (n := n) (a := a) (C := C)
          hCconv hCclosed hCne haC with
      ⟨l, hl⟩
    rcases (Set.mem_iInter.1 haInter l) with ⟨y, hyC, hle⟩
    exact (not_lt_of_ge hle) (hl y hyC)
  · intro haC
    refine Set.mem_iInter.2 ?_
    intro l
    exact ⟨a, haC, le_rfl⟩

/-- `closure (convexHull ℝ S)` is a closed set. -/
lemma closure_convexHull_isClosed (n : Nat) (S : Set (Fin n → Real)) :
    IsClosed (closure (convexHull ℝ S)) := by
  exact isClosed_closure

/-- `closure (convexHull ℝ S)` is a convex set. -/
lemma closure_convexHull_convex (n : Nat) (S : Set (Fin n → Real)) :
    Convex Real (closure (convexHull ℝ S)) := by
  exact (convex_convexHull ℝ S).closure

/-- Corollary 11.5.1. Let `S` be any subset of `ℝ^n`. Then `cl (conv S)` (i.e.
`closure (convexHull ℝ S)`) is the intersection of all the closed half-spaces containing `S`. -/
theorem closure_convexHull_eq_iInter_halfSpaces (n : Nat) (S : Set (Fin n → Real)) :
    closure (convexHull ℝ S) =
      ⋂ l : StrongDual ℝ (Fin n → Real),
        {x : Fin n → Real | ∃ y ∈ closure (convexHull ℝ S), l x ≤ l y} := by
  simpa using
    (isClosed_convex_eq_iInter_halfSpaces (n := n) (C := closure (convexHull ℝ S))
          (hCconv := closure_convexHull_convex (n := n) (S := S))
          (hCclosed := closure_convexHull_isClosed (n := n) (S := S))).symm

end Section11
end Chap03
