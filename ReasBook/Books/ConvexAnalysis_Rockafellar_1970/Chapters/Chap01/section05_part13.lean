/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part12

section Chap01
section Section05

/-- The max-value set used in the infimum is nonempty. -/
lemma inf_max_set_nonempty {n : Nat} {f1 f2 : (Fin n → Real) → EReal} (x : Fin n → Real) :
    Set.Nonempty { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) } := by
  refine ⟨max (f1 (x - 0)) (f2 0), ?_⟩
  refine ⟨0, rfl⟩

/-- If the infimum is below `α`, then the point lies in the Minkowski sum of sublevel sets. -/
lemma mem_add_of_fx_lt {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    {α : EReal} {x : Fin n → Real}
    (hx :
      sInf { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) } < α) :
    x ∈ Set.image2 (fun a b => a + b)
      { a : Fin n → Real | f1 a < α }
      { b : Fin n → Real | f2 b < α } := by
  have hne :
      Set.Nonempty { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) } :=
    inf_max_set_nonempty (x := x) (f1 := f1) (f2 := f2)
  rcases exists_lt_of_csInf_lt
      (s := { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) }) hne hx with
    ⟨z, hzmem, hzlt⟩
  rcases hzmem with ⟨y, rfl⟩
  have hlt : f1 (x - y) < α ∧ f2 y < α := (max_lt_iff).1 hzlt
  rcases hlt with ⟨hx1, hy1⟩
  refine ⟨x - y, ?_, y, ?_, ?_⟩
  · simpa using hx1
  · simpa using hy1
  · simp

/-- If `x` is a sum of sublevel points, then the infimum is below `α`. -/
lemma fx_lt_of_mem_add {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    {α : EReal} {x : Fin n → Real}
    (hx :
      x ∈ Set.image2 (fun a b => a + b)
        { a : Fin n → Real | f1 a < α }
        { b : Fin n → Real | f2 b < α }) :
    sInf { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) } < α := by
  rcases (by simpa [Set.image2] using hx) with ⟨a, ha, b, hb, rfl⟩
  have hmax : max (f1 a) (f2 b) < α := (max_lt_iff).2 ⟨ha, hb⟩
  have hmem :
      max (f1 a) (f2 b) ∈
        { z : EReal | ∃ y, z = max (f1 ((a + b) - y)) (f2 y) } := by
    refine ⟨b, ?_⟩
    simp
  have hle :
      sInf { z : EReal | ∃ y, z = max (f1 ((a + b) - y)) (f2 y) } ≤
        max (f1 a) (f2 b) := sInf_le hmem
  exact lt_of_le_of_lt hle hmax

/-- Text 5.8.5: Let `f1, f2` be proper convex functions on `ℝ^n` and define
`f x = inf_y max { f1 (x - y), f2 y }`. Then, for any `α`,
`{x | f x < α} = {x | f1 x < α} + {x | f2 x < α}` (set sum). -/
theorem sublevelSet_inf_iSup_eq_add {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    let f : (Fin n → Real) → EReal :=
      fun x =>
        sInf { z : EReal | ∃ y : Fin n → Real, z = max (f1 (x - y)) (f2 y) }
    ∀ α : EReal,
      { x : Fin n → Real | f x < α } =
        Set.image2 (fun x y => x + y)
          { x : Fin n → Real | f1 x < α }
          { y : Fin n → Real | f2 y < α } := by
  dsimp
  intro α
  ext x
  constructor
  · intro hx
    have hx' :
        sInf { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) } < α := by
      simpa using hx
    exact mem_add_of_fx_lt (f1 := f1) (f2 := f2) (x := x) (α := α) hx'
  · intro hx
    have hx' :
        sInf { z : EReal | ∃ y, z = max (f1 (x - y)) (f2 y) } < α :=
      fx_lt_of_mem_add (f1 := f1) (f2 := f2) (x := x) (α := α) hx
    simpa using hx'

end Section05
end Chap01
