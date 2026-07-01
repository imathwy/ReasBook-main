/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib

noncomputable section

section Chap02
section Section05

/-- Definiton 8.5.0. Let `f` be a proper convex function on `R^n` and let `f0^+` be its
recession function. The set of all vectors `y` such that `(f0^+)(y) <= 0` is called the
recession cone of `f`. -/
def Function.recessionCone {n : Nat} (f : EuclideanSpace Real (Fin n) → Real)
    (f0_plus : EuclideanSpace Real (Fin n) → Real) :
    Set (EuclideanSpace Real (Fin n)) :=
  { y | f0_plus y <= 0 }

end Section05
end Chap02
