import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Setoid

variable {S : Type u}

-- Proof sketch: if the intersection is nonempty, a common element is related to both `x` and `y`,
-- so symmetry and transitivity yield `s x y`; conversely, if `s x y`, then `x` lies in both
-- canonical classes `{z | s z x}` and `{z | s z y}`.
/-- Lemma 1.1.9: the equivalence classes `C_x` and `C_y` intersect nontrivially if and only if
`x` and `y` are equivalent under `s`. -/
theorem equivClass_inter_nonempty_iff (s : Setoid S) (x y : S) :
    (({z | s z x} : Set S) ∩ {z | s z y}).Nonempty ↔ s x y := by
  constructor
  · rintro ⟨z, hz, hy⟩
    exact s.trans (s.symm hz) hy
  · intro hxy
    exact ⟨x, s.refl x, hxy⟩

-- Proof sketch: the canonical classes of `x` and `y` both contain `y`.
-- Apply `Setoid.eq_of_mem_classes`.
/-- Related elements determine the same canonical equivalence class. -/
theorem equivClass_eq_of_related (s : Setoid S) {x y : S} (h : s x y) :
    ({z | s z x} : Set S) = {z | s z y} := by
  exact s.eq_of_mem_classes (s.mem_classes x) (s.symm h) (s.mem_classes y) (s.refl y)

end Setoid
