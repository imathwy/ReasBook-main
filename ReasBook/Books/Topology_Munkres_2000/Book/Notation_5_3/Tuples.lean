module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

public section

universe u

namespace Book.Tuple

open Set

/-- The zero-based index type `Fin m` is equivalent to the book's one-based
coordinate interval `Set.Icc 1 m`. -/
@[expose]
def indexEquiv (m : ℕ+) : Fin m ≃ Set.Icc 1 m where
  toFun i := ⟨Nat.succPNat i, ⟨one_le, i.isLt⟩⟩
  invFun i :=
    ⟨i.1.natPred, lt_of_le_of_lt (PNat.natPred_monotone i.2.2) (Nat.pred_lt m.2.ne')⟩
  left_inv i := by
    ext
    simp
  right_inv i := by
    ext
    simp

/-- Reindex the book's one-based `m`-tuples as zero-based `Fin m`-indexed functions. -/
@[expose]
def finEquiv (X : Type u) (m : ℕ+) : (Set.Icc 1 m → X) ≃ (Fin m → X) :=
  (indexEquiv m).symm.arrowCongr (Equiv.refl X)

@[simp]
theorem finEquiv_apply (X : Type u) (m : ℕ+) (f : Set.Icc 1 m → X) (i : Fin m) :
    finEquiv X m f i = f (indexEquiv m i) :=
  rfl

@[simp]
theorem finEquiv_symm_apply (X : Type u) (m : ℕ+) (f : Fin m → X) (i : Set.Icc 1 m) :
    (finEquiv X m).symm f i = f ((indexEquiv m).symm i) :=
  rfl


end Book.Tuple

/-- The book's notation for `m`-tuples of elements of `X`, indexed from `1` through `m`. -/
scoped[Book] notation:70 X " ^ " m:71 => (Set.Icc 1 m → X)

/-- The book's notation for `ω`-tuples of elements of `X`. -/
scoped[Book] notation:70 X " ^ω" => (ℕ+ → X)
