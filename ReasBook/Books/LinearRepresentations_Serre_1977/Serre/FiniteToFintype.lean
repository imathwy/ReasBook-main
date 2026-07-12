import Mathlib

-- Low-priority fallback from `Finite` to `Fintype` for Serre aggregate files.
noncomputable instance (priority := 100) instFintypeOfFinite
    (α : Type*) [Finite α] : Fintype α :=
  Fintype.ofFinite α

-- Low-priority fallback for cardinal denominators over characteristic-zero fields.
noncomputable instance (priority := 100) instInvertibleNatCardOfFiniteCharZero
    (K : Type*) [Field K] [CharZero K] (α : Type*) [Finite α] [Nonempty α] :
    Invertible (Nat.card α : K) := by
  refine invertibleOfNonzero ?_
  exact_mod_cast Nat.card_pos.ne'
