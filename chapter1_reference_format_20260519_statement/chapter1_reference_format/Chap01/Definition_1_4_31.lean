import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe uK uV

namespace Submodule

variable {K : Type uK} {V : Type uV} [DivisionRing K] [AddCommGroup V] [Module K V]
variable (W : Submodule K V)

/- Definition 1.4.31: a subspace has finite codimension precisely when the quotient `V ⧸ W`
is finite-dimensional over `K`. -/
#check (FiniteDimensional K (V ⧸ W))

/- The codimension of a subspace is the `K`-dimension of the quotient space `V ⧸ W`. -/
#check (Module.rank K (V ⧸ W))

/-- A hyperplane is a subspace of codimension one. -/
def IsHyperplane : Prop :=
  Module.rank K (V ⧸ W) = 1

@[simp] theorem isHyperplane_iff_rank_quotient_eq_one :
    W.IsHyperplane ↔ Module.rank K (V ⧸ W) = 1 :=
  Iff.rfl

theorem isHyperplane_iff_finrank_quotient_eq_one [FiniteDimensional K (V ⧸ W)] :
    W.IsHyperplane ↔ Module.finrank K (V ⧸ W) = 1 := by
  rw [isHyperplane_iff_rank_quotient_eq_one, ← Module.finrank_eq_rank]
  constructor <;> intro h <;> exact_mod_cast h

end Submodule
