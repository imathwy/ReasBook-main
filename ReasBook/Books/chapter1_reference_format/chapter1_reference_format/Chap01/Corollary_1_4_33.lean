import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Submodule

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (W : Submodule K V)

/- Corollary 1.4.33 (1): every subspace `W` of a finite-dimensional `K`-vector space `V`
has finite codimension, equivalently the quotient space `V ⧸ W` is finite-dimensional. -/
#check (FiniteDimensional.finiteDimensional_quotient W : FiniteDimensional K (V ⧸ W))

/- Corollary 1.4.33 (2): for a subspace `W` of a finite-dimensional `K`-vector space `V`, the
codimension of `W` equals `dim(V) - dim(W)`, formalized by the canonical quotient-dimension
formula. -/
#check (finrank_quotient W :
  Module.finrank K (V ⧸ W) = Module.finrank K V - Module.finrank K W)

end Submodule
