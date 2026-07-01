import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Serre.Chap06.Proposition_6_6_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra

universe u v

section

variable {k : Type u} {G : Type v}
variable [Field k] [CharZero k] [Group G] [Finite G]

local instance : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩

-- Source/core/bridge triage:
-- * source-facing: the Wedderburn-Artin decomposition statement for the group algebra `k[G]`.
-- * core/canonical: `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`.
-- * bridge/view: the characteristic-zero specialization supplying the Maschke input
--   `NeZero (Nat.card G : k)`.
/- Corollary 6-6.1-2: the group algebra `k[G]` is isomorphic, as a `k`-algebra, to a finite
product of matrix algebras over division `k`-algebras of finite dimension over `k`. This is the
characteristic-zero specialization of the canonical Wedderburn-Artin owner theorem. -/
#check IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k k[G]

end
