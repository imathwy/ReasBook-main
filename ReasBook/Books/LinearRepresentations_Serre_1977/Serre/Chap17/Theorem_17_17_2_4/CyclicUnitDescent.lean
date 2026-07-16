import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap09.Corollary_9_9_2_2
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1

open scoped Representation TensorProduct
open CategoryTheory

noncomputable section

universe u

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Theorem 17-17.2-4: the exact unit-witness property needed in the ordinary row.

Once a theorem-local cyclic induction owner `f` satisfies this proposition, the remaining step in
the main file is the formal source-faithful multiplication argument `y = 1 * y`. -/
def HasCyclicRationalizedUnitPreimage
    (f :
      (Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1)) →ₗ[ℚ]
        ℚ ⊗[ℤ] R₀[k](G)) : Prop :=
  ∃ N : ℕ, N ≠ 0 ∧
    ∃ ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1),
      f ξ = (N : ℚ) •
        ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)))

end

end Representation
