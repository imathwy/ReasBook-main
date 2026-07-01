import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe uK uV

namespace Submodule

variable {K : Type uK} {V : Type uV} [DivisionRing K] [AddCommGroup V] [Module K V]

-- Proof sketch: The inclusion `W₂ ≤ W₁` induces a quotient map `V ⧸ W₂ →ₗ[K] V ⧸ W₁`.
-- Since both quotients are finite-dimensional and have the same dimension, this map should be an
-- isomorphism. Its kernel identifies with `W₁ / W₂`, so that quotient is trivial and hence
-- `W₁ = W₂`.
/-- Exercise 1.4.34: if `W₂ ≤ W₁` are finite-codimensional subspaces of `V` with the same
codimension, then the two subspaces are equal. -/
theorem eq_of_le_of_finrank_quotient_eq {W₁ W₂ : Submodule K V} (hW : W₂ ≤ W₁)
    [FiniteDimensional K (V ⧸ W₂)]
    (hcodim : Module.finrank K (V ⧸ W₁) = Module.finrank K (V ⧸ W₂)) : W₁ = W₂ := by
  let U : Submodule K (V ⧸ W₂) := W₁.map W₂.mkQ
  have hquot : Module.finrank K ((V ⧸ W₂) ⧸ U) = Module.finrank K (V ⧸ W₁) := by
    simpa [U] using (quotientQuotientEquivQuotient W₂ W₁ hW).finrank_eq
  have hUfinrank : Module.finrank K U = 0 := by
    have hfinrank := U.finrank_quotient_add_finrank
    rw [hquot, hcodim] at hfinrank
    omega
  have hUbot : U = ⊥ := finrank_eq_zero.mp hUfinrank
  refine le_antisymm ?_ hW
  intro x hx
  have hxU : W₂.mkQ x ∈ U := ⟨x, hx, rfl⟩
  have hx0 : W₂.mkQ x = 0 := by
    simpa [hUbot] using hxU
  exact (Submodule.Quotient.mk_eq_zero W₂).mp <| by
    simpa using hx0

end Submodule
