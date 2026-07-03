import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Pointwise

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

namespace Ideal

-- Proof sketch: apply the canonical owner theorem `exists_pow_inf_eq_pow_smul`, then replace the
-- index `k` by `k + 1` so the same equality holds with a strictly positive constant.
/-- Lemma 10.51.2 (Artin-Rees): for a finite `R`-module `M` over a Noetherian ring, an ideal `I`,
and a submodule `N`, there is a positive integer `c` such that `I^n M ∩ N = I^(n - c) (I^c M ∩ N)`
for all `n ≥ c`. -/
theorem exists_pos_pow_inf_eq_pow_smul (I : Ideal R) (N : Submodule R M) :
    ∃ c > 0, ∀ n ≥ c,
      I ^ n • ⊤ ⊓ N = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  have hk_succ : I ^ (k + 1) • ⊤ ⊓ N = I • (I ^ k • ⊤ ⊓ N) := by
    simpa using hk (k + 1) (Nat.le_succ k)
  refine ⟨k + 1, Nat.succ_pos _, ?_⟩
  intro n hn
  have hkn : k ≤ n := Nat.le_trans (Nat.le_succ k) hn
  calc
    I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
      hk n hkn
    _ = I ^ ((n - (k + 1)) + 1) • (I ^ k • ⊤ ⊓ N) := by
      rw [show n - k = (n - (k + 1)) + 1 by omega]
    _ = I ^ (n - (k + 1)) • (I ^ (k + 1) • ⊤ ⊓ N) := by
      rw [pow_add, pow_one, ← smul_smul, ← hk_succ]

end Ideal

end
