import Mathlib
import StacksProject_2024.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open LinearMap
open scoped Pointwise

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R N] [Module.Finite R M]

-- Proof sketch: a splitting modulo `I ^ n` forces `ker f ⊆ I ^ n N`; since this happens for
-- arbitrarily large `n`, Lemma `10.51.5` gives `ker f = 0`, so `f` is injective. Passing to the
-- quotient `Q = M / f(N)`, the extension class of `0 → N → M → Q → 0` lies in `Ext¹_R(Q, N)`.
-- The split reductions modulo arbitrarily large powers force its image in every large
-- `Ext¹_R(Q / I ^ n Q, N / I ^ n N)` to vanish, and Lemma `10.51.5` again shows the original
-- class is zero. Therefore the short exact sequence splits, giving a retraction of `f`.
/-- Lemma 10.74.1: if a linear map of finite modules over a Noetherian ring becomes split
injective modulo `I ^ n` for arbitrarily large `n`, where `I` lies in the Jacobson radical, then
the original map has a linear retraction and is therefore split injective. -/
theorem exists_retraction_of_split_injective_mod_ideal_pow_frequently
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : N →ₗ[R] M)
    (hsplit :
      ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
          N ⧸ (I ^ n • (⊤ : Submodule R N)),
        s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id) :
    ∃ s : M →ₗ[R] N, s.comp f = LinearMap.id := sorry

end
