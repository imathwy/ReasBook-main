import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped Pointwise

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap

/-- A fixed Artin-Rees bound for a linear map with respect to an ideal `I`. -/
def IsArtinReesBound (f : M →ₗ[R] N) (I : Ideal R) (c : ℕ) : Prop :=
  ∀ n ≥ c,
    f.range ⊓ I ^ n • ⊤ ≤ Submodule.map f (I ^ (n - c) • ⊤)

-- Proof sketch: if `y ∈ f(M) ∩ I^n N`, choose `x` with `f x = y`. Then
-- `x ∈ f ⁻¹(I^n N)`, so the preimage equality writes `x = k + x'` with
-- `k ∈ ker f` and `x' ∈ I^(n - c) f ⁻¹(I^c N)`. Applying `f` kills `k`
-- and places `y = f x'` inside `f(I^(n - c) M)`.
/-- Any Artin-Rees equality for the preimages `f ⁻¹(I^n N)` yields an Artin-Rees bound for `f`. -/
theorem isArtinReesBound_of_preimage_pow_smul_eq
    (I : Ideal R) {f : M →ₗ[R] N} {c : ℕ}
    (hc : ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) :
    f.IsArtinReesBound I c := sorry

end LinearMap

namespace Ideal

-- Proof sketch: apply Lemma 10.51.2 to `f.range ≤ N`; this gives the inclusion
-- `f.range ⊓ I^n N ≤ I^(n - c) • f.range`. Pulling the powers of `I` back
-- along `f` gives the corresponding equality for `f ⁻¹(I^n N)`, and `Submodule.map_smul''`
-- identifies `I^(n - c) • f.range` with `f(I^(n - c) M)`.
/-- A linear map into a finite module over a Noetherian ring has an Artin-Rees constant for the
inverse images of the powers of `I`. -/
theorem exists_exact_preimage_pow_smul_eq [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) := sorry

-- Proof sketch: specialize the owner theorem above to the exact sequence
-- `0 → K → M → N`, then rewrite `LinearMap.ker f` as `K` using exactness.
/-- Lemma 10.51.3: if `0 → K → M → N` is an exact sequence of finite modules over a Noetherian
ring and `I` is an ideal of `R`, then there is a single Artin-Rees constant controlling both the
preimages `f ⁻¹(I^n N)` and the intersections `f(M) ∩ I^n N`. -/
theorem exists_artin_rees_constant_of_exact [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) {K : Submodule R M} {f : M →ₗ[R] N}
    (h_exact : Function.Exact K.subtype f) :
    ∃ c : ℕ,
      (∀ n ≥ c,
        Submodule.comap f (I ^ n • ⊤) = K ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) ∧
        f.IsArtinReesBound I c := sorry

end Ideal

end
