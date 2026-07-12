import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Domain-style sampling:
* primary domain: depth and associated primes for finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `associatedPrimes R M`,
  `ringKrullDim (R ⧸ p)`,
  `depth_le_supportDim`;
* best owner abstraction: the local depth owner is the chapter bridge `moduleDepth R M`, while
  associated primes and quotient dimensions are already carried by the mathlib owners
  `associatedPrimes` and `ringKrullDim`;
* source/core/bridge triage:
  `source-facing`: the lower bound on `ringKrullDim (R ⧸ p)` for `p ∈ associatedPrimes R M`;
  `core/canonical`: `moduleDepth`, `associatedPrimes`, and `ringKrullDim`;
  `bridge/view`: the quotient ring `R ⧸ p`.

Primitive data are only the local ring, the finite module, and the associated prime `p`. The
local specialization of depth is derived API from the owner bridge `moduleDepth`, so the theorem
surface should use that bridge rather than restating `Ideal.depth (maximalIdeal R) M`.
-/
-- Proof sketch: induct on `moduleDepth R M`. If the maximal ideal is associated,
-- the depth is `0`. Otherwise choose a nonzerodivisor `x ∈ maximalIdeal R`, note that
-- `x ∉ p` for `p ∈ associatedPrimes R M`, and use the one-step dimension drop for
-- `(R ⧸ p) ⧸ (x)` together with Lemmas `10.72.8` and `10.72.7` to pass to an associated prime of
-- `M / x^n M`, whose depth is one smaller.
/-- Lemma 10.72.9: if `(R, 𝔪)` is a local Noetherian ring, `M` is a finite `R`-module, and
`p ∈ Ass(M)`, then the Krull dimension of `R / p`, written canonically as `ringKrullDim (R ⧸ p)`,
is at least the local depth `moduleDepth R M` of `M`. Since `ringKrullDim` takes values in
`WithBot ℕ∞`, the depth is viewed in the same codomain via the canonical coercions
`WithTop ℕ = ℕ∞ → WithBot ℕ∞`. -/
theorem moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (p : Ideal R)
    (hp : p ∈ associatedPrimes R M) :
    .some (moduleDepth R M) ≤ ringKrullDim (R ⧸ p) := sorry

end
