import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']
variable {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}

/-
Domain triage:
- primary domain: commutative algebra of weakly associated primes under injective maps and exact
  sequences;
- sampled owner-style declarations of the same kind:
  `associatedPrimes.subset_of_injective`,
  `associatedPrimes.subset_union_of_exact`,
  `associatedPrimesOfModule.subset_of_injective`,
  `associatedPrimesOfModule.subset_union_of_exact`;
- owner abstraction: the chapter declaration `weaklyAssociatedPrimes R M`, parallel to mathlib's
  owner set `associatedPrimes`;
- primitive data: modules and linear maps in an injective map or exact sequence;
- derived API: inclusions between the owner sets attached to those modules.

This file therefore belongs at the `core/canonical` layer, with no additional source-facing
wrapper or packaging declaration.
-/
namespace weaklyAssociatedPrimes

/-- Canonical owner-form of Lemma 10.66.4 (1): an injective linear map sends weakly associated
primes into weakly associated primes. -/
theorem subset_of_injective (hf : Function.Injective f) :
    weaklyAssociatedPrimes R M' ⊆ weaklyAssociatedPrimes R M := sorry

-- Proof sketch: if `𝔭` is weakly associated to `M'`, localize at `𝔭` and use the exact sequence
-- `0 → M'_𝔭 → M_𝔭 → M''_𝔭`. An element of `M_𝔭` whose annihilator has radical `𝔭R_𝔭` either comes
-- from `M'_𝔭` or has nonzero image in `M''_𝔭`, yielding weak association to `M'_𝔭` or `M''_𝔭`.
/-- Canonical owner-form of Lemma 10.66.4 (2): if `0 → M' → M → M''` is exact, then every weakly
associated prime of `M` is weakly associated to `M'` or to `M''`. -/
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    weaklyAssociatedPrimes R M ⊆ weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' :=
  sorry

end weaklyAssociatedPrimes

/- Lemma 10.66.4 (1): the source states this for a short exact sequence
`0 → M' → M → M'' → 0`; the owner theorem is the more general
`weaklyAssociatedPrimes.subset_of_injective`. -/
recall weaklyAssociatedPrimes.subset_of_injective

/- Lemma 10.66.4 (2): the source states this for a short exact sequence
`0 → M' → M → M'' → 0`; the owner theorem is the more general
`weaklyAssociatedPrimes.subset_union_of_exact`. -/
recall weaklyAssociatedPrimes.subset_union_of_exact

end
