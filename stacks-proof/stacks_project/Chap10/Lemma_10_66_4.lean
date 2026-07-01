import Mathlib
import stacks_project.Chap10.Definition_10_66_1
import stacks_project.Chap10.Lemma_10_66_2

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

namespace Ideal

/-- Helper for Lemma 10.66.4: an injective linear map preserves the torsion ideal of a chosen
element. -/
lemma torsionOf_map_eq_of_injective (hf : Function.Injective f) (m : M') :
    Ideal.torsionOf R M (f m) = Ideal.torsionOf R M' m := by
  -- Compare membership in the two torsion ideals pointwise via injectivity of `f`.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply hf
    simpa using ha
  · intro ha
    simpa using congrArg f ha

end Ideal

/-- Helper for Lemma 10.66.4: an associated-prime witness at the maximal ideal of the localization
at `p` descends to a weakly associated prime over the original ring. -/
lemma localized_maximalIdeal_weakAss_of_associated
    (p : Ideal R) [p.IsPrime] {X : Type*} [AddCommGroup X] [Module R X]
    (hp :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p X)) :
    p ∈ weaklyAssociatedPrimes R X := by
  -- Lemma `10.66.2` identifies weak association at `p` with association of the maximal ideal
  -- after localizing at `p`.
  rw [mem_weaklyAssociatedPrimes_iff]
  exact
    (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
      (R := R) (M := X) p).2 hp

/-- Canonical owner-form of Lemma 10.66.4 (1): an injective linear map sends weakly associated
primes into weakly associated primes. -/
theorem subset_of_injective (hf : Function.Injective f) :
    weaklyAssociatedPrimes R M' ⊆ weaklyAssociatedPrimes R M := by
  intro p hp
  rw [mem_weaklyAssociatedPrimes_iff] at hp ⊢
  rcases hp with ⟨m, hm⟩
  -- Preserve the witness element and rewrite its torsion ideal through the injective map.
  refine ⟨f m, ?_⟩
  simpa [Ideal.torsionOf_map_eq_of_injective (R := R) (f := f) hf m] using hm

-- Proof sketch: if `𝔭` is weakly associated to `M'`, localize at `𝔭` and use the exact sequence
-- `0 → M'_𝔭 → M_𝔭 → M''_𝔭`. An element of `M_𝔭` whose annihilator has radical `𝔭R_𝔭` either comes
-- from `M'_𝔭` or has nonzero image in `M''_𝔭`, yielding weak association to `M'_𝔭` or `M''_𝔭`.
/-- Canonical owner-form of Lemma 10.66.4 (2): if `0 → M' → M → M''` is exact, then every weakly
associated prime of `M` is weakly associated to `M'` or to `M''`. -/
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    weaklyAssociatedPrimes R M ⊆ weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' :=
  by
    intro p hp
    rw [mem_weaklyAssociatedPrimes_iff] at hp
    have hp_prime : p.IsPrime := hp.isPrime
    letI : p.IsPrime := hp_prime
    -- Localize at the weakly associated prime `p` and convert to an associated-prime statement.
    have hp_assoc :
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
          associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
      rw [AssociatedPrimes.mem_iff]
      exact
        (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
          (R := R) (M := M) p).1 hp
    have hf_loc : Function.Injective (LocalizedModule.map p.primeCompl f) :=
      LocalizedModule.map_injective p.primeCompl f hf
    have hfg_loc :
        Function.Exact (LocalizedModule.map p.primeCompl f) (LocalizedModule.map p.primeCompl g) :=
      LocalizedModule.map_exact p.primeCompl f g hfg
    -- Exactness survives localization, so the associated-prime union theorem applies upstairs.
    have hp_union :
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
          associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M') ∪
            associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M'') :=
      associatedPrimes.subset_union_of_exact
        (R := Localization.AtPrime p)
        (M := LocalizedModule.AtPrime p M')
        (M' := LocalizedModule.AtPrime p M)
        (M'' := LocalizedModule.AtPrime p M'')
        (f := LocalizedModule.map p.primeCompl f)
        (g := LocalizedModule.map p.primeCompl g)
        hf_loc hfg_loc hp_assoc
    rw [Set.mem_union]
    rcases hp_union with hp_left | hp_right
    · -- Descend the localized associated-prime conclusion back to a weakly associated prime of `M'`.
      left
      exact localized_maximalIdeal_weakAss_of_associated
        (R := R) (X := M') p (AssociatedPrimes.mem_iff.mp hp_left)
    · -- The same descent works for the quotient module `M''`.
      right
      exact localized_maximalIdeal_weakAss_of_associated
        (R := R) (X := M'') p (AssociatedPrimes.mem_iff.mp hp_right)

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
