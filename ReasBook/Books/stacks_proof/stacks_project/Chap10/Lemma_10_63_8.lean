import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum Module.associatedPrimes

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage: this item lies in commutative algebra of module support and associated primes.
The core owner abstraction is mathlib's `associatedPrimes R M`; the theorem below is a
source-facing bridge from minimal support points to membership in that owner set.
-/

namespace Module

/-- Lemma 10.63.8: if a prime point `𝔭` is minimal in the support of an `R`-module `M` over a
Noetherian ring, then its underlying ideal is an associated prime of `M`. -/
-- Proof sketch: choose `m : M` with `(R ∙ m).annihilator ≤ 𝔭.asIdeal`. The cyclic submodule
-- `R ∙ m` is finite, and minimality of `𝔭` in `Supp(M)` makes `𝔭` minimal in `Supp(R ∙ m)` as
-- well. A minimal prime of the annihilator of `R ∙ m` lying under `𝔭.asIdeal` must then equal
-- `𝔭.asIdeal`, so the canonical theorem
-- `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes` gives
-- `𝔭.asIdeal ∈ associatedPrimes R (R ∙ m)`. Finally, associated primes are preserved by the
-- owner theorem `associatedPrimes.subset_of_injective` for the injective subtype map `R ∙ m ↪ M`.
@[stacks 05BV]
theorem minimal_support_mem_associatedPrimes
    (𝔭 : PrimeSpectrum R)
    (h𝔭 : Minimal (· ∈ support R M) 𝔭) :
    𝔭.asIdeal ∈ associatedPrimes R M := by
  obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp h𝔭.1
  let N : Submodule R M := R ∙ m
  have h𝔭_span : 𝔭 ∈ support R N := mem_support_iff_of_finite.mpr hm
  have h𝔭_span_min : Minimal (· ∈ support R N) 𝔭 := by
    refine ⟨h𝔭_span, fun q hq hq𝔭 ↦ ?_⟩
    exact h𝔭.2 (support_subset_of_injective N.subtype N.subtype_injective hq) hq𝔭
  obtain ⟨q, hq, hq𝔭⟩ := Ideal.exists_minimalPrimes_le hm
  let q' : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hq' : q' ∈ support R N := mem_support_iff_of_finite.mpr hq.1.2
  have h𝔭q : 𝔭 ≤ q' := h𝔭_span_min.2 hq' hq𝔭
  have hq_eq : q = 𝔭.asIdeal := le_antisymm hq𝔭 h𝔭q
  have h𝔭_assoc_span : 𝔭.asIdeal ∈ associatedPrimes R N := by
    have h𝔭_min : 𝔭.asIdeal ∈ (Module.annihilator R N).minimalPrimes := by
      simpa [hq_eq] using hq
    exact minimalPrimes_annihilator_subset_associatedPrimes R N h𝔭_min
  exact associatedPrimes.subset_of_injective N.subtype_injective h𝔭_assoc_span

end Module

end
