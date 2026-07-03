import StacksProject_2024.Chap15.Lemma_15_126_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Domain triage:
-- * primary domain: Hilbert-Samuel multiplicity bounds for parameter ideals in Noetherian local
--   rings;
-- * sampled owner API: `parameterIdeal`, `IsSystemOfParameters`,
--   `hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters`,
--   `minimalPrimes.finite_of_isNoetherianRing`;
-- * core/canonical: the chosen parameter family `g` together with its owner ideal
--   `parameterIdeal g`;
-- * source-facing: count the top-dimensional minimal primes `p` of `R`, equivalently those with
--   `ringKrullDim (R ⧸ p) = ringKrullDim R`, and compare that count with the canonical quotient
--   length of `R ⧸ parameterIdeal g`.
-- Primitive-vs-derived split:
-- * primitive data: the local Noetherian ring and the chosen family `g` with
--   `hg : IsSystemOfParameters g`;
-- * derived API: the top-dimensional minimal-prime subset cut out by the ambient dimension and
--   the resulting length bound in `ℕ∞`.

-- Proof sketch: filter the reduced ring by the product of its top-dimensional minimal-prime
-- quotients, so the cokernel has support of dimension `< d`. Hilbert-Samuel theory for the
-- parameter ideal of `g` shows that the leading coefficient of the length polynomial of the product
-- is at least the number of top-dimensional minimal primes, while the lower-dimensional error terms
-- do not affect the leading coefficient. Then apply Lemma `15.126.7`.
/-- Lemma 15.126.8: let `(R, 𝔪)` be a Noetherian local ring, let `g₁, …, g_d` be a system of
parameters, written as `g : Fin d → maximalIdeal R`, and let `t` be the number of minimal prime
ideals `𝔭` of `R` with `ringKrullDim (R ⧸ 𝔭) = ringKrullDim R`. Then `t` is at most the length of
`R / (g₁, …, g_d)`, written canonically as `Module.length R (R ⧸ parameterIdeal g)`. -/
theorem encard_topDimMinimalPrimes_le_length_quotient_parameterIdeal_of_isSystemOfParameters
    {d : ℕ} (g : Fin d → maximalIdeal R) (hg : IsSystemOfParameters g) :
    ({ p : Ideal R | p ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R }).encard ≤
      Module.length R (R ⧸ parameterIdeal g) := sorry

end
