import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

-- Proof sketch: contraction along an integral ring map is strictly monotone on prime ideals.
-- Indeed, if `q ⊊ q'` in `S`, choose `x ∈ q' \ q`; since `x` is integral over `R`,
-- `Ideal.comap_lt_comap_of_integral_mem_sdiff` shows `q ∩ R ⊊ q' ∩ R`. Applying the canonical
-- order-theoretic Krull-dimension monotonicity theorem to `PrimeSpectrum.comap (algebraMap R S)`
-- gives the result directly.
/-- Lemma 10.112.3 (1): if `R → S` is an integral ring map, then the Krull dimension of `S` is at
most the Krull dimension of `R`. -/
theorem ringKrullDim_le_of_isIntegral :
    ringKrullDim S ≤ ringKrullDim R := by
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun {q q'} hqq' ↦ by
    change Ideal.comap (algebraMap R S) q.asIdeal < Ideal.comap (algebraMap R S) q'.asIdeal
    have hqq'_ideal : q.asIdeal < q'.asIdeal := by
      simpa using hqq'
    rcases SetLike.lt_iff_le_and_exists.mp hqq'_ideal with ⟨hqq', x, hxq', hxq⟩
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hqq' ⟨hxq', hxq⟩
      (Algebra.IsIntegral.isIntegral x)

/- Lemma 10.112.3 (2): if `q` is a closed point of `Spec(S)` for an integral ring map `R → S`,
then its image in `Spec(R)` is a closed point. This is exactly the canonical mathlib theorem
`PrimeSpectrum.isClosed_comap_singleton_of_isIntegral` specialized to `algebraMap R S`. -/
recall PrimeSpectrum.isClosed_comap_singleton_of_isIntegral

end
