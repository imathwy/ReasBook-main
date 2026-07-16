import LinearRepresentations_Serre_1977.Serre.Chap11.Proposition_11_11_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v

noncomputable section

open PrimeSpectrum Representation
open scoped Representation

local notation "P0" => tensorCharacterRingZeroPrimeIdeal

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ] [FaithfulSMul A ℂ]
variable [IsDomain A] [Ring.HasFiniteQuotients A]
variable (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))

noncomputable local instance instFintypeG_r1143 : Fintype G := Fintype.ofFinite G

-- Domain-style sampling pass:
-- * primary domain: prime ideals in Serre's tensor character ring `A ⊗R(G)`.
-- * sampled owner declarations:
--   - `PrimeSpectrum.zeroLocus`
--   - `PrimeSpectrum.mem_zeroLocus`
--   - `PrimeSpectrum.zeroLocus_empty_iff_eq_top`
--   - `tensor_character_ring_prime_ideal_classification`
-- * source-facing layer: the source criterion for ideals of `A ⊗R(G)` stated in terms of the
--   indexed prime families `P₀,c` and `P_{M,c}` from Proposition `11-11.4-1`.
-- * core/canonical layer: `PrimeSpectrum.zeroLocus_empty_iff_eq_top`.
-- * bridge/view layer: the classification theorem reducing an arbitrary prime of `A ⊗R(G)` to
--   one of those indexed owners.
-- Primitive data: the owner ring `A ⊗R(G)` and the canonical prime families `P0`, `Pm`.
-- Derived API: `tensor_character_ring_prime_ideal_classification`.

/-- Remark 11-11.4-3: an ideal of Serre's tensor character ring `A ⊗ R(G)` that is contained in
neither any zero-residual prime `P₀,c` nor any regular prime `P_{M,c}` is the whole ring. -/
theorem tensorCharacterRingIdeal_eq_top_of_not_le_indexed_primes
    (I : Ideal (A ⊗R(G)))
    (h0 : ∀ c : ConjClasses G, ¬ I ≤ (P0 A c).asIdeal)
    (hreg : ∀ (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
      (c : PRegularConjClass G p),
        ¬ I ≤ (tensorCharacterRingRegularPrime (A := A) (G := G) (hroots := hroots) p M c).asIdeal) :
    I = ⊤ := by
  refine zeroLocus_empty_iff_eq_top.mp ?_
  refine Set.eq_empty_iff_forall_notMem.mpr fun P hP ↦ ?_
  have hPI : I ≤ P.asIdeal := by
    simpa [mem_zeroLocus, SetLike.coe_subset_coe] using hP
  rcases tensor_character_ring_prime_ideal_classification (hroots := hroots) P with hP0 | hPm
  · rcases hP0 with ⟨c, rfl⟩
    exact h0 c hPI
  · rcases hPm with ⟨p, M, c, rfl⟩
    exact hreg p M c hPI

/- In the Chapter `11` geometric reading, Proposition `11-11.4-1` supplies the indexed families
`P₀,c` and `P_{M,c}`, while Proposition `11-11.4-2` controls when two such indexed primes
coincide. The line-intersection interpretation belongs to that later equality analysis, not to the
main criterion above. -/

end
