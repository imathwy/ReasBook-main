import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation TensorCharacterRing

section

variable {G : Type} [Group G] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: Corollary `11-11.4-5`, deducing connectedness of `Spec (R(G))`.
-- * core/canonical: `tensorCharacterRingPrimeSpectrum_connected`,
--   `PrimeSpectrum.homeomorphOfRingEquiv`, and `Algebra.TensorProduct.lid`.
-- * bridge/view: the standard tensor-product identification `ℤ ⊗R(G) ≃+* R(G)`.
--
-- Sampled owner declarations in this domain:
-- * `tensorCharacterRingPrimeSpectrum_connected`
-- * `PrimeSpectrum.homeomorphOfRingEquiv`
-- * `Algebra.TensorProduct.lid`
--
-- Primitive data: the finite group `G` and LinearRepresentations_Serre_1977's representation ring `R(G)`.
-- Derived API: connectedness of `Spec (R(G))` via the canonical tensor-product identification.
/-- Corollary 11-11.4-5: the prime spectrum `Spec (R(G))` is connected. -/
theorem characterRingPrimeSpectrum_connected :
    ConnectedSpace (PrimeSpectrum (R(G))) := by
  exact
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid ℤ (R(G))).toRingEquiv).connectedSpace_iff.mp
      tensorCharacterRingPrimeSpectrum_connected

end
