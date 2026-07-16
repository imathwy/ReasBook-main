import LinearRepresentations_Serre_1977.Serre.Chap11.Proposition_11_11_4_4
import LinearRepresentations_Serre_1977.Serre.Chap11.Corollary_11_11_4_5.CoefficientRing

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation NumberField

section

variable {G : Type} [Group G] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: Corollary `11-11.4-5`, connectedness of `Spec (R(G))`.
-- * core/canonical: `tensorCharacterRingPrimeSpectrum_connected` applied at the arithmetic
--   coefficient ring `A = 𝓞(ℚ(ζ_{|G|}))` (which satisfies the §11.4 hypothesis bundle, including
--   the `|G|`-th-roots-of-unity hypothesis `hroots`), then the integral-extension connectedness
--   descent `Spec (A ⊗ R(G)) ↠ Spec (R(G))`.
-- * bridge/view: `Corollary_11_11_4_5.connectedSpace_primeSpectrum_of_tensor`.
--
-- This replaces the previous `Algebra.TensorProduct.lid`-at-`A = ℤ` route, which was unsound: the
-- §11.4 chain genuinely requires `A` to contain the `|G|`-th roots of unity, and `A = ℤ` does not.
/-- Corollary 11-11.4-5: the prime spectrum `Spec (R(G))` is connected. -/
theorem characterRingPrimeSpectrum_connected :
    ConnectedSpace (PrimeSpectrum (R(G))) := by
  -- Work over the arithmetic coefficient ring `A = 𝓞(ℚ(ζ_{|G|}))`.
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  letI := Corollary_11_11_4_5.cyclotomicAlgebra (Nat.card G)
  haveI : FaithfulSMul (𝓞 (CyclotomicField (Nat.card G) ℚ)) ℂ :=
    Corollary_11_11_4_5.cyclotomicAlgebra_faithfulSMul (Nat.card G)
  have hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 →
      ((z : ℂ) ∈ Set.range (algebraMap (𝓞 (CyclotomicField (Nat.card G) ℚ)) ℂ)) :=
    Corollary_11_11_4_5.cyclotomicAlgebra_hroots (Nat.card G)
  -- `Spec (A ⊗ R(G))` is connected (the §11.4 main result, now non-vacuous).
  have hconn :
      ConnectedSpace (PrimeSpectrum ((𝓞 (CyclotomicField (Nat.card G) ℚ)) ⊗R(G))) :=
    tensorCharacterRingPrimeSpectrum_connected
      (A := 𝓞 (CyclotomicField (Nat.card G) ℚ)) hroots
  -- Descend connectedness along the integral extension `R(G) → A ⊗ R(G)`.
  haveI := Representation.characterRing_flat_int (G := G)
  exact Corollary_11_11_4_5.connectedSpace_primeSpectrum_of_tensor hconn

end
