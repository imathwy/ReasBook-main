import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R₁ : Type u} {R₂ : Type v} [CommSemiring R₁] [CommSemiring R₂]

/- Lemma 10.21.2 (00ED): if `R = R₁ × R₂`, then the projection maps `R → R₁` and `R → R₂`
induce continuous maps `Spec(R₁) → Spec(R)` and `Spec(R₂) → Spec(R)`, and the induced map from
the disjoint union `Spec(R₁) ⨿ Spec(R₂)` to `Spec(R)` is a homeomorphism. Equivalently, this is
the owner-level mathlib homeomorphism `PrimeSpectrum (R₁ × R₂) ≃ₜ PrimeSpectrum R₁ ⊕
PrimeSpectrum R₂`, whose ring-specialized form is exactly the source statement.
-/
recall PrimeSpectrum.primeSpectrumProdHomeo

end
