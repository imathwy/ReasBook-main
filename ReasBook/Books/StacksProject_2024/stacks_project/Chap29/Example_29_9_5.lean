import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

/- Source/core/bridge triage:
- `source-facing`: the two statements in Example 29.9.5 about the map on points
  `Spec(ℂ) → Spec(ℝ)` and its base change along itself;
- `core/canonical`: `PrimeSpectrum.comap`, `Complex.conjAe`, and the tensor-product universal
  property behind the standard `ℂ ⊗[ℝ] ℂ` base-change ring;
- `bridge/view`: witnesses for noninjectivity on spectra can be built from the identity and complex
  conjugation maps on `ℂ`, but the source-facing file does not need to expose those witness maps as
  separate public owners.

The example remains source-facing. The public API is just the two spectrum-level statements, stated
directly with the canonical `PrimeSpectrum.comap` owner.
-/

/-- Example 29.9.5 (1): the morphism `Spec(ℂ) → Spec(ℝ)` induced by `ℝ → ℂ` is bijective on
points. -/
theorem complexSpecToRealSpec_bijective :
    Function.Bijective (PrimeSpectrum.comap (algebraMap ℝ ℂ)) := sorry

/-- Example 29.9.5 (2): after base change along `Spec(ℂ) → Spec(ℝ)`, the induced map
`Spec(ℂ ⊗[ℝ] ℂ) → Spec(ℂ)` is not injective. -/
theorem complexTensorSquareSpecToComplexSpec_not_injective :
    ¬ Function.Injective (PrimeSpectrum.comap (algebraMap ℂ (ℂ ⊗[ℝ] ℂ))) := sorry
