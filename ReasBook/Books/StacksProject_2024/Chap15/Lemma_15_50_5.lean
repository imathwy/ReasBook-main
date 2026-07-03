import Mathlib
import StacksProject_2024.Chap10.Lemma_10_166_5
import StacksProject_2024.Chap15.Lemma_15_46_5
import StacksProject_2024.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u

section

variable {p : ℕ} [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]
variable (n : ℕ)

local notation "A" => mixedPowerSeriesPolynomialRing (Fin n) (Fin n) k

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (𝔭 : PrimeSpectrum A)

/- Domain triage:
- primary domain: mixed power-series/polynomial rings, completed localizations, and geometric
  regularity of generic formal fibers in commutative algebra;
- sampled owner declarations:
  `mixedPowerSeriesPolynomialRing`,
  `CompletedLocalizationAtPrime`,
  `IsGeometricallyRegular`,
  `IsGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: this numbered lemma is `source-facing`, while the public surface should
  use the canonical chapter owners `mixedPowerSeriesPolynomialRing` and `R̂_[𝔭]`; the prime-pair
  formal-fiber criterion from Lemma `15.50.2` is only a `bridge/view`;
- primitive data: the ambient ring
  `A = mixedPowerSeriesPolynomialRing (Fin n) (Fin n) k`, a fraction field `K` of `A`, and a
  prime `𝔭 : Spec A`;
- derived API: geometric regularity of the generic formal fiber `R̂_[𝔭] ⊗[A] K`.
-/
-- Proof sketch: use the characteristic-`p` criterion for geometric regularity over the field `K`
-- by testing finite purely inseparable extensions `L/K`. Realize such an `L` as the fraction
-- field of a finite purely inseparable extension of the mixed power-series/polynomial ring,
-- reduce by induction to the degree-`p` case, identify the base change of the completed
-- localization with an `AdjoinRoot (X ^ p - f)` over a regular intermediate ring, and then apply
-- the derivation-extension and regularity criteria from Lemmas `15.48.1`, `15.48.4`, and
-- `15.48.5`.
/-- Lemma 15.50.5: let `A = k[[x_1, ..., x_n]][y_1, ..., y_n]` over a field `k` of
characteristic `p`, and let `K` be a fraction field of `A`. For every prime `𝔭` of `A`, the
generic formal fiber `(A_𝔭)^∧ ⊗[A] K` is geometrically regular over `K`. -/
theorem mixedPowerSeriesPolynomialRing_formalFiber_fractionRing_isGeometricallyRegular
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    : IsGeometricallyRegular K (R̂_[𝔭] ⊗[A] K) := sorry

end

end
