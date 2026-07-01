import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.14 (1): let `R → S` be a ring map and let `f₁, …, fₙ ∈ R` generate the unit
ideal. If each localized map `R_{fᵢ} → S_{fᵢ}` is integral, then `R → S` is integral. This is
exactly the canonical mathlib theorem `RingHom.isIntegral_ofLocalizationSpan`. -/
recall RingHom.isIntegral_ofLocalizationSpan :
  RingHom.OfLocalizationSpan RingHom.IsIntegral

/- Lemma 10.36.14 (2): let `R → S` be a ring map and let `f₁, …, fₙ ∈ R` generate the unit
ideal. If each localized map `R_{fᵢ} → S_{fᵢ}` is finite, then `R → S` is finite. This is exactly
the canonical mathlib theorem `RingHom.finite_ofLocalizationSpan`. -/
recall RingHom.finite_ofLocalizationSpan :
  RingHom.OfLocalizationSpan RingHom.Finite
