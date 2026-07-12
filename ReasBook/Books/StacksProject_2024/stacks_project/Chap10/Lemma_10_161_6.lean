import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped LaurentPolynomial

universe u

/-
Domain triage:
- primary domain: `N-1` rings under Laurent-polynomial extension;
- layer: `source-facing`;
- core/canonical owner: `IsN1Ring`;
- sampled bridge/view declarations:
  `R[T;T⁻¹]`, `IsLocalization.Away (X : R[X]) R[T;T⁻¹]`, and `Polynomial.toLaurentAlg`;
- primitive data: the base ring `R` and the canonical Laurent-polynomial ring `R[T;T⁻¹]`;
- derived API: `IsN1Ring.integralClosure_finite`.

The public surface should therefore speak directly about `IsN1Ring R[T;T⁻¹]`, while leaving the
localization presentation as an internal bridge rather than a second owner-level wrapper.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`, and let `S'` be the
-- integral closure of `R[T;T⁻¹]` in its fraction field. The `N-1` hypothesis makes `S'` finite
-- over the Laurent polynomial ring. Expanding finitely many generators as finite Laurent sums
-- shows every element of `R'` lies in a finite `R`-submodule of `FractionRing R`; since `R` is
-- Noetherian, `R'` is finite over `R`.
/-- Lemma 10.161.6: if `R` is a Noetherian domain and the Laurent polynomial ring
`R[z, z^{-1}]`, formalized by the canonical owner `R[T;T⁻¹]`, is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_isN1Ring_laurentPolynomial
    (hLaurent : IsN1Ring R[T;T⁻¹]) :
    IsN1Ring R := sorry

end
