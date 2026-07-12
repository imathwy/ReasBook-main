import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage: this file is in the commutative algebra of localization stability for the
source-facing `N-1` and `N-2` properties of domains.

Owner abstractions sampled for this item:
- `IsN1Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsN2Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsLocalization.integralClosure`, the canonical localization owner for normalization;
- `integralClosure.isFractionRing_of_finite_extension`, the canonical fraction-field owner used to
  compare finite extensions before and after localization.

Primitive data here are only the localization datum `R → Rₘ` and the owner assumptions
`[IsN1Ring R]` or `[IsN2Ring R]`. The finiteness statements for integral closures and the
fraction-ring identifications are derived API internal to the proofs. These results should stay as
theorems, not global instances: the localization parameter `M` is genuine primitive data and is
not recoverable from the target ring `Rₘ` alone.

Layer triage:
- `source-facing`: localization preserves the textbook `N-1` and `N-2` properties;
- `core/canonical`: `IsN1Ring`, `IsN2Ring`, `IsLocalization.integralClosure`, and fraction-ring
  comparison for finite extensions;
- `bridge/view`: the proof-level transport of finite integral-closure modules across the chosen
  localization.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable (M : Submonoid R) {Rₘ : Type v} [CommRing Rₘ] [Algebra R Rₘ]
  [IsLocalization M Rₘ] [IsDomain Rₘ]

/-- Lemma 10.161.3 (1): any localization of an N-1 domain that is still a domain is again
N-1. -/
-- Proof sketch: identify `FractionRing R` as a fraction ring of the chosen localization `Rₘ`,
-- localize the
-- finite `R`-module `integralClosure R (FractionRing R)`, and then use
-- `IsLocalization.integralClosure` to identify that localization with
-- `integralClosure Rₘ (FractionRing R)`.
theorem isN1Ring_of_isLocalization (M : Submonoid R) [IsLocalization M Rₘ] [IsN1Ring R] :
    IsN1Ring Rₘ := sorry

/-- Lemma 10.161.3 (2): any localization of an N-2 domain that is still a domain is again
N-2. -/
-- Proof sketch: for a finite extension `L / FractionRing Rₘ`, transport the
-- fraction-ring structure along localization so that `L` is also a finite extension of
-- `FractionRing R`; apply the `N-2` hypothesis on `R`, then use localization of finite modules and
-- `IsLocalization.integralClosure` to obtain finiteness for the localized integral closure.
theorem isN2Ring_of_isLocalization (M : Submonoid R) [IsLocalization M Rₘ] [IsN2Ring R] :
    IsN2Ring Rₘ := sorry

end
