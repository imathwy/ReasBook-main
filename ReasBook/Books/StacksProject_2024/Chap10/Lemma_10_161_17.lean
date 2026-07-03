import Mathlib
import StacksProject_2024.Chap10.Lemma_10_161_16_Tate
import StacksProject_2024.Chap10.Lemma_10_161_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped PowerSeries

section

/-
Domain-style sampling:
* primary domain: commutative algebra of Japanese (`N-2`) domains, finite normalization, and
  the one-variable formal power series construction;
* source/core/bridge triage:
  - `source-facing`: the stability of the `N-2` property under adjoining one formal parameter;
  - `core/canonical`: the chapter owner `IsN2Ring`;
  - `bridge/view`: the Tate criterion
    `isN2Ring_of_normal_of_adicComplete_of_principal_quotient_isN2Ring`, finite-extension descent
    `isN2Ring_of_finite_extension`, the normalization-permanence bridge
    `isN2Ring_integralClosure_fractionRing`, and the canonical `(X)`-quotient map on `R⟦X⟧`;
* sampled owner declarations:
  - `IsN2Ring`;
  - `isN2Ring_of_normal_of_adicComplete_of_principal_quotient_isN2Ring`;
  - `isN2Ring_of_finite_extension`;
  - `integralClosure`.

The primitive source data are just the Noetherian domain `R` and the owner hypothesis
`[IsN2Ring R]`. The finite normalization of `R`, the `PowerSeries.map` extension, and the
identification of the quotient by `(X)` with the coefficient ring are derived proof-level API from
the sampled owners, so this file should state only the owner-level conclusion and should not
introduce any local wrapper for those constructions.
-/

-- Proof sketch: if `R' = integralClosure R (FractionRing R)`, then for any finite extension `L`
-- of `FractionRing R`, the integral closure of `R'` in `L` agrees with the integral closure of
-- `R` in `L` inside the ambient field extension. The `N-2` hypothesis on `R` makes that larger
-- integral closure finite over `R`; since `R'` is itself finite over `R`, the same ring is a
-- finite `R'`-algebra, so `R'` is again `N-2`.
/-- The normalization of a Noetherian `N-2` domain in its fraction field is again `N-2`. -/
theorem isN2Ring_integralClosure_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsN2Ring R] :
    IsN2Ring (integralClosure R (FractionRing R)) := sorry

/-- Lemma 10.161.17: if `R` is a Noetherian domain and `R` is `N-2`, then the formal power
series ring `R⟦X⟧` is `N-2`. -/
-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`. The owner
-- hypothesis `[IsN2Ring R]` gives that `R'` is finite over `R` and, by
-- `isN2Ring_integralClosure_fractionRing`, that `R'` is itself `N-2`; hence `R'⟦X⟧` is finite
-- over `R⟦X⟧`. The ring `R'⟦X⟧` is a normal Noetherian domain, and the
-- canonical quotient by `(PowerSeries.X)` identifies with `R'` via `PowerSeries.constantCoeff`, so
-- the Tate criterion
-- `isN2Ring_of_normal_of_adicComplete_of_principal_quotient_isN2Ring` applies to `R'⟦X⟧`.
-- Finally descend `N-2` from `R'⟦X⟧` to `R⟦X⟧` via
-- `isN2Ring_of_finite_extension`.
theorem isN2Ring_powerSeries
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsN2Ring R] :
    IsN2Ring R⟦X⟧ := sorry

end
