import StacksProject_2024.Chap10.Definition_10_161_1
import StacksProject_2024.Chap10.Lemma_10_161_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization and the `N-1`/`N-2` conditions;
* owner abstractions sampled:
  - `IsN1Ring` and `IsN2Ring`, the chapter-owner source-facing classes from
    `Definition_10_161_1`;
  - `isN2Ring_of_finite_extension`, the chapter bridge/view theorem for descending `N-2` along a
    finite extension of domains;
  - `Lemma 10.161.8` / `IsIntegralClosure.finite`, the chapter recall of the canonical finite
    integral-closure theorem for finite separable fraction-field extensions over a Noetherian
    normal domain.
* layer triage:
  - `source-facing`: the equivalence theorem below;
  - `core/canonical`: the owner classes `IsN1Ring` and `IsN2Ring`;
  - `bridge/view`: passing to the normalization `integralClosure R (FractionRing R)` and
    descending `N-2` back to `R` through `isN2Ring_of_finite_extension`.
* primitive data are only the ring `R` together with the Noetherian, domain, and
  characteristic-zero hypotheses. Finiteness of the normalization and separability of finite
  fraction-field extensions are derived API from the owner abstractions and mathlib.
-/

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CharZero (FractionRing R)]

-- Proof sketch: the implication `IsN2Ring R → IsN1Ring R` is the owner instance from
-- `Definition 10.161.1`. For the converse, pass to the normalization
-- `S = integralClosure R (FractionRing R)`, which is finite over `R` by the `N-1` hypothesis.
-- The ring `S` is a Noetherian normal domain with fraction field `FractionRing R`, so every
-- finite extension of its fraction field is separable in characteristic zero and
-- Lemma `10.161.8` / `IsIntegralClosure.finite` makes `S` an `N-2` ring. Then descend `N-2`
-- from `S` to `R` via the finite-extension theorem `isN2Ring_of_finite_extension`.
/-- Lemma 10.161.11: A Noetherian domain whose fraction field has characteristic zero is `N-1`
if and only if it is `N-2`, i.e. Japanese. -/
theorem isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero
    : IsN1Ring R ↔ IsN2Ring R := sorry

end
