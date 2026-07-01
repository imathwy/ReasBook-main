import Mathlib
import stacks_project.Chap10.Lemma_10_91_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Module

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain triage:
- `source-facing`: the Stacks lemma for the formal power series ring `MvPowerSeries (Fin n) R`;
- `core/canonical`: the owner predicates `Module.Flat` and `Module.MittagLeffler`;
- `bridge/view`: `MvPowerSeries σ R` is definitionally the product module `(σ →₀ ℕ) → R`, so the
  whole statement is a direct specialization of `noetherian_pi_flat_and_mittagLeffler`.
Primitive data are only the ring `R` and the monomial index type `(Fin n) →₀ ℕ`; the flat and
Mittag-Leffler clauses are derived API of the owner predicates. -/

/-- Lemma 10.91.4: for a Noetherian ring `R` and an integer `n`, the formal power series ring
`MvPowerSeries (Fin n) R`, viewed as an `R`-module, is flat and Mittag-Leffler. -/
lemma noetherian_mvPowerSeries_flat_and_mittagLeffler (n : ℕ) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      MittagLeffler R (MvPowerSeries (Fin n) R) := by
  simpa [MvPowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat R (((Fin n) →₀ ℕ) → R) ∧ MittagLeffler R (((Fin n) →₀ ℕ) → R))

end

end Module
