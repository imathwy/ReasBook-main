import Mathlib
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap15.Lemma_15_47_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: the regular locus on `PrimeSpectrum R` and the chapter owners `IsJ0Ring` and
  `IsJ1Ring`;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.regularLocus`,
  `isJ0Ring_iff_exists_nonempty_open_subset_regularLocus`,
  `isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`;
- best owner abstraction: the source-facing criterion from Lemma `15.47.2` is the canonical owner
  bridge for proving `IsJ1Ring R`, while the hypotheses `IsJ0Ring (R ⧸ p.asIdeal)` are derived
  input on the quotient spectra `Spec (R ⧸ p) ≃ V(p)`;
- primitive vs. derived: the primitive public data are just the ring `R` and the owner hypothesis
  that each prime quotient is `J-0`. The required open subsets of `V(p)` are derived via the
  quotient-spectrum owner bridge, so they should not be packaged as a separate local wrapper API.

Source/core/bridge triage:
- `source-facing`: the chapter lemma asserting that `J-0` prime quotients force `R` to be `J-1`;
- `core/canonical`: `Reg(Spec R)`, `IsJ0Ring`, and `IsJ1Ring`;
- `bridge/view`: the homeomorphism `Spec (R ⧸ p) ≃ V(p)` transporting the quotient regular locus
  back to the closed subset `V(p)`.
-/

-- Proof sketch: apply the criterion of Lemma `15.47.2`. For a regular prime `p`, choose a
-- regular sequence generating `p` after localizing and then after shrinking to a principal open.
-- For any prime `q ⊇ p` whose image in `Spec (R ⧸ p)` is regular, the quotient local ring
-- `R_q / p R_q` is regular; the regular-sequence criterion for regular local rings then implies
-- that `R_q` is regular. Since `R ⧸ p` is `J-0`, this yields the required nonempty open subset of
-- `V(p)` contained in the regular locus, so Lemma `15.47.2` gives that `R` is `J-1`.
/-- Lemma 15.47.3: if `R` is a Noetherian ring and for every prime `p` of `R` the quotient
ring `R ⧸ p` is `J-0`, then `R` is `J-1`. -/
theorem isJ1Ring_of_isJ0Ring_quotient_by_prime
    (hquot : ∀ p : PrimeSpectrum R, IsJ0Ring (R ⧸ p.asIdeal)) :
    IsJ1Ring R := by
  rw [isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset]
  intro p hp
  obtain ⟨V, hV_open, hV_nonempty, hV_reg⟩ :=
    (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).mp (hquot p)
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal
  have hV_reg_zeroLocus :
      ∀ x ∈ V, IsRegularLocalRing (Localization.AtPrime x.asIdeal) := by
    intro x hx
    simpa using hV_reg hx
  -- Transport the nonempty open subset `V ⊆ Reg(Spec (R ⧸ p.asIdeal))` across the canonical
  -- quotient-spectrum homeomorphism `e : Spec (R ⧸ p) ≃ V(p)`, then use the regular-sequence
  -- argument from the proof sketch to upgrade regularity from the quotient local rings to the
  -- ambient local rings along `V(p)`.
  sorry

end
