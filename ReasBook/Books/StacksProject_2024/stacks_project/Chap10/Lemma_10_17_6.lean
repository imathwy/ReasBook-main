import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_17_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_17_5

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/- Layering for this item:
* source-facing: the localization-away map induces a homeomorphism `Spec(R_f) ≃ₜ D(f)`.
* core/canonical owner: `primeSpectrum_localization_homeomorph (Submonoid.powers f)`.
* bridge/view: identify the subtype of primes disjoint from `powers f` with the canonical basic
  open `D(f)`. -/

private theorem disjoint_powers_eq_D (f : R) :
    { p : PrimeSpectrum R | Disjoint (Submonoid.powers f : Set R) p.asIdeal } =
      D(f) := by
  ext p
  change Disjoint (Submonoid.powers f : Set R) p.asIdeal ↔ f ∉ p.asIdeal
  simpa using Ideal.disjoint_powers_iff_notMem f p.2.isRadical

/-- Lemma 10.17.6: the map on prime spectra induced by the localization map
`R → Localization.Away f` is a homeomorphism from `Spec(R_f)` onto the basic open subset
`D(f) ⊆ Spec(R)`. -/
noncomputable def primeSpectrum_localizationAway_homeomorph_D (f : R) :
    PrimeSpectrum (Localization.Away f) ≃ₜ D(f) :=
  (primeSpectrum_localization_homeomorph (Submonoid.powers f)).trans
    (Homeomorph.setCongr (disjoint_powers_eq_D f))

/-- The localization-away homeomorphism is induced by the comap along `R → Localization.Away f`. -/
-- Proof sketch: unfold the homeomorphism as the open-embedding homeomorphism followed by the
-- range identification `Set.range (PrimeSpectrum.comap _) = D(f)`, then track a point through the
-- two components.
@[simp]
theorem primeSpectrum_localizationAway_homeomorph_D_apply (f : R)
    (p : PrimeSpectrum (Localization.Away f)) :
    (primeSpectrum_localizationAway_homeomorph_D f p).1 =
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p :=
  rfl

/-- The inverse homeomorphism sends a prime of `D(f)` to its extension to `Localization.Away f`. -/
-- Proof sketch: identify the inverse of the open-embedding homeomorphism with the unique prime of
-- the localization lying over `p`, then rewrite that prime as the mapped ideal
-- `p.asIdeal.map (algebraMap R (Localization.Away f))`.
theorem primeSpectrum_localizationAway_homeomorph_D_symm_asIdeal
    (f : R) (p : D(f)) :
    ((primeSpectrum_localizationAway_homeomorph_D f).symm p).asIdeal =
      p.1.asIdeal.map (algebraMap R (Localization.Away f)) := by
  have hp_not_mem : f ∉ p.1.asIdeal := (mem_D f p.1).mp p.2
  have hp_disjoint : Disjoint (Submonoid.powers f : Set R) p.1.asIdeal := by
    rw [Ideal.disjoint_powers_iff_notMem _ p.1.2.isRadical]
    exact hp_not_mem
  let p' : { p : PrimeSpectrum R // Disjoint (Submonoid.powers f : Set R) p.asIdeal } :=
    ⟨p.1, hp_disjoint⟩
  change ((primeSpectrum_localization_homeomorph (Submonoid.powers f)).symm p').asIdeal =
      p.1.asIdeal.map (algebraMap R (Localization (Submonoid.powers f)))
  simpa only [p']
    using congrArg PrimeSpectrum.asIdeal
      (primeSpectrum_localization_homeomorph_symm_apply (Submonoid.powers f) p')
