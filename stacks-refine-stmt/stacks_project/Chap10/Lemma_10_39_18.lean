import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section LocalizationFlatness

variable {R : Type u} [CommRing R]
variable (S : Submonoid R) {Rₛ : Type v} [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]

/- Canonical recall: for a multiplicative subset `S` of a ring `R`, the localization `S⁻¹R`
is flat as an `R`-algebra. This is exactly the canonical theorem `IsLocalization.flat`. -/
recall IsLocalization.flat

variable {N : Type w} [AddCommMonoid N] [Module R N] [Module Rₛ N] [IsScalarTower R Rₛ N]

/- Canonical recall: if `M` is a module over a localization `S⁻¹R`, then `M` is flat over `R`
if and only if it is flat over `S⁻¹R`. This is exactly the canonical theorem
`Module.flat_iff_of_isLocalization`. -/
recall Module.flat_iff_of_isLocalization

variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: one direction is preserved by localization at a prime, and the converse follows
-- by reducing to the maximal-local criterion after localizing further at maximal ideals over each
-- prime.
/-- Lemma 10.39.18 (1): an `R`-module `M` is flat if and only if each localization `Mₚ` is flat
over `Rₚ` for every prime ideal `p` of `R`. -/
theorem flat_iff_flat_localizedModule_atPrime
    : Module.Flat R M ↔
        ∀ p : PrimeSpectrum R,
          Module.Flat (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := sorry

-- Proof sketch: use the canonical maximal-local criterion in mathlib for one direction and
-- localization of flat modules for the reverse implication.
/-- Lemma 10.39.18 (2): an `R`-module `M` is flat if and only if each localization `Mₘ` is flat
over `Rₘ` for every maximal ideal `m` of `R`. -/
theorem flat_iff_flat_localizedModule_atMaximal
    : Module.Flat R M ↔
        ∀ m : MaximalSpectrum R,
          Module.Flat (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal M) := sorry

end LocalizationFlatness

section RelativeLocalizationFlatness

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/- The localization of an `A`-module at a prime `Q` of `A` is canonically a module over the
localization of `R` at the inverse-image prime `Q ∩ R`, via the local ring map
`R_(Q ∩ R) → A_Q`. -/
noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    Module (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
  Module.compHom (LocalizedModule.AtPrime Q M)
    (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl)

noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    IsScalarTower (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)
      (LocalizedModule.AtPrime Q M) := by
  letI : Module (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
    Module.compHom (LocalizedModule.AtPrime Q M)
      (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl)
  simpa using
    (IsScalarTower.restrictScalars (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)
      (LocalizedModule.AtPrime Q M))

-- Proof sketch: if `M` is flat over `R`, then every localization away from a generator remains
-- flat; conversely, use the localization-away spanning criterion for flatness over the target ring.
/-- Lemma 10.39.18 (3): if `g₁, …, gₘ` generate the unit ideal of an `R`-algebra `A`, then an
`A`-module `M` is flat over `R` if and only if every localization `M[1 / gᵢ]` is flat over `R`. -/
theorem flat_iff_flat_localizedModule_away_of_span_eq_top
    {n : ℕ} (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔ ∀ i : Fin n, Module.Flat R (LocalizedModule.Away (g i) M) := sorry

-- Proof sketch: localize a flat `R`-module `M` at each prime of `A` for one implication; for the
-- converse, descend flatness from all prime localizations lying over `R`.
/-- Lemma 10.39.18 (4): for an `R`-algebra `A` and an `A`-module `M`, `M` is flat over `R` if and
only if for every prime ideal `q` of `A`, the localization `M_q` is flat over
`R_{q ∩ R}`. -/
theorem flat_iff_flat_localizedModule_atPrime_over_under
    : Module.Flat R M ↔
        ∀ q : PrimeSpectrum A,
          Module.Flat (Localization.AtPrime (q.asIdeal.under R))
            (LocalizedModule.AtPrime q.asIdeal M) := sorry

-- Proof sketch: the forward implication follows by localization at maximal ideals of `A`; the
-- converse is obtained from the prime-local criterion by restricting to maximal ideals.
/-- Lemma 10.39.18 (5): for an `R`-algebra `A` and an `A`-module `M`, `M` is flat over `R` if and
only if for every maximal ideal `m` of `A`, the localization `Mₘ` is flat over
`R_{m ∩ R}`. -/
theorem flat_iff_flat_localizedModule_atMaximal_over_under
    : Module.Flat R M ↔
        ∀ m : MaximalSpectrum A,
          Module.Flat (Localization.AtPrime (m.asIdeal.under R))
            (LocalizedModule.AtPrime m.asIdeal M) := sorry

end RelativeLocalizationFlatness
