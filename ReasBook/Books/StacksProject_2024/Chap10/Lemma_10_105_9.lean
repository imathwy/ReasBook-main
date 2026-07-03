import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap10.Lemma_10_105_6
import StacksProject_2024.Chap10.Lemma_10_105_7
import StacksProject_2024.Chap10.Lemma_10_157_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.105.9: if `M` has full support over `R`, then every prime localization
`M_𝔭` still has full support over `R_𝔭`. -/
private lemma localized_support_eq_univ_of_support_eq_univ [Module.Finite R M]
    (hsupp : Module.support R M = Set.univ) (p : PrimeSpectrum R) :
    Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
      Set.univ := by
  ext q
  -- Detect support after localizing by contracting the prime back to `Spec R`.
  rw [Module.mem_support_localizationAtPrime_iff (R := R) (M := M) p q, hsupp]
  simp

/-- Helper for Lemma 10.105.9: localizing the global hypotheses at a prime produces the local
source theorem input. -/
private theorem localized_cohenMacaulay_and_support_eq_univ
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : PrimeSpectrum R) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) ∧
      Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
        Set.univ := by
  let _ : Module.Finite R M := hCM.toFinite
  constructor
  · -- The locally Cohen-Macaulay owner already packages the localized Cohen-Macaulay statement.
    exact hCM.localizedModule_cohenMacaulay p
  · -- Full support survives the same localization.
    exact localized_support_eq_univ_of_support_eq_univ (R := R) (M := M) hsupp p

/-- Helper for Lemma 10.105.9: catenarity transports across ring equivalences. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space owner across the induced homeomorphism of spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-- Helper for Lemma 10.105.9: over a Noetherian local ring, the polynomial ring is catenary once
the base admits a Cohen-Macaulay module with full support. -/
private theorem isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) (n : ℕ) :
    IsCatenaryRing (MvPolynomial (Fin n) A) := by
  -- Route correction: this is the remaining source-faithful polynomial step. Its intended proof is
  -- to base-change `N` to `A[x₁, …, xₙ]`, check full support primewise, localize at maximal ideals,
  -- and then apply the local chain-length argument there.
  -- TODO: reopen this once the earlier polynomial-base-change dependency compiles again.
  let _ : Module.Finite A N := hCM.toFinite
  let _ := hsupp
  let _ := n
  sorry

/-- Helper for Lemma 10.105.9: over a Noetherian local ring, a Cohen-Macaulay module with full
support forces the ring to be universally catenary. -/
private theorem universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    UniversallyCatenaryRing A := by
  let _ : Module.Finite A N := hCM.toFinite
  refine { catenary_of_finiteType := ?_ }
  intro B _ _ _
  obtain ⟨n, π, hπsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let S := MvPolynomial (Fin n) A
  letI : IsCatenaryRing S :=
    isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
      (A := A) (N := N) hCM hsupp n
  letI : IsCatenaryRing (S ⧸ RingHom.ker π) :=
    quotient_catenaryRing (R := S) (I := RingHom.ker π)
  let e : S ⧸ RingHom.ker π ≃+* B := RingHom.quotientKerEquivOfSurjective hπsurj
  -- Present the finite-type algebra as a quotient of a catenary polynomial ring.
  exact isCatenaryRing_of_ringEquiv e

/-
Domain-style sampling in the Cohen-Macaulay / universal-catenarity interface:
- sampled owner declarations:
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`,
  `UniversallyCatenaryRing`,
  `Module.support_of_algebra`;
- best owner abstraction: the main theorem is a `bridge/view` from the chapter owner
  `Module.LocallyCohenMacaulay R M` plus full support to `UniversallyCatenaryRing R`;
- primitive data: `hCM : Module.LocallyCohenMacaulay R M` and
  `hsupp : Module.support R M = Set.univ`;
- derived API: the Cohen-Macaulay-ring corollary, obtained by specializing to the self-module
  `R`.

Source/core/bridge triage:
* source-facing: Lemma `10.105.9` itself, expressing the textbook criterion via a
  Cohen-Macaulay module with full support;
* core/canonical: the owner classes `Module.LocallyCohenMacaulay` and
  `UniversallyCatenaryRing`;
* bridge/view: the self-module specialization through `CohenMacaulayRing`.
-/
-- Proof sketch: localize at an arbitrary prime `p` of `R`. The localized module remains
-- Cohen-Macaulay and still has full support, so Lemmas `10.103.13` and `10.103.9` show that each
-- polynomial localization over `Rₚ` has prime chains of the expected length. Applying
-- Lemma `10.104.7` to polynomial algebras and then the localization criterion for universal
-- catenarity yields the conclusion.
/-- Lemma 10.105.9: more generally, if `R` is a Noetherian ring and `M` is a Cohen-Macaulay
`R`-module whose support is all of `Spec R`, then `R` is universally catenary. -/
theorem universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ) :
    UniversallyCatenaryRing R := by
  let _ : Module.Finite R M := hCM.toFinite
  -- Reduce universal catenarity to the prime-local criterion from Lemma `10.105.6`.
  refine ((universallyCatenaryRing_localization_tfae (R := R)).out 1 0 rfl rfl).mp ?_
  intro p
  -- Each prime localization now matches the remaining local theorem.
  obtain ⟨hCMp, hsuppp⟩ :=
    localized_cohenMacaulay_and_support_eq_univ (R := R) (M := M) hCM hsupp p
  exact universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local hCMp hsuppp

end

section

variable {R : Type u} [CommRing R]

-- Proof sketch: apply the general theorem to the self-module `R`. A Cohen-Macaulay ring gives the
-- required local Cohen-Macaulay property for `R`, and the support of the self-module is all of
-- `Spec R`. The theorem header does not repeat a separate `[IsNoetherianRing R]` assumption,
-- since that primitive data already belongs to the owner class `CohenMacaulayRing R`.
/-- A Noetherian Cohen-Macaulay ring is universally catenary. -/
theorem universallyCatenaryRing_of_cohenMacaulayRing (hCM : CohenMacaulayRing R) :
    UniversallyCatenaryRing R := by
  let _ : CohenMacaulayRing R := hCM
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  exact universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    hCM.toLocallyCohenMacaulay hsupp

end
