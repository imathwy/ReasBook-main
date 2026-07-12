import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

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
    UniversallyCatenaryRing R := sorry

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
