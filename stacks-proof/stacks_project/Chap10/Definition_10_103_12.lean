import Mathlib
import stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum IsLocalRing

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.LocallyCohenMacaulay R M`, the global condition that a finite module over
  a Noetherian ring has Cohen-Macaulay localizations at every prime;
* core/canonical: the owner class `Module.CohenMacaulay` on each localized ring/module pair;
* bridge/view: `LocallyCohenMacaulay.toCohenMacaulay` and
  `locallyCohenMacaulay_of_cohenMacaulay`, which compare the global source-facing condition with
  the local-ring owner abstraction.

Primitive data are exactly the finiteness hypothesis and the family of localized
`Module.CohenMacaulay` instances. The inherited `Module.Finite` instance is derived from the class
extension and should not be restated as a separate local wrapper.
-/
/-- Definition 10.103.12: a finite `R`-module over a Noetherian ring is Cohen-Macaulay if, for
every prime ideal `𝔭` of `R`, the localization `M_𝔭` is a Cohen-Macaulay module over the
localized ring `R_𝔭`. -/
class LocallyCohenMacaulay : Prop extends Module.Finite R M where
  localizedModule_cohenMacaulay :
    ∀ p : PrimeSpectrum R,
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)

namespace LocallyCohenMacaulay

/-- Over a Noetherian local ring, a locally Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay [IsLocalRing R] (h : LocallyCohenMacaulay R M) :
    Module.CohenMacaulay R M := sorry

end LocallyCohenMacaulay

/-- Over a Noetherian local ring, the local-global condition yields the owner class directly. -/
instance cohenMacaulay_of_locallyCohenMacaulay [IsLocalRing R] [h : LocallyCohenMacaulay R M] :
    Module.CohenMacaulay R M :=
  h.toCohenMacaulay

/-- Over a Noetherian local ring, a Cohen-Macaulay module is locally Cohen-Macaulay. -/
instance locallyCohenMacaulay_of_cohenMacaulay [IsLocalRing R] [Module.CohenMacaulay R M] :
    LocallyCohenMacaulay R M := sorry

end Module

end
