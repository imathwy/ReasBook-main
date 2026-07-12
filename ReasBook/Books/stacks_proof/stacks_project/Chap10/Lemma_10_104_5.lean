import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1
import StacksProject_2024.Chap10.Lemma_10_103_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

namespace Module.CohenMacaulay

/- Domain-style sampling:
* primary domain: Cohen-Macaulay rings/modules under localization in commutative algebra;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.localizedModule_atPrime`,
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`;
* best owner abstraction: the earlier chapter owner `Module.CohenMacaulay R R`;
* primitive data: the local Noetherian ring `R` together with the self-module owner instance
  `[Module.CohenMacaulay R R]`;
* derived API: the localized self-module statement, obtained canonically from
  `Module.CohenMacaulay.localizedModule_atPrime`.

Source/core/bridge triage:
* source-facing: the textbook local-ring statement that a Cohen-Macaulay local ring stays
  Cohen-Macaulay after localization at a prime ideal;
* core/canonical: `Module.CohenMacaulay` together with the earlier localization theorem
  `Module.CohenMacaulay.localizedModule_atPrime`;
* bridge/view: the present theorem, which is only the self-module specialization of that owner
  theorem.
-/

variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p

-- Proof sketch: specialize `Module.CohenMacaulay.localizedModule_atPrime` to the self-module
-- `M = R`. The source-facing local-ring statement is exactly this thin specialization, so no
-- later ring-level wrapper is needed.
/-- Lemma 10.104.5: if `R` is a Cohen-Macaulay local ring and `p` is a prime ideal of `R`, then
the localization `Rₚ` is Cohen-Macaulay. -/
@[stacks 00NB]
theorem cohenMacaulay_localizationAtPrime_self : Module.CohenMacaulay Rₚ Rₚ := by
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  have hp_support : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∈ Module.support R R := by
    rw [hsupp]
    exact Set.mem_univ _
  simpa using localizedModule_atPrime p hp_support

end Module.CohenMacaulay

end
