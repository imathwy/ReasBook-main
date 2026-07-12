import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped ENat
open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling for the local Cohen-Macaulay dimension formula:
- primary domain: Cohen-Macaulay modules over Noetherian local rings, together with local/quotient
  Krull-dimension comparisons at a prime ideal;
- sampled owner declarations:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_moduleDepth`,
  `Module.supportDim_eq_ringKrullDim_quotient_annihilator`;
- best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
- primitive data: the ambient local Noetherian ring, the module structure on `M`, the
  Cohen-Macaulay owner hypothesis `hCM : Module.CohenMacaulay R M`, the full-support hypothesis
  `hsupp`, and the prime ideal `p`;
- derived API: the finiteness instance on `M`, inherited from `Module.CohenMacaulay`, and the
  support-dimension/depth identities recovered from the owner abstraction.

Source/core/bridge triage:
* `source-facing`: the dimension formula for a full-support Cohen-Macaulay module over a local
  Noetherian ring;
* `core/canonical`: `Module.CohenMacaulay`, `moduleDepth`, `Localization.AtPrime`,
  `ringKrullDim`, and `Module.support`;
* `bridge/view`: the quotient ring `R ⧸ p` and the localization `Localization.AtPrime p`.

The old ambient `[Module.Finite R M]` binder was duplicate primitive data: finiteness already comes
from the owner class `Module.CohenMacaulay R M`, so it should not remain a parallel public
assumption.
-/

-- Proof sketch: apply Lemma `10.103.9` to identify the length of every maximal prime chain in
-- `Spec R` with `ringKrullDim R`. Split a maximal chain through the prime `p` into the part below
-- `p`, whose length computes `ringKrullDim (Localization.AtPrime p)`, and the part above `p`,
-- whose length computes `ringKrullDim (R ⧸ p)`, then add the two lengths.
/-- Lemma 10.103.10: if `R` is a Noetherian local ring and `M` is a finite Cohen-Macaulay
`R`-module with full support, then for every prime ideal `p` of `R` the dimension of `R` is the
sum of the dimensions of the localization `Rₚ` and the quotient `R / p`. -/
theorem ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := sorry

end
