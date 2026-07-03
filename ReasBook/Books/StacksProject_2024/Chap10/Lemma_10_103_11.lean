import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped ENat
open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

namespace Module.CohenMacaulay

variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

/- Domain-style sampling:
* primary domain: Cohen-Macaulay modules over Noetherian local rings and their behavior under
  localization at a prime;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `Localization.AtPrime`,
  `LocalizedModule.AtPrime`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* primitive data: the ambient local Noetherian ring, the module structure on `M`, and the owner
  instance `[Module.CohenMacaulay R M]`;
* derived API: the equality `Module.supportDim R M = .some (moduleDepth R M)` and the inherited
  finiteness instance.

Source/core/bridge triage:
* `source-facing`: preservation of the Cohen-Macaulay condition under localization at a prime;
* `core/canonical`: the owner class `Module.CohenMacaulay` together with the canonical
  localization objects `Rₚ` and `Mₚ`;
* `bridge/view`: the equality `supportDim_eq_moduleDepth` extracted from the owner class.

The localized depth-equals-support-dimension equality is derived API from the owner class, so the
public statement should return `Module.CohenMacaulay Rₚ Mₚ` directly instead of restating that
equality as a parallel theorem.
-/

-- Proof sketch: use Lemma `10.72.10` to bound the depth of `Mₚ` from below by the depth of `M`
-- minus `dim (R / p)`, and use Lemma `10.72.3` over `Rₚ` to bound the localized depth above by
-- the support dimension of `Mₚ`. Comparing these inequalities with
-- `supportDim_eq_moduleDepth` for `M` yields the Cohen-Macaulay equality for `Mₚ`.
/-- Lemma 10.103.11: if `M` is a Cohen-Macaulay finite module over a Noetherian local ring `R`,
then for any prime ideal `p` of `R`, the localization `Mₚ` is Cohen-Macaulay over `Rₚ`. -/
theorem localizedModule_atPrime : Module.CohenMacaulay Rₚ Mₚ := sorry

end Module.CohenMacaulay

end
