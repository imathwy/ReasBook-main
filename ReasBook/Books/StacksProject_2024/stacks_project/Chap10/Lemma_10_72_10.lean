import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENat
open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

/- Domain-style sampling:
* primary domain: depth for finite modules over Noetherian local rings and its behavior under
  localization at a prime;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Localization.AtPrime`,
  `LocalizedModule.AtPrime`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`;
* best owner abstraction: the chapter owner surface for local depth is `moduleDepth`, while the
  localized ring/module are the canonical owner constructions `Localization.AtPrime` and
  `LocalizedModule.AtPrime`;
* source/core/bridge triage:
  `source-facing`: the depth inequality relating `M`, `Mₚ`, and `R / p`;
  `core/canonical`: `moduleDepth` together with the owner localization objects `Rₚ` and `Mₚ`;
  `bridge/view`: the quotient ring `R ⧸ p`.

Primitive data are only the local ring, the finite module, and the prime ideal. The localized ring
and module are derived from the owner localization constructions, so the public theorem surface
should name those owner objects directly instead of repeating the full expressions inline.
-/

-- Proof sketch: argue by induction on `moduleDepth R M`. If `LocalizedModule.AtPrime p M = 0`,
-- then the localized depth is `∞`. Otherwise, when the global depth exceeds
-- `ringKrullDim (R ⧸ p)`, Lemma `10.72.9` and prime avoidance produce `x ∈ p` that is a
-- nonzerodivisor on `M`; apply Lemma `10.72.7` to both `M` and its localization at `p`, then use
-- the dimension drop for `R ⧸ (p + (x))` to close the induction.
/-- Lemma 10.72.10: for a prime ideal `p` of a local Noetherian ring `R` and a finite
`R`-module `M`, the local depth `moduleDepth Rₚ Mₚ` of the localization `Mₚ` plus the Krull
dimension of `R / p` is at least the local depth `moduleDepth R M` of `M`. -/
theorem moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_moduleDepth :
    .some (moduleDepth Rₚ Mₚ) + ringKrullDim (R ⧸ p) ≥ .some (moduleDepth R M) := sorry

end
