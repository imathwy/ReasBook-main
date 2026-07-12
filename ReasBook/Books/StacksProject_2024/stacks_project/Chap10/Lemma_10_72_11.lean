import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing
open LocalizedModule

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N]

/- Domain-style sampling:
* primary domain: local depth for finite modules under a finite ring map, compared across maximal
  localizations of the target ring;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Module.Finite`,
  `MaximalSpectrum`,
  `Localization.AtPrime`;
* best owner abstraction: the chapter owner surface for local depth is `moduleDepth`, the finite
  algebra hypothesis is the canonical owner instance `[Module.Finite R S]`, and the canonical
  index type for maximal ideals is `MaximalSpectrum S`;
* source/core/bridge triage:
  `source-facing`: the equality between the depth over the source local ring and the infimum of
    the depths at maximal localizations of the finite target algebra;
  `core/canonical`: `moduleDepth` and `MaximalSpectrum`;
  `bridge/view`: the maximal localizations `Localization.AtPrime m.asIdeal` and localized modules
    `LocalizedModule.AtPrime m.asIdeal N`.

Primitive data are only the local ring `R`, the finite `R`-algebra `S`, the finite `S`-module
`N`, and the family of maximal localizations indexed by `MaximalSpectrum S`. The old surface
spelled this family through `PrimeSpectrum S` together with an `IsMaximal` witness and unfolded
local depth back to `Ideal.depth (maximalIdeal _)`; both are derived API and should be replaced by
the owner abstractions here. The finiteness of `N` over `R` is derived from the owner instance
`[Module.Finite R S]` together with `[Module.Finite S N]`, so it should not remain a primitive
public assumption either.
-/
-- Proof sketch: for each maximal ideal `𝔪ᵢ` of `S`, compare `depth_{𝔪}(N)` with the local depth of
-- `N_{𝔪ᵢ}`. The case where one localized depth is `0` is detected by associated primes after
-- localization and contraction. For positive minimum depth, choose an element of `maximalIdeal R`
-- that is `N`-regular, use the finite-map comparison to see it stays regular at every maximal
-- localization of `S`, apply the depth-drop lemma after quotienting by this element, and conclude
-- by induction on the minimum localized depth.
/-- Lemma 10.72.11: for a finite ring map `R → S` from a Noetherian local ring `R` and a finite
`S`-module `N`, the depth of `N` over `R` with respect to the maximal ideal equals the minimum of
the depths of the localizations `N_𝔪` over the local rings `S_𝔪`, as `𝔪` ranges over the maximal
ideals of `S`. -/
theorem depth_eq_sInf_depth_localizedModule_at_maximalIdeals_of_finite
    [Module.Finite R S] :
    letI : Module.Finite R N := Module.Finite.trans S N
    (⨅ m : MaximalSpectrum S,
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N)) =
      moduleDepth R N := sorry

end
