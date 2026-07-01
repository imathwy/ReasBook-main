import Mathlib
import stacks_project.Chap10.Definition_10_105_1
import stacks_project.Chap10.Lemma_10_105_5
import stacks_project.Chap10.Lemma_10_105_9
import stacks_project.Chap10.Lemma_10_114_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S] [IsDomain S]

/-
Domain-style sampling:
- primary domain: dimension theory of irreducible affine schemes of finite type over a field,
  organized through catenary prime-chain owners and the height/localization API;
- sampled owner declarations of the same kind:
  `IsCatenaryRing.maximalPrimeChainsHaveSameLength`,
  `universallyCatenaryRing_of_cohenMacaulayRing`,
  `universallyCatenaryRing_of_essFiniteType`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the ambient owner is the catenary prime-spectrum API for `S`, while the
  local comparison is owned by the canonical height formula for `Localization.AtPrime`;
- primitive data: the finite type domain `S` over the field `k`, and a maximal ideal
  `m : MaximalSpectrum S`;
- derived API: the source-facing equality between `ringKrullDim S` and the Krull dimension of the
  maximal localization `Localization.AtPrime m.asIdeal`.

Source/core/bridge triage:
* `source-facing`: the equidimensionality statement that all maximal localizations of an affine
  domain of finite type over a field have the same dimension as the ambient ring;
* `core/canonical`: `IsCatenaryRing S` together with the owner equalities
  `IsLocalization.AtPrime.ringKrullDim_eq_height` and
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`;
* `bridge/view`: the finite-type-over-a-field route to catenarity and the maximal-chain
  comparison specialized from polynomial rings in Lemma `10.114.3`.
-/
-- Proof sketch: fields are universally catenary through the Cohen-Macaulay bridge, so every
-- finite type `k`-algebra is catenary by the essentially-finite-type owner theorem. For a domain,
-- `Spec S` is irreducible, and the maximal-chain comparison from Lemma `10.114.3` identifies the
-- common length of maximal chains from the generic point to any closed point. The owner
-- height/localization formulas then identify that common length with both `ringKrullDim S` and
-- `ringKrullDim (Localization.AtPrime m.asIdeal)`.
/-- Lemma 10.114.4: if `S` is a finite type `k`-algebra that is an integral domain, then every
maximal localization `Sₘ`, formalized as `Localization.AtPrime m.asIdeal`, has the same Krull
dimension as `S`. -/
theorem ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := sorry

end
