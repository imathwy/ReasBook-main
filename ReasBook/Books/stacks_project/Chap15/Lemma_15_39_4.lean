import stacks_project.Chap10.Definition_10_160_1
import stacks_project.Chap15.Situation_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R S S' : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [IsCompleteLocalRing S] [IsNoetherianRing S]
variable [IsCompleteLocalRing S'] [IsNoetherianRing S']

/- Domain-style sampling:
- primary domain: surjective pullbacks of complete Noetherian local rings;
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `quotient_isCompleteLocalRing`,
  `IsLocalRing.of_surjective'`,
  `Function.Surjective.isLocalHom`;
- best owner abstraction: the chapter pullback owner `SurjectiveRingPullbackSituation` with its
  derived fibre-product ring `Bprime`;
- primitive data: the two complete Noetherian local source rings `S`, `S'`, the pullback owner
  `T : SurjectiveRingPullbackSituation S R S'`, the built-in surjectivity of `T.fromAprime`, and
  the remaining surjectivity hypothesis on `T.toA`;
- derived API: `R` is a local ring by `IsLocalRing.of_surjective'` applied to `T.fromAprime`, both
  maps to `R` are local by `Function.Surjective.isLocalHom`, `R` is complete local and Noetherian as a
  quotient of `S'`, and the fibre-product ring `T.Bprime` is complete local and Noetherian.

Source/core/bridge triage:
- `source-facing`: the fibre-product ring of two surjective local maps to a common complete local
  base;
- `core/canonical`: the predicates `IsCompleteLocalRing` and `IsNoetherianRing`;
- `bridge/view`: `SurjectiveRingPullbackSituation`, which packages the surjective pullback owner
  already used earlier in the chapter. -/

-- Proof sketch: first note that `R` is already a local ring by surjectivity of
-- `T.fromAprime : S' → R`, and then both maps `T.toA` and `T.fromAprime` are local by the
-- canonical surjective-local API. The same surjective map `T.fromAprime` exhibits `R` as a
-- quotient of the complete Noetherian local ring `S'`, so `R` is complete local and Noetherian.
-- Then realize the fibre product `S ×_R S'` as the categorical pullback of `T.toA` and
-- `T.fromAprime`. Using the Cohen-structure-theorem argument from the source, one gets a
-- surjection from a formal power series ring onto this pullback ring; hence it is complete local.
-- The same presentation shows the pullback is a quotient of a power series ring over a Cohen ring
-- or residue field, hence Noetherian as well.
namespace SurjectiveRingPullbackSituation

variable (T : SurjectiveRingPullbackSituation S R S') (h_toA : Function.Surjective T.toA)

/-- Lemma 15.39.4: if `S → R` and `S' → R` are surjective local homomorphisms of complete
Noetherian local rings, then the fibre product `S ×_R S'`, formalized by the canonical pullback
owner `T.Bprime`, is again a complete local ring. -/
theorem bprime_isCompleteLocalRing_of_surjective :
    IsCompleteLocalRing T.Bprime := by
  sorry

/-- Under the same hypotheses, the pullback ring `T.Bprime = S ×_R S'` is Noetherian. -/
theorem bprime_isNoetherianRing_of_surjective :
    IsNoetherianRing T.Bprime := by
  sorry

end SurjectiveRingPullbackSituation

end
