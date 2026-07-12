import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits CommRingCat

universe u

noncomputable section

section

variable (B A A' : Type u) [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.1:
- primary domain: pullbacks in `CommRingCat` for a surjective map `A' → A`;
- sampled owner declarations:
  `Limits.pullback`,
  `pullback.fst`,
  `pullback.snd`,
  `pullback.condition`;
- best owner abstraction: the source-facing primitive data is just the pair of ring maps
  `B → A`, `A' → A` with `A' → A` surjective, while the ring `B' = B ×_A A'`, its projections,
  and their commutativity relation are derived from the canonical categorical pullback;
- primitive data: `toA`, `fromAprime`, and `fromAprime_surjective`;
- derived API: `Bprime`, `bprimeToB`, `bprimeToAprime`, the pullback witness `isPullback`, and the
  companion equality `comm`.

Source/core/bridge triage:
- `source-facing`: `SurjectiveRingPullbackSituation`;
- `core/canonical`: `Limits.pullback` in `CommRingCat`;
- `bridge/view`: the derived projections and commutativity relation. -/

/-- Situation 15.6.1: a pair of ring maps `B → A` and `A' → A` with `A' → A` surjective, used to
form the fibre product ring `B' = B ×_A A'`. -/
@[stacks 08KH]
structure SurjectiveRingPullbackSituation where
  /-- The ring map `B → A`. -/
  toA : B →+* A
  /-- The ring map `A' → A`. -/
  fromAprime : A' →+* A
  /-- The map `A' → A` is surjective. -/
  fromAprime_surjective : Function.Surjective fromAprime

namespace SurjectiveRingPullbackSituation

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/-- The fibre product ring `B' = B ×_A A'` attached to a surjective pullback situation. -/
abbrev Bprime : CommRingCat :=
  pullback (ofHom S.toA) (ofHom S.fromAprime)

/-- The canonical projection `B' → B` from the pullback ring `B' = B ×_A A'`. -/
abbrev bprimeToB :
    S.Bprime →+* B :=
  (pullback.fst (ofHom S.toA) (ofHom S.fromAprime)).hom

/-- The canonical projection `B' → A'` from the pullback ring `B' = B ×_A A'`. -/
abbrev bprimeToAprime :
    S.Bprime →+* A' :=
  (pullback.snd (ofHom S.toA) (ofHom S.fromAprime)).hom

/-- The two pullback projections satisfy the defining commutativity relation. -/
theorem comm :
    S.toA.comp S.bprimeToB = S.fromAprime.comp S.bprimeToAprime := by
  have h :
      pullback.fst (ofHom S.toA) (ofHom S.fromAprime) ≫ ofHom S.toA =
        pullback.snd (ofHom S.toA) (ofHom S.fromAprime) ≫ ofHom S.fromAprime :=
    pullback.condition
  simpa [Bprime, bprimeToB, bprimeToAprime] using
    congrArg CommRingCat.Hom.hom h

/-- The fibre-product square attached to a surjective pullback situation is the canonical
categorical pullback square. -/
theorem isPullback :
    IsPullback (ofHom S.bprimeToB) (ofHom S.bprimeToAprime) (ofHom S.toA) (ofHom S.fromAprime) := by
  simpa [Bprime, bprimeToB, bprimeToAprime] using
    (IsPullback.of_hasPullback (ofHom S.toA) (ofHom S.fromAprime))

end SurjectiveRingPullbackSituation

end
