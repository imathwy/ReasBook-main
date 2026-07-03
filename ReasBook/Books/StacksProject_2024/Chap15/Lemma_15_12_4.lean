import Mathlib
import StacksProject_2024.Chap15.Lemma_15_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

noncomputable section

namespace RingPairCat

section

/- Domain-style sampling for Lemma 15.12.4:
- primary domain: henselization of ring pairs and the canonical comparison from henselization to
  adic completion in Noetherian commutative algebra;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `RingPairCat.toHenselization`,
  `RingPairCat.henselizationRing`,
  `AdicCompletion.map`;
- best owner abstraction: the source-facing map to adic completion is derived from the canonical
  pair-henselization adjunction of Lemma `15.12.1`, not from any new local wrapper or additional
  public adjunction data;
- primitive data: a ring pair `X` and the Noetherian hypothesis on `X.ring`;
- derived API: the comparison map `A^h → A^∧` and the flatness / faithful-flatness statements
  attached to it.

Source/core/bridge triage:
- `source-facing`: the canonical map from the henselization of `(A, I)` to its `I`-adic
  completion and its properties in Lemma `15.12.4`;
- `core/canonical`: the adjunction owner `henselianPairInclusion` from Lemma `15.12.1`;
- `bridge/view`: the comparison morphism obtained by applying the adjunction universal property to
  the henselian completion pair. -/

variable (X : RingPairCat.{u})
variable [IsNoetherianRing X.ring]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: both composites are induced by the same ring map `X.ring → AdicCompletion X.ideal
-- X.ring`, and the lower horizontal arrow is exactly the quotient map obtained from that ring map
-- by functoriality of quotients.
/-- The quotient square defining the canonical morphism from `X` to its adic completion pair. -/
private lemma toAdicCompletionPair_w :
    CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)) ≫
        CommRingCat.ofHom
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom
          (Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map) := sorry

-- Proof sketch: the completion ring is complete for the extended ideal, hence henselian by the
-- canonical complete-pair instance. The Noetherian hypothesis ensures the completion is complete
-- for that extended ideal in the ring-theoretic sense used by `HenselianRing`.
/-- The `I`-adic completion pair of a Noetherian pair is henselian. -/
private theorem adicCompletion_henselian :
    HenselianRing
      (AdicCompletion X.ideal X.ring)
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal) := by
  let hComplete :
      IsAdicComplete
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
        (AdicCompletion X.ideal X.ring) := by
    exact
      (IsAdicComplete.map_algebraMap_iff X.ideal (AdicCompletion X.ideal X.ring)).2
        (AdicCompletion.isAdicComplete (Ideal.fg_of_isNoetherianRing X.ideal))
  letI :
      IsAdicComplete
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
        (AdicCompletion X.ideal X.ring) := hComplete
  exact
    @IsAdicComplete.henselianRing
      (AdicCompletion X.ideal X.ring)
      inferInstance
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
      hComplete

/-- The canonical ring map from the henselization ring `A^h` to the `I`-adic completion `A^∧`. -/
def henselizationToAdicCompletion :
    henselizationRing X →+* AdicCompletion X.ideal X.ring :=
  let completionMap :
      X ⟶ pairOfIdeal (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal) :=
    InducedCategory.homMk <|
      Arrow.homMk
        (CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)))
        (CommRingCat.ofHom
          (Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map))
        (toAdicCompletionPair_w X)
  let comparison :=
    ((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
      ⟨pairOfIdeal (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal),
        adicCompletion_henselian X⟩).symm
      completionMap
  ringHom comparison.hom

-- Proof sketch: Lemma `15.12.2` identifies every quotient
-- `X.ring ⧸ X.ideal ^ n → henselizationRing X ⧸ (X.ideal)^n henselizationRing X` as a bijection.
-- Passing to inverse limits gives a bijection on the induced map of `X.ideal`-adic completions.
/-- Lemma 15.12.4 (1): the map on `I`-adic completions induced by `A → A^h`, formalized as the
map from the `I`-adic completion of `A` to the `I`-adic completion of the `A`-module `A^h`, is
bijective. -/
theorem adicCompletion_map_toHenselization_bijective :
    Function.Bijective
      (AdicCompletion.map X.ideal (Algebra.linearMap X.ring (henselizationRing X))) := sorry

-- Proof sketch: once `A^h → A^∧` is known faithfully flat and `A^∧` is Noetherian by the standard
-- noetherianity theorem for adic completions of Noetherian rings, Noetherianity descends along
-- faithfully flat maps.
/-- Lemma 15.12.4 (2): the henselization ring `A^h` of a Noetherian pair `(A, I)` is Noetherian. -/
theorem henselizationRing_isNoetherian :
    IsNoetherianRing (henselizationRing X) := sorry

-- Proof sketch: this is exactly Lemma `15.12.2 (1)` recalled in the Noetherian setting.
/- Lemma 15.12.4 (3): the canonical map `A → A^h` is flat. -/
recall toHenselization_flat

-- Proof sketch: the completion map `A → A^∧` is flat for Noetherian rings, and the canonical map
-- `A^h → A^∧` is the comparison morphism from the henselization into that flat completion target.
-- Flatness follows from the quotientwise identification with the completion of `A`.
/-- Lemma 15.12.4 (4): the canonical map from the henselization `A^h` to the `I`-adic completion
`A^∧` is flat. -/
theorem henselizationToAdicCompletion_flat :
    RingHom.Flat (henselizationToAdicCompletion X) := sorry

-- Proof sketch: `I^h = IA^h` lies in the Jacobson radical of the henselization pair, and the map
-- `A^h → A^∧` induces the identity on the special fiber `A^h / I^h ≅ A / I`. Together with the
-- previous flatness statement, the standard Jacobson-radical criterion upgrades flatness to
-- faithful flatness.
/-- Lemma 15.12.4 (5): the canonical map from the henselization `A^h` to the `I`-adic completion
`A^∧` is faithfully flat. -/
theorem henselizationToAdicCompletion_faithfullyFlat :
    RingHom.FaithfullyFlat (henselizationToAdicCompletion X) := sorry

end

end RingPairCat
