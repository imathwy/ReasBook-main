import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_6
import StacksProject_2024.Chap15.Lemma_15_12_3
import StacksProject_2024.Chap15.Lemma_15_12_4

-- Shared owner-level API extracted from `Lemma_15_109_1.lean`.

open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable {R Rh : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

local notation "R_pair" => pairOfIdeal (maximalIdeal R)
local notation "R_h" => henselizationRing R_pair

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Helper for Lemma 15.109.1: compare a chosen henselization with the canonical owner
henselization of the same local ring. -/
private noncomputable abbrev selfHenselizationMapRingHom :
    Rh →+* R_h :=
  @henselizationMapRingHom R Rh R_h _ _ _ _ _ _ R _ _ _ _ _ _

/-- The canonical comparison map from a chosen henselization `Rh` of a Noetherian local ring `R`
to the maximal-ideal completion `AdicCompletion (maximalIdeal R) R`. -/
noncomputable abbrev henselizationCompletionComparison :
    Rh →+* AdicCompletion (maximalIdeal R) R :=
  let R_pair := pairOfIdeal (maximalIdeal R)
  let R_h := henselizationRing R_pair
  (RingPairCat.henselizationToAdicCompletion R_pair).comp
    (selfHenselizationMapRingHom (R := R) (Rh := Rh) (R_h := R_h))

end
