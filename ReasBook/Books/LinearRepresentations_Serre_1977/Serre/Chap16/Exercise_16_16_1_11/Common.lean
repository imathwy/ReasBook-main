import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_11
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_2_1

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

namespace Exercise_16_16_1_11

instance grothendieckCharacterRingCoeFun
    (K : Type) [Field K] (G : Type) [Group G] :
    CoeFun (R[K](G)) fun _ ↦ G → K where
  coe χ := χ.1

abbrev cyclicOrderFourDivisorIndexTwo {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 4) : { d : ℕ // d ∣ Nat.card G } :=
  let _ : Fintype G := Fintype.ofFinite G
  ⟨2, by
    have hcard : Fintype.card G = 4 := by
      simpa using hG
    rw [Nat.card_eq_fintype_card, hcard]
    norm_num⟩

abbrev cyclicOrderFourDivisorIndexFour {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 4) : { d : ℕ // d ∣ Nat.card G } :=
  let _ : Fintype G := Fintype.ofFinite G
  ⟨4, by
    have hcard : Fintype.card G = 4 := by
      simpa using hG
    rw [Nat.card_eq_fintype_card, hcard]⟩

abbrev cyclicOrderFourDivisorIndexOne {G : Type} [Group G] [Finite G]
    (_hG : Nat.card G = 4) : { d : ℕ // d ∣ Nat.card G } :=
  ⟨1, Nat.one_dvd _⟩

end Exercise_16_16_1_11
