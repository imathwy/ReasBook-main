import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.SemisimpleEquivTransport
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.SemisimpleS4Irreducible
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.SemisimpleS4Degrees
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.SemisimpleCharacterValues

/-!
# Completeness of Serre's five explicit `S₄`-models in the semisimple branch (support 18.5.2)

In the semisimple branch `ringChar k ∉ {2, 3}` of Exercise 18.5.2, where `(2 : k) ≠ 0` and
`(3 : k) ≠ 0` (so `k[S₄]` is semisimple), the five explicit `S₄`-models — bundled as the
`ULift`-lifted family `s4_explicit_family k : Fin 5 → FDRep k (ULift S₄)` — are absolutely
irreducible, pairwise non-isomorphic, and have square-degree sum `1²+1²+2²+3²+3² = 24 = |S₄|`.
Hence they form a complete family of irreducibles (`Chap03.Theorem_3_3_2_1`).
-/

attribute [-instance] Field.henselian

noncomputable section

open CategoryTheory
open Representation

namespace Representation

section

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)

universe w

variable {k : Type w} [Field k]

-- The `S₄`-action on `Fin 3` (via the quotient `S₄ / V₄ ≃ S₃`); re-declared locally (cf. siblings).
local instance s4_action_on_three_via_quotient_compl : MulAction S4 (Fin 3) :=
  MulAction.compHom (Fin 3) s4_quotient_hom_s3

-- Finite-dimensionality of the augmentation carriers (needed for `character`).
local instance : FiniteDimensional k
    ((permutationAugmentationSubrepresentation k S4 (Fin 3)).toSubmodule) := inferInstance
local instance : FiniteDimensional k
    ((permutationAugmentationSubrepresentation k S4 (Fin 4)).toSubmodule) := inferInstance
local instance : FiniteDimensional k
    (TensorProduct k k (permutationAugmentationSubrepresentation k S4 (Fin 4)).toSubmodule) :=
  inferInstance

/-! ### Irreducibility of the five native models over `k` -/

/-- The trivial `S₄`-model is irreducible over any field. -/
lemma s4_trivial_isIrreducible_overField :
    (Representation.trivial k S4 k).IsIrreducible := by
  letI : (unitCharacterRepresentation (1 : S4 →* kˣ)).IsIrreducible :=
    unitCharacterRepresentation_isIrreducible (β := (1 : S4 →* kˣ))
  exact isIrreducible_of_equiv_overField
    (ρ := unitCharacterRepresentation (1 : S4 →* kˣ))
    (σ := Representation.trivial k S4 k)
    (unitCharacterRepresentation_one_equiv_trivial (F := k) (G := S4))

/-- The sign `S₄`-model is irreducible over any field. -/
lemma s4_sign_isIrreducible_overField :
    (s4_sign_representation k).IsIrreducible := by
  simpa [s4_sign_representation] using
    (unitCharacterRepresentation_isIrreducible (β := s4_sign_character k))

/-- The degree-`2` quotient-augmentation model is irreducible over any field where `|S₃|` and
`|Fin 3|` are invertible. -/
lemma s4_quotient_isIrreducible_overField
    [Invertible (Nat.card S3 : k)] [Invertible (Nat.card (Fin 3) : k)] :
    (s4_quotient_augmentation_representation k).IsIrreducible := by
  letI : (permutationAugmentationRepresentation k S3 (Fin 3)).IsIrreducible :=
    s3_augmentation_representation_isIrreducible_overField
  simpa [s4_quotient_augmentation_representation] using
    (isIrreducible_comp_of_surjective_local
      s4_quotient_hom_s3 s4_quotient_hom_s3_surjective
      (permutationAugmentationRepresentation k S3 (Fin 3)))

/-- The degree-`3` sign-twist model `sgn ⊗ std` is irreducible over any field where `|S₄|` and
`|Fin 4|` are invertible. -/
lemma s4_sign_standard_tensor_isIrreducible_overField
    [Invertible (Nat.card S4 : k)] [Invertible (Nat.card (Fin 4) : k)] :
    (s4_sign_standard_tensor_representation k).IsIrreducible := by
  letI : (s4_standard_augmentation_representation k).IsIrreducible :=
    s4_standard_augmentation_representation_isIrreducible_overField
  simpa [s4_sign_standard_tensor_representation, s4_sign_representation] using
    (tprod_unitCharacter_preserves_isIrreducible_overField
      (β := s4_sign_character k) (σ := s4_standard_augmentation_representation k))

/-! ### Simplicity of the `ULift` family members -/

/-- Each of the five `ULift`-lifted explicit models is simple in `FDRep k (ULift S₄)` (semisimple
branch). -/
lemma s4_explicit_family_simple
    [Invertible (Nat.card S3 : k)] [Invertible (Nat.card (Fin 3) : k)]
    [Invertible (Nat.card S4 : k)] [Invertible (Nat.card (Fin 4) : k)]
    (i : Fin 5) : Simple (s4_explicit_family k i) := by
  fin_cases i <;> dsimp [s4_explicit_family]
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_trivial_isIrreducible_overField)
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_sign_isIrreducible_overField)
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_quotient_isIrreducible_overField)
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_standard_augmentation_representation_isIrreducible_overField)
  · exact @FDRep.simple_of_isIrreducible _ _ _ _ _
      ((ulift_group_carrier_representation_isIrreducible_iff_overField _).2
        s4_sign_standard_tensor_isIrreducible_overField)

/-! ### Degrees of the `ULift` family members -/

/-- The five `ULift`-lifted explicit models have degrees `1, 1, 2, 3, 3` over any field. -/
lemma s4_explicit_family_finrank (i : Fin 5) :
    Module.finrank k (s4_explicit_family k i) =
      (match i with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 3) := by
  fin_cases i <;> dsimp [s4_explicit_family]
  · exact (ULift.moduleEquiv : ULift.{w} k ≃ₗ[k] k).finrank_eq.trans (Module.finrank_self k)
  · exact (ULift.moduleEquiv : ULift.{w} k ≃ₗ[k] k).finrank_eq.trans (Module.finrank_self k)
  · refine (ULift.moduleEquiv :
        ULift.{w} ((permutationAugmentationSubrepresentation k S4 (Fin 3)).toSubmodule) ≃ₗ[k]
          _).finrank_eq.trans ?_
    rw [permutationAugmentationSubrepresentation_finrank,
      show Nat.card (Fin 3) = 3 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]
  · refine (ULift.moduleEquiv :
        ULift.{w} ((permutationAugmentationSubrepresentation k S4 (Fin 4)).toSubmodule) ≃ₗ[k]
          _).finrank_eq.trans ?_
    rw [permutationAugmentationSubrepresentation_finrank,
      show Nat.card (Fin 4) = 4 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]
  · refine (ULift.moduleEquiv :
        ULift.{w}
            (TensorProduct k k
              (permutationAugmentationSubrepresentation k S4 (Fin 4)).toSubmodule) ≃ₗ[k]
          _).finrank_eq.trans ?_
    exact s4_sign_standard_tensor_representation_finrank

/-- The square-degree sum of the `ULift` family is `|S₄| = |ULift S₄| = 24`. -/
lemma s4_explicit_family_sum_sq_finrank :
    ∑ i : Fin 5, Module.finrank k (s4_explicit_family k i) ^ 2 = Nat.card (ULift.{w} S4) := by
  have hcard : Nat.card (ULift.{w} S4) = 24 := by
    rw [Nat.card_congr Equiv.ulift, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [hcard, Fin.sum_univ_five, s4_explicit_family_finrank 0, s4_explicit_family_finrank 1,
    s4_explicit_family_finrank 2, s4_explicit_family_finrank 3, s4_explicit_family_finrank 4]
  decide

/-! ### Character values used for non-isomorphism -/

/-- Slot `0` (trivial) takes value `1` on a lifted transposition. -/
lemma s4_explicit_family_char_transposition_zero :
    (s4_explicit_family k 0).character (ULift.up (Equiv.swap (0 : Fin 4) 1)) = 1 := by
  show (ulift_group_carrier_representation (Representation.trivial k S4 k)).character _ = 1
  rw [ulift_group_carrier_character_apply]
  exact s4_trivial_character_transposition_overField

/-- Slot `1` (sign) takes value `-1` on a lifted transposition. -/
lemma s4_explicit_family_char_transposition_one :
    (s4_explicit_family k 1).character (ULift.up (Equiv.swap (0 : Fin 4) 1)) = -1 := by
  show (ulift_group_carrier_representation (s4_sign_representation k)).character _ = -1
  rw [ulift_group_carrier_character_apply]
  exact s4_sign_character_transposition_overField

/-- Slot `3` (standard) takes value `1` on a lifted transposition (needs `|Fin 4|` invertible). -/
lemma s4_explicit_family_char_transposition_three [Invertible (Nat.card (Fin 4) : k)] :
    (s4_explicit_family k 3).character (ULift.up (Equiv.swap (0 : Fin 4) 1)) = 1 := by
  show (ulift_group_carrier_representation (s4_standard_augmentation_representation k)).character _
      = 1
  rw [ulift_group_carrier_character_apply]
  exact s4_standard_character_transposition_overField

/-- Slot `4` (`sgn ⊗ std`) takes value `-1` on a lifted transposition (needs `|Fin 4|`
invertible). -/
lemma s4_explicit_family_char_transposition_four [Invertible (Nat.card (Fin 4) : k)] :
    (s4_explicit_family k 4).character (ULift.up (Equiv.swap (0 : Fin 4) 1)) = -1 := by
  show (ulift_group_carrier_representation (s4_sign_standard_tensor_representation k)).character _
      = -1
  rw [ulift_group_carrier_character_apply]
  exact s4_sign_standard_tensor_character_transposition_overField

/-! ### Pairwise non-isomorphism -/

/-- Two family members with a differing character value at some `g` are non-isomorphic. -/
private lemma s4_explicit_family_not_iso_of_char_ne {i j : Fin 5} (g : ULift.{w} S4)
    (h : (s4_explicit_family k i).character g ≠ (s4_explicit_family k j).character g) :
    ¬ Nonempty (s4_explicit_family k i ≅ s4_explicit_family k j) := by
  rintro ⟨e⟩
  exact h (congrFun (FDRep.char_iso e) g)

/-- Isomorphic family members have equal degree (as natural numbers). -/
private lemma s4_explicit_family_finrank_eq_of_iso {i j : Fin 5}
    (h : Nonempty (s4_explicit_family k i ≅ s4_explicit_family k j)) :
    Module.finrank k (s4_explicit_family k i) = Module.finrank k (s4_explicit_family k j) := by
  rcases h with ⟨e⟩
  exact (Representation.equivOfIso
    ((forget₂ (FDRep k (ULift.{w} S4)) (Rep k (ULift.{w} S4))).mapIso e)).toLinearEquiv.finrank_eq

/-- Slots `0` and `1` are non-isomorphic (semisimple branch). -/
private lemma s4_explicit_family_noniso_zero_one (h2 : (2 : k) ≠ 0) :
    ¬ Nonempty (s4_explicit_family k 0 ≅ s4_explicit_family k 1) := by
  apply s4_explicit_family_not_iso_of_char_ne (ULift.up (Equiv.swap (0 : Fin 4) 1))
  rw [s4_explicit_family_char_transposition_zero, s4_explicit_family_char_transposition_one]
  exact fun h ↦ h2 (show (2 : k) = 0 by linear_combination h)

/-- Slots `3` and `4` are non-isomorphic (semisimple branch). -/
private lemma s4_explicit_family_noniso_three_four [Invertible (Nat.card (Fin 4) : k)]
    (h2 : (2 : k) ≠ 0) :
    ¬ Nonempty (s4_explicit_family k 3 ≅ s4_explicit_family k 4) := by
  apply s4_explicit_family_not_iso_of_char_ne (ULift.up (Equiv.swap (0 : Fin 4) 1))
  rw [s4_explicit_family_char_transposition_three, s4_explicit_family_char_transposition_four]
  exact fun h ↦ h2 (show (2 : k) = 0 by linear_combination h)

/-- The five `ULift`-lifted explicit models are pairwise non-isomorphic (semisimple branch). -/
lemma s4_explicit_family_pairwiseNonisomorphic
    [Invertible (Nat.card (Fin 4) : k)] (h2 : (2 : k) ≠ 0) :
    PairwiseNonisomorphic (s4_explicit_family k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      -- distinct degrees: contradiction at the level of natural-number dimensions
      | (intro hiso
         have hf := s4_explicit_family_finrank_eq_of_iso hiso
         rw [s4_explicit_family_finrank, s4_explicit_family_finrank] at hf
         revert hf; decide)
      -- same-degree pairs `{0,1}`, `{1,0}`, `{3,4}`, `{4,3}`:
      | exact s4_explicit_family_noniso_zero_one h2
      | exact fun ⟨e⟩ ↦ s4_explicit_family_noniso_zero_one h2 ⟨e.symm⟩
      | exact s4_explicit_family_noniso_three_four h2
      | exact fun ⟨e⟩ ↦ s4_explicit_family_noniso_three_four h2 ⟨e.symm⟩

/-! ### Completeness -/

/-- **Completeness of Serre's five explicit `S₄`-models in the semisimple branch.** -/
theorem s4_explicit_family_isCompleteIrreducibleFamily
    [IsAlgClosed k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    IsCompleteIrreducibleFamily (s4_explicit_family k) := by
  letI : Invertible (Nat.card (Fin 3) : k) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 3) = 3 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]
    exact h3)
  letI : Invertible (Nat.card (Fin 4) : k) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 4) = 4 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin],
      show ((4 : ℕ) : k) = (2 : k) * (2 : k) by push_cast; ring]
    exact mul_ne_zero h2 h2)
  letI : Invertible (Nat.card S3 : k) := invertibleOfNonzero (by
    rw [show Nat.card S3 = 6 from by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((6 : ℕ) : k) = (2 : k) * (3 : k) by push_cast; ring]
    exact mul_ne_zero h2 h3)
  letI : Invertible (Nat.card S4 : k) := invertibleOfNonzero (by
    rw [show Nat.card S4 = 24 from by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((24 : ℕ) : k) = (2 : k) * (2 : k) * (2 : k) * (3 : k) by push_cast; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3)
  letI : NeZero (Nat.card (ULift.{w} S4) : k) := by
    refine ⟨?_⟩
    rw [show Nat.card (ULift.{w} S4) = 24 from by
          rw [Nat.card_congr Equiv.ulift, Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((24 : ℕ) : k) = (2 : k) * (2 : k) * (2 : k) * (3 : k) by push_cast; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3
  refine isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card (s4_explicit_family k)
    (fun i ↦ s4_explicit_family_simple i)
    (s4_explicit_family_pairwiseNonisomorphic h2) ?_
  convert s4_explicit_family_sum_sq_finrank (k := k) using 2
  exact Finset.ext (fun x ↦ by simp)

end

end Representation
