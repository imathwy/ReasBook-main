import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels

/-!
# Characteristic-uniform transposition character values (support for Exercise 18.5.2)

For the pairwise non-isomorphism of Serre's five `S₄`-models in the semisimple branch
(`ringChar k ∉ {2, 3}`), one only needs to separate the two degree-`1` models (`1` vs `sgn`) and
the two degree-`3` models (`std` vs `sgn ⊗ std`).  Both pairs are separated by the value of the
character on a transposition:

* `1` and `sgn` take values `1` and `-1`;
* `std` and `sgn ⊗ std` take values `1` and `-1`.

These values differ as soon as `(2 : F) ≠ 0` (i.e. `ringChar F ≠ 2`), which holds throughout the
semisimple branch.  The computations below are valid over an *arbitrary* field `F` (the standard
model needs `|Fin 4|` invertible, automatic when `ringChar F ≠ 2`), superseding the `ℂ`-only
versions in `OrdinaryExplicitModels.lean`.
-/

attribute [-instance] Field.henselian

noncomputable section

open Representation

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {F : Type*} [Field F]

/-- The sign model of `S₄` takes value `-1` on the transposition `(0 1)`, over any field. -/
theorem s4_sign_character_transposition_overField :
    (s4_sign_representation F).character (Equiv.swap (0 : Fin 4) 1) = -1 := by
  calc
    (s4_sign_representation F).character (Equiv.swap (0 : Fin 4) 1)
        = ((s4_sign_character F) (Equiv.swap (0 : Fin 4) 1) : F) := by
            simpa [s4_sign_representation] using
              (unitCharacterRepresentation_character_apply
                (β := s4_sign_character F) (Equiv.swap (0 : Fin 4) 1))
    _ = -1 := by
          simp [s4_sign_character]

/-- The standard degree-`3` model of `S₄` takes value `1` on the transposition `(0 1)`, over any
field in which `|Fin 4| = 4` is invertible (in particular whenever `ringChar F ≠ 2`). -/
theorem s4_standard_character_transposition_overField
    [Invertible (Nat.card (Fin 4) : F)] :
    (s4_standard_augmentation_representation F).character (Equiv.swap (0 : Fin 4) 1) = 1 := by
  classical
  set g : S4 := Equiv.swap (0 : Fin 4) 1 with hg
  have hperm_split :=
    permutation_character_eq_trivial_add_augmentation (k := F) (G := S4) (X := Fin 4)
  have hfixed : (MulAction.fixedBy (Fin 4) g).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hperm : (Representation.ofMulAction F S4 (Fin 4)).character g = 2 := by
    rw [Representation.ofMulAction_character_eq_ncard_fixedBy, hfixed]
    norm_num
  have htriv : (Representation.trivial F S4 F).character g = 1 := by
    simp [Representation.character]
  have hvalue :
      (2 : F) = 1 + permutationAugmentationCharacter F S4 (Fin 4) g := by
    simpa [hperm, htriv] using congrFun hperm_split g
  have hvalue' := congrArg (fun z : F ↦ z - 1) hvalue
  norm_num at hvalue'
  simpa [s4_standard_augmentation_representation, permutationAugmentationCharacter] using
    hvalue'.symm

/-- The sign-twist degree-`3` model `sgn ⊗ std` takes value `-1` on the transposition `(0 1)`,
over any field in which `|Fin 4|` is invertible. -/
theorem s4_sign_standard_tensor_character_transposition_overField
    [Invertible (Nat.card (Fin 4) : F)] :
    (s4_sign_standard_tensor_representation F).character (Equiv.swap (0 : Fin 4) 1) = -1 := by
  calc
    (s4_sign_standard_tensor_representation F).character (Equiv.swap (0 : Fin 4) 1)
        = (s4_sign_representation F).character (Equiv.swap (0 : Fin 4) 1) *
            (s4_standard_augmentation_representation F).character (Equiv.swap (0 : Fin 4) 1) := by
            simpa [s4_sign_standard_tensor_representation] using
              congrFun
                (Representation.char_tensor
                  (ρ := s4_sign_representation F)
                  (σ := s4_standard_augmentation_representation F))
                (Equiv.swap (0 : Fin 4) 1)
    _ = (-1 : F) * 1 := by
          rw [s4_sign_character_transposition_overField,
            s4_standard_character_transposition_overField]
    _ = -1 := by norm_num

/-- The trivial model of `S₄` takes value `1` on the transposition `(0 1)`, over any field. -/
theorem s4_trivial_character_transposition_overField :
    (Representation.trivial F S4 F).character (Equiv.swap (0 : Fin 4) 1) = 1 := by
  simp [Representation.character]

/-- The two degree-`1` models (`1` and `sgn`) are non-isomorphic whenever `(2 : F) ≠ 0` (i.e.
`ringChar F ≠ 2`): they take values `1` and `-1` on a transposition. -/
theorem s4_trivial_not_equiv_sign (h2 : (2 : F) ≠ 0) :
    ¬ Nonempty ((Representation.trivial F S4 F).Equiv (s4_sign_representation F)) := by
  rintro ⟨e⟩
  have hchar := Representation.char_iso e
  have := congrFun hchar (Equiv.swap (0 : Fin 4) 1)
  rw [s4_trivial_character_transposition_overField,
    s4_sign_character_transposition_overField] at this
  -- `1 = -1` forces `2 = 0`.
  apply h2
  linear_combination this

/-- The two degree-`3` models (`std` and `sgn ⊗ std`) are non-isomorphic whenever `(2 : F) ≠ 0`:
they take values `1` and `-1` on a transposition.  (`|Fin 4|` is then invertible.) -/
theorem s4_standard_not_equiv_sign_tensor (h2 : (2 : F) ≠ 0) :
    ¬ Nonempty ((s4_standard_augmentation_representation F).Equiv
        (s4_sign_standard_tensor_representation F)) := by
  -- `4 = 2 * 2` is invertible since `2 ≠ 0`.
  letI : Invertible (Nat.card (Fin 4) : F) := by
    apply invertibleOfNonzero
    have h4 : (Nat.card (Fin 4) : F) = 2 * 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
    rw [h4]; exact mul_ne_zero h2 h2
  rintro ⟨e⟩
  have hchar := Representation.char_iso e
  have := congrFun hchar (Equiv.swap (0 : Fin 4) 1)
  rw [s4_standard_character_transposition_overField,
    s4_sign_standard_tensor_character_transposition_overField] at this
  apply h2
  linear_combination this

end

end Representation
