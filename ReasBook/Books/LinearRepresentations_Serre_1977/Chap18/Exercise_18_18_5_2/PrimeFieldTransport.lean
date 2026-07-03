import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_2_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.PrimeFieldInfrastructure
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

noncomputable section

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k]

/-- Helper for Exercise 18-18.5-2: scalar extension transports characters by the coefficient map
over any field extension. -/
lemma scalarExtension_character_eq_map_over_field
    {G : Type*} [Group G]
    {W₀ : Type*} [AddCommGroup W₀] [Module ↥(⊥ : Subfield k) W₀]
    [FiniteDimensional ↥(⊥ : Subfield k) W₀]
    (ρ₀ : Representation ↥(⊥ : Subfield k) G W₀) :
    (Representation.scalarExtension (k := k) ρ₀).character =
      fun g ↦ algebraMap ↥(⊥ : Subfield k) k (ρ₀.character g) := by
  -- Traces commute with base change, so scalar extension keeps the same character values after
  -- applying the coefficient map.
  ext g
  exact LinearMap.trace_baseChange (ρ₀ g) k

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field sign character has the
same ordinary character as the native sign slot over `k`. -/
lemma s4_primefield_sign_character_map
    (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_sign_representation ↥(⊥ : Subfield k)).character g) =
        (s4_sign_representation k).character g := by
  -- Both characters come from the same scalar-valued sign homomorphism.
  simp [s4_sign_representation, s4_sign_character, unitCharacterRepresentation_character_apply]

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field quotient-augmentation
character matches the native degree-`2` slot outside characteristic `3`. -/
lemma s4_primefield_quotient_augmentation_character_map
    (hchar3 : ringChar k ≠ 3) (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_quotient_augmentation_representation ↥(⊥ : Subfield k)).character g) =
        (s4_quotient_augmentation_representation k).character g := by
  -- Route correction: compare both sides through the same permutation-minus-trivial formula,
  -- rather than trying to build the scalar-extension equivalence first.
  calc
    algebraMap ↥(⊥ : Subfield k) k
        ((s4_quotient_augmentation_representation ↥(⊥ : Subfield k)).character g)
        = algebraMap ↥(⊥ : Subfield k) k
            ((Representation.ofMulAction ↥(⊥ : Subfield k) S4 (Fin 3)).character g -
              (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)).character g) := by
              -- First rewrite the prime-field slot by the quotient permutation splitting.
              rw [s4_quotient_augmentation_character_eq_permutation_sub_one
                (k := ↥(⊥ : Subfield k))]
              · rfl
              · simpa using hchar3
    _ = algebraMap ↥(⊥ : Subfield k) k
          ((Representation.ofMulAction ↥(⊥ : Subfield k) S4 (Fin 3)).character g) -
        algebraMap ↥(⊥ : Subfield k) k
          ((Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)).character g) := by
            simp
    _ = (Representation.ofMulAction k S4 (Fin 3)).character g -
          (Representation.trivial k S4 k).character g := by
            -- Permutation characters are fixed-point counts, hence field-independent.
            rw [Representation.ofMulAction_character_eq_ncard_fixedBy,
              Representation.ofMulAction_character_eq_ncard_fixedBy]
            simp [Representation.character]
    _ = (s4_quotient_augmentation_representation k).character g := by
          -- Finally recover the ambient degree-`2` slot from the same splitting formula.
          rw [s4_quotient_augmentation_character_eq_permutation_sub_one (k := k) hchar3 g]

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field standard
augmentation character matches the native degree-`3` slot outside characteristic `2`. -/
lemma s4_primefield_standard_augmentation_character_map
    (hchar2 : ringChar k ≠ 2) (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_standard_augmentation_representation ↥(⊥ : Subfield k)).character g) =
        (s4_standard_augmentation_representation k).character g := by
  -- Route correction: again use the permutation-minus-trivial character identity on both sides.
  calc
    algebraMap ↥(⊥ : Subfield k) k
        ((s4_standard_augmentation_representation ↥(⊥ : Subfield k)).character g)
        = algebraMap ↥(⊥ : Subfield k) k
            ((Representation.ofMulAction ↥(⊥ : Subfield k) S4 (Fin 4)).character g -
              (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)).character g) := by
              -- First rewrite the prime-field standard slot by the natural permutation splitting.
              rw [s4_standard_augmentation_character_eq_permutation_sub_one
                (k := ↥(⊥ : Subfield k))]
              · rfl
              · simpa using hchar2
    _ = algebraMap ↥(⊥ : Subfield k) k
          ((Representation.ofMulAction ↥(⊥ : Subfield k) S4 (Fin 4)).character g) -
        algebraMap ↥(⊥ : Subfield k) k
          ((Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)).character g) := by
            simp
    _ = (Representation.ofMulAction k S4 (Fin 4)).character g -
          (Representation.trivial k S4 k).character g := by
            -- Fixed-point counts do not depend on the coefficient field.
            rw [Representation.ofMulAction_character_eq_ncard_fixedBy,
              Representation.ofMulAction_character_eq_ncard_fixedBy]
            simp [Representation.character]
    _ = (s4_standard_augmentation_representation k).character g := by
          -- Recover the ambient standard slot from the same splitting formula.
          rw [s4_standard_augmentation_character_eq_permutation_sub_one (k := k) hchar2 g]

/-- Helper for Exercise 18-18.5-2: the scalar extension of the prime-field `sgn ⊗ std`
character matches the native sign-twisted standard slot outside characteristic `2`. -/
lemma s4_primefield_sign_standard_tensor_character_map
    (hchar2 : ringChar k ≠ 2) (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
      ((s4_sign_standard_tensor_representation ↥(⊥ : Subfield k)).character g) =
        (s4_sign_standard_tensor_representation k).character g := by
  -- Route correction: compare the tensor slot via `char_tensor` and the already repaired
  -- factorwise prime-field bridges, rather than rebuilding the scalar-extension equivalence.
  calc
    algebraMap ↥(⊥ : Subfield k) k
        ((s4_sign_standard_tensor_representation ↥(⊥ : Subfield k)).character g)
        = algebraMap ↥(⊥ : Subfield k) k
            (((s4_sign_representation ↥(⊥ : Subfield k)).character g) *
              ((s4_standard_augmentation_representation ↥(⊥ : Subfield k)).character g)) := by
              -- First rewrite the prime-field tensor character as the product of its two factors.
              rw [by
                simpa [s4_sign_standard_tensor_representation] using
                  congrFun
                    (Representation.char_tensor
                      (ρ := s4_sign_representation ↥(⊥ : Subfield k))
                      (σ := s4_standard_augmentation_representation ↥(⊥ : Subfield k)))
                    g]
    _ = algebraMap ↥(⊥ : Subfield k) k
          ((s4_sign_representation ↥(⊥ : Subfield k)).character g) *
        algebraMap ↥(⊥ : Subfield k) k
          ((s4_standard_augmentation_representation ↥(⊥ : Subfield k)).character g) := by
            simp
    _ = (s4_sign_representation k).character g *
          (s4_standard_augmentation_representation k).character g := by
            -- The tensor factors already have explicit coefficientwise comparison owners.
            rw [s4_primefield_sign_character_map (k := k) g,
              s4_primefield_standard_augmentation_character_map (k := k) hchar2 g]
    _ = (s4_sign_standard_tensor_representation k).character g := by
          -- Recover the ambient tensor slot from the same character-product identity.
          symm
          simpa [s4_sign_standard_tensor_representation] using
            congrFun
              (Representation.char_tensor
                (ρ := s4_sign_representation k)
                (σ := s4_standard_augmentation_representation k))
              g

/-- Helper for Exercise 18-18.5-2: in characteristic `2`, the scalar extension of the prime-field
augmentation model has the same Brauer character on `2`-regular elements as the native
augmentation slot. -/
lemma s3_primefield_augmentation_scalar_extension_modular_eq_native
    (hchar2 : ringChar k = 2)
    (lift : PrimeToPRoot 2 k →* ℂˣ)
    (s : { t : Equiv.Perm (Fin 3) // IsPRegular 2 t }) :
    φ[PrimeToPRoot.toFieldLift lift]
        (Representation.scalarExtension (k := k)
          (permutationAugmentationRepresentation ↥(⊥ : Subfield k)
            (Equiv.Perm (Fin 3)) (Fin 3))) s =
      φ[PrimeToPRoot.toFieldLift lift]
        (permutationAugmentationRepresentation k (Equiv.Perm (Fin 3)) (Fin 3)) s := by
  let _ := hchar2
  -- Route correction: compare the two modular characters directly on the two `2`-regular
  -- conjugacy-class representatives instead of introducing a separate ordinary-character bridge.
  rcases s with ⟨g, hg⟩
  fin_cases g <;>
    simp [Representation.scalarExtension, permutationAugmentationRepresentation,
      permutationAugmentationCharacter, Representation.modularCharacter,
      Representation.character, Representation.ofMulAction_character_eq_ncard_fixedBy,
      unitCharacterRepresentation_character_apply, charpolyRoot_primeToPRoot_coe, hg]

/-- Helper for Exercise 18-18.5-2: in characteristic `3`, the scalar extensions of the prime-field
standard and sign-twisted-standard models have the same Brauer characters on `3`-regular elements
as the native degree-`3` slots. -/
lemma s4_primefield_degree_three_scalar_extension_modular_eq_native
    (hchar3 : ringChar k = 3)
    (lift : PrimeToPRoot 3 k →* ℂˣ)
    (s : { t : S4 // IsPRegular 3 t }) :
    φ[PrimeToPRoot.toFieldLift lift]
        (Representation.scalarExtension (k := k)
          (s4_standard_augmentation_representation ↥(⊥ : Subfield k))) s =
      φ[PrimeToPRoot.toFieldLift lift]
        (s4_standard_augmentation_representation k) s ∧
    φ[PrimeToPRoot.toFieldLift lift]
        (Representation.scalarExtension (k := k)
          (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))) s =
      φ[PrimeToPRoot.toFieldLift lift]
        (s4_sign_standard_tensor_representation k) s := by
  let _ := hchar3
  rcases s with ⟨g, hg⟩
  constructor
  · -- The standard slot comparison reduces to the four `3`-regular conjugacy-class types.
    fin_cases g <;>
      simp [Representation.scalarExtension, s4_standard_augmentation_representation,
        permutationAugmentationCharacter, Representation.modularCharacter,
        Representation.character, Representation.ofMulAction_character_eq_ncard_fixedBy,
        unitCharacterRepresentation_character_apply, charpolyRoot_primeToPRoot_coe, hg]
  · -- The sign twist uses the same `3`-regular enumeration with the explicit tensor model.
    fin_cases g <;>
      simp [Representation.scalarExtension, s4_sign_standard_tensor_representation,
        s4_sign_representation, s4_sign_character, s4_standard_augmentation_representation,
        permutationAugmentationCharacter, Representation.modularCharacter,
        Representation.character, Representation.ofMulAction_character_eq_ncard_fixedBy,
        unitCharacterRepresentation_character_apply, charpolyRoot_primeToPRoot_coe, hg]

end

end Representation
