import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.Index
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.SemisimpleAssembly
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.ModularDescent
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.CharTwoBaseChange
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.CharTwoS3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.CharThreeCompleteness
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_2.CharThreeBaseChange
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

-- The support chain (via Fong–Swan, `Serre.Chap18.Exercise_18_18_5_1`) re-introduces the global
-- `Field.henselian` instance, which makes typeclass search diverge on trivial `Module …` goals.
-- Instance removals are file-local and don't propagate to importers, so re-disable it here
-- (cf. LinearCharacters, OrdinaryExplicitModels, PrimeFieldInfrastructure, PrimeFieldTransport,
-- ModularDescent).  This is not a heartbeat mask.
attribute [-instance] Field.henselian

noncomputable section

open CategoryTheory

universe u

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V]

-- The `S₄`-action on `Fin 3` (via the quotient `S₄ / V₄ ≃ S₃`) is a `local instance` in
-- `LinearCharacters`, so it does not propagate to importers.  Re-declare it here (cf.
-- `PrimeFieldTransport.lean`) so the degree-`2` quotient-augmentation model typechecks.
local instance s4_action_on_three_via_quotient'' : MulAction S4 (Fin 3) :=
  MulAction.compHom (Fin 3) s4_quotient_hom_s3

-- Pin the canonical submodule `AddCommGroup`/`Module` structures (cf. `PrimeFieldTransport.lean`)
-- to avoid the `AddCommGroup.toAddCommMonoid` vs `Submodule.addCommMonoid` diamond when forming
-- the scalar extension of the augmentation models.
local instance :
    AddCommGroup
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule.addCommGroup
local instance :
    Module ↥(⊥ : Subfield k)
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule.module
local instance :
    AddCommGroup
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule.addCommGroup
local instance :
    Module ↥(⊥ : Subfield k)
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule.module
local instance : FiniteDimensional ↥(⊥ : Subfield k)
    ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 3)).toSubmodule :=
  inferInstance
local instance : FiniteDimensional ↥(⊥ : Subfield k)
    ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  inferInstance

/-- **Remaining gap of the semisimple branch (absolute irreducibility of the five explicit
prime-field models).**  The scalar extensions to the algebraically closed field `k` of Serre's five
explicit prime-field `S₄`-models are irreducible.  This holds because `S₄` is a *rational* group:
each of these five models is absolutely irreducible (Schur index `1`), so base change to `k` keeps
it simple.  This is the single open atom of the semisimple branch of Exercise 18.5.2; everything
else (completeness of the native family, the `ULift S₄ → S₄` transport, the prime-field character
bridge, and character ⟹ isomorphism) is proven.

Note this must be stated for the five *specific* models: the analogous statement for an arbitrary
representation irreducible over the prime field is *false* (e.g. an irreducible `𝔽₂[ℤ/3]`-module
splits over `𝔽̄₂`).  It is proven via `scalarExtension_isIrreducible_of_native` (a Schur argument:
each native model over `k` is irreducible and has the same character and dimension as its
scalar extension, so a nonzero intertwiner between them is an isomorphism). -/
theorem s4_scalarExtension_explicit_models_isIrreducible (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    (Representation.scalarExtension (k := k)
        (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k))).IsIrreducible ∧
    (Representation.scalarExtension (k := k)
        (s4_sign_representation ↥(⊥ : Subfield k))).IsIrreducible ∧
    (Representation.scalarExtension (k := k)
        (s4_quotient_augmentation_representation ↥(⊥ : Subfield k))).IsIrreducible ∧
    (Representation.scalarExtension (k := k)
        (s4_standard_augmentation_representation ↥(⊥ : Subfield k))).IsIrreducible ∧
    (Representation.scalarExtension (k := k)
        (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))).IsIrreducible := by
  haveI : CharP k (ringChar k) := ringChar.charP k
  have hrc2 : ringChar k ≠ 2 := by
    intro h; apply h2; have h0 := CharP.cast_eq_zero k (ringChar k); rw [h] at h0; exact_mod_cast h0
  have hrc3 : ringChar k ≠ 3 := by
    intro h; apply h3; have h0 := CharP.cast_eq_zero k (ringChar k); rw [h] at h0; exact_mod_cast h0
  -- invertibilities over `k`
  letI : Invertible (Nat.card (Fin 3) : k) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 3) = 3 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]; exact h3)
  letI : Invertible (Nat.card (Fin 4) : k) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 4) = 4 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin],
      show ((4 : ℕ) : k) = (2 : k) * (2 : k) by push_cast; ring]
    exact mul_ne_zero h2 h2)
  letI : Invertible (Nat.card (Equiv.Perm (Fin 3)) : k) := invertibleOfNonzero (by
    rw [show Nat.card (Equiv.Perm (Fin 3)) = 6 from by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((6 : ℕ) : k) = (2 : k) * (3 : k) by push_cast; ring]
    exact mul_ne_zero h2 h3)
  letI : Invertible (Nat.card S4 : k) := invertibleOfNonzero (by
    rw [show Nat.card S4 = 24 from by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((24 : ℕ) : k) = (2 : k) * (2 : k) * (2 : k) * (3 : k) by push_cast; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3)
  -- native irreducibilities over `k`
  haveI : (s4_quotient_augmentation_representation k).IsIrreducible :=
    s4_quotient_isIrreducible_overField
  haveI : (s4_standard_augmentation_representation k).IsIrreducible :=
    s4_standard_augmentation_representation_isIrreducible_overField
  haveI : (s4_sign_standard_tensor_representation k).IsIrreducible :=
    s4_sign_standard_tensor_isIrreducible_overField
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- trivial
    haveI : (Representation.trivial k S4 k).IsIrreducible := s4_trivial_isIrreducible_overField
    refine scalarExtension_isIrreducible_of_native
      (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k))
      (Representation.trivial k S4 k) ?_ ?_
    · refine Module.finrank_baseChange.trans ?_
      simp [permutationAugmentationSubrepresentation_finrank,
        s4_sign_standard_tensor_representation_finrank]
    · funext g
      simp only [scalarExtension_character_eq_map_over_field]
      have hb : (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)).character g = 1 := by
        simp [Representation.character]
      have ht : (Representation.trivial k S4 k).character g = 1 := by simp [Representation.character]
      rw [hb, ht, map_one]
  · -- sign
    haveI : (s4_sign_representation k).IsIrreducible := s4_sign_isIrreducible_overField
    refine scalarExtension_isIrreducible_of_native
      (s4_sign_representation ↥(⊥ : Subfield k)) (s4_sign_representation k) ?_ ?_
    · refine Module.finrank_baseChange.trans ?_
      simp [permutationAugmentationSubrepresentation_finrank,
        s4_sign_standard_tensor_representation_finrank]
    · funext g
      simp only [scalarExtension_character_eq_map_over_field]
      exact s4_primefield_sign_character_map (k := k) g
  · -- quotient augmentation
    refine scalarExtension_isIrreducible_of_native
      (s4_quotient_augmentation_representation ↥(⊥ : Subfield k))
      (s4_quotient_augmentation_representation k) ?_ ?_
    · refine Module.finrank_baseChange.trans ?_
      exact permutationAugmentationSubrepresentation_finrank.trans
        (permutationAugmentationSubrepresentation_finrank (F := k)).symm
    · funext g
      simp only [scalarExtension_character_eq_map_over_field]
      exact s4_primefield_quotient_augmentation_character_map (k := k) hrc3 g
  · -- standard augmentation
    refine scalarExtension_isIrreducible_of_native
      (s4_standard_augmentation_representation ↥(⊥ : Subfield k))
      (s4_standard_augmentation_representation k) ?_ ?_
    · refine Module.finrank_baseChange.trans ?_
      exact permutationAugmentationSubrepresentation_finrank.trans
        (permutationAugmentationSubrepresentation_finrank (F := k)).symm
    · funext g
      simp only [scalarExtension_character_eq_map_over_field]
      exact s4_primefield_standard_augmentation_character_map (k := k) hrc2 g
  · -- sign ⊗ standard
    refine scalarExtension_isIrreducible_of_native
      (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))
      (s4_sign_standard_tensor_representation k) ?_ ?_
    · refine Module.finrank_baseChange.trans ?_
      exact s4_sign_standard_tensor_representation_finrank.trans
        (s4_sign_standard_tensor_representation_finrank (F := k)).symm
    · funext g
      simp only [scalarExtension_character_eq_map_over_field]
      exact s4_primefield_sign_standard_tensor_character_map (k := k) hrc2 g

/-- The disjunction asserting that `ρ` is equivalent to the scalar extension of one of the five
explicit prime-field `S₄`-models. -/
abbrev S4PrimefieldModelDisjunction (ρ : Representation k S4 V) : Prop :=
    Nonempty (ρ.Equiv
        (Representation.scalarExtension (k := k)
          (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)))) ∨
    Nonempty (ρ.Equiv
        (Representation.scalarExtension (k := k)
          (s4_sign_representation ↥(⊥ : Subfield k)))) ∨
    Nonempty (ρ.Equiv
        (Representation.scalarExtension (k := k)
          (s4_quotient_augmentation_representation ↥(⊥ : Subfield k)))) ∨
    Nonempty (ρ.Equiv
        (Representation.scalarExtension (k := k)
          (s4_standard_augmentation_representation ↥(⊥ : Subfield k)))) ∨
    Nonempty (ρ.Equiv
        (Representation.scalarExtension (k := k)
          (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))))

/-- **Semisimple branch** (`(2 : k) ≠ 0` and `(3 : k) ≠ 0`, i.e. `ringChar k ∉ {2, 3}`).
Every irreducible `S₄`-representation over the algebraically closed field `k` is equivalent to the
scalar extension of one of Serre's five explicit prime-field models.  This is the fully-proven
branch (modulo the single absolute-irreducibility atom
`scalarExtension_isIrreducible_of_isIrreducible_primeField`): the native family is complete
(`s4_explicit_family_isCompleteIrreducibleFamily`), the matched isomorphism transports from
`ULift S₄` to `S₄` (`rho_char_eq_of_lift`), the prime-field character bridge identifies the
characters (`PrimeFieldTransport`), and equal characters of irreducibles give an equivalence
(`nonempty_equiv_of_char_eq_isIrr`). -/
theorem s4_simple_equiv_scalarExtension_primefield_model_semisimple
    (ρ : Representation k S4 V) [ρ.IsIrreducible] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    S4PrimefieldModelDisjunction ρ := by
  classical
  -- characteristic away from `2` and `3`
  haveI : CharP k (ringChar k) := ringChar.charP k
  have hrc2 : ringChar k ≠ 2 := by
    intro h
    apply h2
    have h0 := CharP.cast_eq_zero k (ringChar k)
    rw [h] at h0
    exact_mod_cast h0
  have hrc3 : ringChar k ≠ 3 := by
    intro h
    apply h3
    have h0 := CharP.cast_eq_zero k (ringChar k)
    rw [h] at h0
    exact_mod_cast h0
  -- transport `2 ≠ 0`, `3 ≠ 0` to the prime subfield
  have h2' : (2 : ↥(⊥ : Subfield k)) ≠ 0 := by
    intro h
    apply h2
    have hmap : (algebraMap ↥(⊥ : Subfield k) k) (2 : ↥(⊥ : Subfield k)) = (2 : k) := map_ofNat _ _
    rw [← hmap, h, map_zero]
  have h3' : (3 : ↥(⊥ : Subfield k)) ≠ 0 := by
    intro h
    apply h3
    have hmap : (algebraMap ↥(⊥ : Subfield k) k) (3 : ↥(⊥ : Subfield k)) = (3 : k) := map_ofNat _ _
    rw [← hmap, h, map_zero]
  -- invertibilities over `k`
  letI : Invertible (Nat.card S4 : k) := invertibleOfNonzero (by
    rw [show Nat.card S4 = 24 from by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((24 : ℕ) : k) = (2 : k) * (2 : k) * (2 : k) * (3 : k) by push_cast; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3)
  -- invertibilities over the prime subfield
  letI : Invertible (Nat.card (Fin 3) : ↥(⊥ : Subfield k)) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 3) = 3 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]; exact h3')
  letI : Invertible (Nat.card (Fin 4) : ↥(⊥ : Subfield k)) := invertibleOfNonzero (by
    rw [show Nat.card (Fin 4) = 4 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin],
      show ((4 : ℕ) : ↥(⊥ : Subfield k)) = (2 : ↥(⊥ : Subfield k)) * (2 : ↥(⊥ : Subfield k)) by
        push_cast; ring]
    exact mul_ne_zero h2' h2')
  letI : Invertible (Nat.card (Equiv.Perm (Fin 3)) : ↥(⊥ : Subfield k)) := invertibleOfNonzero (by
    rw [show Nat.card (Equiv.Perm (Fin 3)) = 6 from by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((6 : ℕ) : ↥(⊥ : Subfield k)) = (2 : ↥(⊥ : Subfield k)) * (3 : ↥(⊥ : Subfield k)) by
        push_cast; ring]
    exact mul_ne_zero h2' h3')
  letI : Invertible (Nat.card S4 : ↥(⊥ : Subfield k)) := invertibleOfNonzero (by
    rw [show Nat.card S4 = 24 from by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide,
      show ((24 : ℕ) : ↥(⊥ : Subfield k))
          = (2 : ↥(⊥ : Subfield k)) * (2 : ↥(⊥ : Subfield k)) * (2 : ↥(⊥ : Subfield k))
            * (3 : ↥(⊥ : Subfield k)) by push_cast; ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2' h2') h2') h3')
  -- finite-dimensionality and the lift of `ρ`
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Representation.IsIrreducible
      (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom) :=
    isIrreducible_comp_of_mulEquiv_overField
      (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4) ρ
  -- completeness of the native family and the matching isomorphism
  have hcomplete := s4_explicit_family_isCompleteIrreducibleFamily (k := k) h2 h3
  obtain ⟨j, ⟨e⟩⟩ := IsCompleteIrreducibleFamily.exists_iso_of_representation
    (s4_explicit_family k) hcomplete
    (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom) inferInstance
  have hcl :
      (FDRep.of (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom)).character
        = (s4_explicit_family k j).character := FDRep.char_iso e
  obtain ⟨hIrr0, hIrr1, hIrr2, hIrr3, hIrr4⟩ :=
    s4_scalarExtension_explicit_models_isIrreducible (k := k) h2 h3
  fin_cases j
  -- slot 0: trivial
  · refine Or.inl ?_
    refine finish_branch ρ (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k))
      hIrr0 (Representation.trivial k S4 k) 0 rfl ?_ hcl
    funext g
    simp only [scalarExtension_character_eq_map_over_field]
    have hb : (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k)).character g = 1 := by
      simp [Representation.character]
    have ht : (Representation.trivial k S4 k).character g = 1 := by simp [Representation.character]
    rw [hb, ht, map_one]
  -- slot 1: sign
  · refine Or.inr (Or.inl ?_)
    refine finish_branch ρ (s4_sign_representation ↥(⊥ : Subfield k))
      hIrr1 (s4_sign_representation k) 1 rfl ?_ hcl
    funext g
    simp only [scalarExtension_character_eq_map_over_field]
    exact s4_primefield_sign_character_map (k := k) g
  -- slot 2: quotient augmentation
  · refine Or.inr (Or.inr (Or.inl ?_))
    refine finish_branch ρ (s4_quotient_augmentation_representation ↥(⊥ : Subfield k))
      hIrr2 (s4_quotient_augmentation_representation k) 2 rfl ?_ hcl
    funext g
    simp only [scalarExtension_character_eq_map_over_field]
    exact s4_primefield_quotient_augmentation_character_map (k := k) hrc3 g
  -- slot 3: standard augmentation
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    refine finish_branch ρ (s4_standard_augmentation_representation ↥(⊥ : Subfield k))
      hIrr3 (s4_standard_augmentation_representation k) 3 rfl ?_ hcl
    funext g
    simp only [scalarExtension_character_eq_map_over_field]
    exact s4_primefield_standard_augmentation_character_map (k := k) hrc2 g
  -- slot 4: sign ⊗ standard
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    refine finish_branch ρ (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))
      hIrr4 (s4_sign_standard_tensor_representation k) 4 rfl ?_ hcl
    funext g
    simp only [scalarExtension_character_eq_map_over_field]
    exact s4_primefield_sign_standard_tensor_character_map (k := k) hrc2 g

/-- The trivial `S₃`-representation inflated along `S₄ ↠ S₃` is the trivial `S₄`-representation. -/
private def char_two_trivialComp_equiv :
    Representation.Equiv
      ((Representation.trivial k (Equiv.Perm (Fin 3)) k).comp s4_quotient_hom_s3)
      (Representation.trivial k S4 k) :=
  Representation.Equiv.mk (LinearEquiv.refl k k) (fun g => rfl)

/-- The natural (augmentation) `S₃`-module inflated along `S₄ ↠ S₃` is the degree-`2` quotient
model `q₂` over `k`. -/
private def char_two_inflationComp_equiv :
    Representation.Equiv
      ((permutationAugmentationRepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).comp
        s4_quotient_hom_s3)
      (s4_quotient_augmentation_representation k) :=
  Representation.Equiv.mk (LinearEquiv.refl k _) (fun g => rfl)

/-- **Characteristic-`2` branch** (`(2 : k) = 0`): residual modular case.  Over an algebraically
closed field of characteristic `2`, `k[S₄]` is not semisimple; only the trivial (= sign) and the
degree-`2` quotient model stay irreducible.  Every irreducible `S₄`-representation descends along
`S₄ ↠ S₃` (the normal Klein-four `2`-subgroup acts trivially), and the descended irreducible
`S₃`-module is either trivial or the natural `2`-dimensional module, which pull back to the trivial
and `q₂` models respectively. -/
theorem s4_simple_equiv_scalarExtension_primefield_model_char_two
    (ρ : Representation k S4 V) [ρ.IsIrreducible] (h2 : (2 : k) = 0) :
    S4PrimefieldModelDisjunction ρ := by
  classical
  -- characteristic `2`
  have hrc2 : ringChar k = 2 := by
    have hdvd : ringChar k ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
    exact ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left CharP.ringChar_ne_one
  -- descend `ρ` to an irreducible `S₃`-representation along `S₄ ↠ S₃`
  obtain ⟨σ, hσirr, hρσ⟩ := s4_char_two_descends_to_s3 hrc2 ρ
  letI : σ.IsIrreducible := hσirr
  -- classify the descended `S₃`-representation
  rcases s3_char_two_irreducible_dichotomy h2 σ with h | h
  · -- trivial slot
    refine Or.inl ⟨?_⟩
    rw [hρσ]
    exact (((h.some).precomp s4_quotient_hom_s3).trans char_two_trivialComp_equiv).trans
      s4_primefield_trivial_scalarExtension_equiv.symm
  · -- degree-`2` quotient-augmentation slot
    refine Or.inr (Or.inr (Or.inl ⟨?_⟩))
    have eB :=
      (scalarExtension_permutationAugmentationRepresentation_equiv
        (k₀ := ↥(⊥ : Subfield k)) (k := k) (G := S4) (X := Fin 3)).some
    rw [hρσ]
    exact (((h.some).precomp s4_quotient_hom_s3).trans char_two_inflationComp_equiv).trans eB.symm

/-- Reverse of `Equiv.precomp`: a representation equivalence between the pullbacks of `ρ` and `σ`
along a group *isomorphism* descends to an equivalence between `ρ` and `σ` themselves. -/
def equiv_of_comp_mulEquiv {G H : Type*} [Group G] [Group H] (φ : H ≃* G)
    {V' : Type*} [AddCommGroup V'] [Module k V'] {W' : Type*} [AddCommGroup W'] [Module k W']
    (ρ : Representation k G V') (σ : Representation k G W')
    (e : Representation.Equiv (ρ.comp φ.toMonoidHom) (σ.comp φ.toMonoidHom)) :
    Representation.Equiv ρ σ :=
  Representation.Equiv.mk e.toLinearEquiv (fun g => by
    have h := e.isIntertwining' (φ.symm g)
    simpa [MulEquiv.apply_symm_apply] using h)

/-- Characteristic-`3` branch matcher: given a categorical isomorphism between the `ULift`-lifted
`ρ` and the `ULift`-lifted native model `ρn`, together with the base-change bridge
`scalarExtension ρ₀ ≅ ρn`, produce the desired equivalence `ρ ≅ scalarExtension ρ₀`.  Unlike the
semisimple `finish_branch`, this uses the categorical isomorphism *directly* (no character argument),
so it is valid in the modular case where `|S₄| = 0` in `k`. -/
theorem finish_branch_char_three
    {Wn : Type u} [AddCommGroup Wn] [Module k Wn] [FiniteDimensional k Wn]
    {W₀ : Type u} [AddCommGroup W₀] [Module ↥(⊥ : Subfield k) W₀]
    [FiniteDimensional ↥(⊥ : Subfield k) W₀]
    (ρ : Representation k S4 V) [FiniteDimensional k V]
    (ρn : Representation k S4 Wn) (ρ₀ : Representation ↥(⊥ : Subfield k) S4 W₀)
    (ebridge : Representation.Equiv (Representation.scalarExtension (k := k) ρ₀) ρn)
    (e : FDRep.of (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom)
          ≅ FDRep.of (ulift_group_carrier_representation ρn)) :
    Nonempty (ρ.Equiv (Representation.scalarExtension (k := k) ρ₀)) := by
  have e1 : Representation.Equiv
      (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom)
      (ulift_group_carrier_representation ρn) :=
    Representation.equivOfIso
      ((forget₂ (FDRep k (ULift.{u} S4)) (Rep k (ULift.{u} S4))).mapIso e)
  have e2 : Representation.Equiv (ulift_group_carrier_representation ρn)
      (ρn.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom) :=
    ulift_carrier_representation_equiv_overField
      (ρn.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom)
  have efinal : ρ.Equiv ρn :=
    equiv_of_comp_mulEquiv (MulEquiv.ulift.{0, u}) ρ ρn (e1.trans e2)
  exact ⟨efinal.trans ebridge.symm⟩

/-- **Characteristic-`3` branch** (`(2 : k) ≠ 0` and `(3 : k) = 0`): residual modular case.
Over a field of characteristic `3`, `k[S₄]` is not semisimple; only the trivial, sign, and the two
degree-`3` models stay irreducible (the four `3`-regular classes).  Completeness is established via
the Brauer count `#(3-regular classes of S₄) = 4` (`s4_char_three_family_isCompleteIrreducibleFamily`,
using the modular-robust augmentation irreducibility): the four explicit models are simple, pairwise
nonisomorphic, and there are exactly four simple isomorphism classes, so every irreducible `ρ` matches
one of them.  The matched categorical isomorphism is transported to the scalar extension of the
prime-field model via the base-change bridges (no character/Schur argument, which would fail in the
modular case). -/
theorem s4_simple_equiv_scalarExtension_primefield_model_char_three
    (ρ : Representation k S4 V) [ρ.IsIrreducible] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) = 0) :
    S4PrimefieldModelDisjunction ρ := by
  classical
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Representation.IsIrreducible
      (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom) :=
    isIrreducible_comp_of_mulEquiv_overField
      (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4) ρ
  -- completeness of the four characteristic-`3` models and the matched categorical isomorphism
  have hcomplete := s4_char_three_family_isCompleteIrreducibleFamily (k := k) h2 h3
  obtain ⟨i, ⟨e⟩⟩ := IsCompleteIrreducibleFamily.exists_iso_of_representation
    (s4_char_three_family k) hcomplete
    (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom) inferInstance
  -- the standard-augmentation base-change bridge over `Fin 4`
  obtain ⟨ebridgeStd⟩ :=
    scalarExtension_permutationAugmentationRepresentation_equiv
      (k₀ := ↥(⊥ : Subfield k)) (k := k) (G := S4) (X := Fin 4)
  -- the `sgn ⊗ std` base-change bridge
  obtain ⟨ebridgeSgnStd⟩ :=
    s4_primefield_sign_standard_tensor_scalarExtension_equiv (k := k) h2
  fin_cases i <;>
    simp only [s4_char_three_family, charThreeSlot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      s4_explicit_family] at e
  -- slot 0: trivial
  · exact Or.inl (finish_branch_char_three ρ (Representation.trivial k S4 k)
      (Representation.trivial ↥(⊥ : Subfield k) S4 ↥(⊥ : Subfield k))
      s4_primefield_trivial_scalarExtension_equiv e)
  -- slot 1: sign
  · exact Or.inr (Or.inl (finish_branch_char_three ρ (s4_sign_representation k)
      (s4_sign_representation ↥(⊥ : Subfield k))
      s4_primefield_sign_scalarExtension_equiv e))
  -- slot 2 (of the four): standard augmentation → disjunction slot `3`
  · exact Or.inr (Or.inr (Or.inr (Or.inl (finish_branch_char_three ρ
      (s4_standard_augmentation_representation k)
      (s4_standard_augmentation_representation ↥(⊥ : Subfield k))
      ebridgeStd e))))
  -- slot 3 (of the four): `sgn ⊗ std` → disjunction slot `4`
  · exact Or.inr (Or.inr (Or.inr (Or.inr (finish_branch_char_three ρ
      (s4_sign_standard_tensor_representation k)
      (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))
      ebridgeSgnStd e))))

/-- Completeness of Serre's five explicit `S₄`-models.  Every irreducible `S₄`-representation over
an algebraically closed field `k` (of *any* characteristic) is equivalent to the scalar extension,
from the prime subfield, of one of the five explicit prime-field models.

The semisimple branch (`ringChar k ∉ {2, 3}`) is fully proven; the two modular branches
(`ringChar k = 2` and `ringChar k = 3`) remain as the residual sorries
`s4_simple_equiv_scalarExtension_primefield_model_char_two` and `…_char_three`. -/
theorem s4_simple_equiv_scalarExtension_primefield_model
    (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    S4PrimefieldModelDisjunction ρ := by
  by_cases h2 : (2 : k) = 0
  · exact s4_simple_equiv_scalarExtension_primefield_model_char_two ρ h2
  · by_cases h3 : (3 : k) = 0
    · exact s4_simple_equiv_scalarExtension_primefield_model_char_three ρ h2 h3
    · exact s4_simple_equiv_scalarExtension_primefield_model_semisimple ρ h2 h3

/-- Helper for Exercise 18-18.5-2: every irreducible `S₄`-representation over an algebraically
closed field is realizable over the prime subfield.

This is fully reduced to the single completeness sub-lemma
`s4_simple_equiv_scalarExtension_primefield_model`: each of the five explicit prime-field models is,
tautologically, realizable over `↥(⊥)` after scalar extension
(`isRealizableOver_prime_subfield_scalarExtension`), and realizability transports across the
equivariant equivalence (`isRealizableOver_prime_subfield_of_equiv`). -/
theorem symmetricGroup_four_irreducible_realizable_over_prime_subfield_support
    (ρ : Representation k S4 V) [ρ.IsIrreducible] :
    IsRealizableOver ↥(⊥ : Subfield k) ρ := by
  rcases s4_simple_equiv_scalarExtension_primefield_model ρ with h | h | h | h | h <;>
    · obtain ⟨e⟩ := h
      exact isRealizableOver_prime_subfield_of_equiv
        (isRealizableOver_prime_subfield_scalarExtension _) e

end

end Representation
