import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_2_3.ResiduePrimeCharacter
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11

noncomputable section

universe u

open scoped MonoidAlgebra Representation
open scoped Pointwise
open CategoryTheory

namespace Representation

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

variable (Λ : Type u) [CommRing Λ]
variable (F : Type u) [Field F] [Algebra Λ F]
variable (G : Type u) [Group G]
variable [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G]

/-- Helper for Exercise 16-16.2-3: in characteristic zero, vanishing away from the identity forces
the generic-fiber character to be a natural-number multiple of the regular character. -/
theorem scalarExtension_character_eq_nsmul_leftRegular_of_eq_zero_off_one
    [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (hχ : ∀ g : G, g ≠ 1 → (P.scalarExtension F).character g = 0) :
    (P.scalarExtension F).character =
      Module.finrank F (Representation.invariants ((P.scalarExtension F).ρ)) •
        (Representation.leftRegular F G).character := by
  let ρ : Representation F G (P.scalarExtension F) := (P.scalarExtension F).ρ
  -- Once the generic-fiber character is supported at `1`, the standard averaging formula shows
  -- that it is the invariants-rank multiple of the regular character.
  change ρ.character = Module.finrank F ρ.invariants • (Representation.leftRegular F G).character
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : F) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  letI : Invertible (Nat.card G : F) := invertibleOfNonzero (NeZero.ne (Nat.card G : F))
  have hsum : ∑ t : G, ρ.character t = ρ.character 1 := by
    classical
    rw [Finset.sum_eq_single 1]
    · intro t _ ht
      simpa [ρ] using hχ t ht
    · intro h
      exact False.elim <| h (Finset.mem_univ 1)
  have havg :
      (Nat.card G : F)⁻¹ * Module.finrank F (P.scalarExtension F) =
        Module.finrank F ρ.invariants := by
    simpa [hsum, ρ.char_one] using ρ.card_inv_mul_sum_char_eq_finrank
  have hdim :
      (Module.finrank F (P.scalarExtension F) : F) =
        (Nat.card G : F) * Module.finrank F ρ.invariants := by
    have hcard : (Nat.card G : F) ≠ 0 := NeZero.ne (Nat.card G : F)
    exact (inv_mul_eq_iff_eq_mul₀ hcard).mp <| by simpa [ρ] using havg
  ext s
  by_cases hs : s = 1
  · subst hs
    simpa [Pi.smul_apply, Representation.leftRegular_character_one, nsmul_eq_mul, mul_comm] using
      hdim
  · have hs_zero : ρ.character s = 0 := by
      simpa [ρ] using hχ s hs
    rw [hs_zero, Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hs,
      nsmul_eq_mul]
    simp

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the global Grothendieck-character map sends each simple-class
basis vector to the matching irreducible-character basis vector. -/
theorem finiteRepGrothendieckCharacter_basis_image
    [CharZero F]
    {ι : Type u}
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∀ i,
      finiteRepGrothendieckCharacter F G
          (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i) =
        irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete i := by
  intro i
  -- Both bases are indexed by the same simple representation, so it remains only to evaluate the
  -- Grothendieck-character map on the honest class `[π i]₀`.
  rw [show
      simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i =
        [π i]₀ by
        simp [simple_finiteRep_classes_basis_of_complete_family_apply]]
  rw [show
      irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete i =
        (letI := hπ_complete.isSimple i
         FDRep.irreducibleCharacter F (π i)) by
        simp [irreducible_characters_basis_of_complete_family_apply]]
  ext g
  simp [finiteRepGrothendieckCharacter_class]

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: in characteristic zero the global Grothendieck-character map is
injective on finite-dimensional Grothendieck classes. -/
theorem finiteRepGrothendieckCharacter_eq_iff_general
    [CharZero F] [NeZero (Nat.card G : F)]
    {x y : R₀[F](G)} :
    finiteRepGrothendieckCharacter F G x =
      finiteRepGrothendieckCharacter F G y ↔ x = y := by
  classical
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := F) (G := G)
  letI : Fintype ι := hι
  let b₀ : Module.Basis ι ℤ (R₀[F](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR : Module.Basis ι ℤ (R[F](G)) :=
    irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete
  let fL : R₀[F](G) →ₗ[ℤ] R[F](G) :=
    (finiteRepGrothendieckCharacter F G).toIntLinearMap
  let sL : R[F](G) →ₗ[ℤ] R₀[F](G) := bR.constr ℤ b₀
  have hf_basis : ∀ i, fL (b₀ i) = bR i := by
    intro i
    -- The previous basis computation says exactly that the character map carries `b₀ i` to
    -- `bR i`.
    simpa [b₀, bR, fL] using
      finiteRepGrothendieckCharacter_basis_image
        (F := F) (G := G) π hπ_pairwise hπ_complete i
  have hs_basis : ∀ i, sL (bR i) = b₀ i := by
    intro i
    -- The basis reconstruction map is defined by sending each character-basis vector back to the
    -- corresponding simple-class basis vector.
    simpa [sL] using bR.constr_basis ℤ b₀ i
  have hleftL : sL.comp fL = LinearMap.id := by
    -- Compare the two endomorphisms on the simple-class basis.
    apply b₀.ext
    intro i
    rw [LinearMap.comp_apply, hf_basis i, hs_basis i]
    simp
  constructor
  · intro hxy
    -- Apply the explicit left inverse to the character equality to recover the class equality.
    have hx :=
      congrArg (fun t : R₀[F](G) →ₗ[ℤ] R₀[F](G) => t x) hleftL
    have hy :=
      congrArg (fun t : R₀[F](G) →ₗ[ℤ] R₀[F](G) => t y) hleftL
    calc
      x = sL (fL x) := by
            simpa [LinearMap.comp_apply] using hx.symm
      _ = sL (fL y) := by
            rw [show fL x = fL y by simpa [fL] using hxy]
      _ = y := by
            simpa [LinearMap.comp_apply] using hy
  · intro hxy
    -- Rewriting by the class equality reduces the character identity to reflexivity.
    simpa [hxy]

/-- Helper for Exercise 16-16.2-3: in characteristic zero, equality of ordinary characters
identifies the Grothendieck classes of finite-dimensional representations. -/
theorem finiteRepGrothendieckClass_eq_of_character_eq_charZero
    [CharZero F]
    {E E' : FDRep F G}
    (hχ : E.character = E'.character) :
    [E]₀ = [E']₀ := by
  letI : NeZero (Nat.card G : F) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  -- Send both Grothendieck classes to the Chapter `16` character ring; characteristic-zero
  -- injectivity then reduces the class equality to the ordinary character identity.
  apply
    (finiteRepGrothendieckCharacter_eq_iff_general
      (F := F) (G := G)).mp
  ext g
  simp [finiteRepGrothendieckCharacter_class, hχ]

/-- Helper for Exercise 16-16.2-3: in characteristic zero, once the generic-fiber character is a
natural-number multiple of the regular character, the generic fiber is actually isomorphic to the
canonical free model. -/
theorem scalarExtension_iso_free_of_character_eq_nsmul_leftRegular
    [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (n : ℕ)
    (hχ : (P.scalarExtension F).character =
      n • (Representation.leftRegular F G).character) :
    Nonempty (P.scalarExtension F ≅ FDRep.of (Rep.free F G (ULift (Fin n))).ρ) := by
  let Vfree : FDRep F G := FDRep.of (Rep.free F G (ULift (Fin n))).ρ
  have hfreeχ :
      Vfree.character = n • (Representation.leftRegular F G).character := by
    simpa [Vfree] using free_character_eq_nsmul_leftRegular (F := F) (G := G) n
  have hχfree : (P.scalarExtension F).character = Vfree.character :=
    hχ.trans hfreeχ.symm
  have hclass : [P.scalarExtension F]₀ = [Vfree]₀ :=
    finiteRepGrothendieckClass_eq_of_character_eq_charZero
      (F := F) (G := G) hχfree
  -- In characteristic zero, equality in the Grothendieck group detects isomorphism.
  simpa [Vfree] using
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_charZero
      (K := F) (G := G)).mp hclass

/-- Helper for Exercise 16-16.2-3: in characteristic zero, once the generic-fiber character is a
natural-number multiple of the regular character, the actual finite projective owner is free. -/
theorem free_of_character_eq_nsmul_leftRegular_charZero
    [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (n : ℕ)
    (hχ : (P.scalarExtension F).character =
      n • (Representation.leftRegular F G).character) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  let α : Type u := ULift (Fin n)
  let Vfree : FDRep F G := FDRep.of (Rep.free F G α).ρ
  obtain ⟨e⟩ :=
    scalarExtension_iso_free_of_character_eq_nsmul_leftRegular
      (Λ := Λ) (F := F) (G := G) P n hχ
  obtain ⟨eM⟩ :=
    nonempty_asModuleLinearEquiv_of_repEquiv
      ((P.scalarExtension F).ρ)
      Vfree.ρ
      (Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep F G) (Rep F G)).mapIso e))
  let _ : Module.Free F[G] (asModule Vfree.ρ) := by
    -- The free model is already free over the group algebra by construction.
    simpa [Vfree, α] using free_module_free (F := F) (G := G) n
  -- Transport the explicit free `F[G]`-basis on the free model back to `P.scalarExtension F`.
  exact Module.Free.of_equiv eM.symm

/-- Helper for Exercise 16-16.2-3: in characteristic zero, the remaining task is to convert the
regular-character identity into an actual free `F[G]`-basis of the generic fiber. -/
theorem scalar_extension_free_of_character_zero_off_one
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (hχ : ∀ g : G, g ≠ 1 → (P.scalarExtension F).character g = 0) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  by_cases hchar0 : ringChar F = 0
  · letI : CharZero F := (CharP.ringChar_zero_iff_CharZero (R := F)).mp hchar0
    exact
      free_of_character_eq_nsmul_leftRegular_charZero
        (Λ := Λ) (F := F) (G := G) P
        (Module.finrank F (Representation.invariants ((P.scalarExtension F).ρ)))
        (scalarExtension_character_eq_nsmul_leftRegular_of_eq_zero_off_one
          (Λ := Λ) (F := F) (G := G) P hχ)
  · let p := ringChar F
    letI : CharP F p := ringChar.charP (R := F)
    have hp_ne_one : p ≠ 1 := CharP.char_ne_one F p
    have hp_two_le : 2 ≤ p := by
      omega
    letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le F p hp_two_le⟩
    have hcard_ne_zero : Nat.card G ≠ 0 := by
      exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
    obtain ⟨m, hm⟩ :=
      eq_prime_pow_of_forall_prime_dvd_eq
        (p := p) (n := Nat.card G) hcard_ne_zero
        (fun q hq =>
          card_prime_divisor_eq_of_charP
            (Λ := Λ) (F := F) (G := G) (p := p) hresidue q hq)
    let Q := scalarExtension_owner (Λ := Λ) (F := F) (G := G) P
    have hG : IsPGroup p G := IsPGroup.of_card hm
    have hfreeQ : Module.Free F[G] Q.V :=
      FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
        (k := F) (G := G) (p := p) Q hG
    simpa [Q, scalarExtension_owner] using hfreeQ

-- Proof sketch: complete `P` at each nonzero maximal ideal whose residue characteristic is a
-- prime divisor of `|G|`, apply Swan's local freeness theorem to those completed modules, and
-- compare the local ranks to conclude that the quotient-field scalar extension is a free

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
