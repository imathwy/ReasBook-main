import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11.RationalSignCharacters

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

namespace Exercise_16_16_1_11

section

variable {G : Type} [Group G]

variable {A : Type} [CommRing A] [IsLocalRing A] [Algebra A ℚ] [IsFractionRing A ℚ]

local notation "k" => IsLocalRing.ResidueField A

variable [CharP (IsLocalRing.ResidueField A) 5]
variable [Finite G] [IsCyclic G] (hG : Nat.card G = 4)

local instance modFiveWitnessFintype : Fintype G := Fintype.ofFinite G
local instance modFiveWitnessCommGroup_modfivewitness : CommGroup G := IsCyclic.commGroup
local instance modFiveWitnessIsDomain : IsDomain A := (IsFractionRing.injective A ℚ).isDomain
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Helper for Exercise 16-16.1-11: there is a degree-`1` characteristic-`5` character whose
values distinguish an element of order `4` from its inverse. -/
theorem exists_faithful_mod_five_linear_class_distinguishing_inverse_modfivewitness
    (hG : Nat.card G = 4) :
    ∃ y : R₀[k](G), ∃ g0 : G, orderOf g0 = 4 ∧
      finiteRepGrothendieckCharacter k G y g0 ≠
        finiteRepGrothendieckCharacter k G y g0⁻¹ := by
  let g0 : G := Classical.choose (IsCyclic.exists_generator (α := G))
  have hg0_gen : ∀ x : G, x ∈ Subgroup.zpowers g0 :=
    Classical.choose_spec (IsCyclic.exists_generator (α := G))
  have hg0_order : orderOf g0 = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg0_gen, hG]
  have htwo_pow_four : (2 : k) ^ 4 = 1 := by
    calc
      (2 : k) ^ 4 = (16 : k) := by
        norm_num
      _ = 1 := by
        have h5 : (5 : k) = 0 := by
          simpa using (CharP.cast_eq_zero (R := k) 5)
        have h16 : (16 : k) = 1 + 3 * (5 : k) := by
          norm_num
        rw [h5] at h16
        norm_num at h16
        simpa using h16
  have htwo_pow_three : (2 : k) ^ 3 = 3 := by
    calc
      (2 : k) ^ 3 = (8 : k) := by
        norm_num
      _ = 3 := by
        have h5 : (5 : k) = 0 := by
          simpa using (CharP.cast_eq_zero (R := k) 5)
        have h8 : (8 : k) = 3 + (5 : k) := by
          norm_num
        rw [h5] at h8
        simpa using h8
  have htwo_primitive : IsPrimitiveRoot (2 : k) 4 := by
    refine ⟨htwo_pow_four, ?_⟩
    intro l hl
    have hlt : l % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases hmod : l % 4
    · exact ⟨l / 4, by omega⟩
    · exfalso
      have hpow : (2 : k) ^ l = 2 := by
        rw [← Nat.mod_add_div l 4, pow_add, pow_mul, htwo_pow_four]
        simp [hmod]
      rw [hl] at hpow
      have hsub : (2 : k) - 1 = 0 := sub_eq_zero.mpr hpow.symm
      norm_num at hsub
    · exfalso
      have hpow : (2 : k) ^ l = 4 := by
        rw [← Nat.mod_add_div l 4, pow_add, pow_mul, htwo_pow_four]
        norm_num [hmod]
      rw [hl] at hpow
      have hthree : (3 : k) = 0 := by
        have hsub : (4 : k) - 1 = 0 := sub_eq_zero.mpr hpow.symm
        norm_num at hsub
        exact hsub
      exact
        (CharP.cast_ne_zero_of_ne_of_prime k Nat.prime_three (by decide : 5 ≠ 3)) hthree
    · exfalso
      have hpow : (2 : k) ^ l = 3 := by
        rw [← Nat.mod_add_div l 4, pow_add, pow_mul, htwo_pow_four]
        simpa [hmod] using htwo_pow_three
      rw [hl] at hpow
      have htwo : (2 : k) = 0 := by
        have hsub : (3 : k) - 1 = 0 := sub_eq_zero.mpr hpow.symm
        norm_num at hsub
        exact hsub
      exact
        (CharP.cast_ne_zero_of_ne_of_prime k Nat.prime_two (by decide : 5 ≠ 2)) htwo
  let u : kˣ := (htwo_primitive.isUnit (by decide)).unit
  have hu_primitive : IsPrimitiveRoot u 4 := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [u] using htwo_primitive
  have hu_order : orderOf u = 4 :=
    IsPrimitiveRoot.iff_orderOf.mp hu_primitive
  let eG : Multiplicative (ZMod 4) ≃* G := zmodMulEquivOfGenerator hg0_gen hG
  have hzu_card : Nat.card (Subgroup.zpowers u) = 4 := by
    simpa [hu_order] using (Nat.card_zpowers u)
  let eU : Multiplicative (ZMod 4) ≃* Subgroup.zpowers u :=
    zmodMulEquivOfGenerator (G := Subgroup.zpowers u) (g := ⟨u, by simp⟩)
      (by
        intro x
        rcases x with ⟨x, hx⟩
        rcases hx with ⟨n, rfl⟩
        refine ⟨n, ?_⟩
        ext
        simp)
      hzu_card
  let β : G →* kˣ :=
    ((Subgroup.zpowers u).subtype.comp eU.toMonoidHom).comp eG.symm.toMonoidHom
  have hβg : β g0 = u := by
    change ((Subgroup.zpowers u).subtype (eU (eG.symm g0))) = u
    rw [zmodMulEquivOfGenerator_symm_apply_generator]
    simpa using
      congrArg Subtype.val
        (zmodMulEquivOfGenerator_apply_ofAdd_one
          (G := Subgroup.zpowers u) (g := ⟨u, by simp⟩)
          (by
            intro x
            rcases x with ⟨x, hx⟩
            rcases hx with ⟨n, rfl⟩
            refine ⟨n, ?_⟩
            ext
            simp)
          hzu_card)
  have hu_ne_inv : u ≠ u⁻¹ := by
    intro hEq
    have hmul : u * u = 1 := by
      have hmul' := congrArg (fun x : kˣ ↦ x * u) hEq
      simpa using hmul'
    have hpow_two : u ^ 2 = 1 := by
      simpa [pow_two] using hmul
    have hdiv : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hpow_two
    rw [hu_order] at hdiv
    omega
  let W : FDRep k G := FDRep.of (unitCharacterToRepresentation β)
  refine ⟨[W]₀, g0, hg0_order, ?_⟩
  intro hy
  have hy' : W.character g0 = W.character g0⁻¹ := by
    simpa [finiteRepGrothendieckCharacter_class] using hy
  have hy'' : (β g0 : k) = (β g0⁻¹ : k) := by
    change (unitCharacterToRepresentation β).character g0 =
      (unitCharacterToRepresentation β).character g0⁻¹ at hy'
    simpa [unitCharacterToRepresentation_character_apply] using hy'
  have hy''' : (u : k) = ((u⁻¹ : kˣ) : k) := by
    simpa [hβg] using hy''
  exact hu_ne_inv (Units.ext hy''')

end

end Exercise_16_16_1_11
