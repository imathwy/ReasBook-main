import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1.ScaledCharacterCore

noncomputable section

open scoped Representation

universe u x

namespace Representation

open CategoryTheory

section

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local instance instFintypeScaledCharacterGroupPairing : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 12-12.2-1: pairing a representation-ring element with the `i`-th
irreducible character recovers the `i`-th irreducible-basis coefficient. -/
theorem basis_coefficient_pairing_eq
    [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](G)) (i : ι) :
    ⟪(x : G → K), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i :
        ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero <| by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : G → K) := by
    -- Rewrite the irreducible-basis expansion into the ambient class-function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr x)
  have horth :
      Pairwise fun j k ↦
        ⟪(π j).character, (π k).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  calc
    ⟪(x : G → K), (π i).character⟫
        = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
            -- Replace `x` by its irreducible-basis expansion before pairing.
            simpa [hx] using
              congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character)
                hx.symm
    _ = ∑ j, (c j : K) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left
              (K := K) (G := G) (s := Finset.univ) c
              (fun j ↦ (π j).character) ((π i).character)
    _ = (c i : K) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            simp [horth hji]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

/-- Helper for Proposition 12-12.2-1: if a scalar multiple of one scaled irreducible character
already lies in `R_K(G)`, then the chosen denominator divides that scalar. -/
theorem denominator_dvd_of_zsmul_scaled_character_mem_characterRing
    [Finite ι] [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι)
    (m : ℕ+)
    (d : ℕ)
    (hmem : ((d : ℤ) • FDRep.schurScaledCharacter (π i) m : G → K) ∈ R[K](G)) :
    (m : ℕ) ∣ d := by
  classical
  let x : R[K](G) := ⟨((d : ℤ) • FDRep.schurScaledCharacter (π i) m : G → K), hmem⟩
  let c : ℤ :=
    (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i
  have hzsmul :
      ((d : ℤ) • FDRep.schurScaledCharacter (π i) m : G → K) =
        (((d : ℤ) : K) • FDRep.schurScaledCharacter (π i) m) := by
    ext g
    simp [zsmul_eq_mul, smul_eq_mul]
  have hpair_scaled :
      ⟪(x : G → K), (π i).character⟫ =
        (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
          ⟪(π i).character, (π i).character⟫ := by
    -- Rewrite the scaled character explicitly so the coefficient appears as a scalar factor.
    calc
      ⟪(x : G → K), (π i).character⟫
          = ⟪(((d : ℤ) : K) • FDRep.schurScaledCharacter (π i) m), (π i).character⟫ := by
              simpa [x] using congrArg
                (fun χ : G → K ↦ groupFunctionPairingOverField K χ (π i).character) hzsmul
      _ = ((d : ℤ) : K) * ⟪FDRep.schurScaledCharacter (π i) m, (π i).character⟫ := by
            rw [groupFunctionPairing_smul_left]
      _ = ((d : ℤ) : K) * ((((m : ℕ) : K)⁻¹) *
            ⟪(π i).character, (π i).character⟫) := by
              rw [FDRep.schurScaledCharacter, groupFunctionPairing_smul_left]
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫ := by
              ring
  have hpair_basis :
      ⟪(x : G → K), (π i).character⟫ =
        ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
    -- The irreducible basis expansion identifies the same pairing with the `i`-th basis
    -- coefficient.
    simpa [c] using
      basis_coefficient_pairing_eq
        (K := K) (G := G) (π := π) hπ_pairwise hπ_complete x i
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
    letI : Simple (π i) := hπ_complete.isSimple i
    exact groupFunctionPairingOverField_character_self_ne_zero (K := K) (G := G) (π i)
  have hcoeff :
      ((c : ℤ) : K) = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) := by
    -- Compare the two formulas for the same pairing and cancel the nonzero self-pairing factor.
    apply mul_right_cancel₀ hself_ne
    calc
      ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫
          = ⟪(x : G → K), (π i).character⟫ := by
              simpa using hpair_basis.symm
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫ := hpair_scaled
  have hmK_ne : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hmulK :
      ((m : ℕ) : K) * ((c : ℤ) : K) = ((d : ℤ) : K) := by
    -- Multiply by the nonzero denominator to remove the inverse factor.
    calc
      ((m : ℕ) : K) * ((c : ℤ) : K)
          = ((m : ℕ) : K) * (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) := by
              rw [hcoeff]
      _ = ((d : ℤ) : K) := by
            field_simp [hmK_ne]
  have hmulZ : ((m : ℤ) * c : ℤ) = d := by
    exact_mod_cast hmulK
  have hdivZ : ((m : ℤ) : ℤ) ∣ (d : ℤ) := ⟨c, hmulZ.symm⟩
  exact Int.natCast_dvd_natCast.mp (by simpa using hdivZ)

end

end Representation
