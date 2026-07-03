import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1.ScaledCharacterPacket
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u v w x

namespace Representation

open CategoryTheory

section

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local instance instFintypeScaledCharacterGroupMain : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 12-12.2-1: the normalized pairing is additive on finite
`K`-linear combinations in its left argument. -/
private theorem groupFunctionPairing_sum_smul_left
    (s : Finset ι) (a : ι → K) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, a j * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, groupFunctionPairing_smul_left,
        ih, Finset.sum_insert hi]

/-- Helper for Proposition 12-12.2-1: pairwise nonisomorphic irreducible characters are already
`K`-linearly independent as class functions. -/
private theorem linearIndependent_character_functions_of_pairwiseNonisomorphic
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π) :
    LinearIndependent K (fun i ↦ (π i).character) := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  rw [linearIndependent_iff']
  intro s g hg i hi
  -- Pair the relation with the `i`-th irreducible character to isolate the `i`-th coefficient.
  have hpair0 :=
    congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hg
  have hpair :
      ⟪∑ j ∈ s, g j • (π j).character, (π i).character⟫ = (0 : K) := by
    simpa [Representation.groupFunctionPairingOverField] using hpair0
  rw [groupFunctionPairing_sum_smul_left
      (K := K) (G := G) (s := s) g (fun j ↦ (π j).character) ((π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · have hself_ne :
        ⟪(π i).character, (π i).character⟫ ≠ (0 : K) :=
      groupFunctionPairingOverField_character_self_ne_zero (K := K) (G := G) (π i)
    exact (mul_eq_zero.mp hpair).resolve_right hself_ne
  · intro j _ hji
    simp [horth hji]
  · intro hnot_mem
    exact (hnot_mem hi).elim

/-- Helper for Proposition 12-12.2-1: a complete pairwise nonisomorphic irreducible family over a
finite group has only finitely many indices. -/
private theorem finite_index_of_complete_pairwiseNonisomorphic
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional K (G → K) := by
    infer_instance
  have hlin :
      LinearIndependent K (fun i ↦ (π i).character) :=
    linearIndependent_character_functions_of_pairwiseNonisomorphic
      (K := K) (G := G) π hπ_complete hπ_pairwise
  exact Cardinal.lt_aleph0_iff_finite.mp
    (LinearIndependent.lt_aleph0_of_finiteDimensional hlin)

/-- Helper for Proposition 12-12.2-1: in the pairwise case, every honest irreducible character
already lies in the `ℤ`-span of the scaled characters. -/
private theorem characterRingOverField_le_span_schurScaledCharacters
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i)) :
    ∀ χ : R[K](G),
      (⟨(χ : G → K), characterRingOverField_le_overlineCharacterRing K G χ.2⟩ : R̄[K](G)) ∈
      Submodule.span ℤ
        (Set.range fun i ↦
          (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) := by
  classical
  letI : Finite ι := finite_index_of_complete_pairwiseNonisomorphic
    (K := K) (G := G) π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let S : Submodule ℤ (R̄[K](G)) :=
    Submodule.span ℤ
      (Set.range fun i ↦
        (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)))
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  have hchar_overline : ∀ i, (π i).character ∈ R̄[K](G) := by
    intro i
    exact
      characterRingOverField_le_overlineCharacterRing K G
        (FDRep.character_mem_characterRingOverField K (π i))
  intro x
  let xbar : R̄[K](G) :=
    ⟨(x : G → K), characterRingOverField_le_overlineCharacterRing K G x.2⟩
  have hxbar :
      ∑ i, b.repr x i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = xbar := by
    -- Rewrite the irreducible-character basis expansion inside the ambient overline owner.
    apply Subtype.ext
    ext g
    simpa [b, xbar, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrFun (congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr x)) g
  change xbar ∈ S
  rw [← hxbar]
  refine Submodule.sum_mem S ?_
  intro i _
  have hscaled_mem :
      (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)) ∈ S := by
    exact Submodule.subset_span ⟨i, rfl⟩
  have hchar_eq :
      ((m i : ℤ) • (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) =
        (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) := by
    -- Multiplying the scaled generator by its denominator recovers the honest character.
    apply Subtype.ext
    ext g
    simpa [zsmul_schurScaledCharacter_eq_character (K := K) (G := G) (π i) (m i)]
  have hchar_mem :
      (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) ∈ S := by
    rw [← hchar_eq]
    exact Submodule.smul_mem S (m i : ℤ) hscaled_mem
  exact Submodule.smul_mem S (b.repr x i) hchar_mem

/-- Helper for Proposition 12-12.2-1: multiplying an overline character by the relative index of
`R[K](G)` in `R̄[K](G)` lands back in `R[K](G)`. -/
private theorem relIndex_multiple_mem_characterRingOverField
    (χ : R̄[K](G)) :
    (((R[K](G)).toSubmodule.toAddSubgroup).relIndex
        ((R̄[K](G)).toSubmodule.toAddSubgroup) • (χ : G → K)) ∈ R[K](G) := by
  have hfin :
      ((R[K](G)).toSubmodule.toAddSubgroup).IsFiniteRelIndex
        ((R̄[K](G)).toSubmodule.toAddSubgroup) := by
    exact characterRingOverField_isFiniteRelIndex_overlineCharacterRing (K := K) (G := G)
  letI := hfin
  have hχ_mem :
      (χ : G → K) ∈ ((R̄[K](G)).toSubmodule.toAddSubgroup) := by
    simpa using χ.2
  simpa using
    ((R[K](G)).toSubmodule.toAddSubgroup.nsmul_relIndex_mem hχ_mem)

/-- Helper for Proposition 12-12.2-1: multiplying an overline character by the relative-index
multiple together with all Schur denominators still lands back in `R[K](G)`. -/
private theorem common_multiple_mem_characterRingOverField
    [Finite ι] [Fintype ι]
    (m : ι → ℕ+)
    (χ : R̄[K](G)) :
    let n : ℕ :=
      ((R[K](G)).toSubmodule.toAddSubgroup).relIndex
        ((R̄[K](G)).toSubmodule.toAddSubgroup)
    let N : ℕ := n * ∏ i : ι, (m i : ℕ)
    ((N : ℤ) • (χ : G → K)) ∈ R[K](G) := by
  let n : ℕ :=
    ((R[K](G)).toSubmodule.toAddSubgroup).relIndex
      ((R̄[K](G)).toSubmodule.toAddSubgroup)
  let D : ℕ := ∏ i : ι, (m i : ℕ)
  have hnχ :
      ((n : ℤ) • (χ : G → K)) ∈ R[K](G) := by
    simpa [n] using
      relIndex_multiple_mem_characterRingOverField (K := K) (G := G) χ
  have hDhnχ :
      ((D : ℤ) • ((n : ℤ) • (χ : G → K))) ∈ R[K](G) := by
    -- First land in `R[K](G)` using the relative index, then multiply by the denominator product.
    exact Submodule.smul_mem (R[K](G)).toSubmodule (D : ℤ) hnχ
  convert hDhnχ using 1
  ext g
  simp [n, D, zsmul_eq_mul, mul_left_comm, mul_comm]

/-- Helper for Proposition 12-12.2-1: once the common-multiple coefficients are divisible by the
expected factors `N / mᵢ`, the common-multiple expansion rewrites as `N` times an integral linear
combination of the scaled generators, so torsion-freeness cancels `N`. -/
private theorem mem_span_schurScaledCharacters_of_coeff_divisibility
    [Finite ι] [Fintype ι]
    (π : ι → FDRep K G)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (χ : R̄[K](G))
    (S : Submodule ℤ (R̄[K](G)))
    (hS_def :
      S =
        Submodule.span ℤ
          (Set.range fun i ↦
            (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))))
    (hchar_overline : ∀ i, (π i).character ∈ R̄[K](G))
    {N : ℕ}
    (hN_ne : N ≠ 0)
    (hNmul : ∀ i, (m i : ℕ) ∣ N)
    (c : ι → ℤ)
    (hχN_expansion :
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = (N : ℤ) • χ)
    (hdiv : ∀ i, (((N / (m i : ℕ)) : ℕ) : ℤ) ∣ c i) :
    χ ∈ S := by
  classical
  rw [hS_def]
  choose z hz using hdiv
  let y : R̄[K](G) :=
    ∑ i, z i • (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))
  have hy_mem :
      y ∈
        Submodule.span ℤ
          (Set.range fun i ↦
            (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) := by
    -- The candidate preimage is already an integral linear combination of the scaled generators.
    refine Submodule.sum_mem _ ?_
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hterm :
      ∀ i,
        ((N : ℤ) • (z i • FDRep.schurScaledCharacter (π i) (m i)) : G → K) =
          c i • (π i).character := by
    intro i
    rcases hNmul i with ⟨k, hk⟩
    have hm_ne : (((m i : ℕ) : K) : K) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (m i).pos.ne'
    have hscalar :
        (((N : ℕ) : K) * (((m i : ℕ) : K)⁻¹)) = (((N / (m i : ℕ)) : ℕ) : K) := by
      simp [hk, Nat.cast_mul, hm_ne, mul_comm]
    have hcoeffK : (((N / (m i : ℕ)) : ℕ) : K) * (z i : K) = ((c i : ℤ) : K) := by
      calc
        (((N / (m i : ℕ)) : ℕ) : K) * (z i : K)
            = ((((N / (m i : ℕ)) : ℕ) : ℤ) : K) * (z i : K) := by
                rw [Int.cast_natCast]
        _ = (((((N / (m i : ℕ)) : ℕ) : ℤ) * z i : ℤ) : K) := by
              rw [Int.cast_mul]
        _ = ((c i : ℤ) : K) := by
              exact congrArg (fun t : ℤ ↦ (t : K)) (hz i).symm
    ext g
    calc
      (((N : ℤ) • (z i • FDRep.schurScaledCharacter (π i) (m i)) : G → K) g)
          = (((N : ℕ) : K) * ((z i : K) * ((((m i : ℕ) : K)⁻¹) * (π i).character g))) := by
              simp [FDRep.schurScaledCharacter, zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = ((((N : ℕ) : K) * (((m i : ℕ) : K)⁻¹)) * ((z i : K) * (π i).character g)) := by
            ring_nf
      _ = (((N / (m i : ℕ)) : ℕ) : K) * ((z i : K) * (π i).character g) := by
            rw [hscalar]
      _ = ((((N / (m i : ℕ)) : ℕ) : K) * (z i : K)) * (π i).character g := by
            ring_nf
      _ = (((c i : ℤ) : K) * (π i).character g) := by
            rw [hcoeffK]
      _ = ((c i • (π i).character : G → K) g) := by
            simp [zsmul_eq_mul]
  have hy_scaled :
      (N : ℤ) • (y : G → K) = ∑ i, c i • (π i).character := by
    ext g
    calc
      (((N : ℤ) • y : R̄[K](G)) : G → K) g
          = ∑ i, (((N : ℤ) • (z i • FDRep.schurScaledCharacter (π i) (m i)) : G → K) g) := by
              simp [y, zsmul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm,
                mul_comm]
      _ = ∑ i, ((c i • (π i).character : G → K) g) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact congrFun (hterm i) g
      _ = (∑ i, c i • (π i).character) g := by
            simp
  have hNy_eq : (N : ℤ) • (y : G → K) = (N : ℤ) • (χ : G → K) := by
    calc
      (N : ℤ) • (y : G → K) = ∑ i, c i • (π i).character :=
        hy_scaled
      _ = (N : ℤ) • (χ : G → K) := by
            simpa using congrArg (fun z : R̄[K](G) ↦ (z : G → K)) hχN_expansion
  have hN_K_ne : ((N : ℕ) : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hN_ne
  have hcancel_fun : (y : G → K) = (χ : G → K) := by
    ext g
    have hg : ((N : ℕ) : K) * (y : G → K) g = ((N : ℕ) : K) * (χ : G → K) g := by
      simpa [zsmul_eq_mul] using congrFun hNy_eq g
    exact mul_left_cancel₀ hN_K_ne hg
  have hcancel : y = χ := by
    apply Subtype.ext
    exact hcancel_fun
  simpa [hcancel] using hy_mem

/-- Helper for Proposition 12-12.2-1: if an element of `R_K(G)` is also written as an integral
combination of the scaled generators, then each scaled-generator coefficient is the corresponding
irreducible-basis coefficient multiplied by the Schur denominator. -/
private theorem scaled_span_coefficient_eq_denominator_mul_basis_coefficient
    [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (χN : R[K](G))
    (z : ι → ℤ)
    (hz :
      ∑ j, z j • (⟨FDRep.schurScaledCharacter (π j) (m j), (hdenom j).1⟩ : R̄[K](G)) =
        (⟨(χN : G → K), characterRingOverField_le_overlineCharacterRing K G χN.2⟩ :
          R̄[K](G)))
    (i : ι) :
    z i = (m i : ℤ) *
      (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr χN i := by
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero <| by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let c : ι → ℤ :=
    (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr χN
  have hz_fun :
      ∑ j, z j • FDRep.schurScaledCharacter (π j) (m j) = (χN : G → K) := by
    -- Forget the overline-owner wrappers so the coefficient comparison happens in class
    -- functions.
    have hz' := congrArg (fun x : R̄[K](G) ↦ (x : G → K)) hz
    simpa using hz'
  have hpair :
      ⟪∑ j, z j • FDRep.schurScaledCharacter (π j) (m j), (π i).character⟫ =
        ⟪(χN : G → K), (π i).character⟫ := by
    -- Pair both sides with the `i`-th honest irreducible character.
    simpa using
      congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hz_fun
  have horth :
      Pairwise fun j k ↦
        ⟪(π j).character, (π k).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  rw [groupFunctionPairing_sum_zsmul_left
      (K := K) (G := G) (s := Finset.univ) z
      (fun j ↦ FDRep.schurScaledCharacter (π j) (m j)) ((π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · have hscaled_pair :
        ⟪FDRep.schurScaledCharacter (π i) (m i), (π i).character⟫ =
          (((m i : ℕ) : K)⁻¹) * ⟪(π i).character, (π i).character⟫ := by
      -- Expand the scaled character so its denominator is visible in the pairing.
      rw [FDRep.schurScaledCharacter, groupFunctionPairing_smul_left]
    rw [hscaled_pair] at hpair
    have hpair_basis :
        ⟪(χN : G → K), (π i).character⟫ =
          ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
      -- The irreducible-character basis identifies the same pairing with the `i`-th basis
      -- coefficient of `χN`.
      simpa [c] using
        basis_coefficient_pairing_eq
          (K := K) (G := G) (π := π) hπ_pairwise hπ_complete χN i
    have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact groupFunctionPairingOverField_character_self_ne_zero (K := K) (G := G) (π i)
    have hcoeffK :
        ((z i : ℤ) : K) * (((m i : ℕ) : K)⁻¹) = ((c i : ℤ) : K) := by
      -- Cancel the nonzero self-pairing factor to compare the scalar coefficients directly.
      apply mul_right_cancel₀ hself_ne
      calc
        ((((z i : ℤ) : K) * (((m i : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫)
            = ((z i : ℤ) : K) * ((((m i : ℕ) : K)⁻¹) *
                ⟪(π i).character, (π i).character⟫) := by ring
        _ = ⟪(χN : G → K), (π i).character⟫ := hpair
        _ = ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := hpair_basis
    have hmK_ne : ((m i : ℕ) : K) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (m i).pos.ne'
    have hmulK :
        ((m i : ℕ) : K) * ((c i : ℤ) : K) = ((z i : ℤ) : K) := by
      -- Multiply by the nonzero denominator to clear the inverse scalar.
      calc
        ((m i : ℕ) : K) * ((c i : ℤ) : K)
            = ((m i : ℕ) : K) * (((z i : ℤ) : K) * (((m i : ℕ) : K)⁻¹)) := by
                rw [hcoeffK]
        _ = ((z i : ℤ) : K) := by
              field_simp [hmK_ne]
    have hmulZ : ((m i : ℤ) *
        (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr χN i :
        ℤ) = z i := by
      exact_mod_cast hmulK
    exact hmulZ.symm
  · intro j _ hji
    letI : Simple (π j) := hπ_complete.isSimple j
    letI : Simple (π i) := hπ_complete.isSimple i
    letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    have hij_rep : ¬ Nonempty (Representation.Equiv ((π j).ρ) ((π i).ρ)) := by
      intro hij_rep
      apply hπ_pairwise hji
      rcases hij_rep with ⟨e⟩
      simpa using (show Nonempty (FDRep.of (π j).ρ ≅ FDRep.of (π i).ρ) from
        ⟨Representation.Equiv.toFDRepIso e⟩)
    have hpair_zero :
        ⟪FDRep.schurScaledCharacter (π j) (m j), (π i).character⟫ = (0 : K) := by
      have hchar_pair_zero :
          ⟪(π j).character, (π i).character⟫ = (0 : K) := by
        simpa using
          groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
            K (π j).ρ (π i).ρ hij_rep
      rw [FDRep.schurScaledCharacter, groupFunctionPairing_smul_left, hchar_pair_zero, mul_zero]
    rw [hpair_zero, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Helper for Proposition 12-12.2-1: admissible denominators for one irreducible character are
closed under least common multiples, so maximality upgrades from an order bound to divisibility. -/
private theorem admissible_denominator_dvd_of_isSchurDenominator
    {V : FDRep K G} [Simple V]
    {m : ℕ+}
    (hm : FDRep.IsSchurDenominator V m)
    {n : ℕ+}
    (hn : FDRep.schurScaledCharacter V n ∈ R̄[K](G)) :
    (n : ℕ) ∣ (m : ℕ) := by
  let g : ℕ := Nat.gcd (m : ℕ) (n : ℕ)
  let a : ℕ := (n : ℕ) / g
  let b : ℕ := (m : ℕ) / g
  have hg_pos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right _ n.pos
  have hga : a * g = (n : ℕ) := by
    dsimp [a, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right (m : ℕ) (n : ℕ))
  have hgb : b * g = (m : ℕ) := by
    dsimp [b, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left (m : ℕ) (n : ℕ))
  have hcop : Nat.Coprime a b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hgdiv : ((n : ℕ) / g).gcd ((m : ℕ) / g) = (n : ℕ).gcd (m : ℕ) / g := by
      exact Nat.gcd_div (Nat.gcd_dvd_right (m : ℕ) (n : ℕ)) (Nat.gcd_dvd_left (m : ℕ) (n : ℕ))
    dsimp [g, a, b] at hgdiv ⊢
    simpa [Nat.gcd_comm, Nat.div_self hg_pos] using hgdiv
  let l : ℕ+ := ⟨Nat.lcm (m : ℕ) (n : ℕ), Nat.lcm_pos m.pos n.pos⟩
  have hma_assoc : (m : ℕ) * (a * g) = ((m : ℕ) * a) * g := by
    simp [Nat.mul_assoc]
  have hma_comm : ((m : ℕ) * a) * g = g * ((m : ℕ) * a) := by
    ac_rfl
  have hnb_assoc : (n : ℕ) * (b * g) = ((n : ℕ) * b) * g := by
    simp [Nat.mul_assoc]
  have hnb_comm : ((n : ℕ) * b) * g = g * ((n : ℕ) * b) := by
    ac_rfl
  have hmn_comm : (m : ℕ) * (n : ℕ) = (n : ℕ) * (m : ℕ) := by
    ac_rfl
  have hl_eq_ma : (l : ℕ) = (m : ℕ) * a := by
    -- Rewrite `lcm(m,n)` as `m * (n / gcd(m,n))` so the source Bézout coefficients become visible.
    apply Nat.eq_of_mul_eq_mul_left hg_pos
    calc
      g * (l : ℕ) = (m : ℕ) * (n : ℕ) := by
        simp [l, g]
      _ = (m : ℕ) * (a * g) := by rw [hga]
      _ = ((m : ℕ) * a) * g := hma_assoc
      _ = g * ((m : ℕ) * a) := hma_comm
  have hl_eq_nb : (l : ℕ) = (n : ℕ) * b := by
    -- The same rewrite with the roles of `m` and `n` exchanged gives the second lcm factor.
    apply Nat.eq_of_mul_eq_mul_left hg_pos
    calc
      g * (l : ℕ) = (m : ℕ) * (n : ℕ) := by
        simp [l, g]
      _ = (n : ℕ) * (m : ℕ) := hmn_comm
      _ = (n : ℕ) * (b * g) := by rw [hgb]
      _ = ((n : ℕ) * b) * g := hnb_assoc
      _ = g * ((n : ℕ) * b) := hnb_comm
  have hbezout : ((1 : ℕ) : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := by
    -- The quotient factors `n / gcd(m,n)` and `m / gcd(m,n)` are coprime, so Bézout applies.
    simpa [Nat.coprime_iff_gcd_eq_one.mp hcop] using (Nat.gcd_eq_gcd_ab a b)
  have hl_mem : FDRep.schurScaledCharacter V l ∈ R̄[K](G) := by
    have hm_mem : FDRep.schurScaledCharacter V m ∈ R̄[K](G) := hm.1
    change FDRep.schurScaledCharacter V l ∈ (R̄[K](G)).toSubmodule
    have hm_eq : (FDRep.schurScaledCharacter V m : G → K) =
        (a : ℤ) • FDRep.schurScaledCharacter V l := by
      have ha_pos : 0 < a := by
        have hna : 0 < a * g := by
          simp [hga]
        exact Nat.pos_of_mul_pos_right hna
      have haK_ne : (a : K) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
      -- Clearing the `lcm/m` factor shows `χ / m` is an integer multiple of `χ / lcm(m,n)`.
      ext x
      simp [FDRep.schurScaledCharacter, zsmul_eq_mul, hl_eq_ma, haK_ne, mul_left_comm, mul_comm]
    have hn_eq : (FDRep.schurScaledCharacter V n : G → K) =
        (b : ℤ) • FDRep.schurScaledCharacter V l := by
      have hb_pos : 0 < b := by
        have hmb : 0 < b * g := by
          simp [hgb]
        exact Nat.pos_of_mul_pos_right hmb
      have hbK_ne : (b : K) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
      -- The companion identity writes `χ / n` as the other integer multiple of `χ / lcm(m,n)`.
      ext x
      simp [FDRep.schurScaledCharacter, zsmul_eq_mul, hl_eq_nb, hbK_ne, mul_left_comm, mul_comm]
    have hm_mem' : ((a : ℤ) • FDRep.schurScaledCharacter V l : G → K) ∈
        (R̄[K](G)).toSubmodule := by
      simpa [hm_eq] using hm_mem
    have hn_mem' : ((b : ℤ) • FDRep.schurScaledCharacter V l : G → K) ∈
        (R̄[K](G)).toSubmodule := by
      simpa [hn_eq] using hn
    have hexpr : (FDRep.schurScaledCharacter V l : G → K) =
        Nat.gcdA a b • ((a : ℤ) • FDRep.schurScaledCharacter V l) +
          Nat.gcdB a b • ((b : ℤ) • FDRep.schurScaledCharacter V l) := by
      have hbezoutK : (1 : K) =
          (a : K) * (Nat.gcdA a b : K) + (b : K) * (Nat.gcdB a b : K) := by
        exact_mod_cast hbezout
      -- Route correction: use the source Bézout decomposition on the quotient factors rather than
      -- trying to prove divisibility first.
      ext x
      calc
        FDRep.schurScaledCharacter V l x = (1 : K) * (FDRep.schurScaledCharacter V l x) := by
          simp
        _ = ((a : K) * (Nat.gcdA a b : K) + (b : K) * (Nat.gcdB a b : K)) *
              (FDRep.schurScaledCharacter V l x) := by
                rw [hbezoutK]
        _ = (Nat.gcdA a b • ((a : ℤ) • FDRep.schurScaledCharacter V l) +
              Nat.gcdB a b • ((b : ℤ) • FDRep.schurScaledCharacter V l)) x := by
                simp [FDRep.schurScaledCharacter, zsmul_eq_mul, mul_add, add_mul, mul_assoc,
                  mul_left_comm, mul_comm]
    rw [hexpr]
    -- Both admissible scaled characters are already in `R̄[K](G)`, so the Bézout combination is
    -- too.
    exact (R̄[K](G)).toSubmodule.add_mem
      ((R̄[K](G)).toSubmodule.smul_mem _ hm_mem')
      ((R̄[K](G)).toSubmodule.smul_mem _ hn_mem')
  have hle_lcm : Nat.lcm (m : ℕ) (n : ℕ) ≤ (m : ℕ) := hm.2 l hl_mem
  have hl_eq_m : Nat.lcm (m : ℕ) (n : ℕ) = (m : ℕ) := by
    -- Maximality of the chosen Schur denominator forces the admissible lcm denominator to be
    -- exactly `m`.
    exact le_antisymm hle_lcm
      (Nat.le_of_dvd (Nat.lcm_pos m.pos n.pos) (Nat.dvd_lcm_left (m : ℕ) (n : ℕ)))
  -- Rewriting `lcm(m,n) = m` is equivalent to the desired divisibility `n ∣ m`.
  exact (Nat.lcm_eq_left_iff_dvd.mp hl_eq_m)

/-- Helper for Proposition 12-12.2-1: the remaining conceptual bridge is to show that the
coprime-reduced `i`-th coefficient term of a common-multiple expansion first lands in the
algebraic-closure character ring. -/
private theorem pairing_eq_int_of_mem_characterRingOverAlgClosure
    (χ : R[AlgebraicClosure K](G))
    {V : Type u} [AddCommGroup V] [Module (AlgebraicClosure K) V]
    (ρ : Representation (AlgebraicClosure K) G V)
    [FiniteDimensional (AlgebraicClosure K) V] [ρ.IsIrreducible] :
    ∃ z : ℤ, ⟪(χ : G → AlgebraicClosure K), ρ.character⟫ = (z : AlgebraicClosure K) := by
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨hcard_ne⟩
  letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family
      (k := AlgebraicClosure K) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete ρ inferInstance
  rcases hi with ⟨e⟩
  let b :=
    irreducible_characters_basis_of_complete_family
      (AlgebraicClosure K) π hπ_pairwise hπ_complete
  let c := b.repr χ
  have hself :
      ⟪(π i).character, (π i).character⟫ = (1 : AlgebraicClosure K) := by
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    have hfinrank :
        Module.finrank (AlgebraicClosure K)
          (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1 := by
      simpa using
        (finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
          (ρ := (π i).ρ) inferInstance (τ := (π i).ρ) inferInstance)
    calc
      ⟪(π i).character, (π i).character⟫
          = Module.finrank (AlgebraicClosure K)
              (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
              simpa using
                (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  (K := AlgebraicClosure K) (G := G) (π i).ρ (π i).ρ)
      _ = 1 := by simpa using hfinrank
  have hpair_basis :
      ⟪(χ : G → AlgebraicClosure K), (π i).character⟫ = ((c i : ℤ) : AlgebraicClosure K) := by
    -- Expand `χ` in the complete irreducible basis and isolate the `i`-th coefficient.
    calc
      ⟪(χ : G → AlgebraicClosure K), (π i).character⟫
          = ((c i : ℤ) : AlgebraicClosure K) * ⟪(π i).character, (π i).character⟫ := by
              simpa [c] using
                basis_coefficient_pairing_eq
                  (K := AlgebraicClosure K) (G := G) (π := π) hπ_pairwise hπ_complete χ i
      _ = (c i : ℤ) := by rw [hself, mul_one]
  refine ⟨c i, ?_⟩
  -- Transport the basis coefficient identity across the irreducible isomorphism `ρ ≅ π i`.
  have hchar_iso : ρ.character = (π i).character := by
    simpa using FDRep.char_iso e
  calc
    ⟪(χ : G → AlgebraicClosure K), ρ.character⟫
        = ⟪(χ : G → AlgebraicClosure K), (π i).character⟫ := by
            rw [hchar_iso]
    _ = (c i : AlgebraicClosure K) := hpair_basis

/-- Helper for Proposition 12-12.2-1: after mapping the common-multiple identity to
`AlgebraicClosure K`, pairing with one packet constituent isolates the `i`-th packet
coefficient. -/
private theorem packet_pairing_eq_of_mapped_common_multiple_expansion
    [Finite ι] [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (χ : R̄[K](G))
    (hchar_overline : ∀ i, (π i).character ∈ R̄[K](G))
    {N : ℕ}
    (c : ι → ℤ)
    (hχN_expansion :
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = (N : ℤ) • χ)
    (i : ι)
    {κ : Type u} [Fintype κ]
    (ψ : κ → Rep.{u} (AlgebraicClosure K) G)
    (d : κ → ℕ)
    (hψ_pos : ∀ j, 0 < d j)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K) (ψ j))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ j, (ψ j).ρ.IsIrreducible)
    (hpacket :
      (Representation.scalarExtension (k := AlgebraicClosure K) (π i).ρ).character =
        ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character)
    (j : κ) :
    ((c i : ℤ) : AlgebraicClosure K) * d j =
      ((N : ℤ) : AlgebraicClosure K) *
        ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (χ : G → K),
          (ψ j).ρ.character⟫ := by
  have hcardK_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcardK_ne
  have horth :
      Pairwise fun k l ↦
        ⟪(π k).character, (π l).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcard_ne
  have hmap_expansion :
      ∑ k,
          ((c k : ℤ) : AlgebraicClosure K) •
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ((π k).character) =
        ((N : ℤ) : AlgebraicClosure K) •
          ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (χ : G → K) := by
    -- Map the common-multiple identity coefficientwise to `AlgebraicClosure K`.
    ext g
    simpa [zsmul_eq_mul, smul_eq_mul, mul_left_comm, mul_assoc, mul_comm] using
      congrFun
        (congrArg
          (fun z : R̄[K](G) ↦
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (z : G → K))
          hχN_expansion) g
  have hpair0 :=
    congrArg
      (fun φ : G → AlgebraicClosure K ↦
        groupFunctionPairingOverField (AlgebraicClosure K) φ (ψ j).ρ.character)
      hmap_expansion
  have hpair :
      ⟪∑ k,
          ((c k : ℤ) : AlgebraicClosure K) •
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ((π k).character),
        (ψ j).ρ.character⟫ =
        ⟪((N : ℤ) : AlgebraicClosure K) •
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (χ : G → K),
          (ψ j).ρ.character⟫ := by
    simpa [Representation.groupFunctionPairingOverField] using hpair0
  -- Off-packet terms vanish, and the `i`-th packet term contributes exactly `d j`.
  calc
    ((c i : ℤ) : AlgebraicClosure K) * d j
        =
          ∑ k,
            ((c k : ℤ) : AlgebraicClosure K) *
              ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ((π k).character),
                (ψ j).ρ.character⟫ := by
                  rw [Finset.sum_eq_single i]
                  · rw [packet_constituent_pairing_eq_multiplicity
                        (K := K) (G := G) (V := π i) ψ d hψ_fd hψ_pairwise hψ_irr
                        hpacket j]
                  · intro k _ hki
                    have hpair_zero :
                        ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                            ((π k).character), (ψ j).ρ.character⟫ =
                          (0 : AlgebraicClosure K) := by
                      exact
                        packet_constituent_pairing_zero_of_source_pairing_zero
                          (K := K) (G := G) (V := π i) (W := π k) ψ d hψ_pos hψ_fd hpacket
                          (horth hki) j
                    rw [hpair_zero, mul_zero]
                  · intro hi
                    exact (hi (Finset.mem_univ i)).elim
    _ = ⟪∑ k,
            ((c k : ℤ) : AlgebraicClosure K) •
              ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ((π k).character),
          (ψ j).ρ.character⟫ := by
            simpa using
              (groupFunctionPairing_sum_smul_left
                (K := AlgebraicClosure K) (G := G) (s := Finset.univ)
                (a := fun k ↦ ((c k : ℤ) : AlgebraicClosure K))
                (χ := fun k ↦
                  ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                    ((π k).character)) ((ψ j).ρ.character)).symm
    _ = ⟪((N : ℤ) : AlgebraicClosure K) •
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (χ : G → K),
          (ψ j).ρ.character⟫ := hpair
    _ = ((N : ℤ) : AlgebraicClosure K) *
          ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (χ : G → K),
            (ψ j).ρ.character⟫ := by
            rw [Representation.groupFunctionPairing_smul_left]

/-- Helper for Proposition 12-12.2-1: the paired common-multiple identity shows that every packet
multiplicity coefficient `cᵢ dⱼ` is divisible by `N`. -/
private theorem packet_multiplicity_divisible_of_mapped_common_multiple_expansion
    [Finite ι] [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (χ : R̄[K](G))
    (hchar_overline : ∀ i, (π i).character ∈ R̄[K](G))
    {N : ℕ}
    (c : ι → ℤ)
    (hχN_expansion :
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = (N : ℤ) • χ)
    (i : ι)
    {κ : Type u} [Fintype κ]
    (ψ : κ → Rep.{u} (AlgebraicClosure K) G)
    (d : κ → ℕ)
    (hψ_pos : ∀ j, 0 < d j)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K) (ψ j))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ j, (ψ j).ρ.IsIrreducible)
    (hpacket :
      (Representation.scalarExtension (k := AlgebraicClosure K) (π i).ρ).character =
        ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character) :
    ∀ j, (N : ℤ) ∣ c i * d j := by
  intro j
  let χmap : G → AlgebraicClosure K :=
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) (χ : G → K)
  have hχmap_mem :
      χmap ∈ R[AlgebraicClosure K](G) := by
    exact
      (mem_overlineCharacterRingOverField_iff (K := K) (G := G) χmap).1
        ⟨(χ : G → K), χ.2, rfl⟩ |>.1
  let χA : R[AlgebraicClosure K](G) := ⟨χmap, hχmap_mem⟩
  obtain ⟨z, hz⟩ :=
    pairing_eq_int_of_mem_characterRingOverAlgClosure
      (K := K) (G := G) χA (ψ j).ρ
  have hpair_eq :
      ((c i : ℤ) : AlgebraicClosure K) * d j =
        ((N : ℤ) : AlgebraicClosure K) * (z : AlgebraicClosure K) := by
    calc
      ((c i : ℤ) : AlgebraicClosure K) * d j
          = ((N : ℤ) : AlgebraicClosure K) *
              ⟪χmap, (ψ j).ρ.character⟫ := by
                simpa [χmap] using
                  packet_pairing_eq_of_mapped_common_multiple_expansion
                    (K := K) (G := G) (ι := ι) π hπ_pairwise hπ_complete χ hchar_overline
                    c hχN_expansion i ψ d hψ_pos hψ_fd hψ_pairwise hψ_irr hpacket j
      _ = ((N : ℤ) : AlgebraicClosure K) * (z : AlgebraicClosure K) := by rw [hz]
  refine ⟨z, ?_⟩
  exact_mod_cast hpair_eq

/-- Helper for Proposition 12-12.2-1: after cancelling the gcd shared by `c` and `N`, the
remaining packet coefficient becomes the integral witness coming from `N ∣ c * d`. -/
private theorem reduced_packet_scalar_eq_integral_witness
    {c z : ℤ} {N d : ℕ}
    (hN_ne : N ≠ 0)
    (hdiv : c * d = (N : ℤ) * z) :
    let g : ℕ := Nat.gcd (Int.natAbs c) N
    ((((c / g : ℤ) : AlgebraicClosure K) * (((N / g : ℕ) : AlgebraicClosure K)⁻¹)) *
        (d : AlgebraicClosure K)) = (z : AlgebraicClosure K) := by
  let g : ℕ := Nat.gcd (Int.natAbs c) N
  have hg_pos : 0 < g := by
    simpa [g] using
      Nat.gcd_pos_of_pos_right (Int.natAbs c) (Nat.pos_of_ne_zero hN_ne)
  have hg_dvd_natAbs : g ∣ Int.natAbs c := by
    simpa [g] using Nat.gcd_dvd_left (Int.natAbs c) N
  have hg_dvd_N : g ∣ N := by
    simpa [g] using Nat.gcd_dvd_right (Int.natAbs c) N
  have hg_dvd_c : (g : ℤ) ∣ c := by
    exact (Int.dvd_natAbs).mp (Int.natCast_dvd_natCast.mpr hg_dvd_natAbs)
  have hc_mul : ((c / g : ℤ) * g : ℤ) = c := by
    simpa [g, mul_comm] using (Int.ediv_mul_cancel hg_dvd_c)
  have hN_mul : ((((N / g : ℕ) : ℤ) * g : ℤ)) = N := by
    exact_mod_cast (Nat.div_mul_cancel hg_dvd_N)
  have hcancel_mul :
      (((c / g : ℤ) * d : ℤ) * g) = ((((N / g : ℕ) : ℤ) * z : ℤ) * g) := by
    calc
      (((c / g : ℤ) * d : ℤ) * g)
          = (((c / g : ℤ) * g : ℤ) * d) := by ring
      _ = c * d := by rw [hc_mul]
      _ = (N : ℤ) * z := hdiv
      _ = ((((N / g : ℕ) : ℤ) * g : ℤ) * z) := by rw [hN_mul]
      _ = ((((N / g : ℕ) : ℤ) * z : ℤ) * g) := by ring
  have hg_int_ne : (g : ℤ) ≠ 0 := by
    exact_mod_cast hg_pos.ne'
  have hcancel :
      ((c / g : ℤ) * d : ℤ) = (((N / g : ℕ) : ℤ) * z : ℤ) := by
    exact mul_right_cancel₀ hg_int_ne hcancel_mul
  have hn_ne : (((N / g : ℕ) : AlgebraicClosure K)) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.div_gcd_pos_of_pos_right (Int.natAbs c)
      (Nat.pos_of_ne_zero hN_ne)).ne'
  have hcast :
      (((c / g : ℤ) : AlgebraicClosure K) * (d : AlgebraicClosure K)) =
        (((N / g : ℕ) : AlgebraicClosure K) * (z : AlgebraicClosure K)) := by
    calc
      (((c / g : ℤ) : AlgebraicClosure K) * (d : AlgebraicClosure K))
          = (((((c / g : ℤ) * d : ℤ)) : AlgebraicClosure K)) := by
              simp [Int.cast_mul]
      _ = (((((N / g : ℕ) : ℤ) * z : ℤ) : AlgebraicClosure K)) := by
            rw [hcancel]
      _ = ((((N / g : ℕ) : ℤ) : AlgebraicClosure K) * (z : AlgebraicClosure K)) := by
            rw [Int.cast_mul]
      _ = (((N / g : ℕ) : AlgebraicClosure K) * (z : AlgebraicClosure K)) := by
            rw [Int.cast_natCast]
  -- Cancel the remaining positive denominator after transporting the integer identity.
  calc
    ((((c / g : ℤ) : AlgebraicClosure K) * (((N / g : ℕ) : AlgebraicClosure K)⁻¹)) *
        (d : AlgebraicClosure K))
        = (((((N / g : ℕ) : AlgebraicClosure K)⁻¹) *
            (((c / g : ℤ) : AlgebraicClosure K) * (d : AlgebraicClosure K)))) := by
              ring
    _ = (((((N / g : ℕ) : AlgebraicClosure K)⁻¹) *
          (((N / g : ℕ) : AlgebraicClosure K) * (z : AlgebraicClosure K)))) := by
            rw [hcast]
    _ = (((((N / g : ℕ) : AlgebraicClosure K)⁻¹) *
          (((N / g : ℕ) : AlgebraicClosure K)) * (z : AlgebraicClosure K))) := by
            ring
    _ = (z : AlgebraicClosure K) := by
          simp [hn_ne]

/-- Helper for Proposition 12-12.2-1: the reduced `i`-th common-multiple term is exactly an
integral packet sum after rewriting the scalar-extension packet decomposition coefficientwise. -/
private theorem mapped_reduced_scaled_character_eq_packet_sum
    [Finite ι] [Fintype ι]
    {N : ℕ}
    (hN_ne : N ≠ 0)
    (π : ι → FDRep K G)
    (c : ι → ℤ)
    (i : ι)
    {κ : Type u} [Fintype κ]
    (ψ : κ → Rep.{u} (AlgebraicClosure K) G)
    (d : κ → ℕ)
    (hpacket :
      (Representation.scalarExtension (k := AlgebraicClosure K) (π i).ρ).character =
        ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character)
    (z : κ → ℤ)
    (hz : ∀ j, c i * d j = (N : ℤ) * z j) :
    let g : ℕ := Nat.gcd (Int.natAbs (c i)) N
    let n : ℕ+ := ⟨N / g, Nat.div_gcd_pos_of_pos_right (Int.natAbs (c i))
      (Nat.pos_of_ne_zero hN_ne)⟩
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K)) =
      ∑ j, z j • (ψ j).ρ.character := by
  classical
  let g : ℕ := Nat.gcd (Int.natAbs (c i)) N
  have hn_pos : 0 < N / g := by
    simpa [g] using
      Nat.div_gcd_pos_of_pos_right (Int.natAbs (c i)) (Nat.pos_of_ne_zero hN_ne)
  let n : ℕ+ := ⟨N / g, hn_pos⟩
  change
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K)) =
      ∑ j, z j • (ψ j).ρ.character
  have hmap_scaled :
      Representation.schurScaledCharacter (Rep.of (π i).ρ) n =
        ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
          (FDRep.schurScaledCharacter (π i) n) := by
    simpa using
      Representation.schurScaledCharacter_eq_map_fdRep_schurScaledCharacter (π i) n
  have hpacket_scaled :
      Representation.schurScaledCharacter (Rep.of (π i).ρ) n =
        (((n : ℕ) : AlgebraicClosure K)⁻¹) •
          ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character := by
    -- Rewrite the mapped source character through the scalar-extension packet decomposition.
    rw [hmap_scaled]
    ext g0
    calc
      (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
          (FDRep.schurScaledCharacter (π i) n) g0)
          = (((n : ℕ) : AlgebraicClosure K)⁻¹) *
              (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                ((π i).character) g0) := by
                  simp [FDRep.schurScaledCharacter, smul_eq_mul]
      _ = (((n : ℕ) : AlgebraicClosure K)⁻¹) *
            ((Representation.scalarExtension (k := AlgebraicClosure K) (π i).ρ).character g0) := by
              rw [scalarExtension_character_eq_map_fdRep_character]
      _ = (((n : ℕ) : AlgebraicClosure K)⁻¹) *
            ((∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character) g0) := by
              rw [hpacket]
      _ = ((((n : ℕ) : AlgebraicClosure K)⁻¹) •
            ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character) g0 := by
              simp [smul_eq_mul]
  calc
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K))
        = ((c i / g : ℤ) •
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
              (FDRep.schurScaledCharacter (π i) n) : G → AlgebraicClosure K) := by
              -- First move the integral scalar through the coefficientwise embedding.
              ext g0
              calc
                (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                    (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K)) g0)
                    = (algebraMap K (AlgebraicClosure K))
                        ((((c i / g : ℤ) : K) * FDRep.schurScaledCharacter (π i) n g0)) := by
                          simp [zsmul_eq_mul, FDRep.schurScaledCharacter, smul_eq_mul]
                          ring
                _ = (((c i / g : ℤ) : AlgebraicClosure K) *
                      (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                        (FDRep.schurScaledCharacter (π i) n) g0)) := by
                        simp [FDRep.schurScaledCharacter, smul_eq_mul]
                _ = (((c i / g : ℤ) •
                      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                        (FDRep.schurScaledCharacter (π i) n) : G → AlgebraicClosure K) g0) := by
                        simp [zsmul_eq_mul]
    _ = ((c i / g : ℤ) • Representation.schurScaledCharacter (Rep.of (π i).ρ) n :
          G → AlgebraicClosure K) := by
            rw [hmap_scaled]
    _ = ((c i / g : ℤ) • ((((n : ℕ) : AlgebraicClosure K)⁻¹) •
          ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character) : G → AlgebraicClosure K) := by
            rw [hpacket_scaled]
    _ = ∑ j, ((((c i / g : ℤ) : AlgebraicClosure K) *
          (((n : ℕ) : AlgebraicClosure K)⁻¹) * (d j : AlgebraicClosure K)) •
            (ψ j).ρ.character) := by
            -- Expand the packet termwise so the coefficient normalization can be applied
            -- constituent by constituent.
            ext g0
            simp [zsmul_eq_mul, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ j, z j • (ψ j).ρ.character := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ext g0
          -- The divisibility witness identifies the reduced scalar with the integral packet
          -- coefficient `z j`.
          have hcoef :
              (((c i / g : ℤ) : AlgebraicClosure K) * (((n : ℕ) : AlgebraicClosure K)⁻¹) *
                  (d j : AlgebraicClosure K)) =
                (z j : AlgebraicClosure K) := by
            simpa [g, n] using
              reduced_packet_scalar_eq_integral_witness
                (K := K) (c := c i) (N := N) (d := d j) (z := z j) hN_ne (hz j)
          simpa [zsmul_eq_mul, smul_eq_mul, hcoef]

private theorem coordinate_term_mem_characterRingOverAlgClosure_of_common_multiple_expansion
    [Finite ι] [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (χ : R̄[K](G))
    (hchar_overline : ∀ i, (π i).character ∈ R̄[K](G))
    {N : ℕ}
    (hN_ne : N ≠ 0)
    (c : ι → ℤ)
    (hχN_expansion :
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = (N : ℤ) • χ)
    (i : ι) :
    let g : ℕ := Nat.gcd (Int.natAbs (c i)) N
    let n : ℕ+ := ⟨N / g, Nat.div_gcd_pos_of_pos_right (Int.natAbs (c i))
      (Nat.pos_of_ne_zero hN_ne)⟩
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K)) ∈
      R[AlgebraicClosure K](G) := by
  obtain ⟨κ, _, ψ, d, hψ_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    scalar_extension_character_eq_sum_irreducible_family_with_nat_coefficients
      (K := K) (G := G) (V := π i)
  have hdiv :
      ∀ j, (N : ℤ) ∣ c i * d j := by
    intro j
    exact
      packet_multiplicity_divisible_of_mapped_common_multiple_expansion
        (K := K) (G := G) (ι := ι) π hπ_pairwise hπ_complete χ hchar_overline c
        hχN_expansion i ψ d hψ_pos hψ_fd hψ_pairwise hψ_irr hpacket j
  choose z hz using hdiv
  let g : ℕ := Nat.gcd (Int.natAbs (c i)) N
  have hn_pos : 0 < N / g := by
    simpa [g] using
      Nat.div_gcd_pos_of_pos_right (Int.natAbs (c i)) (Nat.pos_of_ne_zero hN_ne)
  let n : ℕ+ := ⟨N / g, hn_pos⟩
  change
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K)) ∈
      R[AlgebraicClosure K](G)
  have hrewrite :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
          (((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K)) =
        ∑ j, z j • (ψ j).ρ.character := by
    -- Route correction: the packet-comparison work is finished; only the transport-stable
    -- scalar normalization remained, and the previous helper now packages exactly that step.
    simpa [g, n] using
      mapped_reduced_scaled_character_eq_packet_sum
        (K := K) (G := G) (ι := ι) (N := N) hN_ne π c i ψ d hpacket z hz
  rw [hrewrite]
  -- Each packet constituent is an honest representation character, so the finite integral sum
  -- stays inside the character ring.
  exact (R[AlgebraicClosure K](G)).toSubmodule.sum_mem fun j _ ↦
    Submodule.smul_mem (R[AlgebraicClosure K](G)).toSubmodule (z j) (by
      simpa using
        Representation.rep_character_mem_characterRingOverField
          (K := AlgebraicClosure K) (G := G) (ψ j))

/-- Helper for Proposition 12-12.2-1: once the algebraic-closure packet block is known to be a
virtual character, the coefficientwise embedding descends it back to `\overline{R}_K(G)`. -/
private theorem coprime_scaled_term_mem_overline_of_common_multiple_expansion
    [Finite ι] [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (χ : R̄[K](G))
    (hchar_overline : ∀ i, (π i).character ∈ R̄[K](G))
    {N : ℕ}
    (hN_ne : N ≠ 0)
    (c : ι → ℤ)
    (hχN_expansion :
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = (N : ℤ) • χ)
    (i : ι) :
    let g : ℕ := Nat.gcd (Int.natAbs (c i)) N
    let n : ℕ+ := ⟨N / g, Nat.div_gcd_pos_of_pos_right (Int.natAbs (c i))
      (Nat.pos_of_ne_zero hN_ne)⟩
    ((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n : G → K) ∈ R̄[K](G) := by
  -- Descend the mapped packet block through the defining extension bridge for
  -- `\overline{R}_K(G)`.
  rw [mem_overlineCharacterRingInExtension_iff]
  simpa using
    coordinate_term_mem_characterRingOverAlgClosure_of_common_multiple_expansion
      (K := K) (G := G) (ι := ι) π hπ_pairwise hπ_complete m hdenom χ hchar_overline
      hN_ne c hχN_expansion i

/-- Helper for Proposition 12-12.2-1: in the pairwise case, the remaining task is to show that
every element of `\overline{R}_K(G)` has scaled-character coordinates with the expected
integrality. -/
private theorem mem_span_schurScaledCharacters_of_mem_overline_pairwise
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (χ : R̄[K](G)) :
    χ ∈
      Submodule.span ℤ
        (Set.range fun i ↦
          (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) := by
  classical
  letI : Finite ι := finite_index_of_complete_pairwiseNonisomorphic
    (K := K) (G := G) π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let S : Submodule ℤ (R̄[K](G)) :=
    Submodule.span ℤ
      (Set.range fun i ↦
        (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)))
  have hchar_le :
      ∀ ξ : R[K](G), (⟨(ξ : G → K), characterRingOverField_le_overlineCharacterRing K G ξ.2⟩ :
        R̄[K](G)) ∈ S :=
    characterRingOverField_le_span_schurScaledCharacters
      (K := K) (G := G) π hπ_pairwise hπ_complete m hdenom
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let n : ℕ :=
    ((R[K](G)).toSubmodule.toAddSubgroup).relIndex
      ((R̄[K](G)).toSubmodule.toAddSubgroup)
  let D : ℕ := ∏ i : ι, (m i : ℕ)
  let N : ℕ := n * D
  let χN : R[K](G) :=
    ⟨N • (χ : G → K),
      by
        simpa [n, D, N] using
          common_multiple_mem_characterRingOverField (K := K) (G := G) (ι := ι) m χ⟩
  have hχN_mem : (⟨(χN : G → K), characterRingOverField_le_overlineCharacterRing K G χN.2⟩ :
      R̄[K](G)) ∈ S :=
    hchar_le χN
  have hχN_eq :
      (⟨(χN : G → K), characterRingOverField_le_overlineCharacterRing K G χN.2⟩ : R̄[K](G)) =
        (N : ℤ) • χ := by
    -- Identify the promoted common multiple with the corresponding integer scalar multiple.
    apply Subtype.ext
    ext g
    simp [χN, N]
  have hNχ_mem : (N : ℤ) • χ ∈ S := by
    simpa [hχN_eq] using hχN_mem
  rw [Submodule.mem_span_range_iff_exists_fun] at hNχ_mem
  rcases hNχ_mem with ⟨z, hz⟩
  have hchar_overline : ∀ i, (π i).character ∈ R̄[K](G) := by
    intro i
    exact
      characterRingOverField_le_overlineCharacterRing K G
        (FDRep.character_mem_characterRingOverField K (π i))
  let c : ι → ℤ := b.repr χN
  have hχN_expansion :
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G)) = (N : ℤ) • χ := by
    -- Rewrite the irreducible-basis expansion of `χN` inside the ambient overline owner.
    calc
      ∑ i, c i • (⟨(π i).character, hchar_overline i⟩ : R̄[K](G))
          = (⟨(χN : G → K), characterRingOverField_le_overlineCharacterRing K G χN.2⟩ :
              R̄[K](G)) := by
                apply Subtype.ext
                ext g
                simpa [b, c, χN, irreducible_characters_basis_of_complete_family_apply,
                  FDRep.irreducibleCharacter_apply] using
                  congrFun (congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr χN)) g
      _ = (N : ℤ) • χ := hχN_eq
  have hcoeff_pairing :
      ∀ i,
        ⟪(χN : G → K), (π i).character⟫ =
          ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
    intro i
    simpa [b, c] using
      basis_coefficient_pairing_eq
        (K := K) (G := G) (π := π) hπ_pairwise hπ_complete χN i
  have hzχN :
      ∑ i, z i • (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)) =
        (⟨(χN : G → K), characterRingOverField_le_overlineCharacterRing K G χN.2⟩ : R̄[K](G)) := by
    -- Repackage the scaled-generator expansion of `N • χ` as an expansion of the promoted
    -- `R_K(G)` element `χN`.
    calc
      ∑ i, z i • (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))
          = (N : ℤ) • χ := hz
      _ = (⟨(χN : G → K), characterRingOverField_le_overlineCharacterRing K G χN.2⟩ :
            R̄[K](G)) := hχN_eq.symm
  have hz_coeff :
      ∀ i, z i = (m i : ℤ) * c i := by
    intro i
    simpa [c] using
      scaled_span_coefficient_eq_denominator_mul_basis_coefficient
        (K := K) (G := G) (ι := ι) π hπ_pairwise hπ_complete m hdenom χN z hzχN i
  -- Route correction: the abstract reduction and the explicit common multiple `N` are now fixed.
  -- The first remaining blocker is now purely a divisibility/purity statement inside the scaled
  -- span `S`: the actual scaled coordinates `z i` of `N • χ` are known explicitly by
  -- `hz_coeff i = m i * c i`, so it remains to prove that each `z i` is itself divisible by `N`.
  -- That purity statement is exactly equivalent to the desired `N / m i ∣ c i`, after rewriting
  -- with `hz_coeff`.
  have hfin :
      ((R[K](G)).toSubmodule.toAddSubgroup).IsFiniteRelIndex
        ((R̄[K](G)).toSubmodule.toAddSubgroup) := by
    exact characterRingOverField_isFiniteRelIndex_overlineCharacterRing (K := K) (G := G)
  letI := hfin
  have hN_ne : N ≠ 0 := by
    apply mul_ne_zero
    exact AddSubgroup.relIndex_ne_zero
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (m i).pos.ne')
  have hNmul : ∀ i, (m i : ℕ) ∣ N := by
    intro i
    refine dvd_mul_of_dvd_right ?_ n
    exact Finset.dvd_prod_of_mem (fun j : ι ↦ (m j : ℕ)) (Finset.mem_univ i)
  -- TODO: the remaining blocker is now the purity statement `N ∣ z i` for the scaled-coordinate
  -- vector `z` of `N • χ` in `S`. Equivalently, one needs a coordinate-projection lemma showing
  -- that the coefficient of `χ` along the `i`-th scaled generator is already integral. After that,
  -- `hz_coeff i : z i = m i * c i` and `hNmul i : m i ∣ N` convert the purity statement into the
  -- target divisibility `N / m i ∣ c i`, and the helper
  -- `mem_span_schurScaledCharacters_of_coeff_divisibility` finishes the rewrite-and-cancel
  -- endgame.
  have hdiv :
      ∀ i, (((N / (m i : ℕ)) : ℕ) : ℤ) ∣ c i := by
    intro i
    let g : ℕ := Nat.gcd (Int.natAbs (c i)) N
    let n' : ℕ+ := ⟨N / g,
      Nat.div_gcd_pos_of_pos_right (Int.natAbs (c i)) (Nat.pos_of_ne_zero hN_ne)⟩
    have hscaled_mem :
        ((c i / g : ℤ) • FDRep.schurScaledCharacter (π i) n' : G → K) ∈ R̄[K](G) := by
      -- Use the common-multiple expansion to isolate the coprime-reduced `i`-th term.
      simpa [g, n'] using
        coprime_scaled_term_mem_overline_of_common_multiple_expansion
          (K := K) (G := G) (ι := ι) π hπ_pairwise hπ_complete m hdenom χ hchar_overline
          hN_ne c hχN_expansion i
    have hcop :
        Nat.Coprime (Int.natAbs (c i / g)) (n' : ℕ) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hg_pos : 0 < Int.gcd (c i) (N : ℤ) := by
        simpa [Int.gcd_def, g] using
          Nat.gcd_pos_of_pos_right (Int.natAbs (c i)) (Nat.pos_of_ne_zero hN_ne)
      -- Dividing both numerator and denominator by their gcd produces a coprime pair.
      simpa [Int.gcd_def, g, n'] using
        Int.gcd_div_gcd_div_gcd (i := c i) (j := N) hg_pos
    have hn_mem : FDRep.schurScaledCharacter (π i) n' ∈ R̄[K](G) := by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact
        schurScaledCharacter_mem_of_coprime_zsmul_mem_overline
          (K := K) (G := G) (V := π i) n' hcop hscaled_mem
    have hndvdm : (n' : ℕ) ∣ (m i : ℕ) := by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact
        admissible_denominator_dvd_of_isSchurDenominator
          (K := K) (G := G) (V := π i) (m := m i) (hdenom i) hn_mem
    have hdiv_g : (N / (m i : ℕ)) ∣ g := by
      rcases hNmul i with ⟨d, hd⟩
      rcases hndvdm with ⟨t, ht⟩
      have hn_pos : 0 < (n' : ℕ) := n'.2
      have hNg : (n' : ℕ) * g = N := by
        simpa [n', g] using Nat.div_mul_cancel (Nat.gcd_dvd_right (Int.natAbs (c i)) N)
      have hNm : N = (n' : ℕ) * (t * d) := by
        calc
          N = (m i : ℕ) * d := hd
          _ = ((n' : ℕ) * t) * d := by rw [ht]
          _ = (n' : ℕ) * (t * d) := by ring
      have hg_eq : g = t * d := by
        exact Nat.eq_of_mul_eq_mul_left hn_pos (hNg.trans hNm)
      have hd_eq : d = N / (m i : ℕ) := by
        exact
          Nat.eq_div_of_mul_eq_right (m i).pos.ne'
            (by simpa [Nat.mul_comm] using hd.symm)
      refine ⟨t, ?_⟩
      calc
        g = t * d := hg_eq
        _ = (N / (m i : ℕ)) * t := by rw [hd_eq, Nat.mul_comm]
    have hdiv_natAbs : (N / (m i : ℕ)) ∣ Int.natAbs (c i) := by
      exact dvd_trans hdiv_g (Nat.gcd_dvd_left (Int.natAbs (c i)) N)
    have hdiv_int :
        (((N / (m i : ℕ)) : ℕ) : ℤ) ∣ ((Int.natAbs (c i) : ℕ) : ℤ) := by
      exact Int.natCast_dvd_natCast.mpr hdiv_natAbs
    -- Passing from `natAbs` back to the original integer coefficient finishes the divisibility.
    exact (Int.dvd_natAbs).mp hdiv_int
  exact
    mem_span_schurScaledCharacters_of_coeff_divisibility
      (K := K) (G := G) (ι := ι) π m hdenom χ S rfl hchar_overline hN_ne hNmul c
      hχN_expansion hdiv

/-- Helper for Proposition 12-12.2-1: once the coordinate-divisibility step is available in the
pairwise case, the scaled characters span all of `\overline{R}_K(G)`. -/
private theorem span_schurScaledCharacters_eq_top_of_complete_family_pairwise
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i)) :
      Submodule.span ℤ
        (Set.range fun i ↦
          (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) =
      ⊤ := by
  classical
  letI : Finite ι := finite_index_of_complete_pairwiseNonisomorphic
    (K := K) (G := G) π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let S : Submodule ℤ (R̄[K](G)) :=
    Submodule.span ℤ
      (Set.range fun i ↦
        (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)))
  refine top_unique ?_
  intro χ _
  exact
    mem_span_schurScaledCharacters_of_mem_overline_pairwise
      (K := K) (G := G) π hπ_pairwise hπ_complete m hdenom χ

/-- For a complete irreducible family, the corresponding scaled characters span all of
`R̄[K](G)` provided the denominators are the source-faithful Schur denominators. -/
theorem span_schurScaledCharacters_eq_top_of_complete_family
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i)) :
    Submodule.span ℤ
        (Set.range fun i ↦
          (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) =
      ⊤ := by
  classical
  let Sπ : Submodule ℤ (R̄[K](G)) :=
    Submodule.span ℤ
      (Set.range fun i ↦
        (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)))
  let r : Setoid ι :=
    { r := fun i j ↦ Nonempty (π i ≅ π j)
      iseqv :=
        ⟨fun i ↦ ⟨Iso.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j k} hij hjk ↦ by
            rcases hij with ⟨eij⟩
            rcases hjk with ⟨ejk⟩
            exact ⟨eij.trans ejk⟩⟩ }
  let κ : Type x := Quotient r
  let σ : κ → FDRep K G := fun q ↦ π (Quotient.out q)
  have hσ_pairwise : PairwiseNonisomorphic σ := by
    intro q q' hqq' hIso
    have hclasses :
        (⟦Quotient.out q⟧ : κ) = ⟦Quotient.out q'⟧ := by
      exact Quotient.sound
        (show Nonempty (π (Quotient.out q) ≅ π (Quotient.out q')) from by
          simpa [σ] using hIso)
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : κ) := (Quotient.out_eq q).symm
      _ = ⟦Quotient.out q'⟧ := hclasses
      _ = q' := Quotient.out_eq q'
  have hσ_complete : IsCompleteIrreducibleFamily σ := by
    refine
      { isSimple := ?_
        exists_iso := ?_ }
    · intro q
      simpa [σ] using hπ_complete.isSimple (Quotient.out q)
    · intro τ hτ
      obtain ⟨i, hi⟩ := hπ_complete.exists_iso τ hτ
      refine ⟨(⟦i⟧ : κ), ?_⟩
      have hout : Nonempty (σ (⟦i⟧ : κ) ≅ π i) := by
        exact Quotient.exact (Quotient.out_eq (⟦i⟧ : κ))
      rcases hi with ⟨hi⟩
      rcases hout with ⟨hout⟩
      simpa [σ] using ⟨hi.trans hout.symm⟩
  let mσ : κ → ℕ+ := fun q ↦ m (Quotient.out q)
  have hdenomσ : ∀ q, FDRep.IsSchurDenominator (σ q) (mσ q) := by
    intro q
    simpa [σ, mσ] using hdenom (Quotient.out q)
  let Sσ : Submodule ℤ (R̄[K](G)) :=
    Submodule.span ℤ
      (Set.range fun q ↦
        (⟨FDRep.schurScaledCharacter (σ q) (mσ q), (hdenomσ q).1⟩ : R̄[K](G)))
  have hσ_le : Sσ ≤ Sπ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    -- Each quotient-indexed generator is literally one of the original generators.
    exact Submodule.subset_span ⟨Quotient.out q, rfl⟩
  have hσ_top : Sσ = ⊤ := by
    exact
      span_schurScaledCharacters_eq_top_of_complete_family_pairwise
        (K := K) (G := G) σ hσ_pairwise hσ_complete mσ hdenomσ
  refine top_unique ?_
  intro χ _
  have hχσ : χ ∈ Sσ := by
    rw [hσ_top]
    trivial
  exact hσ_le hχσ

-- Proof sketch: the scaled characters `χᵢ / mᵢ` are the source-facing generators of
-- `\overline{R}_K(G)` when each `mᵢ` is the canonical Schur denominator. The
-- algebraic-closure realization is only a bridge used to compare these generators with the
-- canonical irreducible-character basis over `\overline K`.
/-- Proposition 12-12.2-1: for a complete pairwise nonisomorphic family of finite-dimensional
irreducible `K`-representations, if each `mᵢ` is the maximal positive integer for which the scaled
character `ψᵢ = χᵢ / mᵢ` belongs to `\overline{R}_K(G)`, then the scaled characters form a
`ℤ`-basis of `\overline{R}_K(G)`. -/
def scaled_irreducible_characters_basis_of_complete_family
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i)) :
    Module.Basis ι ℤ (R̄[K](G)) :=
  Module.Basis.mk
    (linearIndependent_schurScaledCharacters_of_pairwiseNonisomorphic
      π hπ_complete.isSimple hπ_pairwise m hdenom)
    (span_schurScaledCharacters_eq_top_of_complete_family π hπ_complete m hdenom).ge

/-- Evaluating the basis from Proposition `12-12.2-1` at `i` returns the scaled character
`χᵢ / mᵢ`, viewed in `R̄[K](G)`. -/
@[simp] theorem scaled_irreducible_characters_basis_of_complete_family_apply
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i))
    (i : ι) :
    scaled_irreducible_characters_basis_of_complete_family
        π hπ_pairwise hπ_complete m hdenom i =
      (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G)) := by
  change
      Module.Basis.mk
          (linearIndependent_schurScaledCharacters_of_pairwiseNonisomorphic
            π hπ_complete.isSimple hπ_pairwise m hdenom)
          (span_schurScaledCharacters_eq_top_of_complete_family
            π hπ_complete m hdenom).ge i =
        (fun j ↦ (⟨FDRep.schurScaledCharacter (π j) (m j), (hdenom j).1⟩ : R̄[K](G))) i
  exact
    Module.Basis.mk_apply
      (linearIndependent_schurScaledCharacters_of_pairwiseNonisomorphic
        π hπ_complete.isSimple hπ_pairwise m hdenom)
      (span_schurScaledCharacters_eq_top_of_complete_family
        π hπ_complete m hdenom).ge
      i

end

end Representation
