import Mathlib
import Serre.Chap02.Corollary_2_2_4_3
import Serre.Chap12.Proposition_12_12_1_3

noncomputable section

open scoped Representation

universe u v w x

namespace Representation

open CategoryTheory

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

namespace FDRep

/-- The source-facing scaled character `χ / m` of a finite-dimensional `K`-representation, viewed
as a `K`-valued class function. -/
abbrev schurScaledCharacter (V : FDRep K G) (m : ℕ+) : G → K :=
  (((m : ℕ) : K)⁻¹) • V.character

@[simp] theorem schurScaledCharacter_apply (V : FDRep K G) (m : ℕ+) (g : G) :
    FDRep.schurScaledCharacter V m g = (((m : ℕ) : K)⁻¹) * V.character g := by
  rfl

/-- The positive integer `m` is the source-facing Schur denominator attached to the
finite-dimensional `K`-representation `V` when `χ_V / m` belongs to `\overline{R}_K(G)` and `m`
is maximal for this property. This is the general-field denominator form of Serre's Schur-index
condition; the
complex-character owner `HasSchurIndex` remains the specialized Chapter 12 owner on the complex
side. -/
def IsSchurDenominator (V : FDRep K G) (m : ℕ+) : Prop :=
  FDRep.schurScaledCharacter V m ∈ R̄[K](G) ∧
    ∀ n : ℕ+, FDRep.schurScaledCharacter V n ∈ R̄[K](G) → n ≤ m

end FDRep

end

section

variable {K : Type v} [Field K]
variable {G : Type u} [Group G]

/-- The algebraic-closure-valued realization of `FDRep.schurScaledCharacter`. This is only the
coefficient-extension bridge of the source-facing `K`-valued scaled character. -/
abbrev schurScaledCharacter (π : Rep.{w} K G) [FiniteDimensional K π] (m : ℕ+) :
    G → AlgebraicClosure K :=
  ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
    ((((m : ℕ) : K)⁻¹) • π.ρ.character)

end

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

/-- The algebraic-closure realization of `FDRep.schurScaledCharacter` is obtained by applying the
coefficientwise embedding `K → AlgebraicClosure K`. -/
theorem schurScaledCharacter_eq_map_fdRep_schurScaledCharacter
    (V : FDRep K G) (m : ℕ+) :
    Representation.schurScaledCharacter (Rep.of V.ρ) m =
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (FDRep.schurScaledCharacter V m) := by
  rfl

end

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

namespace FDRep

/-- A scaled irreducible character whose coefficientwise image in `AlgebraicClosure K` lies in
`R_{\overline K}(G)` is automatically an element of the source-facing owner
`\overline{R}_K(G)`. -/
theorem schurScaledCharacter_mem_overlineCharacterRing
    (V : FDRep K G)
    (m : ℕ+)
    (hscaled : Representation.schurScaledCharacter (Rep.of V.ρ) m ∈ R[AlgebraicClosure K](G)) :
    FDRep.schurScaledCharacter V m ∈ R̄[K](G) := by
  change FDRep.schurScaledCharacter V m ∈ overlineCharacterRingInExtension K (AlgebraicClosure K)
  rw [mem_overlineCharacterRingInExtension_iff]
  have hbridge := Representation.schurScaledCharacter_eq_map_fdRep_schurScaledCharacter V m
  simpa [hbridge] using hscaled

end FDRep

end

section

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local instance instFintypeScaledCharacterGroupCore : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage: the next three declarations are `source-facing`. Their primitive
-- data are the irreducible family `π`, the denominator data `m`, and the source-facing Schur
-- denominator witness `hdenom : FDRep.IsSchurDenominator (π i) (m i)`. This separates the
-- primitive datum `χᵢ / mᵢ ∈ R̄[K](G)` from the derived maximality property `n ≤ mᵢ` for every
-- other admissible denominator `n`, which is the correct source-faithful Schur-index direction.
-- The only bridge/view involved is the coefficientwise embedding `G → K → AlgebraicClosure K`,
-- used when one wants to verify these owner-membership witnesses inside `R_{\overline K}(G)`.
-- Proof sketch: compare the algebraic-closure realizations of the scaled characters with the
-- irreducible-character basis of `R[AlgebraicClosure K](G)`, then transport the result back to
-- the source-facing owner `R̄[K](G)` using the canonical denominator data.
/-- Helper for Proposition 12-12.2-1: multiplying a scaled character by its denominator recovers
the original character. -/
theorem zsmul_schurScaledCharacter_eq_character
    (V : FDRep K G) (n : ℕ+) :
    ((n : ℤ) • FDRep.schurScaledCharacter V n : G → K) = V.character := by
  -- Expand the scaled character pointwise and cancel the inverse denominator.
  ext g
  simp [FDRep.schurScaledCharacter, zsmul_eq_mul]

/-- Helper for Proposition 12-12.2-1: the normalized pairing is additive on finite `ℤ`-linear
combinations in its left argument. -/
theorem groupFunctionPairing_sum_zsmul_left
    (s : Finset ι) (g : ι → ℤ) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, g j • χ j, ψ⟫ = ∑ j ∈ s, (g j : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [groupFunctionPairingOverField]
  | insert a s ha ih =>
      -- Rewrite the inserted term as an honest `K`-scalar multiple before using bilinearity.
      have hzsmul : (g a • χ a : G → K) = ((g a : K) • χ a) := by
        ext x
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert ha, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert ha]

/-- Helper for Proposition 12-12.2-1: the self-pairing of a simple character is nonzero. -/
theorem groupFunctionPairingOverField_character_self_ne_zero
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj V
  let e₁ : (V ⟶ V) ≃ₗ[K] (X ⟶ X) := (FDRep.forget₂HomLinearEquiv V V).symm
  let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := by
    simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
  let e : (V ⟶ V) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := e₁.trans e₂
  letI : FiniteDimensional K (Representation.IntertwiningMap V.ρ V.ρ) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  have hnontriv : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
    refine ⟨0, e (𝟙 V), ?_⟩
    intro h
    apply CategoryTheory.id_nonzero V
    exact e.injective h.symm
  letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := hnontriv
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  -- Compute the self-pairing through the endomorphism-space dimension.
  have hpair :
      ⟪V.character, V.character⟫ =
        Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ) :=
    Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K V.ρ V.ρ
  rw [hpair]
  exact_mod_cast Module.finrank_pos.ne'

/-- For a pairwise nonisomorphic irreducible family, the corresponding scaled characters are
`ℤ`-linearly independent in `R̄[K](G)`. -/
theorem linearIndependent_schurScaledCharacters_of_pairwiseNonisomorphic
    (π : ι → FDRep K G)
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (m : ι → ℕ+)
    (hdenom : ∀ i, FDRep.IsSchurDenominator (π i) (m i)) :
    LinearIndependent ℤ
      (fun i ↦
        (⟨FDRep.schurScaledCharacter (π i) (m i), (hdenom i).1⟩ : R̄[K](G))) := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  rw [linearIndependent_iff']
  intro s g hg i hi
  -- Forget the subtype wrapper so that the relation lives in the ambient function space.
  have hgfun :
      ∑ j ∈ s, g j • FDRep.schurScaledCharacter (π j) (m j) = (0 : G → K) := by
    have hg' := congrArg (fun z : R̄[K](G) ↦ (z : G → K)) hg
    simpa using hg'
  -- Pair the relation with the unscaled irreducible character `χᵢ` to isolate the `i`-th
  -- coefficient.
  have hpair0 :=
    congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hgfun
  have hpair :
      ⟪∑ j ∈ s, g j • FDRep.schurScaledCharacter (π j) (m j), (π i).character⟫ = (0 : K) := by
    have hzero_pair :
        groupFunctionPairingOverField K (0 : G → K) (π i).character = (0 : K) := by
      simp [groupFunctionPairingOverField]
    exact hpair0.trans hzero_pair
  rw [groupFunctionPairing_sum_zsmul_left
      (K := K) (G := G) (s := s) g
      (fun j ↦ FDRep.schurScaledCharacter (π j) (m j)) ((π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · letI : Simple (π i) := hπ_simple i
    have hscaled_pair :
        ⟪FDRep.schurScaledCharacter (π i) (m i), (π i).character⟫ =
          (((m i : ℕ) : K)⁻¹) * ⟪(π i).character, (π i).character⟫ := by
      rw [FDRep.schurScaledCharacter, groupFunctionPairing_smul_left]
    have hm_ne : (((m i : ℕ) : K) : K) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (show (m i : ℕ) ≠ 0 from (m i).pos.ne')
    have hfactor_ne :
        (((m i : ℕ) : K)⁻¹) * ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
      exact mul_ne_zero (inv_ne_zero hm_ne)
        (groupFunctionPairingOverField_character_self_ne_zero (K := K) (G := G) (π i))
    have hcoeff : ((g i : ℤ) : K) = 0 := by
      rw [hscaled_pair] at hpair
      exact (mul_eq_zero.mp hpair).resolve_right hfactor_ne
    exact Int.cast_eq_zero.mp hcoeff
  · intro j hj hji
    letI : Simple (π j) := hπ_simple j
    letI : Simple (π i) := hπ_simple i
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
  · intro hnot_mem
    exact (hnot_mem hi).elim

/-- Helper for Proposition 12-12.2-1: Schur denominators are invariant under `FDRep`
isomorphism. -/
theorem isSchurDenominator_of_iso
    {V W : FDRep K G} (e : V ≅ W) {m : ℕ+}
    (hm : FDRep.IsSchurDenominator V m) :
    FDRep.IsSchurDenominator W m := by
  refine ⟨?_, ?_⟩
  · -- Isomorphic finite-dimensional representations have the same character, so the scaled
    -- membership condition transports verbatim.
    simpa [FDRep.schurScaledCharacter, FDRep.char_iso e] using hm.1
  · intro n hn
    -- Transport the competing denominator witness back across the same character identity.
    have hn' : FDRep.schurScaledCharacter V n ∈ R̄[K](G) := by
      simpa [FDRep.schurScaledCharacter, FDRep.char_iso e] using hn
    exact hm.2 n hn'

/-- Helper for Proposition 12-12.2-1: a coprime integer multiple of a scaled irreducible
character lies in `\overline{R}_K(G)` only if the scaled character itself already does. -/
theorem schurScaledCharacter_mem_of_coprime_zsmul_mem_overline
    (V : FDRep K G) [Simple V]
    (n : ℕ+)
    {a : ℤ}
    (ha : Nat.Coprime a.natAbs (n : ℕ))
    (hmem : (a • FDRep.schurScaledCharacter V n : G → K) ∈ R̄[K](G)) :
    FDRep.schurScaledCharacter V n ∈ R̄[K](G) := by
  change FDRep.schurScaledCharacter V n ∈ (R̄[K](G)).toSubmodule
  have hchar_mem :
      ((n : ℤ) • FDRep.schurScaledCharacter V n : G → K) ∈ (R̄[K](G)).toSubmodule := by
    -- Multiply the scaled character by its denominator to return to the honest character.
    simpa [zsmul_schurScaledCharacter_eq_character (K := K) (G := G) V n] using
      (characterRingOverField_le_overlineCharacterRing K G
        (FDRep.character_mem_characterRingOverField K V))
  have hgcd : Int.gcd a (n : ℤ) = 1 := by
    simpa [Int.gcd_def] using ha.gcd_eq_one
  have hbezout :
      a * Int.gcdA a (n : ℤ) + (n : ℤ) * Int.gcdB a (n : ℤ) = 1 := by
    -- Rewrite the integer gcd identity into a Bézout relation for `a` and `n`.
    simpa [hgcd] using (Int.gcd_eq_gcd_ab a (n : ℤ)).symm
  have hexpr :
      FDRep.schurScaledCharacter V n =
        Int.gcdA a (n : ℤ) • (a • FDRep.schurScaledCharacter V n) +
          Int.gcdB a (n : ℤ) • ((n : ℤ) • FDRep.schurScaledCharacter V n) := by
    -- Express the target scaled character as a Bézout combination of the two known members.
    calc
      FDRep.schurScaledCharacter V n
          = (1 : ℤ) • FDRep.schurScaledCharacter V n := by
              simp
      _ = (a * Int.gcdA a (n : ℤ) + (n : ℤ) * Int.gcdB a (n : ℤ)) •
            FDRep.schurScaledCharacter V n := by
              rw [hbezout]
      _ = Int.gcdA a (n : ℤ) • (a • FDRep.schurScaledCharacter V n) +
            Int.gcdB a (n : ℤ) • ((n : ℤ) • FDRep.schurScaledCharacter V n) := by
              rw [add_zsmul, mul_comm a _, mul_comm (n : ℤ) _, mul_zsmul, mul_zsmul]
  rw [hexpr]
  -- The overline character ring is a `ℤ`-submodule, so the Bézout combination stays inside it.
  exact (R̄[K](G)).toSubmodule.add_mem
    ((R̄[K](G)).toSubmodule.smul_mem _ hmem)
    ((R̄[K](G)).toSubmodule.smul_mem _ hchar_mem)

end

end Representation
