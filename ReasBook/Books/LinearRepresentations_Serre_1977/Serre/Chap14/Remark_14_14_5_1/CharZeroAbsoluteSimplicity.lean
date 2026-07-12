import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1.ScaledCharacterPacket
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap12.SplittingFieldOfEnoughRoots
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients

/-!
# Absolute simplicity over a char-`0` splitting field

This module supplies **Part (A)** of the char-`0` splitting-field theorem
(`Serre/Chap14/Remark_14_14_5_1/AttemptCharZero.lean`): over a characteristic-zero field `k`
that is quasisplit (`R[k](G) = R̄[k](G)`, i.e. every absolutely-irreducible character is already a
`k`-character) and has enough roots of unity for the exponent, the self-intertwiner space of a
simple representation `S` is one-dimensional over `k`.

The argument is the *forward* packet computation: write the scalar extension to the algebraic
closure as a packet `S ⊗ k̄ = ⊕ᵢ ψᵢ^{dᵢ}` with the `ψᵢ` pairwise non-isomorphic irreducibles and
`dᵢ > 0`.  Two proven inputs combine:

* `dim_k End_{k[G]}(S) = ⟨χ_S, χ_S⟩ = Σᵢ dᵢ²` — Schur orthogonality together with the packet
  pairing (`groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`,
  `packet_constituent_pairing_eq_multiplicity`).
* For *one* constituent `ψ_{i₀}` its character is `k`-valued (enough roots of unity:
  `character_value_mem_algebraMap_range_of_hasEnoughRoots_extension`); quasisplit then places that
  `k`-valued character inside `R[k](G)`, and pairing against the orthonormal `k`-irreducible basis
  produces an *integer* `a` with `a · n = d_{i₀}`, where `n = Σᵢ dᵢ²`.  Since `dᵢ₀ ≥ 1` and
  `n ≥ dᵢ₀²`, the arithmetic `a · n = d_{i₀} ≥ 1`, `n ≥ d_{i₀}²` forces `n = 1`.

This is Brauer's splitting-field theorem in characteristic `0`, packaged as the single
absolute-simplicity number that `AttemptCharZero.lean` was missing.  Nothing here depends on the
flagged landmine `simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large`; the only
inputs are the (axiom-clean) algebraic machinery of Chapter 12.
-/

noncomputable section

universe u

open scoped TensorProduct Representation

open CategoryTheory

namespace Representation

section CharZeroAbsoluteSimplicity

variable {k : Type u} [Field k] [CharZero k] {G : Type u} [Group G] [Finite G]

local notation "k̄" => AlgebraicClosure k

local instance instFintypeCharZeroAbsSimplicity : Fintype G := Fintype.ofFinite G

/-- Helper: every constituent `ψ` of a scalar-extension packet has its character in
`R[k̄](G)`. -/
private theorem packet_character_mem_characterRing
    (ψ : Rep.{u} k̄ G) [FiniteDimensional k̄ ψ] :
    ψ.ρ.character ∈ R[k̄](G) :=
  rep_character_mem_characterRingOverField (K := k̄) (G := G) ψ

/-- Helper: if a `k̄`-valued character is in `R[k̄](G)` and takes values in (the image of) `k`,
its `k`-valued preimage lies in `R̄[k](G)`. -/
private theorem preimage_character_mem_overlineCharacterRing
    [HasEnoughRootsOfUnity k (Monoid.exponent G)]
    {χ : G → k̄} (hχ : χ ∈ R[k̄](G))
    (χk : G → k) (hχk : ((IsScalarTower.toAlgHom ℤ k k̄).compLeft G) χk = χ) :
    χk ∈ R̄[k](G) := by
  refine (mem_overlineCharacterRingInExtension_iff k k̄ χk).2 ?_
  exact hχk ▸ hχ

/-- **Part (A) — char-`0` absolute simplicity (field level).**

If `k` has characteristic `0`, has enough roots of unity for the exponent, and is *quasisplit*
(`R[k](G) = R̄[k](G)`), then for any simple `k[G]`-representation `S` the self-intertwiner space is
one-dimensional over `k`. -/
theorem finrank_intertwiningMap_eq_one_of_quasisplit
    [HasEnoughRootsOfUnity k (Monoid.exponent G)]
    (hquasi : R[k](G) = R̄[k](G))
    (S : FDRep k G) [Simple S] :
    Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
  classical
  letI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hcardk : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcardk
  have hcardC : (Nat.card G : k̄) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k̄) := invertibleOfNonzero hcardC
  -- Abbreviation: `n = dim_k End(S)`.
  set n : ℕ := Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) with hn_def
  -- `n ≥ 1` since `End(S)` contains the identity.
  have hn_pos : 0 < n := by
    have hScol : ⟪S.character, S.character⟫ ≠ (0 : k) :=
      self_pairing_character_ne_zero_local (K := k) (G := G) S
    have hpair : ⟪S.character, S.character⟫ = (n : k) := by
      simpa [n] using
        (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
          (K := k) (G := G) S.ρ S.ρ)
    rw [hpair] at hScol
    exact Nat.pos_of_ne_zero fun h => hScol (by simp [h])
  -- The packet decomposition `S ⊗ k̄ = ⊕ ψᵢ^{dᵢ}`.
  obtain ⟨ι, _, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    scalar_extension_character_eq_sum_irreducible_family_with_nat_coefficients
      (K := k) (G := G) S
  letI : Fintype ι := inferInstance
  -- `n = Σᵢ dᵢ²`.
  have hn_sum : (n : k̄) = ∑ i, (d i : k̄) * (d i : k̄) := by
    -- `⟨χ_S, χ_S⟩_k = n`.
    have hpairk : ⟪S.character, S.character⟫ = (n : k) := by
      simpa [n] using
        (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
          (K := k) (G := G) S.ρ S.ρ)
    -- Push to `k̄`: `⟨χ, χ⟩ = n` with `χ` the coefficient extension of `χ_S`.
    set χ : G → k̄ := ((IsScalarTower.toAlgHom ℤ k k̄).compLeft G) S.character with hχ_def
    have hmap_pair : ⟪χ, χ⟫ = (n : k̄) := by
      have := groupFunctionPairing_compLeft_toAlgClosure (K := k) (G := G) S.character S.character
      rw [show ((IsScalarTower.toAlgHom ℤ k k̄).compLeft G) S.character = χ from rfl] at this
      rw [this, hpairk]
      simp
    -- Expand `⟨χ, χ⟩ = Σᵢ dᵢ · ⟨χ_{ψᵢ}, χ⟩ = Σᵢ dᵢ²` via packet orthogonality.
    have hcoeff : ∀ j, ⟪χ, (ψ j).ρ.character⟫ = (d j : k̄) :=
      packet_constituent_pairing_eq_multiplicity
        (K := k) (G := G) S ψ d hψ_fd hψ_pairwise hψ_irr hpacket
    have hpair_sum :
        ⟪χ, χ⟫ = ∑ i, (d i : k̄) * (d i : k̄) := by
      calc
        ⟪χ, χ⟫ = ⟪∑ i, (d i : k̄) • (ψ i).ρ.character, χ⟫ := by
              have : χ = ∑ i, (d i : k̄) • (ψ i).ρ.character := by
                rw [hχ_def, ← scalarExtension_character_eq_map_fdRep_character (K := k) (G := G) S,
                  hpacket]
              rw [this]
        _ = ∑ i, (d i : k̄) * ⟪(ψ i).ρ.character, χ⟫ := by
              simpa using
                groupFunctionPairing_sum_field_smul_left
                  (K := k) (G := G) (s := Finset.univ)
                  (a := fun i ↦ (d i : k̄))
                  (χ := fun i ↦ (ψ i).ρ.character) χ
        _ = ∑ i, (d i : k̄) * (d i : k̄) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Representation.groupFunctionPairing_comm, hcoeff i]
    rw [← hmap_pair, hpair_sum]
  -- Choose one constituent `ψ i₀` (`ι` is nonempty since `Σ dᵢ² = n ≥ 1`).
  have hι_nonempty : Nonempty ι := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hnC0 : (n : k̄) = 0 := by
      rw [hn_sum, Finset.univ_eq_empty, Finset.sum_empty]
    have hn0 : n = 0 := by exact_mod_cast hnC0
    omega
  obtain ⟨i0⟩ := hι_nonempty
  letI : FiniteDimensional k̄ (ψ i0) := hψ_fd i0
  letI : (ψ i0).ρ.IsIrreducible := hψ_irr i0
  -- The character of `ψ i0` is `k`-valued (enough roots of unity).
  have hψ_mem : (ψ i0).ρ.character ∈ R[k̄](G) :=
    packet_character_mem_characterRing (ψ i0)
  have hvalued : ∀ g, ∃ x : k, algebraMap k k̄ x = (ψ i0).ρ.character g := fun g =>
    character_value_mem_algebraMap_range_of_hasEnoughRoots_extension
      (F := k) (E := k̄) (ψ i0).ρ.character hψ_mem g
  -- Build the `k`-valued preimage `χk` of `χ_{ψ i0}`.
  choose χk hχk using hvalued
  have hχk_eq : ((IsScalarTower.toAlgHom ℤ k k̄).compLeft G) χk = (ψ i0).ρ.character := by
    ext g
    simpa using hχk g
  -- `χk ∈ R̄[k](G) = R[k](G)` (quasisplit).
  have hχk_overline : χk ∈ R̄[k](G) :=
    preimage_character_mem_overlineCharacterRing hψ_mem χk hχk_eq
  have hχk_charRing : χk ∈ R[k](G) := by rw [hquasi]; exact hχk_overline
  -- Pick a complete pairwise nonisomorphic family of `k`-simples and locate `S`.
  obtain ⟨κ, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := k) (G := G)
  letI : Fintype κ := inferInstance
  obtain ⟨iS, hiS⟩ := hπ_complete.exists_iso S inferInstance
  rcases hiS with ⟨eS⟩
  -- Let `x := χk` viewed in `R[k](G)`; let `a` be its `χ_S`-coordinate.
  set x : R[k](G) := ⟨χk, hχk_charRing⟩ with hx_def
  set a : ℤ :=
    (irreducible_characters_basis_of_complete_family k π hπ_pairwise hπ_complete).repr x iS
    with ha_def
  -- `⟨χk, χ_{π iS}⟩ = a · ⟨χ_{π iS}, χ_{π iS}⟩` (basis coefficient extraction).
  have hbasis :
      ⟪(x : G → k), (π iS).character⟫ =
        ((a : ℤ) : k) * ⟪(π iS).character, (π iS).character⟫ := by
    simpa [a] using
      basis_coefficient_pairing_eq_local
        (K := k) (G := G) (π := π) hπ_pairwise hπ_complete x iS
  -- `χ_{π iS} = χ_S`, and `⟨χ_S, χ_S⟩ = n`.
  have hπS_char : (π iS).character = S.character := (FDRep.char_iso eS).symm
  have hself_n : ⟪(π iS).character, (π iS).character⟫ = (n : k) := by
    rw [hπS_char]
    simpa [n] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := k) (G := G) S.ρ S.ρ)
  -- So `⟨χk, χ_S⟩ = a · n` over `k`.
  have hxk_pair_k : ⟪χk, S.character⟫ = ((a : ℤ) : k) * (n : k) := by
    have hxval : (x : G → k) = χk := rfl
    rw [← hxval, ← hπS_char, hbasis, hself_n]
  -- Push to `k̄`: `⟨χ_{ψ i0}, χ_S^{k̄}⟩ = a · n` as well.
  have hxk_pair_C :
      ⟪(ψ i0).ρ.character, ((IsScalarTower.toAlgHom ℤ k k̄).compLeft G) S.character⟫
        = ((a : ℤ) : k̄) * (n : k̄) := by
    have hcl := groupFunctionPairing_compLeft_toAlgClosure (K := k) (G := G) χk S.character
    rw [hχk_eq] at hcl
    rw [hcl, hxk_pair_k, map_mul, map_intCast, map_natCast]
  -- The packet pairing gives `⟨χ_{ψ i0}, χ_S^{k̄}⟩ = d i0`.
  have hpacket_pair :
      ⟪(ψ i0).ρ.character, ((IsScalarTower.toAlgHom ℤ k k̄).compLeft G) S.character⟫
        = (d i0 : k̄) := by
    rw [Representation.groupFunctionPairing_comm]
    exact packet_constituent_pairing_eq_multiplicity
      (K := k) (G := G) S ψ d hψ_fd hψ_pairwise hψ_irr hpacket i0
  -- Hence `a · n = d i0` over `k̄`, so over `ℤ`.
  have han_C : ((a : ℤ) : k̄) * (n : k̄) = (d i0 : k̄) := by
    rw [← hxk_pair_C, hpacket_pair]
  have han_Z : a * (n : ℤ) = (d i0 : ℤ) := by
    have : ((a * (n : ℤ) : ℤ) : k̄) = ((d i0 : ℤ) : k̄) := by push_cast; push_cast at han_C; linear_combination han_C
    exact_mod_cast this
  -- Arithmetic: `n = Σⱼ dⱼ² ≥ (d i0)²`, `d i0 ≥ 1`, `a·n = d i0` ⟹ `n = 1`.
  have hn_sum_Z : (n : ℤ) = ∑ i, (d i : ℤ) * (d i : ℤ) := by
    have : ((n : ℤ) : k̄) = ((∑ i, (d i : ℤ) * (d i : ℤ) : ℤ) : k̄) := by
      push_cast
      rw [hn_sum]
    exact_mod_cast this
  have hdi0_pos : 0 < d i0 := hd_pos i0
  have hn_ge_sq : (d i0 : ℤ) * (d i0 : ℤ) ≤ (n : ℤ) := by
    rw [hn_sum_Z]
    exact Finset.single_le_sum (f := fun i => (d i : ℤ) * (d i : ℤ))
      (fun i _ => by positivity) (Finset.mem_univ i0)
  -- From `a · n = d i0 ≥ 1` and `n ≥ 1`: `a ≥ 1`, so `n ≤ a·n = d i0 ≤ d i0²·... `.
  have hn_posZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn_pos
  have hdi0_posZ : (0 : ℤ) < (d i0 : ℤ) := by exact_mod_cast hdi0_pos
  have ha_pos : 0 < a := by
    by_contra hle
    push_neg at hle
    have : a * (n : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hn_posZ)
    rw [han_Z] at this
    omega
  -- `n ≤ a·n = d i0` (since `a ≥ 1`).
  have hn_le_di0 : (n : ℤ) ≤ (d i0 : ℤ) := by
    calc (n : ℤ) = 1 * (n : ℤ) := (one_mul _).symm
      _ ≤ a * (n : ℤ) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hn_posZ)
          omega
      _ = (d i0 : ℤ) := han_Z
  -- `d i0² ≤ n ≤ d i0` ⟹ `d i0 ≤ 1` ⟹ `d i0 = 1`, and then `n ≤ 1`, so `n = 1`.
  have hdi0_one : (d i0 : ℤ) = 1 := by nlinarith [hn_ge_sq, hn_le_di0, hdi0_posZ]
  have hn_one : (n : ℤ) = 1 := by
    have := hn_le_di0
    rw [hdi0_one] at this
    omega
  have : n = 1 := by exact_mod_cast hn_one
  rw [hn_def] at this ⊢
  exact this

end CharZeroAbsoluteSimplicity

end Representation
