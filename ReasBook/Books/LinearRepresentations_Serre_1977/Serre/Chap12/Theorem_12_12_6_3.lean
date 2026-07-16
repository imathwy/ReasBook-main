import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_6_2

open scoped NumberField Representation

noncomputable section

universe u v

namespace Representation

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeTheorem121263Group : Fintype G := Fintype.ofFinite G

section

variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)

local notation "ΓK" => Γ[K](G)

/-- Helper for Theorem 12-12.6-3: the mixed-universe version of Serre's fixed-`p` subgroup
`V_{K,p} ≤ R_K(G)`, defined directly inside this file to avoid the same-universe restriction in
the public notation. -/
private abbrev gammaPElementaryInducedCharacterSpan_local (p : ℕ) : Submodule ℤ R[K](G) :=
  let _ : DecidablePred (fun H : Subgroup G ↦ Subgroup.IsGammaPElementary ΓK p H) :=
    Classical.decPred _
  inducedCharacterSubmoduleOverField K
    (Finset.univ.filter fun H : Subgroup G ↦ Subgroup.IsGammaPElementary ΓK p H)

/-- Helper for Theorem 12-12.6-3: the only remaining missing step is the membership of the
constant virtual character `l • 1` in Serre's fixed-`p` subgroup `V_{K,p}`. -/
private theorem primeToPart_constantCharacter_mem_gammaPImage
    (p n l : ℕ) [Fact p.Prime]
    (hcard : Nat.card G = p ^ n * l) (hl : Nat.Coprime p l) :
    l • (1 : R[K](G)) ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p := by
  let _ := hl
  let pPrime : Nat.Primes := ⟨p, Fact.out⟩
  let Vkp := gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p
  let χ : R[K](G) := l • (1 : R[K](G))
  have hNann_raw :=
    Representation.exists_coprime_scalar_smul_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) pPrime
  have hNann :
      ∃ N : ℕ, Nat.Coprime p N ∧
        ∀ ψ : R[K](G), N • ψ ∈ Vkp := by
    -- Route correction: reuse the public prime-to-`p` annihilator and transport it to the
    -- theorem-local owner by definitional equality, avoiding broad owner unfolding.
    change ∃ N : ℕ, Nat.Coprime p N ∧
      ∀ ψ : R[K](G),
        N • ψ ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p
    exact hNann_raw
  obtain ⟨N, hNcoprime, hNann⟩ := hNann
  have hNχ : N • χ ∈ Vkp := hNann χ
  have hgroupOrder_raw :=
    Representation.groupOrder_smul_one_mem_gammaPElementaryInducedCharacterSpan
      (G := G) (L := L) (K := K) pPrime
  have hgroupOrder :
      Nat.card G • (1 : R[K](G)) ∈ Vkp := by
    -- Transport the public `|G| • 1` membership to the theorem-local owner without invoking a
    -- large `simp` normalization.
    change Nat.card G • (1 : R[K](G)) ∈
      gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p
    exact hgroupOrder_raw
  have hpowχ : p ^ n • χ ∈ Vkp := by
    -- Rewrite Serre's factorization `|G| = p^n l` so the group-order multiple becomes the
    -- `p^n`-multiple of the target constant character.
    have hpow_eq : p ^ n • χ = Nat.card G • (1 : R[K](G)) := by
      calc
        p ^ n • χ = p ^ n • (l • (1 : R[K](G))) := by rfl
        _ = (p ^ n * l) • (1 : R[K](G)) := by rw [smul_smul]
        _ = Nat.card G • (1 : R[K](G)) := by rw [hcard]
    rw [hpow_eq]
    exact hgroupOrder
  have hpow_coprime : Nat.Coprime N (p ^ n) := by
    exact hNcoprime.symm.pow_right n
  have hbezout :
      ((1 : ℕ) : ℤ) = (N : ℤ) * Nat.gcdA N (p ^ n) + ((p ^ n : ℕ) : ℤ) * Nat.gcdB N (p ^ n) := by
    simpa [Nat.coprime_iff_gcd_eq_one.mp hpow_coprime] using (Nat.gcd_eq_gcd_ab N (p ^ n))
  have hχ_eq :
      χ =
        Nat.gcdA N (p ^ n) • (N • χ) +
          Nat.gcdB N (p ^ n) • ((p ^ n) • χ) := by
    -- Use Bézout on the coprime scalars `N` and `p^n` to recover the exact prime-to-`p` factor
    -- `l` from the two already-known multiples lying in `V_{K,p}`.
    have hbezout_smul :
        (1 : ℤ) • χ =
          ((N : ℤ) * Nat.gcdA N (p ^ n) +
              ((p ^ n : ℕ) : ℤ) * Nat.gcdB N (p ^ n)) • χ := by
      exact congrArg (fun z : ℤ ↦ z • χ) hbezout
    calc
      χ = (1 : ℤ) • χ := by simp
      _ =
          ((N : ℤ) * Nat.gcdA N (p ^ n) +
              ((p ^ n : ℕ) : ℤ) * Nat.gcdB N (p ^ n)) • χ := hbezout_smul
      _ =
          Nat.gcdA N (p ^ n) • (N • χ) +
            Nat.gcdB N (p ^ n) • ((p ^ n) • χ) := by
            simp [zsmul_eq_mul, add_mul, mul_assoc, mul_comm]
  change χ ∈ Vkp
  rw [hχ_eq]
  exact Submodule.add_mem Vkp
    (Submodule.smul_mem Vkp _ hNχ)
    (Submodule.smul_mem Vkp _ hpowχ)

-- Proof sketch: this is the fixed-`p` refinement of Brauer induction over `K`: by combining the
-- prime-to-`p` annihilation argument for the trivial character with the `Γ_K`-`p`-elementary
-- induction span, one gets the constant function `l` in `V_{K,p}`; the same annihilation of
-- the quotient `R_K(G) / V_{K,p}` yields finite index and index prime to `p`.
/-- Theorem 12-12.6-3: if `|G| = p^n l` with `(p, l) = 1`, then the constant virtual
`K`-character with value `l` belongs to the subgroup `V_{K,p}` generated by induction from the
`Γ_K`-`p`-elementary subgroups of `G`; in particular, `V_{K,p}` has finite index in `R_K(G)` and
that index is prime to `p`. -/
theorem primeToPart_card_constantCharacter_mem_gammaPElementarySubgroupInductionImage_and_primeTo
    (p n l : ℕ) [Fact p.Prime]
    (hcard : Nat.card G = p ^ n * l) (hl : Nat.Coprime p l) :
    let Vkp := gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p
    l • (1 : R[K](G)) ∈ Vkp ∧
      Vkp.toAddSubgroup.FiniteIndex ∧ Nat.Coprime p Vkp.toAddSubgroup.index :=
  by
    have hmem :
        l • (1 : R[K](G)) ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p :=
      primeToPart_constantCharacter_mem_gammaPImage (G := G) (K := K) p n l hcard hl
    have hindex :
        (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p).toAddSubgroup.FiniteIndex ∧
          Nat.Coprime p
            (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p).toAddSubgroup.index := by
      let pPrime : Nat.Primes := ⟨p, Fact.out⟩
      -- Reuse the public fixed-`p` index theorem from `12-12.6-2`.
      simpa [gammaPElementaryInducedCharacterSpan_local, Representation.gammaPElementaryInducedCharacterSpan,
        pPrime] using
        Representation.gammaPElementaryInducedCharacterSpan_finiteIndex_and_index_coprime
          (G := G) (L := L) (K := K) pPrime
    -- Assemble the stabilized membership frontier with the now-closed index conclusion.
    change
      l • (1 : R[K](G)) ∈ gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p ∧
        (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p).toAddSubgroup.FiniteIndex ∧
          Nat.Coprime p
            (gammaPElementaryInducedCharacterSpan_local (K := K) (G := G) p).toAddSubgroup.index
    exact ⟨hmem, hindex⟩

end

end Representation
