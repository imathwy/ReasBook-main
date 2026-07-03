import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_17.RepresentativeSpan

noncomputable section

namespace Representation

open scoped Pointwise Representation

section Exercise138RepresentativeIndependence

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Exercise 13-13.1-17: a subgroup permutation character is nonzero at `x` exactly
when some conjugate of `x` lies in the subgroup. -/
theorem subgroupPermutationCharacter_apply_ne_zero_iff_exists_conj_mem
    {K : Subgroup G} {x : G} :
    (ℓ_{K}^G : G → ℚ) x ≠ 0 ↔ ∃ s : G, s⁻¹ * x * s ∈ K := by
  classical
  let _ : DecidablePred fun s : G ↦ s⁻¹ * x * s ∈ K := Classical.decPred _
  let S : Finset G := Finset.univ.filter fun s : G ↦ s⁻¹ * x * s ∈ K
  have happly :
      (ℓ_{K}^G : G → ℚ) x =
        (Nat.card K : ℚ)⁻¹ * ∑ s : G, if s⁻¹ * x * s ∈ K then (1 : ℚ) else 0 := by
    rw [Subgroup.characterRingOverFieldInduction_apply, Subgroup.inducedClassFunction]
    simp
  have hsum :
      ∑ s : G, (if s⁻¹ * x * s ∈ K then (1 : ℚ) else 0) = (S.card : ℚ) := by
    simp [S]
  rw [happly]
  constructor
  · intro hne
    have hcard_ne : (S.card : ℚ) ≠ 0 := by
      intro hzero
      apply hne
      rw [hsum, hzero]
      simp
    have hcard_nat : S.card ≠ 0 := Nat.cast_ne_zero.mp hcard_ne
    rcases Finset.card_ne_zero.mp hcard_nat with ⟨s, hs⟩
    exact ⟨s, (Finset.mem_filter.mp hs).2⟩
  · rintro ⟨s, hs⟩ hzero
    have hSin : s ∈ S := by
      simp [S, hs]
    have hcard_nat : S.card ≠ 0 := Finset.card_ne_zero.mpr ⟨s, hSin⟩
    have hcard_ne : (S.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcard_nat
    have hinv : ((Nat.card K : ℚ)⁻¹) ≠ 0 := by
      exact inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    apply hcard_ne
    exact (mul_eq_zero.mp (by rw [hsum] at hzero; exact hzero)).resolve_left hinv

/-- Helper for Exercise 13-13.1-17: inclusion in a conjugate together with the opposite
cardinality inequality forces subgroup conjugacy. -/
theorem isConj_of_le_smul_of_natCard_le
    {H K : Subgroup G} (g : ConjAct G)
    (hHK : H ≤ (g • K : Subgroup G))
    (hcard : Nat.card K ≤ Nat.card H) :
    H.IsConj K := by
  have hcard_smul : Nat.card (g • K : Subgroup G) = Nat.card K := by
    rw [Subgroup.pointwise_smul_def]
    exact Nat.card_congr
      (((MulAut.conj (ConjAct.ofConjAct g)).subgroupMap K).symm.toEquiv)
  have hle_card : Nat.card H ≤ Nat.card (g • K : Subgroup G) := by
    exact Nat.card_le_card_of_injective
      (fun h : H ↦ ⟨h.1, hHK h.2⟩)
      (fun a b hab ↦ by simpa using congrArg Subtype.val hab)
  have hcard_eq : Nat.card H = Nat.card (g • K : Subgroup G) := by
    apply le_antisymm hle_card
    rw [hcard_smul]
    exact hcard
  have htop_card :
      Nat.card (H.subgroupOf (g • K : Subgroup G)) =
        Nat.card (g • K : Subgroup G) := by
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hHK).toEquiv), hcard_eq]
  have htop : H.subgroupOf (g • K : Subgroup G) = ⊤ := by
    exact
      (Subgroup.card_eq_iff_eq_top (H.subgroupOf (g • K : Subgroup G))).mp
        htop_card
  have hEq : H = (g • K : Subgroup G) := by
    exact le_antisymm hHK (Subgroup.subgroupOf_eq_top.mp htop)
  rw [hEq]
  rw [Subgroup.isConj_iff_orbitRel, MulAction.orbitRel_apply]
  exact ⟨g, rfl⟩

/-- Helper for Exercise 13-13.1-17: the representative-family permutation characters are linearly
independent. -/
theorem linearIndependent_representative_cyclic_permutation_characters
    (d : ℕ) (C : Fin d → Subgroup G)
    (hC_cyclic : ∀ i, IsCyclic (C i))
    (hC_pairwise :
      Pairwise fun i j : Fin d ↦
        ¬ (C i).IsConj (C j)) :
    LinearIndependent ℚ
      (representativeCyclicPermutationCharacter (G := G) C) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_cases hzero : l = 0
  · exact hzero
  · exfalso
    have hsupp : l.support.Nonempty :=
      Finsupp.support_nonempty_iff.2 hzero
    obtain ⟨imax, himax, hmax⟩ :=
      Finset.exists_max_image l.support (fun i : Fin d ↦ Nat.card (C i)) hsupp
    rcases (Subgroup.isCyclic_iff_exists_zpowers_eq_top (C imax)).1 (hC_cyclic imax) with
      ⟨x, hx⟩
    have hsum_zero :
        l.sum
            (fun i a ↦ a *
              ((representativeCyclicPermutationCharacter (G := G) C i : G → ℚ) x)) =
          0 := by
      have hsum :
          l.sum (fun i a ↦ a • representativeCyclicPermutationCharacter (G := G) C i) = 0 := by
        simpa [Finsupp.linearCombination_apply] using hl
      have hfun :=
        congrArg (fun θ : ℚ ⊗R[ℚ](G) ↦ (θ : G → ℚ) x) hsum
      rw [Finsupp.sum] at hfun
      simpa [Pi.smul_apply] using hfun
    have hoff :
        ∀ i ∈ l.support,
          i ≠ imax →
            ((representativeCyclicPermutationCharacter (G := G) C i : G → ℚ) x) = 0 := by
      intro i hi hne
      by_contra hvalue
      have hvalueK : (ℓ_{C i}^G : G → ℚ) x ≠ 0 := by
        simpa [representativeCyclicPermutationCharacter] using hvalue
      rcases
          (subgroupPermutationCharacter_apply_ne_zero_iff_exists_conj_mem
            (G := G) (K := C i) (x := x)).1 hvalueK with
        ⟨s, hs⟩
      have hx_smul : x ∈ (ConjAct.toConjAct s) • C i := by
        rw [Subgroup.pointwise_smul_def]
        refine ⟨s⁻¹ * x * s, hs, ?_⟩
        simp [ConjAct.toConjAct_smul, mul_assoc]
      have hle : C imax ≤ (ConjAct.toConjAct s) • C i := by
        rw [← hx]
        exact Subgroup.zpowers_le.2 hx_smul
      have hcard_le : Nat.card (C i) ≤ Nat.card (C imax) := by
        exact hmax i (by simpa using hi)
      have hconj : (C imax).IsConj (C i) :=
        isConj_of_le_smul_of_natCard_le (G := G) (g := ConjAct.toConjAct s) hle hcard_le
      have himax_ne_i : imax ≠ i := by
        simpa [ne_comm] using hne
      exact (hC_pairwise himax_ne_i) hconj
    have hdiag :
        ((representativeCyclicPermutationCharacter (G := G) C imax : G → ℚ) x) ≠ 0 := by
      have hx_mem : x ∈ C imax := by
        exact hx ▸ Subgroup.mem_zpowers x
      have hnonzero : (ℓ_{C imax}^G : G → ℚ) x ≠ 0 := by
        exact
          (subgroupPermutationCharacter_apply_ne_zero_iff_exists_conj_mem
            (G := G) (K := C imax) (x := x)).2
            ⟨1, by simpa using hx_mem⟩
      simpa [representativeCyclicPermutationCharacter] using hnonzero
    have hsum_single :
        l.sum
            (fun i a ↦ a *
              ((representativeCyclicPermutationCharacter (G := G) C i : G → ℚ) x)) =
          l imax *
            ((representativeCyclicPermutationCharacter (G := G) C imax : G → ℚ) x) := by
      simp only [Finsupp.sum]
      exact
        Finset.sum_eq_single_of_mem
          imax
          (by simpa using himax)
          (fun i hi hne ↦ by simp [hoff i hi hne])
    have hcoeff_zero : l imax = 0 := by
      rw [hsum_single] at hsum_zero
      exact (mul_eq_zero.mp hsum_zero).resolve_right hdiag
    exact (Finsupp.mem_support_iff.1 (by simpa using himax)) hcoeff_zero

end Exercise138RepresentativeIndependence

end Representation
