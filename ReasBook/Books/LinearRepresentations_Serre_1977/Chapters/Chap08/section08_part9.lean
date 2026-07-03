import Mathlib
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_8_8_5_5 (from Chap08) -/
open scoped BigOperators
open CategoryTheory

universe v

namespace Representation

attribute [local instance] Fintype.ofFinite

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
variable {G : Type} [Group G] [Finite G]
variable {ι : Type v}

/-- Helper for Exercise 8-8.5-5: every irreducible degree in a complete family over a group of
order `p ^ n` is itself a bounded power of `p`. -/
lemma degree_eq_prime_pow_bounded
    (π : ι → FDRep K G) (hπ_complete : IsCompleteIrreducibleFamily π)
    {n : ℕ} (hnG : Nat.card G = p ^ n) (j : ι) :
    ∃ a ≤ n, Module.finrank K (π j) = p ^ a := by
  -- Convert irreducibility of `π j` into the divisibility statement from Chapter 6.
  let _ : Simple (π j) := hπ_complete.isSimple j
  let _ : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
  exact (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp <| hnG ▸ finrank_dvd_card (π j).ρ

/-- Helper for Exercise 8-8.5-5: once two irreducible degrees are compared by size, their squared
`p`-power forms compare by divisibility. -/
lemma chosen_degree_square_dvd_degree_square_of_le
    (π : ι → FDRep K G) (hπ_complete : IsCompleteIrreducibleFamily π)
    {n : ℕ} (hnG : Nat.card G = p ^ n) {i j : ι}
    (hdj : Module.finrank K (π i) ≤ Module.finrank K (π j)) :
    Module.finrank K (π i) ^ 2 ∣ Module.finrank K (π j) ^ 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨ai, -, hai⟩ := degree_eq_prime_pow_bounded (π := π) hπ_complete hnG i
  obtain ⟨aj, -, haj⟩ := degree_eq_prime_pow_bounded (π := π) hπ_complete hnG j
  -- Compare the exponents after rewriting the degree inequality as an inequality of powers.
  have hiaj : ai ≤ aj := by
    have hpow_le : p ^ ai ≤ p ^ aj := by
      simpa [hai, haj] using hdj
    exact (pow_right_strictMono₀ hp.one_lt).le_iff_le.mp hpow_le
  have hsq : ai * 2 ≤ aj * 2 := Nat.mul_le_mul_right 2 hiaj
  -- Squaring preserves the divisibility relation between these powers of `p`.
  calc
    Module.finrank K (π i) ^ 2 = p ^ (ai * 2) := by
      simp [hai, pow_mul]
    _ ∣ p ^ (aj * 2) := pow_dvd_pow p hsq
    _ = Module.finrank K (π j) ^ 2 := by
      simp [haj, pow_mul]

/-- Helper for Exercise 8-8.5-5: the total square-degree sum splits into the contribution from
strictly smaller degrees and the complementary contribution. -/
lemma square_degree_sum_partition_by_lt [Fintype ι] (degree : ι → ℕ) (i : ι) :
    (∑ j : ι, degree j ^ 2) =
      (∑ j : ι, if degree j < degree i then degree j ^ 2 else 0) +
      (∑ j : ι, if degree i ≤ degree j then degree j ^ 2 else 0) := by
  -- Split each summand according to whether its degree is below the chosen threshold.
  calc
    (∑ j : ι, degree j ^ 2) =
        ∑ j : ι,
          ((if degree j < degree i then degree j ^ 2 else 0) +
            (if degree i ≤ degree j then degree j ^ 2 else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hj : degree j < degree i
      · simp [hj, Nat.not_le_of_lt hj]
      · simp [hj, Nat.le_of_not_lt hj]
    _ =
        (∑ j : ι, if degree j < degree i then degree j ^ 2 else 0) +
          (∑ j : ι, if degree i ≤ degree j then degree j ^ 2 else 0) := by
      rw [Finset.sum_add_distrib]

-- Source/core/bridge triage: this theorem is source-facing. Its primitive mathematical data are
-- the finite `p`-group `G`, the complete pairwise nonisomorphic irreducible family `π`, and the
-- chosen index `i`. The core owners reused by the proof are
-- `sum_sq_degree_eq_card_of_complete_irreducible_family` for the complete-family identity and
-- `finrank_dvd_card` for the divisibility of irreducible degrees. The finiteness of the index set
-- is derived from the canonical owner hypothesis `IsCompleteIrreducibleFamily π`, so the theorem
-- surface should use the owner-level `tsum` formulation rather than exposing proof-only
-- `Finite`/`Fintype` bookkeeping. The source text is the specialization `K = ℂ`, but the reused
-- owner theorems already live over an algebraically closed characteristic-zero field `K`, so the
-- public statement should stay at that canonical field-generic layer.
--
-- Sampled owner declarations in this domain:
-- * `IsCompleteIrreducibleFamily`
-- * `IsCompleteIrreducibleFamily.finite_index`
-- * `sum_sq_degree_eq_card_of_complete_irreducible_family`
-- * `finrank_dvd_card`
--
-- Proof sketch: apply the complete-family identity
-- `sum_sq_degree_eq_card_of_complete_irreducible_family` to the family `π`. For a finite
-- `p`-group, the order of `G` is a power of `p`, and every irreducible degree is also a power of
-- `p`. The square `(Module.finrank K (π i)) ^ 2` is itself one summand in the total square-degree
-- sum `Nat.card G`, so it is at most that `p`-power and therefore divides it. Any summand whose
-- degree is at least `Module.finrank K (π i)` is a square of a larger `p`-power, so it is also
-- divisible by `(Module.finrank K (π i)) ^ 2`. Cancelling those larger-degree terms modulo
-- `(Module.finrank K (π i)) ^ 2` leaves the sum over the strictly smaller degrees.
/-- Exercise 8-8.5-5: for a complete family of pairwise nonisomorphic irreducible representations
of a finite `p`-group over an algebraically closed characteristic-zero field, the sum of the
squares of the degrees of those with degree strictly smaller than `π i` is congruent to `0`
modulo `(Module.finrank K (π i)) ^ 2`. The source text is the specialization `K = ℂ`. -/
theorem sum_sq_degree_lt_modEq_zero_of_isPGroup_of_complete_irreducible_family
    (hG : IsPGroup p G) (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    (∑' j : ι,
        if Module.finrank K (π j) < Module.finrank K (π i) then
          Module.finrank K (π j) ^ 2
        else
          0) ≡ 0 [MOD Module.finrank K (π i) ^ 2] := by
  classical
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  have hp : p.Prime := Fact.out
  obtain ⟨n, hnG⟩ := hG.exists_card_eq
  let _ : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  let degree : ι → ℕ := fun j ↦ Module.finrank K (π j)
  let d : ℕ := degree i
  let small : ℕ := ∑ j : ι, if degree j < d then degree j ^ 2 else 0
  let large : ℕ := ∑ j : ι, if d ≤ degree j then degree j ^ 2 else 0
  let total : ℕ := ∑ j : ι, degree j ^ 2
  have htotal :
      total = Nat.card G := by
    -- The global invariant is the complete-family square-degree identity.
    simpa [total, degree] using
      (sum_sq_degree_eq_card_of_complete_irreducible_family π hπ_complete hπ_pairwise)
  have hdegree_pow (j : ι) : ∃ a ≤ n, degree j = p ^ a := by
    simpa [degree] using degree_eq_prime_pow_bounded (π := π) hπ_complete hnG j
  obtain ⟨ai, -, hai⟩ := hdegree_pow i
  have hterm_le_total : d ^ 2 ≤ total := by
    -- The chosen degree square is one nonnegative summand of the total sum.
    change degree i ^ 2 ≤ ∑ j : ι, degree j ^ 2
    rw [← Finset.sum_erase_add (Finset.univ : Finset ι) (fun j ↦ degree j ^ 2)
      (Finset.mem_univ i)]
    exact Nat.le_add_left _ _
  have htwoai_le_n : ai * 2 ≤ n := by
    have hpow_le_card : p ^ (ai * 2) ≤ Fintype.card G := by
      simpa [d, degree, hai, htotal, pow_mul] using hterm_le_total
    have hcard : Fintype.card G = p ^ n := by
      simpa using hnG
    have hpow_le : p ^ (ai * 2) ≤ p ^ n := by
      rwa [hcard] at hpow_le_card
    exact (pow_right_strictMono₀ hp.one_lt).le_iff_le.mp hpow_le
  have htotal_dvd : d ^ 2 ∣ total := by
    -- Rewriting both sides as powers of `p` makes the required divisibility explicit.
    calc
      d ^ 2 = p ^ (ai * 2) := by simp [d, hai, pow_mul]
      _ ∣ p ^ n := pow_dvd_pow _ htwoai_le_n
      _ = Nat.card G := hnG.symm
      _ = total := htotal.symm
  have hlarge_dvd : d ^ 2 ∣ large := by
    -- Route correction: instead of handling the complementary sum ad hoc, prove divisibility
    -- termwise and assemble it with `Finset.dvd_sum`.
    refine Finset.dvd_sum ?_
    intro j _
    by_cases hdj : d ≤ degree j
    · obtain ⟨aj, -, haj⟩ := hdegree_pow j
      have hpow_dvd : d ^ 2 ∣ degree j ^ 2 := by
        simpa [d, degree] using
          chosen_degree_square_dvd_degree_square_of_le
            (π := π) hπ_complete hnG (i := i) (j := j) hdj
      simpa [large, hdj] using hpow_dvd
    · simp [hdj]
  have hsplit : total = small + large := by
    -- Split the total square-degree sum at the chosen degree threshold.
    simpa [total, small, large, d] using square_degree_sum_partition_by_lt degree i
  have hsum_mod : small + large ≡ 0 + 0 [MOD d ^ 2] := by
    -- Both the total sum and the complementary large-degree sum vanish modulo `d ^ 2`.
    simpa [hsplit] using htotal_dvd.modEq_zero_nat
  have hsmall_mod : small ≡ 0 [MOD d ^ 2] :=
    Nat.ModEq.add_right_cancel hlarge_dvd.modEq_zero_nat hsum_mod
  -- Rewrite the finite sum back to the source-facing `tsum` statement.
  simpa [small, degree, d, tsum_fintype] using hsmall_mod

end

end Representation

/-! ### Lemma_8_8_5_1 (from Chap08) -/
universe u

section

open Subgroup

variable {G : Type u} [Group G]

/-- Helper for Lemma 8-8.5-1: a nontrivial supersolvable group has a nontrivial normal cyclic
subgroup, obtained from the first nontrivial term of a supersolvable series. -/
lemma exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable
    {Q : Type u} [Group Q] [IsSupersolvable Q] [Nontrivial Q] :
    ∃ B : Subgroup Q, B.Normal ∧ B ≠ ⊥ ∧ IsCyclic B := by
  classical
  let hsup : IsSupersolvable Q := inferInstance
  rcases hsup.supersolvable with ⟨n, f, _, hnormal, hcyclic, h0, hn⟩
  -- Pick the earliest nontrivial term in the finite series by minimizing the index.
  have hex : ∃ m, m ≤ n ∧ f m ≠ ⊥ := by
    refine ⟨n, le_rfl, ?_⟩
    simp [hn]
  let m := Nat.find hex
  have hm_le_n : m ≤ n := (Nat.find_spec hex).1
  have hm_ne_bot : f m ≠ ⊥ := (Nat.find_spec hex).2
  have hm_min : ∀ k, k < m → f k = ⊥ := by
    intro k hk
    by_contra hk_ne_bot
    have hk_witness : k ≤ n ∧ f k ≠ ⊥ :=
      ⟨Nat.le_trans (Nat.le_of_lt hk) hm_le_n, hk_ne_bot⟩
    exact Nat.find_min hex hk hk_witness
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    apply hm_ne_bot
    simp [m, hm0, h0]
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
  have hk1_le_n : k + 1 ≤ n := by
    simpa [m, hk_eq] using hm_le_n
  have hk_lt : k < n := Nat.lt_of_succ_le hk1_le_n
  have hk_bot : f k = ⊥ := hm_min k (by simp [m, hk_eq])
  -- The first nontrivial term is normal, and its quotient by the previous trivial term is cyclic.
  have hk1_normal : (f (k + 1)).Normal := by
    by_cases hk1_lt_n : k + 1 < n
    · exact hnormal (k + 1) hk1_lt_n
    · have hk1_eq_n : k + 1 = n := le_antisymm hk1_le_n (Nat.le_of_not_gt hk1_lt_n)
      rw [hk1_eq_n, hn]
      infer_instance
  refine ⟨f (k + 1), hk1_normal, ?_, ?_⟩
  · simpa [m, hk_eq] using hm_ne_bot
  · letI : (f k).Normal := hnormal k hk_lt
    letI : ((f k).subgroupOf (f (k + 1))).Normal := (hnormal k hk_lt).subgroupOf (f (k + 1))
    let e : f (k + 1) ⧸ (f k).subgroupOf (f (k + 1)) ≃* f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1))) :=
        QuotientGroup.quotientMulEquivOfEq (by simp [hk_bot])
    -- Replace the trivial predecessor by `⊥`, then remove the trivial quotient.
    have hcyc_quot : IsCyclic (f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1)))) :=
      e.isCyclic.mp (hcyclic k hk_lt)
    exact (QuotientGroup.quotientBot (G := f (k + 1))).isCyclic.mp hcyc_quot

/-- Helper for Lemma 8-8.5-1: elements of the ambient center remain central after restricting to a
subgroup. -/
lemma center_subgroupOf_le_center (A : Subgroup G) : (center G).subgroupOf A ≤ center A := by
  intro x hx
  change x.1 ∈ center G at hx
  -- Ambient centrality immediately implies centrality against every element of the subgroup.
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  exact Subtype.ext (hx y.1)

/-- Helper for Lemma 8-8.5-1: the pullback of a cyclic subgroup of `G ⧸ center G` is
commutative. -/
lemma isMulCommutative_comap_center_of_isCyclic (B : Subgroup (G ⧸ center G))
    (hB : IsCyclic B) :
    IsMulCommutative (B.comap (QuotientGroup.mk' (center G))) := by
  let q : G →* G ⧸ center G := QuotientGroup.mk' (center G)
  let A : Subgroup G := B.comap q
  have hmap : A.map q = B :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center G)) B
  have hcyc : IsCyclic (A.map q) := by
    rw [hmap]
    exact hB
  let φ : A →* A.map q := q.subgroupMap A
  have hker : φ.ker ≤ center A := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact center_subgroupOf_le_center A
  letI : IsCyclic (A.map q) := hcyc
  -- The restricted quotient map has cyclic image and central kernel, so the pullback is abelian.
  rw [show B.comap (QuotientGroup.mk' (center G)) = A by rfl, isMulCommutative_iff]
  intro a b
  exact commutative_of_cyclic_center_quotient φ hker a b

/-- Helper for Lemma 8-8.5-1: the pullback of a nontrivial subgroup of `G ⧸ center G` is not
contained in `center G`. -/
lemma comap_center_not_le_center_of_nontrivial (B : Subgroup (G ⧸ center G)) (hB : B ≠ ⊥) :
    ¬ B.comap (QuotientGroup.mk' (center G)) ≤ center G := by
  let q : G →* G ⧸ center G := QuotientGroup.mk' (center G)
  intro hle
  have hmap : (B.comap q).map q = B :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center G)) B
  have hbot : (B.comap q).map q ≤ ⊥ := by
    calc
      (B.comap q).map q ≤ (center G).map q := Subgroup.map_mono hle
      _ = ⊥ := QuotientGroup.map_mk'_self (center G)
  -- Mapping the pullback into the quotient would force `B` to be trivial, contradicting `hB`.
  apply hB
  rw [← hmap]
  exact le_antisymm hbot bot_le

variable [IsSupersolvable G]

-- Source/core/bridge triage:
-- * `source-facing`: the lemma asserts existence of a normal commutative subgroup not contained in
--   the center.
-- * `core/canonical`: the ambient owner notions are `IsSupersolvable G`,
--   `IsSupersolvableSeries`, and `center G`.
-- * `bridge/view`: the quotient closure result
--   `supersolvable_quotient_of_supersolvable` for `G ⧸ center G` from Exercise `8-8.3-9` is
--   proof-only support, not a second owner in this file.
--
-- Proof sketch: let `C = Subgroup.center G` and pass to the supersolvable quotient `G ⧸ C`.
-- Choose the first nontrivial term in a cyclic normal series of that quotient; its inverse image in
-- `G` is normal and abelian, and if it were contained in the center then the quotient term would be
-- trivial, contradicting the choice. The nonabelian hypothesis and `center_eq_top_iff` rule out
-- the degenerate case `center G = ⊤`.
/-- Lemma 8-8.5-1: a nonabelian supersolvable group has a normal commutative subgroup that is not
contained in the center. -/
theorem exists_normal_commutative_subgroup_not_le_center_of_nonabelian_supersolvable
    (hnonabelian : ¬ IsMulCommutative G) :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧ ¬ A ≤ center G := by
  have hcenter_ne_top : center G ≠ ⊤ := by
    intro hcenter_top
    apply hnonabelian
    exact Subgroup.center_eq_top_iff.mp hcenter_top
  letI : Nontrivial (G ⧸ center G) := QuotientGroup.nontrivial_iff.mpr hcenter_ne_top
  letI : IsSupersolvable (G ⧸ center G) := supersolvable_quotient_of_supersolvable (center G)
  -- Follow the source proof: choose a first nontrivial cyclic quotient term in `G ⧸ center G`.
  obtain ⟨B, hBnormal, hBne, hBcyc⟩ :=
    exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable (Q := G ⧸ center G)
  refine ⟨B.comap (QuotientGroup.mk' (center G)), ?_, ?_, ?_⟩
  · exact Subgroup.Normal.comap hBnormal (QuotientGroup.mk' (center G))
  · exact isMulCommutative_comap_center_of_isCyclic B hBcyc
  · exact comap_center_not_le_center_of_nontrivial B hBne

end
