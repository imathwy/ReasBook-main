import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4

-- Declarations for this item will be appended below by the statement pipeline.

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
