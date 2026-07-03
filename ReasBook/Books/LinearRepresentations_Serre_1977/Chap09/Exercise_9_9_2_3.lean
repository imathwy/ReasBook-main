import Mathlib
import Serre.Chap05.Exercise_5_5_7_1
import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap07.Exercise_7_7_2_5
import Serre.Chap07.Exercise_7_7_2_4
import Serre.Chap09.Corollary_9_9_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open Representation
open scoped BigOperators Pointwise Representation SubgroupInduction

noncomputable section

local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)

local instance : Fintype A4 := Fintype.ofFinite A4

local instance (H : Subgroup A4) : Fintype H := Fintype.ofFinite H

local instance (H : Subgroup A4) : DecidablePred fun g : A4 ↦ g ∈ H := Classical.decPred _

local instance (H : Subgroup A4) : Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')

local instance (H : Subgroup A4) : NeZero (Nat.card H : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

local instance : Invertible (Nat.card A4 : ℂ) :=
  invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')

local instance : Invertible (Nat.card V4 : ℂ) :=
  invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')

/-- Helper for Exercise 9-9.2-3: the nonlinear character `ψ` is realized by inducing Serre's
Klein-four character `θ` to `A₄`. -/
private abbrev a4_psi : R(A4) :=
  (V4).characterRingInduction (MonoidHom.toCharacterRing a4_theta)

local notation "ψ" => a4_psi

/-- Helper for Exercise 9-9.2-3: every cyclic subgroup of `A₄` has even index. -/
private lemma a4_cyclic_subgroup_index_even
    (H : Subgroup.cyclicSubgroups A4) :
    Even H.1.index := by
  have hHcyc : IsCyclic H.1 := Subgroup.mem_cyclicSubgroups.1 H.2
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hcard_dvd : Nat.card H.1 ∣ 12 := by
    simpa [hA4] using Subgroup.card_subgroup_dvd_card H.1
  have hcard_le : Nat.card H.1 ≤ 12 := Nat.le_of_dvd (by decide) hcard_dvd
  have hnot4 : Nat.card H.1 ≠ 4 := by
    intro h4
    have hindex3 : H.1.index = 3 := by
      have hmul : H.1.index * Nat.card H.1 = Nat.card A4 := H.1.index_mul_card
      rw [h4, hA4] at hmul
      omega
    have hpH : IsPGroup 2 H.1 := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [h4]
      norm_num
    let P : Sylow 2 A4 := hpH.toSylow (by
      simpa [hindex3] using (show ¬ 2 ∣ 3 by decide))
    have hHV4 : H.1 = V4 := by
      calc
        H.1 = (P : Subgroup A4) := by
          symm
          simpa [P] using
            (show ((hpH.toSylow (by
                simpa [hindex3] using (show ¬ 2 ∣ 3 by decide)) : Sylow 2 A4) : Subgroup A4) =
                H.1 from
              IsPGroup.toSylow_coe hpH (by
                simpa [hindex3] using (show ¬ 2 ∣ 3 by decide)))
        _ = V4 := by
          simpa using
            alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (α := Fin 4) (by simp) P
    letI : IsKleinFour V4 := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
    -- A subgroup of order `4` would have to be the Klein four subgroup, which is not cyclic.
    have hcycV4 : IsCyclic V4 := hHV4 ▸ hHcyc
    exact IsKleinFour.not_isCyclic hcycV4
  have hnot12 : Nat.card H.1 ≠ 12 := by
    intro h12
    have hindex : H.1.index = 1 := by
      have hmul : H.1.index * Nat.card H.1 = Nat.card A4 := H.1.index_mul_card
      rw [h12, hA4] at hmul
      omega
    have htop : H.1 = ⊤ := (Subgroup.index_eq_one).1 hindex
    have hA4_not_cyclic : ¬ IsCyclic A4 := by
      intro hcyc
      letI : IsMulCommutative A4 := hcyc.isMulCommutative
      let a : A4 :=
        ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup]
          decide⟩
      let b : A4 :=
        ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup]
          decide⟩
      have hab : a * b = b * a := Std.Commutative.comm a b
      have hneq : a * b ≠ b * a := by
        decide
      exact hneq hab
    -- A cyclic subgroup of order `12` would coincide with `A₄`, but `A₄` is not cyclic.
    have hcyc_top : IsCyclic (⊤ : Subgroup A4) := htop ▸ hHcyc
    exact hA4_not_cyclic (Subgroup.topEquiv.isCyclic.mp hcyc_top)
  have hcases :
      Nat.card H.1 = 1 ∨ Nat.card H.1 = 2 ∨ Nat.card H.1 = 3 ∨
        Nat.card H.1 = 4 ∨ Nat.card H.1 = 6 ∨ Nat.card H.1 = 12 := by
    interval_cases hcard : Nat.card H.1 <;> simp_all
  have hmul : H.1.index * Nat.card H.1 = 12 := by
    simpa [hA4] using H.1.index_mul_card
  rcases hcases with h1 | h2 | h3 | h4 | h6 | h12
  · rw [h1] at hmul
    refine ⟨6, ?_⟩
    omega
  · rw [h2] at hmul
    refine ⟨3, ?_⟩
    omega
  · rw [h3] at hmul
    refine ⟨2, ?_⟩
    omega
  · exact False.elim (hnot4 h4)
  · rw [h6] at hmul
    refine ⟨1, ?_⟩
    omega
  · exact False.elim (hnot12 h12)

/-- Helper for Exercise 9-9.2-3: every cyclic induction into `R(A₄)` has even value at `1`. -/
private lemma a4_induced_character_value_at_one_even
    (H : Subgroup.cyclicSubgroups A4) (χ : R(H.1)) :
    ∃ n : ℤ, (((H.1.characterRingInduction χ : R(A4)) : A4 → ℂ) 1) = (2 * n : ℂ) := by
  rcases Representation.virtual_character_eq_character_difference H.1 χ with
    ⟨Vpos, Vneg, hχ⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (χ : H.1 → ℂ) 1 = (m : ℂ) := by
    -- Evaluate the virtual-character splitting at `1` to package the subgroup degree as an integer.
    refine ⟨Module.finrank ℂ Vpos - Module.finrank ℂ Vneg, ?_⟩
    rw [hχ]
    simp
  rcases a4_cyclic_subgroup_index_even H with ⟨k, hk⟩
  refine ⟨k * m, ?_⟩
  -- The value at `1` is the subgroup index times the subgroup degree, and the index is even.
  rw [Subgroup.characterRingInduction_apply, Subgroup.inducedClassFunction_one_eq_index_mul_value,
    hm, hk]
  have hk' : ((k + k : ℕ) : ℂ) = 2 * (k : ℂ) := by
    exact_mod_cast (two_mul k).symm
  rw [hk']
  norm_num [mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 9-9.2-3: every element of the cyclic-induced submodule of `R(A₄)` has
even value at `1`. -/
private lemma a4_even_value_at_one_of_mem_cyclicInducedCharacterSubmodule
    (φ : R(A4)) (hφ : φ ∈ cyclicInducedCharacterSubmodule A4) :
    ∃ n : ℤ, (φ : A4 → ℂ) 1 = (2 * n : ℂ) := by
  classical
  rcases
      Representation.exists_family_characterRingInduction_eq_of_mem_artinInducedCharacterSubmodule
        hφ with
    ⟨ξ, rfl⟩
  choose n hn using
    fun H : Subgroup.cyclicSubgroups A4 ↦ a4_induced_character_value_at_one_even H (ξ H)
  refine ⟨∑ H : Subgroup.cyclicSubgroups A4, n H, ?_⟩
  -- Evaluate the finite induction sum at `1` and then rewrite each summand by the evenness lemma.
  calc
    (((∑ H : Subgroup.cyclicSubgroups A4, H.1.characterRingInduction (ξ H) : R(A4)) :
        A4 → ℂ) 1) =
        ∑ H : Subgroup.cyclicSubgroups A4,
          (((H.1.characterRingInduction (ξ H) : R(A4)) : A4 → ℂ) 1) := by
            simp
    _ = ∑ H : Subgroup.cyclicSubgroups A4, (2 * n H : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro H _
          exact hn H
    _ = (2 * (∑ H : Subgroup.cyclicSubgroups A4, n H) : ℂ) := by
          simp [mul_add, add_mul, Finset.mul_sum]

/-- Helper for Exercise 9-9.2-3: an explicit `3`-cycle in `A₄` used to exhibit one order-`3`
subgroup. -/
private def a4_three_cycle_012 : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- Helper for Exercise 9-9.2-3: a second explicit `3`-cycle in `A₄` used to exhibit a distinct
order-`3` subgroup. -/
private def a4_three_cycle_013 : A4 :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- Helper for Exercise 9-9.2-3: the explicit element `a4_three_cycle_012` has order `3`. -/
private lemma a4_three_cycle_012_order :
    orderOf a4_three_cycle_012 = 3 := by
  -- The explicit permutation is a nontrivial `3`-cycle, so the prime-order criterion applies.
  exact orderOf_eq_prime
    (by decide : a4_three_cycle_012 ^ 3 = 1)
    (by decide : a4_three_cycle_012 ≠ 1)

/-- Helper for Exercise 9-9.2-3: the explicit element `a4_three_cycle_013` has order `3`. -/
private lemma a4_three_cycle_013_order :
    orderOf a4_three_cycle_013 = 3 := by
  -- The second explicit permutation is another nontrivial `3`-cycle.
  exact orderOf_eq_prime
    (by decide : a4_three_cycle_013 ^ 3 = 1)
    (by decide : a4_three_cycle_013 ≠ 1)

/-- Helper for Exercise 9-9.2-3: the two explicit order-`3` cyclic subgroups generated by the
chosen `3`-cycles are distinct. -/
private lemma a4_three_cycle_subgroups_distinct :
    Subgroup.zpowers a4_three_cycle_012 ≠ Subgroup.zpowers a4_three_cycle_013 := by
  intro h
  have hmem :
      a4_three_cycle_012 ∈ Subgroup.zpowers a4_three_cycle_013 := by
    -- Equality of the generated subgroups would place the first generator in the second subgroup.
    simpa [h] using
      (show a4_three_cycle_012 ∈ Subgroup.zpowers a4_three_cycle_012 from
        Subgroup.mem_zpowers a4_three_cycle_012)
  have hnot :
      a4_three_cycle_012 ∉ Subgroup.zpowers a4_three_cycle_013 := by
    -- In a finite cyclic subgroup of order `3`, membership is detected by the three visible powers.
    rw [mem_zpowers_iff_mem_range_orderOf, a4_three_cycle_013_order]
    decide
  exact hnot hmem

/-- Helper for Exercise 9-9.2-3: `A₄` has no normal subgroup of cardinality `3`. -/
private lemma a4_no_normal_subgroup_of_card_three
    (K : Subgroup A4) (hKNorm : K.Normal) (hK : Nat.card K = 3) :
    False := by
  letI : K.Normal := hKNorm
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hKindex : K.index = 4 := by
    -- Convert the subgroup cardinality into the index needed for the Sylow calculation.
    have hmul : K.index * Nat.card K = Nat.card A4 := K.index_mul_card
    rw [hK, hA4] at hmul
    omega
  have hKp : IsPGroup 3 K := by
    -- A subgroup of cardinality `3` is automatically a `3`-group.
    refine IsPGroup.of_card (n := 1) ?_
    rw [hK]
    norm_num
  let PK : Sylow 3 A4 :=
    hKp.toSylow (by
      simpa [hKindex] using (show ¬ 3 ∣ 4 by decide))
  have hPKcoe : (PK : Subgroup A4) = K := by
    simpa [PK] using
      (IsPGroup.toSylow_coe hKp (by
        simpa [hKindex] using (show ¬ 3 ∣ 4 by decide)))
  have hPKnorm : PK.Normal := by
    simpa [hPKcoe] using hKNorm
  letI : Unique (Sylow 3 A4) := Sylow.unique_of_normal PK hPKnorm
  have hσcard : Nat.card (Subgroup.zpowers a4_three_cycle_012) = 3 := by
    -- The first explicit `3`-cycle generates a Sylow `3`-subgroup.
    simpa [a4_three_cycle_012_order] using Nat.card_zpowers a4_three_cycle_012
  have hσp : IsPGroup 3 (Subgroup.zpowers a4_three_cycle_012) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hσcard]
    norm_num
  have hσindex : (Subgroup.zpowers a4_three_cycle_012).index = 4 := by
    have hmul :
        (Subgroup.zpowers a4_three_cycle_012).index *
            Nat.card (Subgroup.zpowers a4_three_cycle_012) =
          Nat.card A4 := (Subgroup.zpowers a4_three_cycle_012).index_mul_card
    rw [hσcard, hA4] at hmul
    omega
  let Pσ : Sylow 3 A4 :=
    hσp.toSylow (by
      simpa [hσindex] using (show ¬ 3 ∣ 4 by decide))
  have hτcard : Nat.card (Subgroup.zpowers a4_three_cycle_013) = 3 := by
    -- The second explicit `3`-cycle also generates a Sylow `3`-subgroup.
    simpa [a4_three_cycle_013_order] using Nat.card_zpowers a4_three_cycle_013
  have hτp : IsPGroup 3 (Subgroup.zpowers a4_three_cycle_013) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hτcard]
    norm_num
  have hτindex : (Subgroup.zpowers a4_three_cycle_013).index = 4 := by
    have hmul :
        (Subgroup.zpowers a4_three_cycle_013).index *
            Nat.card (Subgroup.zpowers a4_three_cycle_013) =
          Nat.card A4 := (Subgroup.zpowers a4_three_cycle_013).index_mul_card
    rw [hτcard, hA4] at hmul
    omega
  let Pτ : Sylow 3 A4 :=
    hτp.toSylow (by
      simpa [hτindex] using (show ¬ 3 ∣ 4 by decide))
  have hSyl : Pσ = Pτ := Subsingleton.elim _ _
  have hEq :
      Subgroup.zpowers a4_three_cycle_012 = Subgroup.zpowers a4_three_cycle_013 := by
    -- A normal Sylow `3`-subgroup would force all Sylow `3`-subgroups to coincide.
    calc
      Subgroup.zpowers a4_three_cycle_012 = (Pσ : Subgroup A4) := by
        symm
        simpa [Pσ] using
          (IsPGroup.toSylow_coe hσp (by
            simpa [hσindex] using (show ¬ 3 ∣ 4 by decide)))
      _ = (Pτ : Subgroup A4) := by simpa [hSyl]
      _ = Subgroup.zpowers a4_three_cycle_013 := by
        simpa [Pτ] using
          (IsPGroup.toSylow_coe hτp (by
            simpa [hτindex] using (show ¬ 3 ∣ 4 by decide)))
  exact a4_three_cycle_subgroups_distinct hEq

/-- Helper for Exercise 9-9.2-3: every cyclic subgroup of `A₄` has order `1`, `2`, or `3`. -/
private lemma a4_cyclic_subgroup_card_eq_one_or_two_or_three
    (H : Subgroup.cyclicSubgroups A4) :
    Nat.card H.1 = 1 ∨ Nat.card H.1 = 2 ∨ Nat.card H.1 = 3 := by
  have hHcyc : IsCyclic H.1 := Subgroup.mem_cyclicSubgroups.1 H.2
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hcard_dvd : Nat.card H.1 ∣ 12 := by
    simpa [hA4] using Subgroup.card_subgroup_dvd_card H.1
  have hcard_le : Nat.card H.1 ≤ 12 := Nat.le_of_dvd (by decide) hcard_dvd
  have hnot4 : Nat.card H.1 ≠ 4 := by
    intro h4
    have hindex3 : H.1.index = 3 := by
      -- Convert the order calculation into the Sylow-2 setting.
      have hmul : H.1.index * Nat.card H.1 = Nat.card A4 := H.1.index_mul_card
      rw [h4, hA4] at hmul
      omega
    have hpH : IsPGroup 2 H.1 := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [h4]
      norm_num
    let P : Sylow 2 A4 := hpH.toSylow (by
      simpa [hindex3] using (show ¬ 2 ∣ 3 by decide))
    have hHV4 : H.1 = V4 := by
      -- A subgroup of order `4` is a Sylow `2`-subgroup, and `V₄` is the unique one.
      calc
        H.1 = (P : Subgroup A4) := by
          symm
          simpa [P] using
            (show ((hpH.toSylow (by
                simpa [hindex3] using (show ¬ 2 ∣ 3 by decide)) : Sylow 2 A4) : Subgroup A4) =
                H.1 from
              IsPGroup.toSylow_coe hpH (by
                simpa [hindex3] using (show ¬ 2 ∣ 3 by decide)))
        _ = V4 := by
          simpa using
            alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (α := Fin 4) (by simp) P
    letI : IsKleinFour V4 := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
    -- Route correction: rather than analyzing generators directly, identify the order-`4` case
    -- with the unique Sylow `2`-subgroup `V₄`, which is not cyclic.
    have hcycV4 : IsCyclic V4 := hHV4 ▸ hHcyc
    exact IsKleinFour.not_isCyclic hcycV4
  have hnot6 : Nat.card H.1 ≠ 6 := by
    intro h6
    have hindex2 : H.1.index = 2 := by
      -- Order `6` forces index `2`.
      have hmul : H.1.index * Nat.card H.1 = Nat.card A4 := H.1.index_mul_card
      rw [h6, hA4] at hmul
      omega
    letI : H.1.Normal := Subgroup.normal_of_index_eq_two hindex2
    have hquot_card : Nat.card (A4 ⧸ H.1) = 2 := by
      simpa [Subgroup.index_eq_card] using hindex2
    have hcommQ : IsMulCommutative (A4 ⧸ H.1) := by
      exact (isCyclic_of_prime_card hquot_card).isMulCommutative
    have hcomm_le : commutator A4 ≤ H.1 := by
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H.1)).mp hcommQ
    have hV4_le : V4 ≤ H.1 := by
      simpa [alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp)] using hcomm_le
    letI : IsKleinFour V4 := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
    letI : IsCyclic H.1 := hHcyc
    -- An index-`2` subgroup contains the commutator subgroup `V₄`, but every subgroup of a cyclic
    -- group is cyclic, contradiction.
    have hcycV4 : IsCyclic V4 := Subgroup.isCyclic_of_le hV4_le
    exact IsKleinFour.not_isCyclic hcycV4
  have hnot12 : Nat.card H.1 ≠ 12 := by
    intro h12
    have hindex : H.1.index = 1 := by
      -- Full cardinality forces the subgroup to be all of `A₄`.
      have hmul : H.1.index * Nat.card H.1 = Nat.card A4 := H.1.index_mul_card
      rw [h12, hA4] at hmul
      omega
    have htop : H.1 = ⊤ := (Subgroup.index_eq_one).1 hindex
    have hA4_not_cyclic : ¬ IsCyclic A4 := by
      intro hcyc
      letI : IsMulCommutative A4 := hcyc.isMulCommutative
      let a : A4 :=
        ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup]
          decide⟩
      let b : A4 :=
        ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup]
          decide⟩
      have hab : a * b = b * a := Std.Commutative.comm a b
      have hneq : a * b ≠ b * a := by
        decide
      exact hneq hab
    -- The top subgroup would identify `H` with `A₄`, but `A₄` is not cyclic.
    have hcyc_top : IsCyclic (⊤ : Subgroup A4) := htop ▸ hHcyc
    exact hA4_not_cyclic (Subgroup.topEquiv.isCyclic.mp hcyc_top)
  have hcases :
      Nat.card H.1 = 1 ∨ Nat.card H.1 = 2 ∨ Nat.card H.1 = 3 ∨
        Nat.card H.1 = 4 ∨ Nat.card H.1 = 6 ∨ Nat.card H.1 = 12 := by
    interval_cases hcard : Nat.card H.1 <;> simp_all
  rcases hcases with h1 | h2 | h3 | h4 | h6 | h12
  · exact Or.inl h1
  · exact Or.inr <| Or.inl h2
  · exact Or.inr <| Or.inr h3
  · exact False.elim (hnot4 h4)
  · exact False.elim (hnot6 h6)
  · exact False.elim (hnot12 h12)

/-- Helper for Exercise 9-9.2-3: every subgroup of `A₄` of cardinality `4` is the canonical Klein
four subgroup `V₄`. -/
private lemma a4_subgroup_eq_kleinFour_of_card_four
    (K : Subgroup A4) (hK : Nat.card K = 4) :
    K = V4 := by
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hindex3 : K.index = 3 := by
    -- Convert the order calculation into the Sylow-`2` index needed for uniqueness of `V₄`.
    have hmul : K.index * Nat.card K = Nat.card A4 := K.index_mul_card
    rw [hK, hA4] at hmul
    omega
  have hpK : IsPGroup 2 K := by
    -- A subgroup of cardinality `4` is a `2`-group.
    refine IsPGroup.of_card (n := 2) ?_
    rw [hK]
    norm_num
  let P : Sylow 2 A4 := hpK.toSylow (by
    simpa [hindex3] using (show ¬ 2 ∣ 3 by decide))
  calc
    K = (P : Subgroup A4) := by
      symm
      simpa [P] using
        (show ((hpK.toSylow (by
            simpa [hindex3] using (show ¬ 2 ∣ 3 by decide)) : Sylow 2 A4) : Subgroup A4) = K
          from IsPGroup.toSylow_coe hpK (by
            simpa [hindex3] using (show ¬ 2 ∣ 3 by decide)))
    _ = V4 := by
      simpa using
        alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (α := Fin 4) (by simp) P

/-- Helper for Exercise 9-9.2-3: every element of the Klein four subgroup is one of the source
elements `1`, `x`, `y`, or `z`. -/
private lemma a4_v4_eq_one_or_source
    (h : V4) :
    h = 1 ∨ h = a4_v4_x ∨ h = a4_v4_y ∨ h = a4_v4_z := by
  by_cases h1 : h = 1
  · exact Or.inl h1
  by_cases hx : h = a4_v4_x
  · exact Or.inr <| Or.inl hx
  by_cases hy : h = a4_v4_y
  · exact Or.inr <| Or.inr <| Or.inl hy
  letI : IsKleinFour V4 :=
    alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have hz : h = a4_v4_z := by
    -- Once `1`, `x`, and `y` are excluded, the Klein-four multiplication table forces `z`.
    calc
      h = a4_v4_x * a4_v4_y := by
        exact IsKleinFour.eq_mul_of_ne_all
          (x := a4_v4_x) (y := a4_v4_y) (z := h)
          (by decide) (by decide) (by decide) h1 hx hy
      _ = a4_v4_z := by
        symm
        simpa [mul_comm] using
          (IsKleinFour.eq_mul_of_ne_all
            (x := a4_v4_x) (y := a4_v4_y) (z := a4_v4_z)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  exact Or.inr <| Or.inr <| Or.inr hz

/-- Helper for Exercise 9-9.2-3: the chosen order-`3` subgroup generated by
`a4_three_cycle_012` complements `V₄`. -/
private lemma a4_order_three_subgroup_isComplement_kleinFour :
    (Subgroup.zpowers a4_three_cycle_012).IsComplement' V4 := by
  have hcard_mul :
      Nat.card (Subgroup.zpowers a4_three_cycle_012) * Nat.card V4 = Nat.card A4 := by
    rw [show Nat.card (Subgroup.zpowers a4_three_cycle_012) = 3 by
        simpa [a4_three_cycle_012_order] using Nat.card_zpowers a4_three_cycle_012]
    rw [show Nat.card V4 = 4 by
        simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)]
    simpa using (show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp))
  have hcoprime :
      Nat.Coprime (Nat.card (Subgroup.zpowers a4_three_cycle_012)) (Nat.card V4) := by
    rw [show Nat.card (Subgroup.zpowers a4_three_cycle_012) = 3 by
        simpa [a4_three_cycle_012_order] using Nat.card_zpowers a4_three_cycle_012]
    rw [show Nat.card V4 = 4 by
        simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)]
    decide
  -- Coprime cardinalities and the product formula identify the chosen cyclic subgroup as a
  -- complement to `V₄`.
  exact Subgroup.isComplement'_of_coprime hcard_mul hcoprime

/-- Helper for Exercise 9-9.2-3: an element of the chosen order-`3` subgroup is either `1`, the
generator `a4_three_cycle_012`, or its square. -/
private lemma a4_order_three_subgroup_eq_one_or_generator_or_sq
    (s : Subgroup.zpowers a4_three_cycle_012) :
    (s : A4) = 1 ∨ (s : A4) = a4_three_cycle_012 ∨
      (s : A4) = a4_three_cycle_012 ^ 2 := by
  -- The subgroup `⟨a4_three_cycle_012⟩` has order `3`, so only the first three powers occur.
  have hs_mem : (s : A4) ∈ Subgroup.zpowers a4_three_cycle_012 := s.2
  rw [mem_zpowers_iff_mem_range_orderOf, a4_three_cycle_012_order] at hs_mem
  simp at hs_mem
  rcases hs_mem with ⟨n, hnlt, hn⟩
  interval_cases n
  · simp at hn
    exact Or.inl hn.symm
  · simp at hn
    exact Or.inr <| Or.inl hn.symm
  · simp [pow_succ] at hn
    exact Or.inr <| Or.inr hn.symm

/-- Helper for Exercise 9-9.2-3: conjugation by the chosen `3`-cycle permutes the three
nontrivial elements of `V₄` cyclically. -/
private lemma a4_three_cycle_conj_v4_cycle :
    (a4_three_cycle_012 : A4) * (a4_v4_x : A4) * a4_three_cycle_012⁻¹ = a4_v4_z ∧
      (a4_three_cycle_012 : A4) * (a4_v4_y : A4) * a4_three_cycle_012⁻¹ = a4_v4_x ∧
      (a4_three_cycle_012 : A4) * (a4_v4_z : A4) * a4_three_cycle_012⁻¹ = a4_v4_y := by
  -- These are direct computations in the explicit permutation model of `A₄`.
  decide

/-- Helper for Exercise 9-9.2-3: conjugation by the square of the chosen `3`-cycle cyclically
permutes the nontrivial Klein-four elements in the opposite direction. -/
private lemma a4_three_cycle_sq_conj_v4_cycle :
    (a4_three_cycle_012 ^ 2 : A4) * (a4_v4_x : A4) * (a4_three_cycle_012 ^ 2)⁻¹ = a4_v4_y ∧
      (a4_three_cycle_012 ^ 2 : A4) * (a4_v4_y : A4) * (a4_three_cycle_012 ^ 2)⁻¹ = a4_v4_z ∧
      (a4_three_cycle_012 ^ 2 : A4) * (a4_v4_z : A4) * (a4_three_cycle_012 ^ 2)⁻¹ = a4_v4_x := by
  -- These are the corresponding explicit conjugation formulas for the other nonidentity element.
  decide

/-- Helper for Exercise 9-9.2-3: the chosen order-`3` subgroup is a Frobenius subgroup of `A₄`,
with normal complement `V₄`. -/
private lemma a4_order_three_subgroup_isFrobenius :
    (Subgroup.zpowers a4_three_cycle_012).IsFrobeniusSubgroup := by
  have hV4_normal : Subgroup.Normal V4 := by
    -- Identify `V₄` with the commutator subgroup to inherit normality.
    simpa [alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp), commutator] using
      (Subgroup.commutator_normal
        (H₁ := (⊤ : Subgroup A4))
        (H₂ := (⊤ : Subgroup A4)))
  -- Route correction: replace the failed abstract fixed-point search with explicit conjugation on
  -- the three nontrivial elements of `V₄`, after classifying the nonidentity elements of `⟨σ⟩`.
  refine
    (Subgroup.isFrobeniusSubgroup_iff_free_on_normal_complement
      (H := Subgroup.zpowers a4_three_cycle_012)
      (A := V4) hV4_normal a4_order_three_subgroup_isComplement_kleinFour).2 ?_
  intro s hs t ht
  rcases a4_order_three_subgroup_eq_one_or_generator_or_sq s with hs1 | hsgen | hssq
  · exact (hs (Subtype.ext hs1)).elim
  · rcases a4_v4_eq_one_or_source t with ht1 | htx | hty | htz
    · exact (ht ht1).elim
    · rcases a4_three_cycle_conj_v4_cycle with ⟨hx, hy, hz⟩
      -- The generator sends `x` to `z`, so `x` is not fixed.
      rw [hsgen, htx, hx]
      decide
    · rcases a4_three_cycle_conj_v4_cycle with ⟨hx, hy, hz⟩
      -- The generator sends `y` to `x`, so `y` is not fixed.
      rw [hsgen, hty, hy]
      decide
    · rcases a4_three_cycle_conj_v4_cycle with ⟨hx, hy, hz⟩
      -- The generator sends `z` to `y`, so `z` is not fixed.
      rw [hsgen, htz, hz]
      decide
  · rcases a4_v4_eq_one_or_source t with ht1 | htx | hty | htz
    · exact (ht ht1).elim
    · rcases a4_three_cycle_sq_conj_v4_cycle with ⟨hx, hy, hz⟩
      -- The square sends `x` to `y`, so `x` is not fixed.
      rw [hssq, htx, hx]
      decide
    · rcases a4_three_cycle_sq_conj_v4_cycle with ⟨hx, hy, hz⟩
      -- The square sends `y` to `z`, so `y` is not fixed.
      rw [hssq, hty, hy]
      decide
    · rcases a4_three_cycle_sq_conj_v4_cycle with ⟨hx, hy, hz⟩
      -- The square sends `z` to `x`, so `z` is not fixed.
      rw [hssq, htz, hz]
      decide

local instance : (V4).Normal :=
  alternatingGroup.normal_kleinFour (show Nat.card (Fin 4) = 4 by simp)

/-- Helper for Exercise 9-9.2-3: the canonical Klein four subgroup of `A₄` has quotient of
order `3`. -/
private lemma a4_quotient_by_kleinFour_card :
    Nat.card (A4 ⧸ V4) = 3 := by
  -- Compare the orders of `A₄`, `V₄`, and the quotient.
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hV4 : Nat.card V4 = 4 := by
    simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  have hmul : Nat.card A4 = Nat.card (A4 ⧸ V4) * Nat.card V4 := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A4) V4)
  rw [hA4, hV4] at hmul
  omega

/-- Helper for Exercise 9-9.2-3: the abelian quotient `A₄/V₄` is a cyclic group of order `3`. -/
private lemma a4_quotient_by_kleinFour_mulEquiv_c3 :
    Nonempty ((A4 ⧸ V4) ≃* Multiplicative (ZMod 3)) := by
  -- Prime-cardinality groups are cyclic and hence canonically isomorphic up to choice.
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact ⟨mulEquivOfPrimeCardEq
    (G := A4 ⧸ V4)
    (G' := Multiplicative (ZMod 3))
    a4_quotient_by_kleinFour_card
    (by simp)⟩

/-- Helper for Exercise 9-9.2-3: the complex linear characters of `A₄/V₄`. -/
private abbrev a4_linearCharacters :=
  (A4 ⧸ V4) →* ℂˣ

/-- Helper for Exercise 9-9.2-3: via `A₄/V₄ ≃ C₃`, the quotient linear-character group identifies
with the dual of `C₃`. -/
private noncomputable def a4_linearCharacters_mulEquiv_c3Dual :
    a4_linearCharacters ≃* ((Multiplicative (ZMod 3)) →* ℂˣ) := by
  -- Precompose with a chosen quotient isomorphism.
  let eQ : (A4 ⧸ V4) ≃* Multiplicative (ZMod 3) :=
    Classical.choice a4_quotient_by_kleinFour_mulEquiv_c3
  exact eQ.monoidHomCongrLeft

/-- Helper for Exercise 9-9.2-3: the quotient `A₄/V₄` has exactly three complex linear
characters. -/
private lemma a4_linearCharacters_card :
    Nat.card a4_linearCharacters = 3 := by
  -- Finite abelian duality identifies the dual of `C₃` with another copy of `C₃`.
  have hC3 :
      Nat.card ((Multiplicative (ZMod 3)) →* ℂˣ) = 3 := by
    simpa using
      (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod 3)) (M := ℂ))
  exact
    (Nat.card_congr a4_linearCharacters_mulEquiv_c3Dual.toEquiv).trans hC3

private instance : Finite a4_linearCharacters := by
  -- Transport finiteness from the cyclic group `C₃`.
  let eDual :
      ((Multiplicative (ZMod 3)) →* ℂˣ) ≃* Multiplicative (ZMod 3) :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
        (G := Multiplicative (ZMod 3)) (M := ℂ))
  exact
    Finite.of_equiv (Multiplicative (ZMod 3))
      (a4_linearCharacters_mulEquiv_c3Dual.trans eDual).symm.toEquiv

private noncomputable instance : Fintype a4_linearCharacters :=
  Fintype.ofFinite a4_linearCharacters

/-- Helper for Exercise 9-9.2-3: each quotient linear character pulls back to a degree-`1`
character of `A₄`. -/
private abbrev a4_linearCharacterFamily (χ : a4_linearCharacters) : Rep ℂ A4 :=
  Rep.of ((χ.comp (QuotientGroup.mk' V4)).toRepresentation)

/-- Helper for Exercise 9-9.2-3: the pulled-back quotient linear representation has the expected
degree-`1` class function on `A₄`. -/
private lemma a4_linearCharacterFamily_character_eq
    (χ : a4_linearCharacters) :
    ((a4_linearCharacterFamily χ).ρ.character : A4 → ℂ) =
      (((MonoidHom.toCharacterRing (χ.comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
  -- Both sides are the same degree-`1` character, viewed once through `Rep` and once in `R(A₄)`.
  ext g
  simp [a4_linearCharacterFamily, MonoidHom.toCharacterRing_apply,
    MonoidHom.toRepresentation_character_apply]

/-- Helper for Exercise 9-9.2-3: restricting a pulled-back quotient linear character to the chosen
order-`3` subgroup agrees with the corresponding subgroup character-ring class function. -/
private lemma a4_linearCharacterFamily_restrict_order_three_character_eq
    (χ : a4_linearCharacters) :
    Representation.character
        (((a4_linearCharacterFamily χ).ρ).comp (Subgroup.zpowers a4_three_cycle_012).subtype) =
      (((MonoidHom.toCharacterRing
          ((χ.comp (QuotientGroup.mk' V4)).comp (Subgroup.zpowers a4_three_cycle_012).subtype) :
          R(Subgroup.zpowers a4_three_cycle_012)) :
        Subgroup.zpowers a4_three_cycle_012 → ℂ)) := by
  -- Restriction only changes the ambient group; the linear character formula is unchanged.
  ext s
  change
    (((((
        (χ.comp (QuotientGroup.mk' V4)).comp (Subgroup.zpowers a4_three_cycle_012).subtype) :
          (Subgroup.zpowers a4_three_cycle_012) →* ℂˣ).toRepresentation).character) s) =
      (((MonoidHom.toCharacterRing
          ((χ.comp (QuotientGroup.mk' V4)).comp (Subgroup.zpowers a4_three_cycle_012).subtype) :
          R(Subgroup.zpowers a4_three_cycle_012)) :
        Subgroup.zpowers a4_three_cycle_012 → ℂ) s)
  rw [MonoidHom.toRepresentation_character_apply]
  simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Exercise 9-9.2-3: distinct quotient linear characters remain nonisomorphic after
pullback to `A₄`. -/
private lemma a4_linearCharacterFamily_pairwise :
    CategoryTheory.PairwiseNonisomorphic a4_linearCharacterFamily := by
  intro χ χ' hχψ hiso
  rcases hiso with ⟨e⟩
  -- Equality of pulled-back characters descends through the surjective quotient map.
  have hchar :
      ((χ.comp (QuotientGroup.mk' V4)).toRepresentation).character =
        ((χ'.comp (QuotientGroup.mk' V4)).toRepresentation).character :=
    Representation.char_iso (Representation.equivOfIso e)
  have hχeqψ : χ = χ' := by
    ext q
    rcases QuotientGroup.mk'_surjective V4 q with ⟨g, hg⟩
    have hval : (χ (QuotientGroup.mk' V4 g) : ℂ) = (χ' (QuotientGroup.mk' V4 g) : ℂ) := by
      simpa [MonoidHom.toRepresentation_character_apply] using congrFun hchar g
    simpa [hg] using hval
  exact hχψ hχeqψ

/-- Helper for Exercise 9-9.2-3: the three quotient linear characters already form the complete
irreducible family for `A₄/V₄`. -/
private lemma a4_quotient_linearCharacterFamily_complete :
    IsCompleteIrreducibleFamily
      (fun χ : a4_linearCharacters ↦
        FDRep.of χ.toRepresentation) := by
  letI : NeZero (Nat.card (A4 ⧸ V4) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hsimple :
      ∀ χ : a4_linearCharacters, CategoryTheory.Simple (FDRep.of χ.toRepresentation) := by
    intro χ
    have hχirr : Representation.IsIrreducible (FDRep.of χ.toRepresentation).ρ := by
      simpa using (MonoidHom.toRepresentation_isIrreducible χ)
    letI : Representation.IsIrreducible (FDRep.of χ.toRepresentation).ρ := hχirr
    exact FDRep.simple_of_isIrreducible (FDRep.of χ.toRepresentation)
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic
        (fun χ : a4_linearCharacters ↦ FDRep.of χ.toRepresentation) := by
    intro χ χ' hχψ hiso
    rcases hiso with ⟨e⟩
    have hchar : χ.toRepresentation.character = χ'.toRepresentation.character :=
      FDRep.char_iso e
    have hχeqψ : χ = χ' := by
      ext q
      simpa [MonoidHom.toRepresentation_character_apply] using congrFun hchar q
    exact hχψ hχeqψ
  refine
    Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      (π := fun χ : a4_linearCharacters ↦ FDRep.of χ.toRepresentation)
      hsimple hpairwise ?_
  -- Every quotient linear character has degree `1`, so the square-degree sum is just `3`.
  have hsum :
      ∑ χ : a4_linearCharacters, Module.finrank ℂ (FDRep.of χ.toRepresentation) ^ 2 =
        Fintype.card a4_linearCharacters := by
    simp
  rw [hsum, ← Nat.card_eq_fintype_card, a4_linearCharacters_card, a4_quotient_by_kleinFour_card]

/-- Helper for Exercise 9-9.2-3: Serre's nonlinear augmentation constituent of `A₄`. -/
private abbrev a4_augmentationRepresentation :
    Representation ℂ A4 (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) :=
  ind (Subgroup.subtype V4) a4_theta.toRepresentation

/-- Helper for Exercise 9-9.2-3: Serre's nonlinear constituent is irreducible. -/
private lemma a4_augmentation_representation_isIrreducible :
    a4_augmentationRepresentation.IsIrreducible := by
  -- Reuse the Chapter 5 proof of irreducibility for `Ind_{V₄}^{A₄}(θ)`.
  simpa [a4_augmentationRepresentation] using a4_induced_theta_isIrreducible

private instance a4_augmentationRepresentation_moduleFinite :
    Module.Finite ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) := by
  letI : a4_augmentationRepresentation.IsIrreducible :=
    a4_augmentation_representation_isIrreducible
  letI : FiniteDimensional ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) :=
    IsIrreducible.finiteDimensional_of_finite a4_augmentationRepresentation
  infer_instance

/-- Helper for Exercise 9-9.2-3: Serre's nonlinear constituent has degree `3`. -/
private lemma a4_augmentationRepresentation_finrank_three :
    Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) = 3 := by
  -- Evaluate the known character identity at the identity element.
  have hchar' := congrFun a4_induced_theta_character_eq_psi 1
  change (a4_augmentationRepresentation.character 1 : ℂ) =
      (ofMulAction ℂ A4 (Fin 4)).character 1 - 1 at hchar'
  have hfinrank_complex :
      (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) = 3 := by
    calc
      (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) =
          a4_augmentationRepresentation.character 1 := by
            symm
            exact Representation.char_one a4_augmentationRepresentation
      _ = (ofMulAction ℂ A4 (Fin 4)).character 1 - 1 := hchar'
      _ = 3 := by
            norm_num [Representation.char_one]
  exact_mod_cast hfinrank_complex

/-- Helper for Exercise 9-9.2-3: no pulled-back quotient linear character is isomorphic to
Serre's nonlinear augmentation constituent. -/
private lemma a4_linearCharacterFamily_not_isomorphic_augmentation
    (χ : a4_linearCharacters) :
    ¬ Nonempty
      (a4_linearCharacterFamily χ ≅
        Rep.of a4_augmentationRepresentation) := by
  intro hiso
  rcases hiso with ⟨e⟩
  -- Compare degrees at the identity: the linear slot has degree `1`, the augmentation slot `3`.
  have hchar :
      (a4_linearCharacterFamily χ).ρ.character = a4_augmentationRepresentation.character :=
    Representation.char_iso (Representation.equivOfIso e)
  have hdeg :
      ((a4_linearCharacterFamily χ).ρ.character) 1 =
        a4_augmentationRepresentation.character 1 := by
    exact congrFun hchar 1
  have hdeg' : (1 : ℂ) = 3 := by
    have hdeg'' := hdeg
    simp [a4_linearCharacterFamily, a4_augmentationRepresentation_finrank_three,
      Representation.char_one] at hdeg''
  norm_num at hdeg'

/-- Helper for Exercise 9-9.2-3: after choosing an ordering of the three quotient linear
characters, the four complex irreducible constituents of `A₄` are indexed by `Fin 4`. -/
private noncomputable def a4_explicitComplexFamily
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    Fin 4 → Rep ℂ A4
  | ⟨0, _⟩ => a4_linearCharacterFamily (eLin 0)
  | ⟨1, _⟩ => a4_linearCharacterFamily (eLin 1)
  | ⟨2, _⟩ => a4_linearCharacterFamily (eLin 2)
  | ⟨3, _⟩ => Rep.of a4_augmentationRepresentation

private instance a4_explicitComplexFamily_moduleFinite
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    Module.Finite ℂ (a4_explicitComplexFamily eLin i) := by
  fin_cases i <;> dsimp [a4_explicitComplexFamily]
  · exact Module.Finite.self ℂ
  · exact Module.Finite.self ℂ
  · exact Module.Finite.self ℂ
  · exact a4_augmentationRepresentation_moduleFinite

/-- Helper for Exercise 9-9.2-3: the explicit `Fin 4`-indexed family, viewed in `FDRep`. -/
private abbrev a4_explicitFDRepFamily
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    Fin 4 → FDRep ℂ A4 :=
  fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)

/-- Helper for Exercise 9-9.2-3: the explicit `Fin 4`-indexed complex family for `A₄` is pairwise
nonisomorphic. -/
private lemma a4_explicit_complex_family_pairwise
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    CategoryTheory.PairwiseNonisomorphic (a4_explicitComplexFamily eLin) := by
  intro i j hij hij_iso
  -- Enumerate the four slots: three linear characters and the unique nonlinear constituent.
  fin_cases i <;> fin_cases j
  · contradiction
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 0) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · contradiction
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 1) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · exact a4_linearCharacterFamily_pairwise (by simp) hij_iso
  · contradiction
  · exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 2) hij_iso
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 0) ⟨h.symm⟩
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 1) ⟨h.symm⟩
  · rcases hij_iso with ⟨h⟩
    exact a4_linearCharacterFamily_not_isomorphic_augmentation (eLin 2) ⟨h.symm⟩
  · contradiction

/-- Helper for Exercise 9-9.2-3: the four explicit constituents have degrees `1,1,1,3`. -/
private lemma a4_explicit_complex_family_degree
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    Module.finrank ℂ (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)).V =
      match i with
      | 0 => 1
      | 1 => 1
      | 2 => 1
      | 3 => 3 := by
  -- Enumerate the four slots and reduce each degree separately.
  fin_cases i <;> dsimp [a4_explicitComplexFamily]
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · exact Module.finrank_self ℂ
  · simpa using a4_augmentationRepresentation_finrank_three

/-- Helper for Exercise 9-9.2-3: the explicit family of three linear characters together with the
augmentation constituent is a complete irreducible family of `A₄`. -/
private lemma a4_explicit_complex_family_complete
    (eLin : Fin 3 ≃ a4_linearCharacters) :
    IsCompleteIrreducibleFamily
      (a4_explicitFDRepFamily eLin) := by
  letI : NeZero (Nat.card A4 : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hlinear_simple :
      ∀ χ : a4_linearCharacters,
        CategoryTheory.Simple (FDRep.of ((a4_linearCharacterFamily χ).ρ)) := by
    intro χ
    have hχirr : Representation.IsIrreducible ((a4_linearCharacterFamily χ).ρ) := by
      simpa [a4_linearCharacterFamily] using
        (MonoidHom.toRepresentation_isIrreducible (χ.comp (QuotientGroup.mk' V4)))
    letI : Representation.IsIrreducible (FDRep.of ((a4_linearCharacterFamily χ).ρ)).ρ := by
      simpa using hχirr
    exact FDRep.simple_of_isIrreducible (FDRep.of ((a4_linearCharacterFamily χ).ρ))
  have haugmentation_simple :
      CategoryTheory.Simple (FDRep.of a4_augmentationRepresentation) := by
    letI : Representation.IsIrreducible (FDRep.of a4_augmentationRepresentation).ρ := by
      simpa using a4_augmentation_representation_isIrreducible
    exact FDRep.simple_of_isIrreducible (FDRep.of a4_augmentationRepresentation)
  have hcomplete :
      IsCompleteIrreducibleFamily
        (fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
    have hsimple :
        ∀ i, CategoryTheory.Simple (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
      intro i
      fin_cases i <;> dsimp [a4_explicitComplexFamily]
      · exact hlinear_simple (eLin 0)
      · exact hlinear_simple (eLin 1)
      · exact hlinear_simple (eLin 2)
      · simpa using haugmentation_simple
    have hpairwise :
        CategoryTheory.PairwiseNonisomorphic
          (fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ)) := by
      intro i j hij hij_iso
      rcases hij_iso with ⟨e⟩
      exact
        a4_explicit_complex_family_pairwise eLin hij
          ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
    refine
      Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
        (π := fun i ↦ FDRep.of ((a4_explicitComplexFamily eLin i).ρ))
        hsimple hpairwise ?_
    -- The explicit degree table is `1,1,1,3`, so the square-degree sum is `12 = |A₄|`.
    rw [show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)]
    have hdeg :
        ∀ i : Fin 4,
          Module.finrank ℂ (FDRep.of ((a4_explicitComplexFamily eLin i).ρ)).V ^ 2 =
            (match i with
            | 0 => 1
            | 1 => 1
            | 2 => 1
            | 3 => 3) ^ 2 := by
      intro i
      rw [a4_explicit_complex_family_degree]
    simp_rw [hdeg]
    have huniv :
        (@Finset.univ (Fin 4) Representation.instFintype_serre) =
          (@Finset.univ (Fin 4) (Fin.fintype 4)) := by
      ext x
      simp
    rw [huniv]
    decide
  simpa [a4_explicitFDRepFamily] using hcomplete

/-- Helper for Exercise 9-9.2-3: every degree-`1` character of `A₄` factors through the quotient
`A₄/V₄`. -/
private lemma a4_linear_character_factors_through_kleinFour_quotient
    (ρ : A4 →* ℂˣ) :
    ∃ α : a4_linearCharacters, ρ = α.comp (QuotientGroup.mk' V4) := by
  have hV4_le_ker : V4 ≤ ρ.ker := by
    -- Route correction: use `V₄ = [A₄, A₄]`, so every linear character kills `V₄`.
    simpa [alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp)] using
      (Abelianization.commutator_subset_ker ρ)
  refine ⟨QuotientGroup.lift V4 ρ hV4_le_ker, ?_⟩
  -- The quotient lift is characterized by composing back with the quotient map.
  simpa using (QuotientGroup.lift_comp_mk' V4 ρ hV4_le_ker).symm

/-- Helper for Exercise 9-9.2-3: every degree-`1` character of `A₄` restricts trivially to the
Klein four subgroup `V₄`. -/
private lemma a4_linear_character_restrict_kleinFour_eq_one
    (ρ : A4 →* ℂˣ) (h : V4) :
    ρ h = 1 := by
  rcases a4_linear_character_factors_through_kleinFour_quotient ρ with ⟨α, hρ⟩
  have hq : (QuotientGroup.mk' V4) (h : A4) = 1 := by
    exact (QuotientGroup.eq_one_iff (h : A4)).mpr h.2
  -- After factoring through the quotient, every element of `V₄` maps to the identity class.
  rw [hρ]
  simpa using congrArg α hq

/-- Helper for Exercise 9-9.2-3: Serre's Klein-four character `θ` is orthogonal to the trivial
character of `V₄`. -/
private lemma a4_theta_pairing_trivial_eq_zero :
    ⟪a4_theta.toRepresentation.character, (Representation.trivial ℂ V4 ℂ).character⟫ = 0 := by
  have htheta_irr : a4_theta.toRepresentation.IsIrreducible := by
    simpa using MonoidHom.toRepresentation_isIrreducible a4_theta
  letI : a4_theta.toRepresentation.IsIrreducible := htheta_irr
  have htriv_irr : (Representation.trivial ℂ V4 ℂ).IsIrreducible := by
    simpa using isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ V4 ℂ)
  letI : (Representation.trivial ℂ V4 ℂ).IsIrreducible := htriv_irr
  have hnot :
      ¬ Nonempty (Representation.Equiv (Representation.trivial ℂ V4 ℂ) a4_theta.toRepresentation) := by
    intro hEq
    rcases hEq with ⟨e⟩
    have htrivy :
        (Representation.trivial ℂ V4 ℂ).character a4_v4_y = (1 : ℂ) := by
      simp [Representation.character, Representation.trivial]
    have hthetay :
        a4_theta.toRepresentation.character a4_v4_y = (-1 : ℂ) := by
      simpa using congrArg (fun z : ℂˣ => (z : ℂ)) (a4_theta_apply_y)
    have hy := congrFun (Representation.char_iso e) a4_v4_y
    rw [htrivy, hthetay] at hy
    norm_num at hy
  -- Orthogonality of nonisomorphic irreducible characters gives the required vanishing.
  calc
    ⟪a4_theta.toRepresentation.character, (Representation.trivial ℂ V4 ℂ).character⟫
      = (Nat.card V4 : ℂ)⁻¹ * ∑ g : V4,
          a4_theta.toRepresentation.character g *
            (Representation.trivial ℂ V4 ℂ).character g⁻¹ := by
              exact
                Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply
                  a4_theta.toRepresentation.character
                  (Representation.trivial ℂ V4 ℂ).character
    _ = 0 := by
          simpa [hnot] using
            (Representation.char_orthonormal
              (ρ := a4_theta.toRepresentation)
              (σ := Representation.trivial ℂ V4 ℂ))

/-- Helper for Exercise 9-9.2-3: every degree-`1` character of `A₄` is orthogonal to Serre's
nonlinear character `ψ`. -/
private lemma a4_psi_eq_augmentation_character :
    (ψ : A4 → ℂ) = a4_augmentationRepresentation.character := by
  -- Identify `ψ` with the induced representation character coming from `θ`.
  simpa [a4_psi, a4_augmentationRepresentation, Subgroup.characterRingInduction_apply,
    MonoidHom.toCharacterRing_apply] using
    (Subgroup.inducedClassFunction_eq_character_ind (H := V4) (K := ℂ)
      a4_theta.toRepresentation)

/-- Helper for Exercise 9-9.2-3: every degree-`1` character of `A₄` is orthogonal to Serre's
nonlinear character `ψ`. -/
private lemma a4_linear_character_pairing_psi_eq_zero
    (ρ : A4 →* ℂˣ) :
    ⟪((MonoidHom.toCharacterRing ρ : R(A4)) : A4 → ℂ), (ψ : A4 → ℂ)⟫ = 0 := by
  rcases a4_linear_character_factors_through_kleinFour_quotient ρ with ⟨α, hρ⟩
  have hρchar :
      ((MonoidHom.toCharacterRing ρ : R(A4)) : A4 → ℂ) =
        (a4_linearCharacterFamily α).ρ.character := by
    -- Rewrite the given linear character through its quotient factorization.
    ext g
    simpa [a4_linearCharacterFamily, hρ, MonoidHom.toCharacterRing_apply]
  have hlin_irr : (a4_linearCharacterFamily α).ρ.IsIrreducible := by
    simpa [a4_linearCharacterFamily] using
      (MonoidHom.toRepresentation_isIrreducible (α.comp (QuotientGroup.mk' V4)))
  letI : (a4_linearCharacterFamily α).ρ.IsIrreducible := hlin_irr
  letI : a4_augmentationRepresentation.IsIrreducible :=
    a4_augmentation_representation_isIrreducible
  have hnot :
      ¬ Nonempty (a4_augmentationRepresentation.Equiv (a4_linearCharacterFamily α).ρ) := by
    intro hEq
    rcases hEq with ⟨e⟩
    have hdeg : (3 : ℂ) = 1 := by
      have hchar :
          a4_augmentationRepresentation.character =
            (a4_linearCharacterFamily α).ρ.character :=
        Representation.char_iso e
      have hdeg' := congrFun hchar 1
      simpa [a4_linearCharacterFamily, Representation.char_one,
        a4_augmentationRepresentation_finrank_three] using hdeg'
    norm_num at hdeg
  -- The quotient factorization identifies `ρ` with one of the linear slots, and that slot is
  -- nonisomorphic to the augmentation constituent.
  calc
    ⟪((MonoidHom.toCharacterRing ρ : R(A4)) : A4 → ℂ), (ψ : A4 → ℂ)⟫
      = ⟪(a4_linearCharacterFamily α).ρ.character, a4_augmentationRepresentation.character⟫ := by
          rw [hρchar, a4_psi_eq_augmentation_character]
    _ = (Nat.card A4 : ℂ)⁻¹ * ∑ g : A4,
          (a4_linearCharacterFamily α).ρ.character g *
            a4_augmentationRepresentation.character g⁻¹ := by
              exact
                Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply
                  (a4_linearCharacterFamily α).ρ.character
                  a4_augmentationRepresentation.character
    _ = 0 := by
          simpa [hnot] using
            (Representation.char_orthonormal
              (ρ := (a4_linearCharacterFamily α).ρ)
              (σ := a4_augmentationRepresentation))

/-- Helper for Exercise 9-9.2-3: a distinguished order-`2` cyclic subgroup of `A₄`, generated by
the double transposition `y`. -/
private abbrev a4_order_two_subgroup : Subgroup A4 :=
  Subgroup.zpowers (a4_v4_y : A4)

/-- Helper for Exercise 9-9.2-3: the preferred generator of the distinguished order-`2` subgroup. -/
private def a4_order_two_generator : a4_order_two_subgroup :=
  ⟨a4_v4_y, Subgroup.mem_zpowers (a4_v4_y : A4)⟩

/-- Helper for Exercise 9-9.2-3: the chosen double transposition has order `2`. -/
private lemma a4_order_two_generator_order :
    orderOf (a4_v4_y : A4) = 2 := by
  -- The explicit permutation `y = (13)(24)` is a nontrivial involution.
  exact orderOf_eq_prime
    (by decide : (a4_v4_y : A4) ^ 2 = 1)
    (by decide : (a4_v4_y : A4) ≠ 1)

/-- Helper for Exercise 9-9.2-3: the distinguished order-`2` subgroup lies inside the Klein four
subgroup. -/
private lemma a4_order_two_subgroup_le_kleinFour :
    a4_order_two_subgroup ≤ V4 := by
  -- A cyclic subgroup generated by an element of `V₄` remains inside `V₄`.
  rw [a4_order_two_subgroup]
  exact Subgroup.zpowers_le.2 a4_v4_y.2

/-- Helper for Exercise 9-9.2-3: the preferred order-`2` generator is not the identity. -/
private lemma a4_order_two_generator_ne_one :
    a4_order_two_generator ≠ 1 := by
  -- The chosen generator is the explicit nontrivial double transposition `y`.
  intro h
  have hy : (a4_v4_y : A4) = 1 := by
    simpa [a4_order_two_generator] using
      congrArg (fun z : a4_order_two_subgroup => (z : A4)) h
  have hy_ne : (a4_v4_y : A4) ≠ 1 := by
    decide
  exact hy_ne hy

/-- Helper for Exercise 9-9.2-3: every element of the distinguished order-`2` subgroup is either
the identity or the preferred generator. -/
private lemma a4_order_two_subgroup_eq_one_or_generator
    (h : a4_order_two_subgroup) :
    h = 1 ∨ h = a4_order_two_generator := by
  rcases h with ⟨h, hh⟩
  rw [a4_order_two_subgroup, mem_zpowers_iff_mem_range_orderOf] at hh
  rw [a4_order_two_generator_order, Finset.mem_image] at hh
  rcases hh with ⟨n, hn, rfl⟩
  rw [Finset.mem_range] at hn
  interval_cases n <;> simp [a4_order_two_generator]

/-- Helper for Exercise 9-9.2-3: the nontrivial linear character of the distinguished order-`2`
subgroup, obtained by restricting Serre's Klein-four character `θ`. -/
private def a4_order_two_character : a4_order_two_subgroup →* ℂˣ :=
  a4_theta.comp (Subgroup.inclusion a4_order_two_subgroup_le_kleinFour)

/-- Helper for Exercise 9-9.2-3: the preferred order-`2` generator maps to `-1` under the chosen
nontrivial linear character. -/
private lemma a4_order_two_character_apply_generator :
    a4_order_two_character a4_order_two_generator = -1 := by
  -- After transporting the generator into `V₄`, this is exactly the defining value `θ(y) = -1`.
  have hgen :
      (Subgroup.inclusion a4_order_two_subgroup_le_kleinFour a4_order_two_generator : V4) =
        a4_v4_y := by
    apply Subtype.ext
    rfl
  simpa [a4_order_two_character, hgen] using a4_theta_apply_y

/-- Helper for Exercise 9-9.2-3: every ambient linear character of `A₄` restricts trivially to
the distinguished order-`2` subgroup. -/
private lemma a4_linear_character_restrict_order_two_eq_one
    (ρ : A4 →* ℂˣ) (h : a4_order_two_subgroup) :
    ρ h = 1 := by
  -- The distinguished order-`2` subgroup lies in `V₄`, and every linear character kills `V₄`.
  simpa using
    a4_linear_character_restrict_kleinFour_eq_one ρ
      (Subgroup.inclusion a4_order_two_subgroup_le_kleinFour h)

/-- Helper for Exercise 9-9.2-3: restricting one of the three ambient linear constituents of `A₄`
to the distinguished order-`2` subgroup gives the trivial character there. -/
private lemma a4_linearCharacterFamily_restrict_order_two_character_eq
    (χ : a4_linearCharacters) :
    Representation.character
        (((a4_linearCharacterFamily χ).ρ).comp a4_order_two_subgroup.subtype) =
      (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
  -- Restricting a quotient-linear character to the order-`2` subgroup lands on the trivial slot.
  ext h
  change
    (((((
        (χ.comp (QuotientGroup.mk' V4)).comp a4_order_two_subgroup.subtype) :
          a4_order_two_subgroup →* ℂˣ).toRepresentation).character) h) =
      (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ) h)
  rw [MonoidHom.toRepresentation_character_apply]
  simpa [MonoidHom.toCharacterRing_apply] using
    congrArg (fun z : ℂˣ => (z : ℂ))
      (a4_linear_character_restrict_order_two_eq_one
        ((χ.comp (QuotientGroup.mk' V4))) h)

/-- Helper for Exercise 9-9.2-3: the natural permutation character of `A₄` vanishes on the chosen
double transposition `y`, since that involution fixes no point of `Fin 4`. -/
private lemma a4_permutation_character_apply_order_two_generator :
    (ofMulAction ℂ A4 (Fin 4)).character (a4_v4_y : A4) = 0 := by
  -- Evaluate the permutation character by counting fixed points of the explicit double
  -- transposition `y`.
  rw [Representation.ofMulAction_character_eq_ncard_fixedBy]
  have hempty : MulAction.fixedBy (Fin 4) (a4_v4_y : A4) = ∅ := by
    ext x
    fin_cases x <;> decide
  simpa [hempty]

/-- Helper for Exercise 9-9.2-3: the restriction table on the distinguished order-`2` subgroup:
ambient linear characters become trivial, and `ψ` restricts to `1 + 2ε`. -/
private lemma a4_order_two_subgroup_restriction_table
    (ρ : A4 →* ℂˣ) :
    (∀ h : a4_order_two_subgroup, ρ h = 1) ∧
      Representation.character (a4_augmentationRepresentation.comp a4_order_two_subgroup.subtype) =
        (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) +
          2 • (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
            a4_order_two_subgroup → ℂ)) := by
  refine ⟨a4_linear_character_restrict_order_two_eq_one ρ, ?_⟩
  ext h
  rcases a4_order_two_subgroup_eq_one_or_generator h with rfl | rfl
  · -- Evaluate both characters at the identity; they both have degree `3`.
    change a4_augmentationRepresentation.character (1 : A4) =
      ((((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) 1 +
        (2 •
          (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
            a4_order_two_subgroup → ℂ))) 1)
    calc
      a4_augmentationRepresentation.character (1 : A4)
        = (Module.finrank ℂ (IndV (Subgroup.subtype V4) a4_theta.toRepresentation) : ℂ) := by
            simpa using Representation.char_one a4_augmentationRepresentation
      _ = 3 := by
            norm_num [a4_augmentationRepresentation_finrank_three]
      _ = ((((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) 1 +
            (2 •
              (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
                a4_order_two_subgroup → ℂ))) 1) := by
            norm_num
  · -- Route correction: evaluate the augmentation character on the distinguished involution using
    -- the already-proved `A₄` character table, rather than recomputing induction values locally.
    change a4_augmentationRepresentation.character (a4_v4_y : A4) =
      ((((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) a4_order_two_generator +
        (2 •
          (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
            a4_order_two_subgroup → ℂ))) a4_order_two_generator)
    calc
      a4_augmentationRepresentation.character (a4_v4_y : A4) = (-1 : ℂ) := by
        have hpsi := congrFun a4_induced_theta_character_eq_psi (a4_v4_y : A4)
        change a4_augmentationRepresentation.character (a4_v4_y : A4) =
          (ofMulAction ℂ A4 (Fin 4)).character (a4_v4_y : A4) - 1 at hpsi
        calc
          a4_augmentationRepresentation.character (a4_v4_y : A4) =
              (ofMulAction ℂ A4 (Fin 4)).character (a4_v4_y : A4) - 1 := by
                simpa [a4_augmentationRepresentation] using hpsi
          _ = (-1 : ℂ) := by
                rw [a4_permutation_character_apply_order_two_generator]
                norm_num
      _ =
          ((((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))
              a4_order_two_generator +
            (2 •
              (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
                a4_order_two_subgroup → ℂ))) a4_order_two_generator) := by
            norm_num [a4_order_two_character_apply_generator]

/-- Helper for Exercise 9-9.2-3: the two degree-`1` characters of the distinguished order-`2`
subgroup are orthonormal. -/
private lemma a4_order_two_subgroup_linear_pairing_eq_ite
    (χ χ' : a4_order_two_subgroup →* ℂˣ) :
    ⟪(((MonoidHom.toCharacterRing χ : R(a4_order_two_subgroup)) :
        a4_order_two_subgroup → ℂ)),
      (((MonoidHom.toCharacterRing χ' : R(a4_order_two_subgroup)) :
        a4_order_two_subgroup → ℂ))⟫ =
      if χ = χ' then 1 else 0 := by
  letI : χ.toRepresentation.IsIrreducible := by
    simpa using MonoidHom.toRepresentation_isIrreducible χ
  letI : χ'.toRepresentation.IsIrreducible := by
    simpa using MonoidHom.toRepresentation_isIrreducible χ'
  by_cases h : χ = χ'
  · subst h
    have hself : Nonempty (χ.toRepresentation.Equiv χ.toRepresentation) :=
      ⟨Representation.Equiv.refl _⟩
    -- For a degree-`1` irreducible character, the normalized self-pairing is `1`.
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
      MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply, hself] using
      (Representation.char_orthonormal (ρ := χ.toRepresentation) (σ := χ.toRepresentation))
  · have hnot' : ¬ Nonempty (χ'.toRepresentation.Equiv χ.toRepresentation) := by
      intro hiso
      rcases hiso with ⟨e⟩
      have hchar : χ'.toRepresentation.character = χ.toRepresentation.character :=
        Representation.char_iso e
      have hEq : χ = χ' := by
        ext s
        simpa [MonoidHom.toRepresentation_character_apply] using (congrFun hchar s).symm
      exact h hEq
    -- Distinct degree-`1` characters are orthogonal.
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
      MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply, h, hnot'] using
      (Representation.char_orthonormal (ρ := χ.toRepresentation) (σ := χ'.toRepresentation))

/-- Helper for Exercise 9-9.2-3: the nontrivial order-`2` character is orthogonal to the trivial
character on the distinguished order-`2` subgroup. -/
private lemma a4_order_two_character_pairing_trivial_eq_zero :
    ⟪(((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
        a4_order_two_subgroup → ℂ)),
      (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))⟫ = 0 := by
  have hsign_ne_trivial : a4_order_two_character ≠ (1 : a4_order_two_subgroup →* ℂˣ) := by
    intro hEq
    have hgen := congrArg (fun f : a4_order_two_subgroup →* ℂˣ => f a4_order_two_generator) hEq
    simp [a4_order_two_character_apply_generator] at hgen
  calc
    ⟪(((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
        a4_order_two_subgroup → ℂ)),
      (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))⟫ =
        ⟪(((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
            a4_order_two_subgroup → ℂ)),
          (((MonoidHom.toCharacterRing (1 : a4_order_two_subgroup →* ℂˣ) :
              R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))⟫ := by
          congr 2
          ext s
          simp [MonoidHom.toCharacterRing_apply]
    _ = 0 := by
          rw [a4_order_two_subgroup_linear_pairing_eq_ite a4_order_two_character 1]
          simp [hsign_ne_trivial]

/-- Helper for Exercise 9-9.2-3: pairing the nontrivial order-`2` character against the
restriction of `ψ` to the distinguished order-`2` subgroup gives `2`. -/
private lemma a4_order_two_character_pairing_augmentation_restriction_eq_two :
    ⟪(((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
        a4_order_two_subgroup → ℂ)),
      Representation.character (a4_augmentationRepresentation.comp a4_order_two_subgroup.subtype)⟫
      = 2 := by
  have hrestrict :=
    (a4_order_two_subgroup_restriction_table (1 : A4 →* ℂˣ)).2
  have htwo :
      (2 • (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
          a4_order_two_subgroup → ℂ))) =
        ((2 : ℂ) •
          (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
            a4_order_two_subgroup → ℂ))) := by
    ext s
    simp [two_nsmul, smul_eq_mul]
  rw [hrestrict, Representation.groupFunctionPairing_add_right,
    htwo, Representation.groupFunctionPairing_smul_right]
  rw [a4_order_two_character_pairing_trivial_eq_zero,
    a4_order_two_subgroup_linear_pairing_eq_ite a4_order_two_character a4_order_two_character]
  simp

/-- Helper for Exercise 9-9.2-3: the tensor-level map used in Frobenius reciprocity is compatible
with the defining coinvariant relation for induction. -/
private theorem frobenius_tensor_relation_local
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {W : Type*} [AddCommGroup W] [Module K W]
    (α : H →* G) (E : Representation K G V) (θ : Representation K H W)
    (f : θ.IntertwiningMap (E.comp α)) (g : H) (x : G) (y : W) :
    (((((Finsupp.lift (W →ₗ[K] V) K G) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
          (Representation.leftRegular K G) (α g)).compl₂
        (θ g) ∘ₗ Finsupp.lsingle x)
      (1 : K))
    y =
    ((((Finsupp.lift (W →ₗ[K] V) K G) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
        Finsupp.lsingle x)
      (1 : K)) y := by
  -- Expand the tensor relation on a pure tensor and rewrite the inner `H`-action via `f`.
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, smul_eq_mul,
    Finsupp.lift_apply, map_mul, mul_inv_rev, zero_smul, Finsupp.sum_single_index, one_smul,
    IntertwiningMap.toLinearMap_apply, Module.End.mul_apply]
  have hg := LinearMap.congr_fun (f.2 g) y
  simp only [LinearMap.comp_apply] at hg
  change (E x⁻¹) ((E (α g)⁻¹) (f.toLinearMap ((θ g) y))) = (E x⁻¹) (f.toLinearMap y)
  rw [hg]
  simp

/-- Helper for Exercise 9-9.2-3: Frobenius reciprocity gives a linear equivalence between the
intertwining maps `Ind_α θ ⟶ E` and `θ ⟶ Res_α E` without passing through the `Rep` wrapper. -/
private def frobenius_intertwining_equiv_local
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {W : Type*} [AddCommGroup W] [Module K W]
    (α : H →* G) (E : Representation K G V) (θ : Representation K H W) :
    ((ind α θ).IntertwiningMap E) ≃ₗ[K] θ.IntertwiningMap (E.comp α) where
  toFun f :=
    { toLinearMap := f.toLinearMap ∘ₗ IndV.mk α θ 1
      isIntertwining' := fun g => by
        -- Evaluate the induced intertwiner on the canonical generator `IndV.mk α θ 1`.
        ext x
        have hf := LinearMap.congr_fun (f.2 (α g)) (IndV.mk α θ 1 x)
        simpa [← Representation.Coinvariants.mk_inv_tmul] using hf }
  invFun f :=
    { toLinearMap := Representation.Coinvariants.lift _
        (TensorProduct.lift <| Finsupp.lift _ _ _ fun h => E h⁻¹ ∘ₗ f.toLinearMap)
        (fun g => by
          -- The tensor-level formula descends because the defining relation is exactly the
          -- previous helper theorem.
          simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
            TensorProduct.lift_comp_map]
          congr 1
          ext x y
          exact frobenius_tensor_relation_local α E θ f g x y)
      isIntertwining' := fun g => by
        -- On coinvariant classes, the induced action is the explicit inverse translation action.
        ext x
        simp }
  left_inv f := by
    -- Evaluating back on the canonical induced generators recovers `f`.
    ext h a
    have hf := LinearMap.congr_fun (f.2 h⁻¹) (IndV.mk α θ 1 a)
    simpa using hf.symm
  right_inv f := by
    -- The descended map sends `IndV.mk α θ 1` back to the original intertwiner.
    ext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper for Exercise 9-9.2-3: the Frobenius-reciprocity pairing identity needed for the order-3
and order-2 induction computations. -/
private theorem groupFunctionPairing_character_comp_eq_character_ind_local
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (α : H →* G) (E : Representation ℂ G V) (θ : Representation ℂ H W)
    [Invertible (Nat.card H : ℂ)] [Invertible (Nat.card G : ℂ)] :
    ⟪θ.character, Representation.character (E.comp α)⟫ =
      ⟪(ind α θ).character, E.character⟫ := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional ℂ (G →₀ ℂ) := by
    infer_instance
  letI : FiniteDimensional ℂ (TensorProduct ℂ (G →₀ ℂ) W) := by
    infer_instance
  letI : FiniteDimensional ℂ (IndV α θ) :=
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)
  -- Route correction: work directly with the Frobenius equivalence on intertwining spaces and then
  -- translate both sides into normalized character pairings.
  calc
    ⟪θ.character, Representation.character (E.comp α)⟫ =
        Module.finrank ℂ (θ.IntertwiningMap (E.comp α)) := by
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ θ (E.comp α))
    _ = Module.finrank ℂ ((ind α θ).IntertwiningMap E) := by
          have hdim : Module.finrank ℂ (θ.IntertwiningMap (E.comp α)) =
              Module.finrank ℂ ((ind α θ).IntertwiningMap E) :=
            (frobenius_intertwining_equiv_local α E θ).symm.finrank_eq
          simpa [hdim]
    _ = ⟪(ind α θ).character, E.character⟫ := by
          symm
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ (ind α θ) E)

/-- Helper for Exercise 9-9.2-3: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → A4 → ℂ) (psiFun : A4 → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, psiFun⟫ = ∑ j ∈ s, ((a j : ℤ) : ℂ) * ⟪χ j, psiFun⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Convert the inserted integer multiple into the scalar form used by the pairing API.
      have hzsmul : (a i • χ i : A4 → ℂ) = (((a i : ℤ) : ℂ) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left, hzsmul,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 9-9.2-3: pairing with the irreducible-character basis recovers the
corresponding coefficient. -/
private theorem basis_coefficient_pairing_eq
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ A4)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R(A4)) (i : ι) :
    ⟪(x : A4 → ℂ), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
  letI : Invertible (Nat.card A4 : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : A4 → ℂ) := by
    -- Rewrite the basis expansion of `x` inside the ambient function space of class functions.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr x)
  have horth : Pairwise fun j k ↦ ⟪(π j).character, (π k).character⟫ = (0 : ℂ) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  have hdiag : ∀ j, ⟪(π j).character, (π j).character⟫ = (1 : ℂ) := by
    intro j
    letI : CategoryTheory.Simple (π j) := hπ_complete.isSimple j
    have hself : Nonempty (π j ≅ π j) := ⟨CategoryTheory.Iso.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (FDRep.char_orthonormal (π j) (π j))
  calc
    ⟪(x : A4 → ℂ), (π i).character⟫ = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
      -- Replace `x` by its irreducible-basis expansion.
      simpa [hx] using
        congrArg (fun f : A4 → ℂ ↦ groupFunctionPairingOverField ℂ f (π i).character) hx.symm
    _ = ∑ j, ((c j : ℤ) : ℂ) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the irreducible basis.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left (s := Finset.univ) (a := c)
              (χ := fun j ↦ (π j).character) (psiFun := (π i).character)
    _ = ((c i : ℤ) : ℂ) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal coefficient.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            rw [horth hji, mul_zero]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    _ = (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
          simp [b, c, hdiag]

/-- Helper for Exercise 9-9.2-3: the distinguished order-`3` subgroup used in the source proof. -/
private abbrev a4_order_three_subgroup : Subgroup A4 :=
  Subgroup.zpowers a4_three_cycle_012

/-- Helper for Exercise 9-9.2-3: the distinguished order-`3` subgroup has index `4` in `A₄`. -/
private lemma a4_order_three_subgroup_index_four :
    a4_order_three_subgroup.index = 4 := by
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hC : Nat.card a4_order_three_subgroup = 3 := by
    simpa [a4_order_three_subgroup, a4_three_cycle_012_order] using
      Nat.card_zpowers a4_three_cycle_012
  have hmul : a4_order_three_subgroup.index * Nat.card a4_order_three_subgroup = Nat.card A4 := by
    simpa [a4_order_three_subgroup] using a4_order_three_subgroup.index_mul_card
  rw [hC, hA4] at hmul
  omega

/-- Helper for Exercise 9-9.2-3: the distinguished order-`2` subgroup has index `6` in `A₄`. -/
private lemma a4_distinguished_order_two_index_six :
    a4_order_two_subgroup.index = 6 := by
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hC : Nat.card a4_order_two_subgroup = 2 := by
    calc
      Nat.card a4_order_two_subgroup = orderOf (a4_v4_y : A4) := by
        simpa [a4_order_two_subgroup] using Nat.card_zpowers (a4_v4_y : A4)
      _ = 2 := a4_order_two_generator_order
  have hmul : a4_order_two_subgroup.index * Nat.card a4_order_two_subgroup = Nat.card A4 := by
    simpa [a4_order_two_subgroup] using a4_order_two_subgroup.index_mul_card
  rw [hC, hA4] at hmul
  omega

/-- Helper for Exercise 9-9.2-3: the Klein four subgroup has index `3` in `A₄`. -/
private lemma a4_klein_four_index_three :
    (show Subgroup A4 from V4).index = 3 := by
  let K : Subgroup A4 := V4
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hV4 : Nat.card V4 = 4 := by
    simpa using alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  have hmul : K.index * Nat.card K = Nat.card A4 := K.index_mul_card
  rw [hV4, hA4] at hmul
  have hindex : K.index = 3 := by
    omega
  simpa [K] using hindex

/-- Helper for Exercise 9-9.2-3: a quotient character is determined by its pullback to `A₄`. -/
private lemma a4_quotient_linear_character_eq_of_pullback_eq
    {α β : a4_linearCharacters}
    (h : α.comp (QuotientGroup.mk' V4) = β.comp (QuotientGroup.mk' V4)) :
    α = β := by
  ext q
  rcases QuotientGroup.mk'_surjective V4 q with ⟨g, hg⟩
  have hg' :
      (α ((QuotientGroup.mk' V4) g) : ℂ) = (β ((QuotientGroup.mk' V4) g) : ℂ) := by
    exact congrArg (fun z : ℂˣ => (z : ℂ))
      (congrArg (fun f : A4 →* ℂˣ => f g) h)
  simpa [hg] using hg'

/-- Helper for Exercise 9-9.2-3: two linear characters of `A₄` coincide once they agree on the
chosen order-`3` complement of `V₄`. -/
private lemma a4_linear_character_eq_of_eq_on_order_three_subgroup
    {ρ ρ' : A4 →* ℂˣ}
    (hC : ρ.comp a4_order_three_subgroup.subtype = ρ'.comp a4_order_three_subgroup.subtype) :
    ρ = ρ' := by
  ext g
  change (ρ g : ℂ) = (ρ' g : ℂ)
  obtain ⟨⟨c, v⟩, hcv⟩ := a4_order_three_subgroup_isComplement_kleinFour.2 g
  have hc_eq : (ρ c.1 : ℂ) = (ρ' c.1 : ℂ) := by
    exact congrArg (fun z : ℂˣ => (z : ℂ))
      (congrArg (fun f : a4_order_three_subgroup →* ℂˣ => f c) hC)
  -- Split `g` along the complement decomposition and use that every linear character is trivial on
  -- `V₄`.
  calc
    (ρ g : ℂ) = (ρ (c.1 * v.1) : ℂ) := by rw [← hcv]
    _ = (ρ c.1 : ℂ) * (ρ v.1 : ℂ) := by simp [map_mul]
    _ = (ρ c.1 : ℂ) := by
          simp [a4_linear_character_restrict_kleinFour_eq_one ρ v]
    _ = (ρ' c.1 : ℂ) := hc_eq
    _ = (ρ' c.1 : ℂ) * (ρ' v.1 : ℂ) := by
          simp [a4_linear_character_restrict_kleinFour_eq_one ρ' v]
    _ = (ρ' (c.1 * v.1) : ℂ) := by simp [map_mul]
    _ = (ρ' g : ℂ) := by simpa [hcv]

/-- Helper for Exercise 9-9.2-3: distinct linear characters of the chosen cyclic subgroup of order
`3` are orthogonal. -/
private lemma a4_order_three_subgroup_linear_pairing_eq_ite
    (χ χ' : a4_order_three_subgroup →* ℂˣ) :
    ⟪(((MonoidHom.toCharacterRing χ : R(a4_order_three_subgroup)) :
        a4_order_three_subgroup → ℂ)),
      (((MonoidHom.toCharacterRing χ' : R(a4_order_three_subgroup)) :
        a4_order_three_subgroup → ℂ))⟫ =
      if χ = χ' then 1 else 0 := by
  letI : χ.toRepresentation.IsIrreducible := by
    simpa using MonoidHom.toRepresentation_isIrreducible χ
  letI : χ'.toRepresentation.IsIrreducible := by
    simpa using MonoidHom.toRepresentation_isIrreducible χ'
  by_cases h : χ = χ'
  · subst h
    have hself : Nonempty (χ.toRepresentation.Equiv χ.toRepresentation) :=
      ⟨Representation.Equiv.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
      MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply, hself] using
      (Representation.char_orthonormal (ρ := χ.toRepresentation) (σ := χ.toRepresentation))
  · have hnot' : ¬ Nonempty (χ'.toRepresentation.Equiv χ.toRepresentation) := by
      intro hiso
      rcases hiso with ⟨e⟩
      have hchar : χ'.toRepresentation.character = χ.toRepresentation.character :=
        Representation.char_iso e
      have hEq : χ = χ' := by
        ext s
        simpa [MonoidHom.toRepresentation_character_apply] using (congrFun hchar s).symm
      exact h hEq
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
      MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply, h, hnot'] using
      (Representation.char_orthonormal (ρ := χ.toRepresentation) (σ := χ'.toRepresentation))

/-- Helper for Exercise 9-9.2-3: inducing a linear character from the chosen order-`3` subgroup
produces a linear character of `A₄` plus the nonlinear constituent `ψ`. -/
private lemma a4_order_three_induced_linear_eq_linear_plus_psi
    (χ : a4_order_three_subgroup →* ℂˣ) :
    ∃ ρ : A4 →* ℂˣ,
      ρ.comp a4_order_three_subgroup.subtype = χ ∧
      a4_order_three_subgroup.characterRingInduction (MonoidHom.toCharacterRing χ) =
        MonoidHom.toCharacterRing ρ + ψ := by
  classical
  obtain ⟨ρ, hρrestrict, hρker⟩ :=
    Subgroup.exists_linear_representation_extension_with_frobeniusNonconjugateSet_in_kernel
      a4_order_three_subgroup a4_order_three_subgroup_isFrobenius χ
  rcases a4_linear_character_factors_through_kleinFour_quotient ρ with ⟨α, hρα⟩
  have hcard_lin : Fintype.card a4_linearCharacters = 3 := by
    simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card
  let eBase : a4_linearCharacters ≃ Fin 3 := Fintype.equivFinOfCardEq hcard_lin
  let eLin : Fin 3 ≃ a4_linearCharacters :=
    (Equiv.swap 0 (eBase α)).trans eBase.symm
  have heLin0 : eLin 0 = α := by
    simp [eLin, eBase]
  let chiSlot1 : a4_order_three_subgroup →* ℂˣ :=
    ((eLin 1).comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype
  let chiSlot2 : a4_order_three_subgroup →* ℂˣ :=
    ((eLin 2).comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype
  have hchiSlot1_ne : chiSlot1 ≠ χ := by
    intro hchiSlot1
    have hpull :
        ((eLin 1).comp (QuotientGroup.mk' V4) : A4 →* ℂˣ) = ρ := by
      apply a4_linear_character_eq_of_eq_on_order_three_subgroup
      calc
        ((eLin 1).comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype = chiSlot1 := by
          rfl
        _ = χ := hchiSlot1
        _ = ρ.comp a4_order_three_subgroup.subtype := by
          simpa using hρrestrict.symm
    have hlin : eLin 1 = α := by
      apply a4_quotient_linear_character_eq_of_pullback_eq
      simpa [hρα] using hpull.trans hρα
    have hEq : (1 : Fin 3) = 0 := eLin.injective (by simpa [heLin0] using hlin)
    have hFalse : False := by
      simpa using hEq
    exact hFalse.elim
  have hchiSlot2_ne : chiSlot2 ≠ χ := by
    intro hchiSlot2
    have hpull :
        ((eLin 2).comp (QuotientGroup.mk' V4) : A4 →* ℂˣ) = ρ := by
      apply a4_linear_character_eq_of_eq_on_order_three_subgroup
      calc
        ((eLin 2).comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype = chiSlot2 := by
          rfl
        _ = χ := hchiSlot2
        _ = ρ.comp a4_order_three_subgroup.subtype := by
          simpa using hρrestrict.symm
    have hlin : eLin 2 = α := by
      apply a4_quotient_linear_character_eq_of_pullback_eq
      simpa [hρα] using hpull.trans hρα
    have hEq : (2 : Fin 3) = 0 := eLin.injective (by simpa [heLin0] using hlin)
    have hFalse : False := by
      simpa using hEq
    exact hFalse.elim
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic (a4_explicitFDRepFamily eLin) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise eLin hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete : IsCompleteIrreducibleFamily (a4_explicitFDRepFamily eLin) :=
    a4_explicit_complex_family_complete eLin
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily eLin) hpairwise hcomplete
  let x : R(A4) := a4_order_three_subgroup.characterRingInduction (MonoidHom.toCharacterRing χ)
  let c := b.repr x
  have hx_character :
      (x : A4 → ℂ) =
        (ind a4_order_three_subgroup.subtype χ.toRepresentation).character := by
    -- Route correction: rewrite the induced character through the canonical subgroup-induction
    -- character formula before pairing against the irreducible basis.
    simpa [x, Subgroup.characterRingInduction_apply, MonoidHom.toCharacterRing_apply] using
      (Subgroup.inducedClassFunction_eq_character_ind
        (H := a4_order_three_subgroup) (K := ℂ) χ.toRepresentation)
  have hpair0 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ = 1 := by
    -- Frobenius reciprocity reduces the first linear-basis coefficient to the self-pairing of `χ`.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ =
          ⟪χ.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 0).ρ).comp a4_order_three_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_three_subgroup.subtype
                (a4_explicitFDRepFamily eLin 0).ρ
                χ.toRepresentation
      _ = 1 := by
            have hslot0_hom :
                ((eLin 0).comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype = χ := by
              simpa [heLin0, hρα] using hρrestrict
            have hchi0 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 0).ρ).comp a4_order_three_subgroup.subtype) =
                  ((MonoidHom.toCharacterRing χ : R(a4_order_three_subgroup)) :
                    a4_order_three_subgroup → ℂ) := by
              -- Rewrite the restricted degree-`1` slot as the subgroup character coming from `χ`.
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily, hslot0_hom] using
                a4_linearCharacterFamily_restrict_order_three_character_eq (eLin 0)
            rw [hchi0]
            simpa using a4_order_three_subgroup_linear_pairing_eq_ite χ χ
  have hpair1 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ = 0 := by
    -- The second linear slot restricts to a different degree-`1` character of the order-`3`
    -- subgroup, so orthogonality forces the coefficient to vanish.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ =
          ⟪χ.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 1).ρ).comp a4_order_three_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_three_subgroup.subtype
                (a4_explicitFDRepFamily eLin 1).ρ
                χ.toRepresentation
      _ = 0 := by
            have hchiSlot1_ne' : χ ≠ chiSlot1 := by
              intro hEq
              exact hchiSlot1_ne hEq.symm
            have hchi1 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 1).ρ).comp a4_order_three_subgroup.subtype) =
                  ((MonoidHom.toCharacterRing chiSlot1 : R(a4_order_three_subgroup)) :
                    a4_order_three_subgroup → ℂ) := by
              -- The second slot is exactly the second pulled-back quotient character on `⟨σ⟩`.
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily, chiSlot1] using
                a4_linearCharacterFamily_restrict_order_three_character_eq (eLin 1)
            rw [hchi1]
            rw [a4_order_three_subgroup_linear_pairing_eq_ite χ chiSlot1, if_neg hchiSlot1_ne']
  have hpair2 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ = 0 := by
    -- The same orthogonality argument applies to the third linear slot.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ =
          ⟪χ.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 2).ρ).comp a4_order_three_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_three_subgroup.subtype
                (a4_explicitFDRepFamily eLin 2).ρ
                χ.toRepresentation
      _ = 0 := by
            have hchiSlot2_ne' : χ ≠ chiSlot2 := by
              intro hEq
              exact hchiSlot2_ne hEq.symm
            have hchi2 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 2).ρ).comp a4_order_three_subgroup.subtype) =
                  ((MonoidHom.toCharacterRing chiSlot2 : R(a4_order_three_subgroup)) :
                    a4_order_three_subgroup → ℂ) := by
              -- The third slot is the remaining pulled-back quotient character on `⟨σ⟩`.
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily, chiSlot2] using
                a4_linearCharacterFamily_restrict_order_three_character_eq (eLin 2)
            rw [hchi2]
            rw [a4_order_three_subgroup_linear_pairing_eq_ite χ chiSlot2, if_neg hchiSlot2_ne']
  have hc0 : c 0 = 1 := by
    have hcoeff0 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 0
    rw [hpair0] at hcoeff0
    have hcoeff0' : ((c 0 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff0.symm
    exact_mod_cast hcoeff0'
  have hc1 : c 1 = 0 := by
    have hcoeff1 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 1
    rw [hpair1] at hcoeff1
    have hcoeff1' : ((c 1 : ℤ) : ℂ) = 0 := by
      simpa [c] using hcoeff1.symm
    exact_mod_cast hcoeff1'
  have hc2 : c 2 = 0 := by
    have hcoeff2 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 2
    rw [hpair2] at hcoeff2
    have hcoeff2' : ((c 2 : ℤ) : ℂ) = 0 := by
      simpa [c] using hcoeff2.symm
    exact_mod_cast hcoeff2'
  have hx_basis :
      ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) = (x : A4 → ℂ) := by
    -- The complete irreducible family turns the character computation into an integral basis
    -- expansion inside `R(A₄)`.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr x)
  have hdegree_value (i : Fin 4) :
      ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) 1 =
        match i with
        | 0 => 1
        | 1 => 1
        | 2 => 1
        | 3 => 3 := by
    fin_cases i <;>
      simp [a4_explicitFDRepFamily, a4_explicitComplexFamily, Representation.char_one,
        a4_augmentationRepresentation_finrank_three]
  have hx_eval :
      (∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ)) 1 = (4 : ℂ) := by
    rw [hx_basis]
    simp [x, a4_order_three_subgroup_index_four, Subgroup.characterRingInduction_apply,
      Subgroup.inducedClassFunction_one_eq_index_mul_value, MonoidHom.toCharacterRing_apply]
  have hc3 : c 3 = 1 := by
    rw [Fin.sum_univ_four, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, Pi.smul_apply, Pi.smul_apply] at hx_eval
    rw [hdegree_value 0, hdegree_value 1, hdegree_value 2, hdegree_value 3] at hx_eval
    have hx_eval' : (1 : ℂ) + ((c 3 : ℤ) : ℂ) * 3 = 4 := by
      simpa [hc0, hc1, hc2] using hx_eval
    have hcoeff3_int : 1 + c 3 * 3 = 4 := by
      exact_mod_cast hx_eval'
    omega
  refine ⟨ρ, hρrestrict, ?_⟩
  have hslot0_char :
      ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing ρ : R(A4)) : A4 → ℂ)) := by
    -- The first basis slot was chosen to be the ambient extension `ρ`.
    ext g
    simp only [a4_explicitFDRepFamily, a4_explicitComplexFamily, heLin0, hρα]
    rfl
  have hslot3_char :
      ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ) = (ψ : A4 → ℂ) := by
    simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
      a4_psi_eq_augmentation_character.symm
  apply Subtype.ext
  calc
    (x : A4 → ℂ) = ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) := by
      simpa using hx_basis.symm
    _ =
        ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ) +
          ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ) := by
            rw [Fin.sum_univ_four]
            simp [hc0, hc1, hc2, hc3]
    _ = (((MonoidHom.toCharacterRing ρ + ψ : R(A4)) : A4 → ℂ)) := by
          rw [hslot0_char, hslot3_char]
          rfl

/-- Helper for Exercise 9-9.2-3: inducing the nontrivial degree-`1` character from the canonical
order-`2` subgroup produces exactly `2ψ`. -/
private lemma a4_order_two_induced_sign_eq_double_psi :
    a4_order_two_subgroup.characterRingInduction
        (MonoidHom.toCharacterRing a4_order_two_character) =
      2 • ψ := by
  classical
  have hcard_lin : Fintype.card a4_linearCharacters = 3 := by
    simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card
  let eLin : Fin 3 ≃ a4_linearCharacters := (Fintype.equivFinOfCardEq hcard_lin).symm
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic (a4_explicitFDRepFamily eLin) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise eLin hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete : IsCompleteIrreducibleFamily (a4_explicitFDRepFamily eLin) :=
    a4_explicit_complex_family_complete eLin
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily eLin) hpairwise hcomplete
  let x : R(A4) :=
    a4_order_two_subgroup.characterRingInduction
      (MonoidHom.toCharacterRing a4_order_two_character)
  let c := b.repr x
  have hsign_char :
      a4_order_two_character.toRepresentation.character =
        (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
          a4_order_two_subgroup → ℂ)) := by
    -- The order-`2` sign character has the same class-function realization in both APIs.
    ext h
    simp [MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply]
  have hx_character :
      (x : A4 → ℂ) =
        (ind a4_order_two_subgroup.subtype a4_order_two_character.toRepresentation).character := by
    -- Rewrite the virtual induction inside `R(A₄)` as the honest induced representation character.
    simpa [x, Subgroup.characterRingInduction_apply, MonoidHom.toCharacterRing_apply] using
      (Subgroup.inducedClassFunction_eq_character_ind
        (H := a4_order_two_subgroup) (K := ℂ) a4_order_two_character.toRepresentation)
  have hpair0 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ = 0 := by
    -- Frobenius reciprocity turns the first linear coefficient into the subgroup pairing with the
    -- trivial order-`2` character.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ =
          ⟪a4_order_two_character.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 0).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 0).ρ
                a4_order_two_character.toRepresentation
      _ = 0 := by
            have hslot0 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 0).ρ).comp a4_order_two_subgroup.subtype) =
                  (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
                a4_linearCharacterFamily_restrict_order_two_character_eq (eLin 0)
            rw [hsign_char, hslot0]
            exact a4_order_two_character_pairing_trivial_eq_zero
  have hpair1 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ = 0 := by
    -- The second linear slot restricts trivially to the order-`2` subgroup as well.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ =
          ⟪a4_order_two_character.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 1).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 1).ρ
                a4_order_two_character.toRepresentation
      _ = 0 := by
            have hslot1 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 1).ρ).comp a4_order_two_subgroup.subtype) =
                  (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
                a4_linearCharacterFamily_restrict_order_two_character_eq (eLin 1)
            rw [hsign_char, hslot1]
            exact a4_order_two_character_pairing_trivial_eq_zero
  have hpair2 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ = 0 := by
    -- The third linear slot contributes the same vanishing coefficient.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ =
          ⟪a4_order_two_character.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 2).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 2).ρ
                a4_order_two_character.toRepresentation
      _ = 0 := by
            have hslot2 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 2).ρ).comp a4_order_two_subgroup.subtype) =
                  (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
                a4_linearCharacterFamily_restrict_order_two_character_eq (eLin 2)
            rw [hsign_char, hslot2]
            exact a4_order_two_character_pairing_trivial_eq_zero
  have hpair3 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ)⟫ = 2 := by
    -- The nonlinear slot restricts as `1 + 2ε`, so its sign pairing is exactly `2`.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ)⟫ =
          ⟪a4_order_two_character.toRepresentation.character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 3).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 3).ρ
                a4_order_two_character.toRepresentation
      _ = 2 := by
            rw [hsign_char]
            simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
              a4_order_two_character_pairing_augmentation_restriction_eq_two
  have hc0 : c 0 = 0 := by
    have hcoeff0 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 0
    rw [hpair0] at hcoeff0
    have hcoeff0' : ((c 0 : ℤ) : ℂ) = 0 := by
      simpa [c] using hcoeff0.symm
    exact_mod_cast hcoeff0'
  have hc1 : c 1 = 0 := by
    have hcoeff1 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 1
    rw [hpair1] at hcoeff1
    have hcoeff1' : ((c 1 : ℤ) : ℂ) = 0 := by
      simpa [c] using hcoeff1.symm
    exact_mod_cast hcoeff1'
  have hc2 : c 2 = 0 := by
    have hcoeff2 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 2
    rw [hpair2] at hcoeff2
    have hcoeff2' : ((c 2 : ℤ) : ℂ) = 0 := by
      simpa [c] using hcoeff2.symm
    exact_mod_cast hcoeff2'
  have hc3 : c 3 = 2 := by
    have hcoeff3 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 3
    rw [hpair3] at hcoeff3
    have hcoeff3' : ((c 3 : ℤ) : ℂ) = 2 := by
      simpa [c] using hcoeff3.symm
    exact_mod_cast hcoeff3'
  have hx_basis :
      ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) = (x : A4 → ℂ) := by
    -- The induced character is now identified by its coordinates in the irreducible basis.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr x)
  have hslot3_char :
      ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ) = (ψ : A4 → ℂ) := by
    simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
      a4_psi_eq_augmentation_character.symm
  apply Subtype.ext
  calc
    (x : A4 → ℂ) = ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) := by
      simpa using hx_basis.symm
    _ = 2 • ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ) := by
          rw [Fin.sum_univ_four]
          simp [hc0, hc1, hc2, hc3]
    _ = ((2 • ψ : R(A4)) : A4 → ℂ) := by
          rw [hslot3_char]
          rfl

/-- Helper for Exercise 9-9.2-3: the distinguished order-`2` subgroup is one of the cyclic
subgroups used in cyclic induction. -/
private lemma a4_order_two_subgroup_mem_cyclicSubgroups :
    a4_order_two_subgroup ∈ Subgroup.cyclicSubgroups A4 := by
  exact Subgroup.mem_cyclicSubgroups.2 inferInstance

/-- Helper for Exercise 9-9.2-3: the distinguished order-`3` subgroup is one of the cyclic
subgroups used in cyclic induction. -/
private lemma a4_order_three_subgroup_mem_cyclicSubgroups :
    a4_order_three_subgroup ∈ Subgroup.cyclicSubgroups A4 := by
  exact Subgroup.mem_cyclicSubgroups.2 inferInstance

/-- Helper for Exercise 9-9.2-3: inducing the restriction of an ambient linear character from the
distinguished order-`3` subgroup recovers that linear character together with `ψ`. -/
private lemma a4_order_three_induced_restriction_linear_eq_linear_plus_psi
    (ρ : A4 →* ℂˣ) :
    a4_order_three_subgroup.characterRingInduction
        (MonoidHom.toCharacterRing (ρ.comp a4_order_three_subgroup.subtype)) =
      MonoidHom.toCharacterRing ρ + ψ := by
  -- The order-`3` induction formula already supplies an ambient extension; uniqueness on the
  -- distinguished complement shows that extension is exactly the original linear character.
  rcases
      a4_order_three_induced_linear_eq_linear_plus_psi
        (ρ.comp a4_order_three_subgroup.subtype) with
    ⟨ρ', hρ'restrict, hind⟩
  have hρ' : ρ' = ρ := by
    apply a4_linear_character_eq_of_eq_on_order_three_subgroup
    simpa using hρ'restrict
  simpa [hρ'] using hind

/-- Helper for Exercise 9-9.2-3: the generator `2ψ` already lies in the cyclic-induced owner
submodule of `R(A₄)`. -/
private lemma a4_double_psi_mem_cyclicInducedCharacterSubmodule :
    2 • ψ ∈ cyclicInducedCharacterSubmodule A4 := by
  -- Place the distinguished order-`2` induction in the owner submodule, then rewrite it by the
  -- exact character identity already proved above.
  simpa [cyclicInducedCharacterSubmodule, a4_order_two_induced_sign_eq_double_psi] using
    (Representation.characterRingInduction_mem_artinInducedCharacterSubmodule
      (X := Subgroup.cyclicSubgroups A4)
      a4_order_two_subgroup_mem_cyclicSubgroups
      (MonoidHom.toCharacterRing a4_order_two_character))

/-- Helper for Exercise 9-9.2-3: every generator `ρ + ψ` coming from a linear character of `A₄`
already lies in the cyclic-induced owner submodule. -/
private lemma a4_linear_plus_psi_mem_cyclicInducedCharacterSubmodule
    (ρ : A4 →* ℂˣ) :
    MonoidHom.toCharacterRing ρ + ψ ∈ cyclicInducedCharacterSubmodule A4 := by
  -- Use the distinguished order-`3` subgroup as the source cyclic subgroup for Serre's formula.
  simpa [cyclicInducedCharacterSubmodule,
    a4_order_three_induced_restriction_linear_eq_linear_plus_psi ρ] using
    (Representation.characterRingInduction_mem_artinInducedCharacterSubmodule
      (X := Subgroup.cyclicSubgroups A4)
      a4_order_three_subgroup_mem_cyclicSubgroups
      (MonoidHom.toCharacterRing (ρ.comp a4_order_three_subgroup.subtype)))

/-- Helper for Exercise 9-9.2-3: the character of an internal direct sum is the sum of the
characters of its stable summands. -/
private theorem character_eq_sum_of_internal_family_local
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (ρ : Representation ℂ G V) (σ : κ → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i : κ, ((σ i).toRepresentation).character := by
  -- The trace of `ρ g` splits across the internal direct-sum decomposition.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := ℂ) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Exercise 9-9.2-3: an honest finite-dimensional character is a finite nonnegative
integral combination of any fixed complete irreducible family. -/
private theorem fdRep_character_eq_sum_complete_family_with_nat_coefficients_local
    {G : Type} [Group G] [Finite G]
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (W : FDRep ℂ G) :
    ∃ m : ι → ℕ, W.character = ∑ i, (m i : ℂ) • (π i).character := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation W.ρ),
        iSupIndep (fun j ↦ (σ j).toSubmodule) ∧
          (⨆ j, (σ j).toSubmodule) = ⊤ ∧
          ∀ j,
            Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
              ((σ j).toRepresentation) :=
    exists_isInternal_irreducible_subrepresentations (ρ := W.ρ)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (Representation.Equiv (σ j).toRepresentation (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let m : ι → ℕ := fun i ↦ (S i).card
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    -- Distinct complete-family classes cannot share one irreducible summand of `W`.
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii <| ⟨(e.symm.trans e').toFDRepIso⟩
  have hcovered_univ : covered = Finset.univ := by
    -- Completeness sends every irreducible summand to exactly one class in `π`.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hτ_irreducible :
          Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
            ((σ j).toRepresentation) := hσ_irr j
      letI :
          Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
            ((σ j).toRepresentation) := hτ_irreducible
      obtain ⟨i, hi⟩ :=
        Representation.IsCompleteIrreducibleFamily.exists_iso_of_representation
          (π := π) hπ_complete (W := (σ j).toSubmodule) (σ j).toRepresentation inferInstance
      refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
      rcases hi with ⟨e⟩
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact ⟨Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
  have hcovered_raw (g : G) :
      Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) =
        ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  refine ⟨m, ?_⟩
  -- Regroup the irreducible summands by their unique complete-family representative.
  ext g
  have hsum_sigma :
      W.character g = ∑ j : κ, ((σ j).toRepresentation).character g := by
    simpa using
      congrArg (fun χ : G → ℂ ↦ χ g)
        (character_eq_sum_of_internal_family_local (ρ := W.ρ) σ hinternal)
  have hS_sum (i : ι) :
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
        (m i : ℂ) * (π i).character g := by
    calc
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
          Finset.sum (S i) (fun _j ↦ (π i).character g) := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
            simpa using congrArg (fun χ : G → ℂ ↦ χ g) (Representation.char_iso e)
      _ = (S i).card * (π i).character g := by
            simp
      _ = (m i : ℂ) * (π i).character g := by
            simp [m]
  calc
    W.character g = ∑ j : κ, ((σ j).toRepresentation).character g := hsum_sigma
    _ = Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) := by
          simpa [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) :=
          hcovered_raw g
    _ = ∑ i : ι, (m i : ℂ) * (π i).character g := by
          refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
    _ = (∑ i, (m i : ℂ) • (π i).character) g := by
          simp

/-- Helper for Exercise 9-9.2-3: the distinguished order-`2` subgroup has cardinality `2`. -/
private lemma a4_order_two_subgroup_card_two :
    Nat.card a4_order_two_subgroup = 2 := by
  calc
    Nat.card a4_order_two_subgroup = orderOf (a4_v4_y : A4) := by
      simpa [a4_order_two_subgroup] using Nat.card_zpowers (a4_v4_y : A4)
    _ = 2 := a4_order_two_generator_order

/-- Helper for Exercise 9-9.2-3: the distinguished order-`2` subgroup has index `6` in `A₄`. -/
private lemma a4_order_two_subgroup_index_six :
    a4_order_two_subgroup.index = 6 := by
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hmul : a4_order_two_subgroup.index * Nat.card a4_order_two_subgroup = Nat.card A4 := by
    simpa [a4_order_two_subgroup] using a4_order_two_subgroup.index_mul_card
  rw [a4_order_two_subgroup_card_two, hA4] at hmul
  omega

/-- Helper for Exercise 9-9.2-3: the Klein four subgroup has index `3` in `A₄`. -/
private lemma a4_kleinFour_index_three :
    (show Subgroup A4 from V4).index = 3 := by
  simpa using a4_klein_four_index_three

/-- Helper for Exercise 9-9.2-3: the distinguished order-`3` subgroup has cardinality `3`. -/
private lemma a4_order_three_subgroup_card_three :
    Nat.card a4_order_three_subgroup = 3 := by
  simpa [a4_order_three_subgroup, a4_three_cycle_012_order] using
    Nat.card_zpowers a4_three_cycle_012

/-- Helper for Exercise 9-9.2-3: the two irreducible characters of the distinguished order-`2`
subgroup. -/
private def a4_order_two_irreducible_family : Fin 2 → FDRep ℂ a4_order_two_subgroup
  | 0 => FDRep.of (MonoidHom.toRepresentation (1 : a4_order_two_subgroup →* ℂˣ))
  | 1 => FDRep.of a4_order_two_character.toRepresentation

/-- Helper for Exercise 9-9.2-3: the order-`2` irreducible family is pairwise nonisomorphic. -/
private lemma a4_order_two_irreducible_family_pairwise :
    CategoryTheory.PairwiseNonisomorphic a4_order_two_irreducible_family := by
  have htriv :
      (a4_order_two_irreducible_family 0).character a4_order_two_generator = 1 := by
    change (((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character a4_order_two_generator) = 1
    simp [MonoidHom.toRepresentation_character_apply]
  have hsign :
      (a4_order_two_irreducible_family 1).character a4_order_two_generator = (-1 : ℂ) := by
    change ((a4_order_two_character.toRepresentation).character a4_order_two_generator) = -1
    simpa [MonoidHom.toRepresentation_character_apply] using
      congrArg (fun z : ℂˣ => (z : ℂ)) a4_order_two_character_apply_generator
  intro i j hij hiso
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · rcases hiso with ⟨e⟩
    have hval := congrFun (FDRep.char_iso e) a4_order_two_generator
    have hleft :
        (a4_order_two_irreducible_family ((fun i ↦ i) ⟨0, by decide⟩)).character
          a4_order_two_generator = 1 := by
      simpa using htriv
    have hright :
        (a4_order_two_irreducible_family ((fun i ↦ i) ⟨1, by decide⟩)).character
          a4_order_two_generator = (-1 : ℂ) := by
      simpa using hsign
    have : (1 : ℂ) = -1 := by
      calc
        (1 : ℂ) =
            (a4_order_two_irreducible_family ((fun i ↦ i) ⟨0, by decide⟩)).character
              a4_order_two_generator := hleft.symm
        _ =
            (a4_order_two_irreducible_family ((fun i ↦ i) ⟨1, by decide⟩)).character
              a4_order_two_generator := hval
        _ = (-1 : ℂ) := hright
    norm_num at this
  · rcases hiso with ⟨e⟩
    have hval := congrFun (FDRep.char_iso e) a4_order_two_generator
    have hleft :
        (a4_order_two_irreducible_family ((fun i ↦ i) ⟨1, by decide⟩)).character
          a4_order_two_generator = (-1 : ℂ) := by
      simpa using hsign
    have hright :
        (a4_order_two_irreducible_family ((fun i ↦ i) ⟨0, by decide⟩)).character
          a4_order_two_generator = 1 := by
      simpa using htriv
    have : (-1 : ℂ) = 1 := by
      calc
        (-1 : ℂ) =
            (a4_order_two_irreducible_family ((fun i ↦ i) ⟨1, by decide⟩)).character
              a4_order_two_generator := hleft.symm
        _ =
            (a4_order_two_irreducible_family ((fun i ↦ i) ⟨0, by decide⟩)).character
              a4_order_two_generator := hval
        _ = (1 : ℂ) := hright
    norm_num at this
  · exact (hij rfl).elim

/-- Helper for Exercise 9-9.2-3: the two degree-`1` representations already form the complete
irreducible family of the distinguished order-`2` subgroup. -/
private lemma a4_order_two_irreducible_family_degree_sum :
    Finset.sum (@Finset.univ (Fin 2) Representation.instFintype_serre)
      (fun i : Fin 2 ↦ Module.finrank ℂ (a4_order_two_irreducible_family i).V ^ 2) = 2 := by
  -- Both order-`2` constituents are linear, so the square-degree sum is `1^2 + 1^2`.
  have hdeg :
      ∀ i : Fin 2,
        Module.finrank ℂ (a4_order_two_irreducible_family i).V ^ 2 =
          (match i with
          | 0 => 1
          | 1 => 1) ^ 2 := by
    intro i
    fin_cases i
    · change Module.finrank ℂ ℂ ^ 2 = 1 ^ 2
      rw [Module.finrank_self]
    · change Module.finrank ℂ ℂ ^ 2 = 1 ^ 2
      rw [Module.finrank_self]
  simp_rw [hdeg]
  have huniv :
      (@Finset.univ (Fin 2) Representation.instFintype_serre) =
        (@Finset.univ (Fin 2) (Fin.fintype 2)) := by
    ext x
    simp
  rw [huniv]
  decide

/-- Helper for Exercise 9-9.2-3: the two degree-`1` representations already form the complete
irreducible family of the distinguished order-`2` subgroup. -/
private lemma a4_order_two_irreducible_family_complete :
    IsCompleteIrreducibleFamily a4_order_two_irreducible_family := by
  letI : NeZero (Nat.card a4_order_two_subgroup : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hsimple :
      ∀ i : Fin 2, CategoryTheory.Simple (a4_order_two_irreducible_family i) := by
    intro i
    fin_cases i
    · have hirr : Representation.IsIrreducible (a4_order_two_irreducible_family 0).ρ := by
        simpa [a4_order_two_irreducible_family] using
          (MonoidHom.toRepresentation_isIrreducible (1 : a4_order_two_subgroup →* ℂˣ))
      letI : Representation.IsIrreducible (a4_order_two_irreducible_family 0).ρ := hirr
      exact FDRep.simple_of_isIrreducible (a4_order_two_irreducible_family 0)
    · have hirr : Representation.IsIrreducible (a4_order_two_irreducible_family 1).ρ := by
        simpa [a4_order_two_irreducible_family] using
          (MonoidHom.toRepresentation_isIrreducible a4_order_two_character)
      letI : Representation.IsIrreducible (a4_order_two_irreducible_family 1).ρ := hirr
      exact FDRep.simple_of_isIrreducible (a4_order_two_irreducible_family 1)
  refine
    Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      (π := a4_order_two_irreducible_family)
      hsimple a4_order_two_irreducible_family_pairwise ?_
  -- Route correction: isolate the local `Fin 2` square-degree computation before applying the
  -- complete-family criterion, so the competing `Fintype` instances never leak into the main proof.
  rw [a4_order_two_subgroup_card_two]
  exact a4_order_two_irreducible_family_degree_sum

/-- Helper for Exercise 9-9.2-3: every honest character of the distinguished order-`2` subgroup
is a nonnegative integral combination of the trivial and sign characters. -/
private lemma a4_order_two_character_eq_nat_trivial_add_sign
    (W : FDRep ℂ a4_order_two_subgroup) :
    ∃ m n : ℕ,
      (W.character : a4_order_two_subgroup → ℂ) =
        (m : ℂ) • (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) +
          (n : ℂ) •
            (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
              a4_order_two_subgroup → ℂ)) := by
  rcases
      fdRep_character_eq_sum_complete_family_with_nat_coefficients_local
        (π := a4_order_two_irreducible_family)
        a4_order_two_irreducible_family_pairwise
        a4_order_two_irreducible_family_complete W with
    ⟨m, hm⟩
  have htriv_char :
      (a4_order_two_irreducible_family 0).character =
        (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
    ext h
    change (((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character h) =
      ((((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) h)
    simp [MonoidHom.toRepresentation_character_apply, MonoidHom.toCharacterRing_apply]
  have hsign_char :
      (a4_order_two_irreducible_family 1).character =
        (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
          a4_order_two_subgroup → ℂ)) := by
    ext h
    change ((a4_order_two_character.toRepresentation).character h) =
      ((((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
          a4_order_two_subgroup → ℂ) h))
    simp [MonoidHom.toRepresentation_character_apply, MonoidHom.toCharacterRing_apply]
  refine ⟨m 0, m 1, ?_⟩
  -- Expand the complete-family decomposition across the two explicit order-`2` constituents.
  calc
    W.character =
        (m 0 : ℂ) • (a4_order_two_irreducible_family 0).character +
          (m 1 : ℂ) • (a4_order_two_irreducible_family 1).character := by
            simpa [Fin.sum_univ_two] using hm
    _ =
        (m 0 : ℂ) • (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) +
          (m 1 : ℂ) •
            (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
              a4_order_two_subgroup → ℂ)) := by
            rw [htriv_char, hsign_char]

/-- Helper for Exercise 9-9.2-3: the distinguished order-`3` subgroup linear characters obtained
from the quotient family. -/
private abbrev a4_order_three_irreducible_family
    (χ : a4_linearCharacters) : FDRep ℂ a4_order_three_subgroup :=
  FDRep.of (((χ.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype).toRepresentation)

/-- Helper for Exercise 9-9.2-3: distinct quotient linear characters remain nonisomorphic after
restriction to the distinguished order-`3` subgroup. -/
private lemma a4_order_three_irreducible_family_pairwise :
    CategoryTheory.PairwiseNonisomorphic a4_order_three_irreducible_family := by
  intro χ χ' hχχ' hiso
  rcases hiso with ⟨e⟩
  have hchar :
      Representation.character (a4_order_three_irreducible_family χ).ρ =
        Representation.character (a4_order_three_irreducible_family χ').ρ := by
    exact FDRep.char_iso e
  have hrestrict :
      (χ.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype =
        (χ'.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype := by
    ext h
    simpa [a4_order_three_irreducible_family, MonoidHom.toRepresentation_character_apply] using
      congrFun hchar h
  have hpullback :
      χ.comp (QuotientGroup.mk' V4) = χ'.comp (QuotientGroup.mk' V4) :=
    a4_linear_character_eq_of_eq_on_order_three_subgroup hrestrict
  exact hχχ' (a4_quotient_linear_character_eq_of_pullback_eq hpullback)

/-- Helper for Exercise 9-9.2-3: the restricted quotient linear characters form the complete
irreducible family of the distinguished order-`3` subgroup. -/
private lemma a4_order_three_irreducible_family_complete :
    IsCompleteIrreducibleFamily a4_order_three_irreducible_family := by
  letI : NeZero (Nat.card a4_order_three_subgroup : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hsimple :
      ∀ χ : a4_linearCharacters, CategoryTheory.Simple (a4_order_three_irreducible_family χ) := by
    intro χ
    have hirr : Representation.IsIrreducible (a4_order_three_irreducible_family χ).ρ := by
      simpa [a4_order_three_irreducible_family] using
        (MonoidHom.toRepresentation_isIrreducible
          ((χ.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype))
    letI : Representation.IsIrreducible (a4_order_three_irreducible_family χ).ρ := hirr
    exact FDRep.simple_of_isIrreducible (a4_order_three_irreducible_family χ)
  refine
    Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      (π := a4_order_three_irreducible_family)
      hsimple a4_order_three_irreducible_family_pairwise ?_
  -- The three restricted quotient characters are linear, so the square-degree sum is `3 = |C₃|`.
  have hsum :
      ∑ χ : a4_linearCharacters, Module.finrank ℂ (a4_order_three_irreducible_family χ).V ^ 2 =
        Fintype.card a4_linearCharacters := by
    simp [a4_order_three_irreducible_family]
  rw [hsum, ← Nat.card_eq_fintype_card, a4_linearCharacters_card, a4_order_three_subgroup_card_three]

/-- Helper for Exercise 9-9.2-3: every honest character of the distinguished order-`3` subgroup
is a nonnegative integral combination of the three restricted quotient linear characters. -/
private lemma a4_order_three_character_eq_nat_sum_linear
    (W : FDRep ℂ a4_order_three_subgroup) :
    ∃ m : a4_linearCharacters → ℕ,
      (W.character : a4_order_three_subgroup → ℂ) =
        ∑ χ : a4_linearCharacters,
          (m χ : ℂ) •
            (((MonoidHom.toCharacterRing
              ((χ.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype) :
                R(a4_order_three_subgroup)) :
              a4_order_three_subgroup → ℂ)) := by
  rcases
      fdRep_character_eq_sum_complete_family_with_nat_coefficients_local
        (π := a4_order_three_irreducible_family)
        a4_order_three_irreducible_family_pairwise
        a4_order_three_irreducible_family_complete W with
    ⟨m, hm⟩
  refine ⟨m, ?_⟩
  -- Unfold the explicit order-`3` family so the decomposition is written in subgroup characters.
  simpa [a4_order_three_irreducible_family] using hm

/-- Helper for Exercise 9-9.2-3: the explicit `Fin 4` family for `A₄` has degrees `1, 1, 1, 3`
at the identity. -/
private lemma a4_explicitFDRepFamily_character_at_one
    (eLin : Fin 3 ≃ a4_linearCharacters) (i : Fin 4) :
    ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) 1 =
      match i with
      | 0 => 1
      | 1 => 1
      | 2 => 1
      | 3 => 3 := by
  fin_cases i <;>
    simp [a4_explicitFDRepFamily, a4_explicitComplexFamily,
      a4_augmentationRepresentation_finrank_three]

-- Helper for Exercise 9-9.2-3: the actual proof of the order-`2` trivial induction identity
-- appears below.
-- The actual proof of the order-`2` trivial induction identity appears below.
/-- Helper for Exercise 9-9.2-3: inducing the trivial character from the Klein four subgroup
produces exactly the three linear constituents of `A₄`. -/
private lemma a4_klein_four_induced_trivial_eq_sum_linear :
    (V4).characterRingInduction (1 : R(V4)) =
      ∑ i : Fin 3,
        MonoidHom.toCharacterRing
          ((((Fintype.equivFinOfCardEq
            (by simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card)).symm i :
              a4_linearCharacters).comp (QuotientGroup.mk' V4))) := by
  classical
  have hcard_lin : Fintype.card a4_linearCharacters = 3 := by
    simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card
  let eLin : Fin 3 ≃ a4_linearCharacters := (Fintype.equivFinOfCardEq hcard_lin).symm
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic (a4_explicitFDRepFamily eLin) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise eLin hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete : IsCompleteIrreducibleFamily (a4_explicitFDRepFamily eLin) :=
    a4_explicit_complex_family_complete eLin
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily eLin) hpairwise hcomplete
  let x : R(A4) := (V4).characterRingInduction (1 : R(V4))
  let c := b.repr x
  have htriv_pair :
      ⟪(((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)),
        (((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ))⟫ = 1 := by
    have htriv_irr : ((1 : V4 →* ℂˣ).toRepresentation).IsIrreducible := by
      simpa using MonoidHom.toRepresentation_isIrreducible (1 : V4 →* ℂˣ)
    letI : ((1 : V4 →* ℂˣ).toRepresentation).IsIrreducible := htriv_irr
    have hself :
        Nonempty (((1 : V4 →* ℂˣ).toRepresentation).Equiv ((1 : V4 →* ℂˣ).toRepresentation)) :=
      ⟨Representation.Equiv.refl _⟩
    simpa [MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply,
      Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (Representation.char_orthonormal
        (ρ := (1 : V4 →* ℂˣ).toRepresentation)
        (σ := (1 : V4 →* ℂˣ).toRepresentation))
  have hx_character :
      (x : A4 → ℂ) =
        (ind (Subgroup.subtype V4) ((1 : V4 →* ℂˣ).toRepresentation)).character := by
    -- Route correction: rewrite the induced class function through the honest induced trivial
    -- representation before extracting basis coefficients.
    have htrivfun :
        (((1 : R(V4)) : V4 → ℂ)) = ((1 : V4 →* ℂˣ).toRepresentation).character := by
      ext h
      simp [MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply]
    ext g
    have hleft :
        (x : A4 → ℂ) g =
          Ind[V4](((1 : V4 →* ℂˣ).toRepresentation).character) g := by
      rw [← htrivfun]
      simp [x, Subgroup.characterRingInduction_apply]
    have hind :
        Ind[V4](((1 : V4 →* ℂˣ).toRepresentation).character) g =
          (ind (Subgroup.subtype V4) ((1 : V4 →* ℂˣ).toRepresentation)).character g := by
      simpa using
        congrFun
          (Subgroup.inducedClassFunction_eq_character_ind
            (H := V4) (K := ℂ) ((1 : V4 →* ℂˣ).toRepresentation)) g
    exact hleft.trans hind
  have hslot0 :
      Representation.character
          (((a4_explicitFDRepFamily eLin (0 : Fin 4)).ρ).comp (Subgroup.subtype V4)) =
        (((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)) := by
    -- The first ambient linear constituent restricts trivially to `V₄`.
    ext h
    change
      ((((((eLin 0).comp (QuotientGroup.mk' V4)).comp (Subgroup.subtype V4)).toRepresentation).character
        h)) =
        ((((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ) h))
    rw [MonoidHom.toRepresentation_character_apply, MonoidHom.toCharacterRing_apply]
    simpa using
      congrArg (fun z : ℂˣ => (z : ℂ))
        (a4_linear_character_restrict_kleinFour_eq_one ((eLin 0).comp (QuotientGroup.mk' V4)) h)
  have hslot1 :
      Representation.character
          (((a4_explicitFDRepFamily eLin (1 : Fin 4)).ρ).comp (Subgroup.subtype V4)) =
        (((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)) := by
    -- The second ambient linear constituent restricts trivially to `V₄` as well.
    ext h
    change
      ((((((eLin 1).comp (QuotientGroup.mk' V4)).comp (Subgroup.subtype V4)).toRepresentation).character
        h)) =
        ((((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ) h))
    rw [MonoidHom.toRepresentation_character_apply, MonoidHom.toCharacterRing_apply]
    simpa using
      congrArg (fun z : ℂˣ => (z : ℂ))
        (a4_linear_character_restrict_kleinFour_eq_one ((eLin 1).comp (QuotientGroup.mk' V4)) h)
  have hslot2 :
      Representation.character
          (((a4_explicitFDRepFamily eLin (2 : Fin 4)).ρ).comp (Subgroup.subtype V4)) =
        (((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)) := by
    -- The third ambient linear constituent gives the same trivial restriction.
    ext h
    change
      ((((((eLin 2).comp (QuotientGroup.mk' V4)).comp (Subgroup.subtype V4)).toRepresentation).character
        h)) =
        ((((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ) h))
    rw [MonoidHom.toRepresentation_character_apply, MonoidHom.toCharacterRing_apply]
    simpa using
      congrArg (fun z : ℂˣ => (z : ℂ))
        (a4_linear_character_restrict_kleinFour_eq_one ((eLin 2).comp (QuotientGroup.mk' V4)) h)
  have hpair0 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ = 1 := by
    -- Frobenius reciprocity reduces the first linear coefficient to the self-pairing of the
    -- trivial Klein-four character.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ =
          ⟪(((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)),
            Representation.character
              (((a4_explicitFDRepFamily eLin 0).ρ).comp (Subgroup.subtype V4))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype V4)
                (a4_explicitFDRepFamily eLin 0).ρ
                ((1 : V4 →* ℂˣ).toRepresentation)
      _ = 1 := by
            rw [hslot0, htriv_pair]
  have hpair1 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ = 1 := by
    -- The second linear slot restricts trivially to `V₄` as well.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ =
          ⟪(((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)),
            Representation.character
              (((a4_explicitFDRepFamily eLin 1).ρ).comp (Subgroup.subtype V4))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype V4)
                (a4_explicitFDRepFamily eLin 1).ρ
                ((1 : V4 →* ℂˣ).toRepresentation)
      _ = 1 := by
            rw [hslot1, htriv_pair]
  have hpair2 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ = 1 := by
    -- The third linear slot gives the same coefficient.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ =
          ⟪(((MonoidHom.toCharacterRing (1 : V4 →* ℂˣ) : R(V4)) : V4 → ℂ)),
            Representation.character
              (((a4_explicitFDRepFamily eLin 2).ρ).comp (Subgroup.subtype V4))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype V4)
                (a4_explicitFDRepFamily eLin 2).ρ
                ((1 : V4 →* ℂˣ).toRepresentation)
      _ = 1 := by
            rw [hslot2, htriv_pair]
  have hc0 : c 0 = 1 := by
    have hcoeff0 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 0
    rw [hpair0] at hcoeff0
    have hcoeff0' : ((c 0 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff0.symm
    exact_mod_cast hcoeff0'
  have hc1 : c 1 = 1 := by
    have hcoeff1 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 1
    rw [hpair1] at hcoeff1
    have hcoeff1' : ((c 1 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff1.symm
    exact_mod_cast hcoeff1'
  have hc2 : c 2 = 1 := by
    have hcoeff2 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 2
    rw [hpair2] at hcoeff2
    have hcoeff2' : ((c 2 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff2.symm
    exact_mod_cast hcoeff2'
  have hx_basis :
      ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) = (x : A4 → ℂ) := by
    -- The complete explicit irreducible family turns the induced character into an integral basis
    -- expansion.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr x)
  have hx_eval :
      (∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ)) 1 = (3 : ℂ) := by
    -- Evaluating at the identity forces the augmentation coefficient to vanish.
    rw [hx_basis]
    simp [x, a4_kleinFour_index_three, Subgroup.characterRingInduction_apply,
      Subgroup.inducedClassFunction_one_eq_index_mul_value]
  have hcoeff_relation :
      c 0 + c 1 + c 2 + 3 * c 3 = 3 := by
    rw [Fin.sum_univ_four, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, Pi.smul_apply, Pi.smul_apply] at hx_eval
    rw [a4_explicitFDRepFamily_character_at_one eLin 0,
      a4_explicitFDRepFamily_character_at_one eLin 1,
      a4_explicitFDRepFamily_character_at_one eLin 2,
      a4_explicitFDRepFamily_character_at_one eLin 3] at hx_eval
    have hx_eval' :
        (((((c 0 : ℤ) * 1 + (c 1 : ℤ) * 1 + (c 2 : ℤ) * 1) + (c 3 : ℤ) * 3 : ℤ) : ℂ)) = 3 := by
      simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hx_eval
    have hcoeff_relation' :
        ((c 0 : ℤ) * 1 + (c 1 : ℤ) * 1 + (c 2 : ℤ) * 1) + (c 3 : ℤ) * 3 = 3 := by
      exact_mod_cast hx_eval'
    simpa [mul_comm] using hcoeff_relation'
  have hc3 : c 3 = 0 := by
    omega
  have hslot0_char :
      ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 0).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 0)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 0)
  have hslot1_char :
      ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 1).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 1)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 1)
  have hslot2_char :
      ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 2).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 2)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 2)
  apply Subtype.ext
  calc
    (x : A4 → ℂ) = ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) := by
      simpa using hx_basis.symm
    _ =
        ∑ i : Fin 3,
          (((MonoidHom.toCharacterRing
            ((eLin i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
            rw [Fin.sum_univ_four, Fin.sum_univ_three]
            simp [hc0, hc1, hc2, hc3, hslot0_char, hslot1_char, hslot2_char]
    _ =
        (((∑ i : Fin 3,
            MonoidHom.toCharacterRing
              ((eLin i).comp (QuotientGroup.mk' V4)) : R(A4)) : R(A4)) : A4 → ℂ) := by
          simp
    _ =
        (((∑ i : Fin 3,
            MonoidHom.toCharacterRing
              ((((Fintype.equivFinOfCardEq
                  (by simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card)).symm i :
                    a4_linearCharacters).comp (QuotientGroup.mk' V4))) : R(A4)) : R(A4)) :
          A4 → ℂ) := by
            simp [eLin, hcard_lin]

/-- Helper for Exercise 9-9.2-3: inducing the trivial character from the trivial subgroup
produces the Klein-four trivial induction together with an additional `2ψ`. -/
private lemma a4_bot_induced_trivial_eq_generator_sum :
    (⊥ : Subgroup A4).characterRingInduction (1 : R((⊥ : Subgroup A4))) =
      ((V4).characterRingInduction (1 : R(V4)) + ψ) + (2 • ψ) := by
  classical
  have hcard_lin : Fintype.card a4_linearCharacters = 3 := by
    simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card
  let eLin : Fin 3 ≃ a4_linearCharacters := (Fintype.equivFinOfCardEq hcard_lin).symm
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic (a4_explicitFDRepFamily eLin) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise eLin hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete : IsCompleteIrreducibleFamily (a4_explicitFDRepFamily eLin) :=
    a4_explicit_complex_family_complete eLin
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily eLin) hpairwise hcomplete
  let x : R(A4) := (⊥ : Subgroup A4).characterRingInduction (1 : R((⊥ : Subgroup A4)))
  let c := b.repr x
  have htriv_char :
      ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character =
        (((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ)) := by
    ext h
    simp [MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply]
  have hx_character :
      (x : A4 → ℂ) =
        (ind (Subgroup.subtype (⊥ : Subgroup A4))
          ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)).character := by
    -- Rewrite the induced trivial class function through the honest induced representation.
    ext g
    have hleft :
        (x : A4 → ℂ) g =
          Ind[(⊥ : Subgroup A4)]((((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character)) g := by
      dsimp [x]
      change
        Ind[(⊥ : Subgroup A4)]((((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ))) g =
          Ind[(⊥ : Subgroup A4)]((((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character)) g
      rw [htriv_char.symm]
    have hind :
        Ind[(⊥ : Subgroup A4)]((((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character)) g =
          (ind (Subgroup.subtype (⊥ : Subgroup A4))
            ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)).character g := by
      simpa using
        congrFun
          (Subgroup.inducedClassFunction_eq_character_ind
            (H := (⊥ : Subgroup A4)) (K := ℂ)
            ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)) g
    exact hleft.trans hind
  have hbot_trivial_pair :
      ⟪(((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ)),
        (((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ))⟫ = 1 := by
    have hself :
        Nonempty (((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).Equiv
          ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)) :=
      ⟨Representation.Equiv.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
      MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply, hself] using
      (Representation.char_orthonormal
        (ρ := ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation))
        (σ := ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)))
  have hpair_eval (i : Fin 4) :
      ⟪(((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ)),
        Representation.character (((a4_explicitFDRepFamily eLin i).ρ).comp
          (Subgroup.subtype (⊥ : Subgroup A4)))⟫ =
        (match i with
        | 0 => 1
        | 1 => 1
        | 2 => 1
        | 3 => 3) := by
    have hrestrict :
        Representation.character (((a4_explicitFDRepFamily eLin i).ρ).comp
            (Subgroup.subtype (⊥ : Subgroup A4))) =
          ((match i with
            | 0 => 1
            | 1 => 1
            | 2 => 1
            | 3 => 3 : ℂ)) •
            (((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ)) := by
      ext h
      have hh : h = 1 := Subsingleton.elim _ _
      subst hh
      simpa [MonoidHom.toCharacterRing_apply] using a4_explicitFDRepFamily_character_at_one eLin i
    rw [hrestrict, Representation.groupFunctionPairing_smul_right, hbot_trivial_pair]
    simp
  have hpair0 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ = 1 := by
    -- Frobenius reciprocity reduces the first coefficient to the degree of the first basis slot.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ =
          ⟪((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 0).ρ).comp
                (Subgroup.subtype (⊥ : Subgroup A4)))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype (⊥ : Subgroup A4))
                (a4_explicitFDRepFamily eLin 0).ρ
                ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)
      _ = 1 := by
            rw [htriv_char]
            simpa using hpair_eval 0
  have hpair1 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ = 1 := by
    -- The second linear slot has the same degree-one restriction to the trivial subgroup.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ =
          ⟪((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 1).ρ).comp
                (Subgroup.subtype (⊥ : Subgroup A4)))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype (⊥ : Subgroup A4))
                (a4_explicitFDRepFamily eLin 1).ρ
                ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)
      _ = 1 := by
            rw [htriv_char]
            simpa using hpair_eval 1
  have hpair2 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ = 1 := by
    -- The third linear slot again contributes degree `1`.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ =
          ⟪((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 2).ρ).comp
                (Subgroup.subtype (⊥ : Subgroup A4)))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype (⊥ : Subgroup A4))
                (a4_explicitFDRepFamily eLin 2).ρ
                ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)
      _ = 1 := by
            rw [htriv_char]
            simpa using hpair_eval 2
  have hpair3 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ)⟫ = 3 := by
    -- The augmentation slot contributes its degree `3`.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ)⟫ =
          ⟪((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation).character,
            Representation.character
              (((a4_explicitFDRepFamily eLin 3).ρ).comp
                (Subgroup.subtype (⊥ : Subgroup A4)))⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                (Subgroup.subtype (⊥ : Subgroup A4))
                (a4_explicitFDRepFamily eLin 3).ρ
                ((1 : (⊥ : Subgroup A4) →* ℂˣ).toRepresentation)
      _ = 3 := by
            rw [htriv_char]
            simpa using hpair_eval 3
  have hc0 : c 0 = 1 := by
    have hcoeff0 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 0
    rw [hpair0] at hcoeff0
    have hcoeff0' : ((c 0 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff0.symm
    exact_mod_cast hcoeff0'
  have hc1 : c 1 = 1 := by
    have hcoeff1 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 1
    rw [hpair1] at hcoeff1
    have hcoeff1' : ((c 1 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff1.symm
    exact_mod_cast hcoeff1'
  have hc2 : c 2 = 1 := by
    have hcoeff2 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 2
    rw [hpair2] at hcoeff2
    have hcoeff2' : ((c 2 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff2.symm
    exact_mod_cast hcoeff2'
  have hc3 : c 3 = 3 := by
    have hcoeff3 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 3
    rw [hpair3] at hcoeff3
    have hcoeff3' : ((c 3 : ℤ) : ℂ) = 3 := by
      simpa [c] using hcoeff3.symm
    exact_mod_cast hcoeff3'
  have hx_basis :
      ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) = (x : A4 → ℂ) := by
    -- The regular character of `A₄` is determined by its coordinates in the explicit basis.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr x)
  have hslot0_char :
      ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 0).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 0)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 0)
  have hslot1_char :
      ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 1).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 1)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 1)
  have hslot2_char :
      ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 2).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 2)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 2)
  have hslot3_char :
      ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ) = (ψ : A4 → ℂ) := by
    simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
      a4_psi_eq_augmentation_character.symm
  have hsum_linear :
      (∑ i : Fin 3,
        (((MonoidHom.toCharacterRing
            ((eLin i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ))) =
        ((((V4).characterRingInduction (1 : R(V4)) : R(A4)) : A4 → ℂ)) := by
    simpa [eLin, hcard_lin] using
      congrArg (fun χ : R(A4) ↦ (χ : A4 → ℂ))
        a4_klein_four_induced_trivial_eq_sum_linear.symm
  have hthree_psi :
      ((3 : ℤ) • ψ : R(A4)) = ψ + (2 • ψ : R(A4)) := by
    abel
  apply Subtype.ext
  calc
    (x : A4 → ℂ) = ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) := by
      simpa using hx_basis.symm
    _ =
        (∑ i : Fin 3,
          (((MonoidHom.toCharacterRing
              ((eLin i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ))) +
          (3 : ℤ) • (ψ : A4 → ℂ) := by
            rw [Fin.sum_univ_four, Fin.sum_univ_three]
            simp [hc0, hc1, hc2, hc3, hslot0_char, hslot1_char, hslot2_char, hslot3_char]
    _ =
        ((((V4).characterRingInduction (1 : R(V4)) : R(A4)) : A4 → ℂ)) +
          (3 : ℤ) • (ψ : A4 → ℂ) := by
            rw [hsum_linear]
    _ =
        (((((V4).characterRingInduction (1 : R(V4)) : R(A4)) + ((3 : ℤ) • ψ : R(A4)) :
          R(A4)) : A4 → ℂ)) := by
            rfl
    _ =
        ((((V4).characterRingInduction (1 : R(V4)) + (ψ + (2 • ψ : R(A4))) : R(A4)) :
          A4 → ℂ)) := by
            rw [hthree_psi]
    _ =
        ((((V4).characterRingInduction (1 : R(V4)) + ψ) + (2 • ψ) : R(A4)) :
          A4 → ℂ) := by
            simp [add_assoc]

private lemma a4_order_two_induced_trivial_eq_kleinFour_trivial_plus_psi :
    a4_order_two_subgroup.characterRingInduction (1 : R(a4_order_two_subgroup)) =
      (V4).characterRingInduction (1 : R(V4)) + ψ := by
  classical
  have hcard_lin : Fintype.card a4_linearCharacters = 3 := by
    simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card
  let eLin : Fin 3 ≃ a4_linearCharacters := (Fintype.equivFinOfCardEq hcard_lin).symm
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic (a4_explicitFDRepFamily eLin) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise eLin hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete : IsCompleteIrreducibleFamily (a4_explicitFDRepFamily eLin) :=
    a4_explicit_complex_family_complete eLin
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily eLin) hpairwise hcomplete
  let x : R(A4) := a4_order_two_subgroup.characterRingInduction (1 : R(a4_order_two_subgroup))
  let c := b.repr x
  have htriv_char :
      ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character =
        (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
    ext h
    simp [MonoidHom.toCharacterRing_apply, MonoidHom.toRepresentation_character_apply]
  have htriv_pair :
      ⟪(((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)),
        (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))⟫ = 1 := by
    calc
      ⟪(((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)),
        (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))⟫ =
          ⟪(((MonoidHom.toCharacterRing (1 : a4_order_two_subgroup →* ℂˣ) :
                R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)),
            (((MonoidHom.toCharacterRing (1 : a4_order_two_subgroup →* ℂˣ) :
                R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))⟫ := by
            congr 2 <;> ext h <;> simp [MonoidHom.toCharacterRing_apply]
      _ = 1 := by
            rw [a4_order_two_subgroup_linear_pairing_eq_ite 1 1]
            simp
  have htriv_sign_pair :
      ⟪(((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)),
        (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
          a4_order_two_subgroup → ℂ))⟫ = 0 := by
    calc
      ⟪(((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)),
        (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
          a4_order_two_subgroup → ℂ))⟫ =
          ⟪(((MonoidHom.toCharacterRing (1 : a4_order_two_subgroup →* ℂˣ) :
                R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)),
            (((MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) :
              a4_order_two_subgroup → ℂ))⟫ := by
            congr 1
            ext s
            simp [MonoidHom.toCharacterRing_apply]
      _ = 0 := by
            have hne : (1 : a4_order_two_subgroup →* ℂˣ) ≠ a4_order_two_character := by
              intro hEq
              have hgen := congrArg (fun f : a4_order_two_subgroup →* ℂˣ =>
                (f a4_order_two_generator : ℂ)) hEq
              simp [a4_order_two_character_apply_generator] at hgen
              norm_num at hgen
            rw [a4_order_two_subgroup_linear_pairing_eq_ite (1 : a4_order_two_subgroup →* ℂˣ)
              a4_order_two_character]
            simp [hne]
  have hx_character :
      (x : A4 → ℂ) =
        (ind a4_order_two_subgroup.subtype
          ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)).character := by
    -- Rewrite the trivial cyclic induction through the honest induced representation.
    ext g
    have hleft :
        (x : A4 → ℂ) g =
          Ind[a4_order_two_subgroup]((((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character)) g := by
      dsimp [x]
      change
        Ind[a4_order_two_subgroup]((((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))) g =
          Ind[a4_order_two_subgroup]((((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character)) g
      rw [htriv_char.symm]
    have hind :
        Ind[a4_order_two_subgroup]((((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character)) g =
          (ind a4_order_two_subgroup.subtype
            ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)).character g := by
      simpa using
        congrFun
          (Subgroup.inducedClassFunction_eq_character_ind
            (H := a4_order_two_subgroup) (K := ℂ)
            ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)) g
    exact hleft.trans hind
  have hpair0 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ = 1 := by
    -- Every linear ambient character restricts trivially to the chosen order-`2` subgroup.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ)⟫ =
          ⟪((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation.character),
            Representation.character
              (((a4_explicitFDRepFamily eLin 0).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 0).ρ
                ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)
      _ = 1 := by
            have hslot0 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 0).ρ).comp a4_order_two_subgroup.subtype) =
                  (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
                a4_linearCharacterFamily_restrict_order_two_character_eq (eLin 0)
            rw [hslot0, htriv_char, htriv_pair]
  have hpair1 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ = 1 := by
    -- The second linear slot has the same trivial restriction.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ)⟫ =
          ⟪((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation.character),
            Representation.character
              (((a4_explicitFDRepFamily eLin 1).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 1).ρ
                ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)
      _ = 1 := by
            have hslot1 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 1).ρ).comp a4_order_two_subgroup.subtype) =
                  (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
                a4_linearCharacterFamily_restrict_order_two_character_eq (eLin 1)
            rw [hslot1, htriv_char, htriv_pair]
  have hpair2 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ = 1 := by
    -- The third linear slot again pairs as the subgroup trivial character.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ)⟫ =
          ⟪((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation.character),
            Representation.character
              (((a4_explicitFDRepFamily eLin 2).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 2).ρ
                ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)
      _ = 1 := by
            have hslot2 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 2).ρ).comp a4_order_two_subgroup.subtype) =
                  (((1 : R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ)) := by
              simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
                a4_linearCharacterFamily_restrict_order_two_character_eq (eLin 2)
            rw [hslot2, htriv_char, htriv_pair]
  have hpair3 :
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ)⟫ = 1 := by
    -- The nonlinear slot restricts as `1 + 2ε`, and only the trivial summand contributes.
    calc
      ⟪(x : A4 → ℂ), ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ)⟫ =
          ⟪((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation.character),
            Representation.character
              (((a4_explicitFDRepFamily eLin 3).ρ).comp a4_order_two_subgroup.subtype)⟫ := by
            rw [hx_character]
            symm
            exact
              groupFunctionPairing_character_comp_eq_character_ind_local
                a4_order_two_subgroup.subtype
                (a4_explicitFDRepFamily eLin 3).ρ
                ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)
      _ = 1 := by
            have hslot3 :
                Representation.character
                    (((a4_explicitFDRepFamily eLin 3).ρ).comp a4_order_two_subgroup.subtype) =
                  Representation.character
                    (a4_augmentationRepresentation.comp a4_order_two_subgroup.subtype) := by
              rfl
            have hrestrict :=
              (a4_order_two_subgroup_restriction_table (1 : A4 →* ℂˣ)).2
            have htwo :
                (2 • (((MonoidHom.toCharacterRing a4_order_two_character :
                    R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))) =
                  ((2 : ℂ) •
                    (((MonoidHom.toCharacterRing a4_order_two_character :
                        R(a4_order_two_subgroup)) : a4_order_two_subgroup → ℂ))) := by
              ext s
              simp [two_nsmul, smul_eq_mul]
            rw [htriv_char, hslot3, hrestrict, Representation.groupFunctionPairing_add_right, htwo,
              Representation.groupFunctionPairing_smul_right, htriv_pair, htriv_sign_pair]
            simp
  have hc0 : c 0 = 1 := by
    have hcoeff0 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 0
    rw [hpair0] at hcoeff0
    have hcoeff0' : ((c 0 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff0.symm
    exact_mod_cast hcoeff0'
  have hc1 : c 1 = 1 := by
    have hcoeff1 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 1
    rw [hpair1] at hcoeff1
    have hcoeff1' : ((c 1 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff1.symm
    exact_mod_cast hcoeff1'
  have hc2 : c 2 = 1 := by
    have hcoeff2 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 2
    rw [hpair2] at hcoeff2
    have hcoeff2' : ((c 2 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff2.symm
    exact_mod_cast hcoeff2'
  have hc3 : c 3 = 1 := by
    have hcoeff3 :=
      basis_coefficient_pairing_eq
        (π := a4_explicitFDRepFamily eLin) hpairwise hcomplete x 3
    rw [hpair3] at hcoeff3
    have hcoeff3' : ((c 3 : ℤ) : ℂ) = 1 := by
      simpa [c] using hcoeff3.symm
    exact_mod_cast hcoeff3'
  have hx_basis :
      ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) = (x : A4 → ℂ) := by
    -- The explicit irreducible basis turns the induction formula into an integral coefficient
    -- computation.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr x)
  have hslot0_char :
      ((a4_explicitFDRepFamily eLin 0).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 0).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 0)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 0)
  have hslot1_char :
      ((a4_explicitFDRepFamily eLin 1).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 1).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 1)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 1)
  have hslot2_char :
      ((a4_explicitFDRepFamily eLin 2).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((eLin 2).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (eLin 2)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (eLin 2)
  have hslot3_char :
      ((a4_explicitFDRepFamily eLin 3).character : A4 → ℂ) = (ψ : A4 → ℂ) := by
    simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
      a4_psi_eq_augmentation_character.symm
  have hsum_linear :
      (∑ i : Fin 3,
        (((MonoidHom.toCharacterRing
            ((eLin i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ))) =
        ((((V4).characterRingInduction (1 : R(V4)) : R(A4)) : A4 → ℂ)) := by
    simpa [eLin, hcard_lin] using
      congrArg (fun χ : R(A4) ↦ (χ : A4 → ℂ))
        a4_klein_four_induced_trivial_eq_sum_linear.symm
  apply Subtype.ext
  calc
    (x : A4 → ℂ) = ∑ i, c i • ((a4_explicitFDRepFamily eLin i).character : A4 → ℂ) := by
      simpa using hx_basis.symm
    _ =
        ∑ i : Fin 3,
          (((MonoidHom.toCharacterRing
              ((eLin i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) +
          (ψ : A4 → ℂ) := by
            rw [Fin.sum_univ_four, Fin.sum_univ_three]
            simp [hc0, hc1, hc2, hc3, hslot0_char, hslot1_char, hslot2_char, hslot3_char]
    _ =
        ((((V4).characterRingInduction (1 : R(V4)) : R(A4)) : A4 → ℂ)) +
          (ψ : A4 → ℂ) := by
            rw [hsum_linear]
    _ =
        (((V4).characterRingInduction (1 : R(V4)) + ψ : R(A4)) : A4 → ℂ) := by
            rfl
/-- Helper for Exercise 9-9.2-3: fix an enumeration of the three linear characters of `A₄`. -/
private abbrev a4_linearCharacterEquiv : Fin 3 ≃ a4_linearCharacters :=
  (Fintype.equivFinOfCardEq
    (by simpa [Nat.card_eq_fintype_card] using a4_linearCharacters_card)).symm

/-- Helper for Exercise 9-9.2-3: reindex the order-`3` subgroup character decomposition along the
chosen `Fin 3` enumeration of the ambient linear characters. -/
private lemma a4_order_three_character_eq_nat_sum_linear_fin
    (W : FDRep ℂ a4_order_three_subgroup) :
    ∃ z : Fin 3 → ℕ,
      (⟨W.character, rep_character_mem_characterRing (Rep.of W.ρ)⟩ :
          R(a4_order_three_subgroup)) =
        ∑ i : Fin 3,
          z i •
            (MonoidHom.toCharacterRing
              (((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)).comp
                a4_order_three_subgroup.subtype) : R(a4_order_three_subgroup)) := by
  rcases a4_order_three_character_eq_nat_sum_linear W with ⟨m, hm⟩
  refine ⟨fun i ↦ m (a4_linearCharacterEquiv i), ?_⟩
  apply Subtype.ext
  ext h
  -- Evaluate the subgroup character decomposition pointwise before reindexing it along `Fin 3`.
  calc
    (((⟨W.character, rep_character_mem_characterRing (Rep.of W.ρ)⟩ :
        R(a4_order_three_subgroup)) : a4_order_three_subgroup → ℂ) h) = W.character h := rfl
    _ =
        ∑ χ : a4_linearCharacters,
          (m χ : ℂ) *
            (((MonoidHom.toCharacterRing
              ((χ.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype) :
                R(a4_order_three_subgroup)) :
              a4_order_three_subgroup → ℂ) h) := by
          simpa using congrFun hm h
    _ =
        ∑ i : Fin 3,
          (m (a4_linearCharacterEquiv i) : ℂ) *
            (((MonoidHom.toCharacterRing
              (((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)).comp
                a4_order_three_subgroup.subtype) :
                R(a4_order_three_subgroup)) :
              a4_order_three_subgroup → ℂ) h) := by
          exact
            Fintype.sum_equiv a4_linearCharacterEquiv.symm
              (fun χ : a4_linearCharacters ↦
                (m χ : ℂ) *
                  (((MonoidHom.toCharacterRing
                    ((χ.comp (QuotientGroup.mk' V4)).comp a4_order_three_subgroup.subtype) :
                      R(a4_order_three_subgroup)) :
                    a4_order_three_subgroup → ℂ) h))
              (fun i : Fin 3 ↦
                (m (a4_linearCharacterEquiv i) : ℂ) *
                  (((MonoidHom.toCharacterRing
                    (((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)).comp
                      a4_order_three_subgroup.subtype) :
                      R(a4_order_three_subgroup)) :
                    a4_order_three_subgroup → ℂ) h))
              (fun χ ↦ by simp)
    _ =
        (((∑ i : Fin 3,
            m (a4_linearCharacterEquiv i) •
              (MonoidHom.toCharacterRing
                (((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)).comp
                  a4_order_three_subgroup.subtype) : R(a4_order_three_subgroup))) :
          R(a4_order_three_subgroup)) : a4_order_three_subgroup → ℂ) h := by
          -- Convert natural multiples in the subgroup character ring into scalar multiples of
          -- class functions.
          simp

/-- Helper for Exercise 9-9.2-3: transport an `A₄`-subgroup representation across conjugation. -/
private def a4_conjugateFDRep (H : Subgroup A4) (s : A4) (W : FDRep ℂ H) :
    FDRep ℂ (MulAut.conj s • H : Subgroup A4) :=
  FDRep.of (W.ρ.comp (((MulAut.conj s).subgroupMap H).symm.toMonoidHom))

/-- Helper for Exercise 9-9.2-3: pull back class functions along a subgroup isomorphism. -/
private def a4_classFunctionTransport {H J : Type*} [Group H] [Group J] (e : H ≃* J) :
    _root_.classFunctionSubspace J →ₗ[ℂ] _root_.classFunctionSubspace H :=
  LinearMap.codRestrict (_root_.classFunctionSubspace H)
    (((LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv).toLinearMap).comp
      (_root_.classFunctionSubspace J).subtype)
    (fun χ ↦ by
      refine ⟨?_⟩
      intro x y hxy
      have hχ : _root_.IsClassFunction (χ : J → ℂ) :=
        (_root_.mem_classFunctionSubspace_iff _).1 χ.2
      exact hχ.eq_of_isConj <|
        e.toMonoidHom.map_isConj ((ConjClasses.mk_eq_mk_iff_isConj.1 hxy)))

/-- Helper for Exercise 9-9.2-3: the canonical conjugation transport on subgroup class functions.
-/
private def a4_conjugateClassFunctionTransport (H : Subgroup A4) (s : A4) :
    _root_.classFunctionSubspace H →ₗ[ℂ]
      _root_.classFunctionSubspace (MulAut.conj s • H : Subgroup A4) :=
  a4_classFunctionTransport (((MulAut.conj s).subgroupMap H).symm)

/-- Helper for Exercise 9-9.2-3: evaluating the conjugation transport is composition with the
subgroup conjugation isomorphism. -/
@[simp] private lemma a4_conjugateClassFunctionTransport_apply
    (H : Subgroup A4) (s : A4) (χ : _root_.classFunctionSubspace H)
    (x : (MulAut.conj s • H : Subgroup A4)) :
    (a4_conjugateClassFunctionTransport H s χ : (MulAut.conj s • H : Subgroup A4) → ℂ) x =
      (χ : H → ℂ) (((MulAut.conj s).subgroupMap H).symm x) :=
  rfl

/-- Helper for Exercise 9-9.2-3: the normalized pairing is additive over finite complex linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_smul_left_complex
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (χ : ι → A4 → ℂ) (psiFun : A4 → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, psiFun⟫ = ∑ j ∈ s, a j * ⟪χ j, psiFun⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 9-9.2-3: package the character of a finite-dimensional subgroup
representation as an element of the subgroup character ring. -/
private abbrev a4_fdrepCharacter {H : Subgroup A4} (W : FDRep ℂ H) : R(H) :=
  ⟨W.character, rep_character_mem_characterRing (Rep.of W.ρ)⟩

/-- Helper for Exercise 9-9.2-3: transporting a subgroup representation along an equality of
subgroups does not change the induced character in `R(A₄)`. -/
private lemma a4_characterRingInduction_eq_of_subgroup_eq
    {H K : Subgroup A4} (hHK : H = K) (W : FDRep ℂ H) :
    K.characterRingInduction (a4_fdrepCharacter (hHK ▸ W)) =
      H.characterRingInduction (a4_fdrepCharacter W) := by
  -- After substituting the subgroup equality, the transported representation is definitionally the
  -- original one.
  subst hHK
  rfl

/-- A complex-valued class function on `A₄` is a positive rational combination of cyclically
induced characters if it is a finite positive `ℚ`-linear combination of characters induced from
cyclic subgroups. -/
def a4PositiveRatCombinationOfCyclicInductions (χ : A4 → ℂ) : Prop :=
  ∃ s : Finset (Σ H : Subgroup.cyclicSubgroups A4, FDRep ℂ H.1), ∃ c : s → ℚ,
    (∀ i : s, 0 < c i) ∧
      χ = ∑ i : s,
        match i.1 with
        | ⟨H, W⟩ => (c i : ℂ) • Ind[H.1](W.character)

/-- Helper for Exercise 9-9.2-3: conjugating subgroup data does not change the induced character
in `R(A₄)`. -/
private lemma a4_characterRingInduction_conjugate_eq
    (H : Subgroup A4) (s : A4) (W : FDRep ℂ H) :
    (MulAut.conj s • H).characterRingInduction
        ⟨(a4_conjugateFDRep H s W).character, by
          simpa [a4_conjugateFDRep] using
            rep_character_mem_characterRing (Rep.of (a4_conjugateFDRep H s W).ρ)⟩ =
      H.characterRingInduction
        ⟨W.character, by simpa using rep_character_mem_characterRing (Rep.of W.ρ)⟩ := by
  classical
  let χ : _root_.classFunctionSubspace H :=
    ⟨W.character, by
      refine ⟨?_⟩
      intro x y hxy
      rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, ha⟩
      rw [← ha]
      exact (W.char_conj x a).symm⟩
  have hconj :
      ((((MulAut.conj s • H : Subgroup A4)).classFunctionInduction
        (a4_conjugateClassFunctionTransport H s χ :
          ((MulAut.conj s • H : Subgroup A4) → ℂ))) :
          A4 → ℂ) =
        (H.classFunctionInduction (χ : H → ℂ) : A4 → ℂ) := by
    let _ : DecidablePred fun z : A4 ↦ z ∈ H := Classical.decPred _
    let _ : DecidablePred fun z : A4 ↦ z ∈ (MulAut.conj s • H : Subgroup A4) := Classical.decPred _
    ext g
    have hcard : Nat.card (MulAut.conj s • H : Subgroup A4) = Nat.card H := by
      exact Nat.card_congr (((MulAut.conj s).subgroupMap H).symm.toEquiv)
    rw [Subgroup.classFunctionInduction_apply, Subgroup.classFunctionInduction_apply,
      Subgroup.inducedClassFunction, Subgroup.inducedClassFunction, hcard]
    let e : A4 ≃ A4 := Equiv.mulRight s
    exact congrArg (fun t : ℂ ↦ (↑(Nat.card ↥H) : ℂ)⁻¹ * t) <|
      Fintype.sum_equiv e
        (fun x : A4 ↦
          if hxs : x⁻¹ * g * x ∈ (MulAut.conj s • H : Subgroup A4) then
            (χ : H → ℂ) (((MulAut.conj s).subgroupMap H).symm ⟨x⁻¹ * g * x, hxs⟩)
          else
            0)
        (fun x : A4 ↦
          if hxH : x⁻¹ * g * x ∈ H then
            (χ : H → ℂ) ⟨x⁻¹ * g * x, hxH⟩
          else
            0)
        (fun x ↦ by
          change
            (if hxs : x⁻¹ * g * x ∈ (MulAut.conj s • H : Subgroup A4) then
              (χ : H → ℂ) (((MulAut.conj s).subgroupMap H).symm ⟨x⁻¹ * g * x, hxs⟩)
            else
              0) =
            if hxH : (x * s)⁻¹ * g * (x * s) ∈ H then
              (χ : H → ℂ) ⟨(x * s)⁻¹ * g * (x * s), hxH⟩
            else
              0
          by_cases hxs : x⁻¹ * g * x ∈ (MulAut.conj s • H : Subgroup A4)
          · have hxH : ((x * s) : A4)⁻¹ * g * (x * s) ∈ H := by
              change x⁻¹ * g * x ∈ H.map (MulAut.conj s).toMonoidHom at hxs
              simpa [mul_assoc] using
                (Subgroup.mem_map_equiv (f := MulAut.conj s) (K := H)).1 hxs
            have hsub :
                (((MulAut.conj s).subgroupMap H).symm ⟨x⁻¹ * g * x, hxs⟩ : H) =
                  ⟨(x * s)⁻¹ * g * (x * s), hxH⟩ := by
              apply Subtype.ext
              simp [MulEquiv.subgroupMap_symm_apply, mul_assoc]
            rw [dif_pos hxs, dif_pos hxH]
            simpa using congrArg (fun z : H ↦ (χ : H → ℂ) z) hsub
          · have hxH : ¬ ((x * s) : A4)⁻¹ * g * (x * s) ∈ H := by
              intro hxH
              apply hxs
              change x⁻¹ * g * x ∈ H.map (MulAut.conj s).toMonoidHom
              exact (Subgroup.mem_map_equiv (f := MulAut.conj s) (K := H)).2 <|
                by simpa [mul_assoc] using hxH
            rw [dif_neg hxs, dif_neg hxH])
  apply Subtype.ext
  have htransport_fun :
      (((a4_conjugateFDRep H s W).character) :
          (MulAut.conj s • H : Subgroup A4) → ℂ) =
        (a4_conjugateClassFunctionTransport H s χ :
          (MulAut.conj s • H : Subgroup A4) → ℂ) := by
    ext x
    rfl
  -- Rewrite the left-hand induced character through the transported subgroup class function and
  -- then apply the already proved conjugation invariance for class-function induction.
  simpa [Subgroup.characterRingInduction_apply, χ, htransport_fun] using hconj

/-- Helper for Exercise 9-9.2-3: inverse conjugation transports an induction formula from a
representative cyclic subgroup back to the original subgroup. -/
private lemma a4_characterRingInduction_eq_of_inverse_conjugate
    {H K : Subgroup A4} (s : A4)
    (hback : MulAut.conj s⁻¹ • H = K) (W : FDRep ℂ H) :
    H.characterRingInduction (a4_fdrepCharacter W) =
      K.characterRingInduction
        (a4_fdrepCharacter (hback ▸ a4_conjugateFDRep H s⁻¹ W)) := by
  -- First move the induction formula to the inverse-conjugate subgroup, then rewrite the subgroup
  -- index from that inverse conjugate to the chosen representative.
  calc
    H.characterRingInduction (a4_fdrepCharacter W) =
        (MulAut.conj s⁻¹ • H).characterRingInduction
          (a4_fdrepCharacter (a4_conjugateFDRep H s⁻¹ W)) := by
            symm
            simpa using a4_characterRingInduction_conjugate_eq H s⁻¹ W
    _ =
        K.characterRingInduction
          (a4_fdrepCharacter (hback ▸ a4_conjugateFDRep H s⁻¹ W)) := by
            symm
            exact
              a4_characterRingInduction_eq_of_subgroup_eq hback
                (a4_conjugateFDRep H s⁻¹ W)

/-- Helper for Exercise 9-9.2-3: every representation of the trivial subgroup has constant
character equal to its dimension. -/
private lemma a4_bot_character_eq_nat_trivial
    (W : FDRep ℂ (⊥ : Subgroup A4)) :
    ∃ m : ℕ,
      (W.character : (⊥ : Subgroup A4) → ℂ) =
        (m : ℂ) • (((1 : R((⊥ : Subgroup A4))) : (⊥ : Subgroup A4) → ℂ)) := by
  refine ⟨Module.finrank ℂ W, ?_⟩
  -- The trivial subgroup has one element, so the character is constant at the dimension.
  ext h
  have hh : h = 1 := by
    simpa using (Subsingleton.elim h 1)
  subst hh
  simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Exercise 9-9.2-3: every cyclic subgroup of `A₄` of order `2` is conjugate to the
distinguished order-`2` subgroup. -/
private lemma a4_order_two_cyclic_subgroup_conj_representative
    (H : Subgroup.cyclicSubgroups A4) (hH : Nat.card H.1 = 2) :
    ∃ s : A4, MulAut.conj s • a4_order_two_subgroup = H.1 := by
  have hcyc : IsCyclic H.1 := Subgroup.mem_cyclicSubgroups.1 H.2
  have hP : IsPGroup 2 H.1 := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hH]
    norm_num
  obtain ⟨Q, hHQ⟩ := hP.exists_le_sylow
  have hQV4 : (Q : Subgroup A4) = V4 := by
    simpa using
      alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (α := Fin 4) (by simp) Q
  obtain ⟨g, hg⟩ := H.1.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hgH : g ∈ H.1 := by
    rw [← hg]
    exact Subgroup.mem_zpowers g
  have hgV4 : g ∈ V4 := by
    simpa [hQV4] using hHQ hgH
  let gV4 : V4 := ⟨g, hgV4⟩
  rcases a4_v4_eq_one_or_source gV4 with hg1 | hgx | hgy | hgz
  · have hbot : H.1 = ⊥ := by
      have hg1' : g = 1 := by
        have hg1A4 : (gV4 : A4) = 1 := by
          exact congrArg (fun z : V4 ↦ (z : A4)) hg1
        simpa [gV4] using hg1A4
      calc
        H.1 = Subgroup.zpowers g := hg.symm
        _ = ⊥ := by rw [hg1', Subgroup.zpowers_one_eq_bot]
    exact False.elim <| by simpa [hbot] using hH
  · refine ⟨a4_three_cycle_012, ?_⟩
    have hgx' : g = a4_v4_x := by
      have hgxA4 : (gV4 : A4) = a4_v4_x := by
        exact congrArg (fun z : V4 ↦ (z : A4)) hgx
      simpa [gV4] using hgxA4
    -- Conjugation by the chosen `3`-cycle sends the preferred involution to `x`.
    calc
      MulAut.conj a4_three_cycle_012 • a4_order_two_subgroup
          = Subgroup.zpowers (((MulAut.conj a4_three_cycle_012).toMonoidHom) (a4_v4_y : A4)) := by
              rw [Subgroup.pointwise_smul_def, a4_order_two_subgroup]
              simpa using
                (MonoidHom.map_zpowers ((MulAut.conj a4_three_cycle_012).toMonoidHom)
                  (a4_v4_y : A4))
      _ = Subgroup.zpowers (a4_v4_x : A4) := by
            rcases a4_three_cycle_conj_v4_cycle with ⟨hx, hy, hz⟩
            simpa using congrArg Subgroup.zpowers (by simpa [MulAut.conj_apply] using hy)
      _ = H.1 := by simpa [hgx'] using hg
  · refine ⟨1, ?_⟩
    have hgy' : g = a4_v4_y := by
      have hgyA4 : (gV4 : A4) = a4_v4_y := by
        exact congrArg (fun z : V4 ↦ (z : A4)) hgy
      simpa [gV4] using hgyA4
    -- For the middle source element, the distinguished subgroup already matches `H`.
    simpa [a4_order_two_subgroup, hgy'] using hg
  · refine ⟨a4_three_cycle_012 ^ 2, ?_⟩
    have hgz' : g = a4_v4_z := by
      have hgzA4 : (gV4 : A4) = a4_v4_z := by
        exact congrArg (fun z : V4 ↦ (z : A4)) hgz
      simpa [gV4] using hgzA4
    -- Conjugation by the square of the chosen `3`-cycle sends the preferred involution to `z`.
    calc
      MulAut.conj (a4_three_cycle_012 ^ 2) • a4_order_two_subgroup
          = Subgroup.zpowers (((MulAut.conj (a4_three_cycle_012 ^ 2)).toMonoidHom) (a4_v4_y : A4)) := by
              rw [Subgroup.pointwise_smul_def, a4_order_two_subgroup]
              simpa using
                (MonoidHom.map_zpowers
                  ((MulAut.conj (a4_three_cycle_012 ^ 2)).toMonoidHom) (a4_v4_y : A4))
      _ = Subgroup.zpowers (a4_v4_z : A4) := by
            rcases a4_three_cycle_sq_conj_v4_cycle with ⟨hx, hy, hz⟩
            have hconj :
                ((MulAut.conj (a4_three_cycle_012 ^ 2)).toMonoidHom) (a4_v4_y : A4) = a4_v4_z := by
              change
                (a4_three_cycle_012 ^ 2 : A4) * (a4_v4_y : A4) * (a4_three_cycle_012 ^ 2)⁻¹ =
                  a4_v4_z
              exact hy
            rw [hconj]
      _ = H.1 := by simpa [hgz'] using hg

/-- Helper for Exercise 9-9.2-3: every cyclic subgroup of `A₄` of order `3` is conjugate to the
distinguished order-`3` subgroup. -/
private lemma a4_order_three_cyclic_subgroup_conj_representative
    (H : Subgroup.cyclicSubgroups A4) (hH : Nat.card H.1 = 3) :
    ∃ s : A4, MulAut.conj s • a4_order_three_subgroup = H.1 := by
  have hcardP0 : Nat.card a4_order_three_subgroup = 3 := by
    simpa [a4_order_three_subgroup, a4_three_cycle_012_order] using
      Nat.card_zpowers a4_three_cycle_012
  have hP0 : IsPGroup 3 a4_order_three_subgroup := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hcardP0]
    norm_num
  have hPH : IsPGroup 3 H.1 := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hH]
    norm_num
  have hP0_not_dvd : ¬ 3 ∣ a4_order_three_subgroup.index := by
    simpa [a4_order_three_subgroup_index_four] using (show ¬ 3 ∣ 4 by decide)
  let P0 : Sylow 3 A4 := hP0.toSylow hP0_not_dvd
  have hHindex : H.1.index = 4 := by
    have hA4 : Nat.card A4 = 12 := by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
    have hmul : H.1.index * Nat.card H.1 = Nat.card A4 := H.1.index_mul_card
    rw [hH, hA4] at hmul
    omega
  have hPH_not_dvd : ¬ 3 ∣ H.1.index := by
    simpa [hHindex] using (show ¬ 3 ∣ 4 by decide)
  let PH : Sylow 3 A4 := hPH.toSylow hPH_not_dvd
  have hmem : PH ∈ MulAction.orbit A4 P0 := by
    simpa [Sylow.orbit_eq_top (P := P0)] using show PH ∈ (⊤ : Set (Sylow 3 A4)) by simp
  rcases (MulAction.mem_orbit_iff).1 hmem with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  -- Sylow conjugacy identifies the ambient order-`3` subgroup with a conjugate of the
  -- distinguished one.
  calc
    MulAut.conj s • a4_order_three_subgroup = ((s • P0 : Sylow 3 A4) : Subgroup A4) := by
      simpa [P0] using (Sylow.coe_subgroup_smul (g := s) (P := P0)).symm
    _ = (PH : Subgroup A4) := by simpa using congrArg (fun P : Sylow 3 A4 ↦ (P : Subgroup A4)) hs
    _ = H.1 := by
      simpa [PH] using
        (IsPGroup.toSylow_coe hPH hPH_not_dvd)

/-- Helper for Exercise 9-9.2-3: the nonlinear character `ψ` has unit self-pairing. -/
private lemma a4_psi_pairing_psi_eq_one :
    ⟪((ψ : R(A4)) : A4 → ℂ), (ψ : A4 → ℂ)⟫ = 1 := by
  letI : a4_augmentationRepresentation.IsIrreducible :=
    a4_augmentation_representation_isIrreducible
  have hself :
      Nonempty (a4_augmentationRepresentation.Equiv a4_augmentationRepresentation) :=
    ⟨Representation.Equiv.refl _⟩
  have hrewrite :
      ⟪((ψ : R(A4)) : A4 → ℂ), (ψ : A4 → ℂ)⟫ =
        ⟪a4_augmentationRepresentation.character, a4_augmentationRepresentation.character⟫ := by
    calc
      ⟪((ψ : R(A4)) : A4 → ℂ), (ψ : A4 → ℂ)⟫ =
          ⟪a4_augmentationRepresentation.character, (ψ : A4 → ℂ)⟫ := by
            rw [a4_psi_eq_augmentation_character]
      _ =
          ⟪a4_augmentationRepresentation.character, a4_augmentationRepresentation.character⟫ := by
            rw [a4_psi_eq_augmentation_character]
  calc
    ⟪((ψ : R(A4)) : A4 → ℂ), (ψ : A4 → ℂ)⟫ =
        ⟪a4_augmentationRepresentation.character, a4_augmentationRepresentation.character⟫ :=
          hrewrite
    _ = 1 := by
          simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
            (Representation.char_orthonormal
              (ρ := a4_augmentationRepresentation)
              (σ := a4_augmentationRepresentation))

/-- Helper for Exercise 9-9.2-3: coercing a natural multiple in `R(A₄)` to a class function
matches scalar multiplication by the same natural number. -/
private lemma a4_nsmul_character_fun (n : ℕ) (χ : R(A4)) :
    (((n • χ : R(A4)) : A4 → ℂ)) = (n : ℂ) • ((χ : R(A4)) : A4 → ℂ) := by
  induction n with
  | zero =>
      ext g
      simp
  | succ n ih =>
      ext g
      simp [Nat.succ_eq_add_one, ih, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 9-9.2-3: coercing a natural multiple in `R(H)` to a class function
matches scalar multiplication by the same natural number. -/
private lemma a4_subgroup_nsmul_character_fun
    (H : Subgroup A4) (n : ℕ) (χ : R(H)) :
    (((n • χ : R(H)) : H → ℂ)) = (n : ℂ) • ((χ : R(H)) : H → ℂ) := by
  induction n with
  | zero =>
      ext h
      simp
  | succ n ih =>
      ext h
      simp [Nat.succ_eq_add_one, ih, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 9-9.2-3: the doubled nonlinear generator has `ψ`-pairing `2`. -/
private lemma a4_double_psi_pairing_psi_eq_two :
    ⟪(((2 • ψ : R(A4)) : A4 → ℂ)), (ψ : A4 → ℂ)⟫ = 2 := by
  have htwo :
      (((2 • ψ : R(A4)) : A4 → ℂ)) = (2 : ℂ) • (ψ : A4 → ℂ) := by
    -- Convert the natural double in `R(A₄)` into scalar multiplication on functions.
    simpa using a4_nsmul_character_fun 2 ψ
  rw [htwo, Representation.groupFunctionPairing_smul_left, a4_psi_pairing_psi_eq_one]
  norm_num

/-- Helper for Exercise 9-9.2-3: every generator of the form `ρ + ψ` has `ψ`-pairing `1`. -/
private lemma a4_linear_plus_psi_pairing_psi_eq_one
    (ρ : A4 →* ℂˣ) :
    ⟪(((MonoidHom.toCharacterRing ρ + ψ : R(A4)) : A4 → ℂ)), (ψ : A4 → ℂ)⟫ = 1 := by
  have hadd :
      (((MonoidHom.toCharacterRing ρ + ψ : R(A4)) : A4 → ℂ)) =
        (((MonoidHom.toCharacterRing ρ : R(A4)) : A4 → ℂ)) + (ψ : A4 → ℂ) := by
    rfl
  rw [hadd, Representation.groupFunctionPairing_add_left,
    a4_linear_character_pairing_psi_eq_zero ρ, a4_psi_pairing_psi_eq_one]
  simp

/-- Helper for Exercise 9-9.2-3: the shifted Klein-four generator has `ψ`-pairing `1`. -/
private lemma a4_klein_four_trivial_plus_psi_pairing_psi_eq_one :
    ⟪((((V4).characterRingInduction (1 : R(V4)) + ψ : R(A4)) : A4 → ℂ)),
      (ψ : A4 → ℂ)⟫ = 1 := by
  have hsum :
      (((V4).characterRingInduction (1 : R(V4)) : R(A4)) : A4 → ℂ) =
        ∑ i : Fin 3,
          (((MonoidHom.toCharacterRing
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    -- Rewrite the Klein-four induction as the sum of the three ambient linear constituents.
    simpa [a4_linearCharacterEquiv] using
      congrArg (fun χ : R(A4) ↦ (χ : A4 → ℂ)) a4_klein_four_induced_trivial_eq_sum_linear
  have hpair_sum :
      ⟪∑ i : Fin 3,
          (((MonoidHom.toCharacterRing
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ = 0 := by
    -- The three linear constituents are all orthogonal to `ψ`.
    calc
      ⟪∑ i : Fin 3,
          (((MonoidHom.toCharacterRing
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ =
          ∑ i : Fin 3,
            (1 : ℂ) *
              ⟪(((MonoidHom.toCharacterRing
                    ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4)) :
                  A4 → ℂ)),
                (ψ : A4 → ℂ)⟫ := by
            simpa using
              groupFunctionPairing_sum_smul_left_complex
                (s := Finset.univ)
                (a := fun _ : Fin 3 ↦ (1 : ℂ))
                (χ := fun i : Fin 3 ↦
                  (((MonoidHom.toCharacterRing
                      ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4)) :
                    A4 → ℂ)))
                (psiFun := (ψ : A4 → ℂ))
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            rw [a4_linear_character_pairing_psi_eq_zero
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4))]
            simp
  have hadd :
      ((((V4).characterRingInduction (1 : R(V4)) + ψ : R(A4)) : A4 → ℂ)) =
        (((V4).characterRingInduction (1 : R(V4)) : R(A4)) : A4 → ℂ) + (ψ : A4 → ℂ) := by
    rfl
  -- Pair the rewritten Klein-four generator and the extra `ψ` term separately.
  rw [hadd, hsum, Representation.groupFunctionPairing_add_left, hpair_sum, a4_psi_pairing_psi_eq_one]
  simp

/-- Helper for Exercise 9-9.2-3: every representation of the trivial subgroup induces to a natural
combination of the five target generators. -/
private lemma a4_bot_fdrep_induction_eq_generator_sum
    (W : FDRep ℂ (⊥ : Subgroup A4)) :
    ∃ a b : ℕ, ∃ z : Fin 3 → ℕ,
      (⊥ : Subgroup A4).characterRingInduction (a4_fdrepCharacter W) =
        a • (2 • ψ) +
          b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
            ∑ i : Fin 3,
              z i •
                (MonoidHom.toCharacterRing
                  ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) := by
  -- Route correction: reuse the explicit formula for `Ind_{⊥} 1` and only supply the subgroup
  -- character decomposition.
  rcases a4_bot_character_eq_nat_trivial W with ⟨m, hW⟩
  have hchar :
      a4_fdrepCharacter W = m • (1 : R((⊥ : Subgroup A4))) := by
    apply Subtype.ext
    ext h
    simpa [a4_fdrepCharacter, a4_subgroup_nsmul_character_fun] using congrFun hW h
  refine ⟨m, m, fun _ ↦ 0, ?_⟩
  -- Induce the unique subgroup character and expand the resulting explicit induction formula.
  rw [hchar, map_nsmul, a4_bot_induced_trivial_eq_generator_sum, nsmul_add]
  rw [Fin.sum_univ_three]
  simp only [zero_nsmul, zero_add, add_zero]
  ac_rfl

/-- Helper for Exercise 9-9.2-3: every representation of the distinguished order-`2` subgroup
induces to a natural combination of the five target generators. -/
private lemma a4_order_two_fdrep_induction_eq_generator_sum
    (W : FDRep ℂ a4_order_two_subgroup) :
    ∃ a b : ℕ, ∃ z : Fin 3 → ℕ,
      a4_order_two_subgroup.characterRingInduction (a4_fdrepCharacter W) =
        a • (2 • ψ) +
          b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
            ∑ i : Fin 3,
              z i •
                (MonoidHom.toCharacterRing
                  ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) := by
  rcases a4_order_two_character_eq_nat_trivial_add_sign W with ⟨m, n, hW⟩
  have hchar :
      a4_fdrepCharacter W =
        m • (1 : R(a4_order_two_subgroup)) +
          n • (MonoidHom.toCharacterRing a4_order_two_character : R(a4_order_two_subgroup)) := by
    apply Subtype.ext
    ext h
    simpa [a4_fdrepCharacter, a4_subgroup_nsmul_character_fun] using congrFun hW h
  refine ⟨n, m, fun _ ↦ 0, ?_⟩
  -- Induce the trivial and sign pieces separately and rewrite them using the established formulas.
  rw [hchar, map_add, map_nsmul, map_nsmul, a4_order_two_induced_trivial_eq_kleinFour_trivial_plus_psi,
    a4_order_two_induced_sign_eq_double_psi]
  rw [Fin.sum_univ_three]
  simp only [zero_nsmul, zero_add, add_zero]
  ac_rfl

/-- Helper for Exercise 9-9.2-3: every representation of the distinguished order-`3` subgroup
induces to a natural combination of the five target generators. -/
private lemma a4_order_three_fdrep_induction_eq_generator_sum
    (W : FDRep ℂ a4_order_three_subgroup) :
    ∃ a b : ℕ, ∃ z : Fin 3 → ℕ,
      a4_order_three_subgroup.characterRingInduction (a4_fdrepCharacter W) =
        a • (2 • ψ) +
          b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
            ∑ i : Fin 3,
              z i •
                (MonoidHom.toCharacterRing
                  ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) := by
  rcases a4_order_three_character_eq_nat_sum_linear_fin W with ⟨z, hz⟩
  have hz' :
      a4_fdrepCharacter W =
        ∑ i : Fin 3,
          z i •
            (MonoidHom.toCharacterRing
              (((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)).comp
                a4_order_three_subgroup.subtype) : R(a4_order_three_subgroup)) := by
    simpa [a4_fdrepCharacter] using hz
  refine ⟨0, 0, z, ?_⟩
  -- Induce the reindexed subgroup decomposition termwise and rewrite each summand by the
  -- established order-`3` induction formula.
  rw [hz', map_sum]
  simp_rw [map_nsmul, a4_order_three_induced_restriction_linear_eq_linear_plus_psi]
  simp

/-- Helper for Exercise 9-9.2-3: every honest cyclic induction in `R(A₄)` is a natural
combination of the five target generators. -/
private lemma a4_cyclic_induced_eq_generator_sum
    (H : Subgroup.cyclicSubgroups A4) (W : FDRep ℂ H.1) :
    ∃ a b : ℕ, ∃ z : Fin 3 → ℕ,
      H.1.characterRingInduction (a4_fdrepCharacter W) =
        a • (2 • ψ) +
          b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
            ∑ i : Fin 3,
              z i •
                (MonoidHom.toCharacterRing
                  ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) := by
  rcases a4_cyclic_subgroup_card_eq_one_or_two_or_three H with hH | hH | hH
  · have hbot : H.1 = ⊥ := by
      -- Cardinality `1` means every subgroup element is the identity, hence `H = ⊥`.
      letI : Subsingleton H.1 := (Nat.card_eq_one_iff_unique.mp hH).1
      refine (Subgroup.eq_bot_iff_forall H.1).2 ?_
      intro x hx
      let xH : H.1 := ⟨x, hx⟩
      have : xH = 1 := Subsingleton.elim _ _
      simpa [xH] using congrArg Subtype.val this
    let Wbot : FDRep ℂ (⊥ : Subgroup A4) := hbot ▸ W
    have htransport :
        (⊥ : Subgroup A4).characterRingInduction (a4_fdrepCharacter Wbot) =
          H.1.characterRingInduction (a4_fdrepCharacter W) := by
      exact a4_characterRingInduction_eq_of_subgroup_eq hbot W
    -- Route correction: the order-`1` branch is now a pure transport to the trivial subgroup.
    rcases a4_bot_fdrep_induction_eq_generator_sum Wbot with ⟨a, b, z, hz⟩
    refine ⟨a, b, z, ?_⟩
    exact htransport.symm.trans hz
  · rcases a4_order_two_cyclic_subgroup_conj_representative H hH with ⟨s, hs⟩
    have hback : MulAut.conj s⁻¹ • H.1 = a4_order_two_subgroup := by
      -- Apply inverse conjugation to the representative equality to recover the chosen model.
      simpa [smul_smul] using
        (congrArg (fun L : Subgroup A4 ↦ MulAut.conj s⁻¹ • L) hs).symm
    let Wrep : FDRep ℂ a4_order_two_subgroup := hback ▸ a4_conjugateFDRep H.1 s⁻¹ W
    have htransport :
        H.1.characterRingInduction (a4_fdrepCharacter W) =
          a4_order_two_subgroup.characterRingInduction (a4_fdrepCharacter Wrep) := by
      simpa [Wrep] using a4_characterRingInduction_eq_of_inverse_conjugate s hback W
    -- Use the distinguished order-`2` subgroup formula and transport it back along inverse
    -- conjugation.
    rcases a4_order_two_fdrep_induction_eq_generator_sum Wrep with ⟨a, b, z, hz⟩
    refine ⟨a, b, z, ?_⟩
    exact htransport.trans hz
  · rcases a4_order_three_cyclic_subgroup_conj_representative H hH with ⟨s, hs⟩
    have hback : MulAut.conj s⁻¹ • H.1 = a4_order_three_subgroup := by
      -- The inverse conjugation recovers the chosen order-`3` representative subgroup.
      simpa [smul_smul] using
        (congrArg (fun L : Subgroup A4 ↦ MulAut.conj s⁻¹ • L) hs).symm
    let Wrep : FDRep ℂ a4_order_three_subgroup := hback ▸ a4_conjugateFDRep H.1 s⁻¹ W
    have htransport :
        H.1.characterRingInduction (a4_fdrepCharacter W) =
          a4_order_three_subgroup.characterRingInduction (a4_fdrepCharacter Wrep) := by
      simpa [Wrep] using a4_characterRingInduction_eq_of_inverse_conjugate s hback W
    -- The order-`3` branch is the same transport pattern, now using the `Fin 3`-indexed
    -- representative formula already proved above.
    rcases a4_order_three_fdrep_induction_eq_generator_sum Wrep with ⟨a, b, z, hz⟩
    refine ⟨a, b, z, ?_⟩
    exact htransport.trans hz

/-- Helper for Exercise 9-9.2-3: the `ψ`-pairing of a natural combination of the five generators
is the corresponding weighted coefficient sum. -/
private lemma a4_generator_sum_pairing_psi_eq
    (a b : ℕ) (z : Fin 3 → ℕ) :
    ⟪(((a • (2 • ψ) +
        b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
        ∑ i : Fin 3,
          z i •
            (MonoidHom.toCharacterRing
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) : R(A4)) :
        A4 → ℂ)),
      (ψ : A4 → ℂ)⟫ =
      ((2 * a + b + ∑ i : Fin 3, z i : ℕ) : ℂ) := by
  have hsplit :
      (((a • (2 • ψ) +
          b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
          ∑ i : Fin 3,
            z i •
              (MonoidHom.toCharacterRing
                ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) : R(A4)) :
        A4 → ℂ)) =
        (((a • (2 • ψ : R(A4)) : R(A4)) : A4 → ℂ)) +
          ((((b • ((V4).characterRingInduction (1 : R(V4)) + ψ) : R(A4)) : R(A4)) :
            A4 → ℂ)) +
            ((((∑ i : Fin 3,
                  z i •
                    (MonoidHom.toCharacterRing
                      ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) : R(A4)) :
                R(A4)) : A4 → ℂ)) := by
    rfl
  have hpair_a :
      ⟪(((a • (2 • ψ : R(A4)) : R(A4)) : A4 → ℂ)), (ψ : A4 → ℂ)⟫ = (a : ℂ) * 2 := by
    rw [a4_nsmul_character_fun, Representation.groupFunctionPairing_smul_left,
      a4_double_psi_pairing_psi_eq_two]
  have hpair_b :
      ⟪((((b • ((V4).characterRingInduction (1 : R(V4)) + ψ) : R(A4)) : R(A4)) :
            A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ = (b : ℂ) := by
    rw [a4_nsmul_character_fun, Representation.groupFunctionPairing_smul_left,
      a4_klein_four_trivial_plus_psi_pairing_psi_eq_one]
    simp
  have hsum_fun :
      ((((∑ i : Fin 3,
            z i •
              (MonoidHom.toCharacterRing
                ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) : R(A4)) :
          R(A4)) : A4 → ℂ)) =
        ∑ i : Fin 3,
          (z i : ℂ) •
            (((MonoidHom.toCharacterRing
                ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ : R(A4)) :
              A4 → ℂ)) := by
    ext g
    simp [a4_nsmul_character_fun]
  have hsum_pair :
      ⟪((((∑ i : Fin 3,
              z i •
                (MonoidHom.toCharacterRing
                  ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) : R(A4)) :
            R(A4)) : A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ =
          ∑ i : Fin 3, (z i : ℂ) := by
    rw [hsum_fun]
    calc
      ⟪∑ i : Fin 3,
          (z i : ℂ) •
            (((MonoidHom.toCharacterRing
                ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ : R(A4)) :
              A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ =
          ∑ i : Fin 3,
            (z i : ℂ) *
              ⟪(((MonoidHom.toCharacterRing
                    ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ :
                    R(A4)) :
                  A4 → ℂ)),
                (ψ : A4 → ℂ)⟫ := by
            simpa using
              groupFunctionPairing_sum_smul_left_complex
                (s := Finset.univ)
                (a := fun i : Fin 3 ↦ (z i : ℂ))
                (χ := fun i : Fin 3 ↦
                  (((MonoidHom.toCharacterRing
                      ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ : R(A4)) :
                    A4 → ℂ)))
                (psiFun := (ψ : A4 → ℂ))
      _ = ∑ i : Fin 3, (z i : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [a4_linear_plus_psi_pairing_psi_eq_one]
            simp
  -- Pair the three blocks separately and evaluate them with the previously computed base values.
  rw [hsplit, Representation.groupFunctionPairing_add_left, Representation.groupFunctionPairing_add_left,
    hpair_a, hpair_b, hsum_pair]
  norm_num [Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm, mul_assoc,
    mul_left_comm, mul_comm]

/-- Helper for Exercise 9-9.2-3: the source-view induction `Ind[H](W.character)` agrees with the
owner-view coercion of `H.characterRingInduction`. -/
private lemma a4_induced_fdrep_character_eq_characterRingInduction_fun
    (H : Subgroup.cyclicSubgroups A4) (W : FDRep ℂ H.1) :
    Ind[H.1](W.character) =
      (((H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
        A4 → ℂ)) := by
  -- The source-level induction and the owner-level induction are definitionally the same
  -- complex-valued class function.
  simp [Subgroup.characterRingInduction_apply]

/-- Helper for Exercise 9-9.2-3: a zero generator weight forces every natural coefficient in that
generator expression to vanish. -/
private lemma a4_generator_weight_eq_zero
    (a0 b0 : ℕ) (z0 : Fin 3 → ℕ)
    (hN : 2 * a0 + b0 + ∑ j : Fin 3, z0 j = 0) :
    a0 = 0 ∧ b0 = 0 ∧ ∀ j : Fin 3, z0 j = 0 := by
  rw [Fin.sum_univ_three] at hN
  have htotal : 2 * a0 + b0 + z0 0 + z0 1 + z0 2 = 0 := by
    simpa [add_assoc] using hN
  have ha0 : a0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      a0 ≤ 2 * a0 := by
        rw [two_mul]
        exact Nat.le_add_left _ _
      _ ≤ 2 * a0 + b0 := Nat.le_add_right _ _
      _ ≤ 2 * a0 + b0 + z0 0 := Nat.le_add_right _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 := Nat.le_add_right _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 + z0 2 := Nat.le_add_right _ _
      _ = 0 := htotal
  have hb0 : b0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      b0 ≤ 2 * a0 + b0 := Nat.le_add_left _ _
      _ ≤ 2 * a0 + b0 + z0 0 := Nat.le_add_right _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 := Nat.le_add_right _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 + z0 2 := Nat.le_add_right _ _
      _ = 0 := htotal
  have hz00 : z0 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      z0 0 ≤ 2 * a0 + b0 + z0 0 := Nat.le_add_left _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 := Nat.le_add_right _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 + z0 2 := Nat.le_add_right _ _
      _ = 0 := htotal
  have hz01 : z0 1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      z0 1 ≤ 2 * a0 + b0 + z0 0 + z0 1 := Nat.le_add_left _ _
      _ ≤ 2 * a0 + b0 + z0 0 + z0 1 + z0 2 := Nat.le_add_right _ _
      _ = 0 := htotal
  have hz02 : z0 2 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      z0 2 ≤ 2 * a0 + b0 + z0 0 + z0 1 + z0 2 := Nat.le_add_left _ _
      _ = 0 := htotal
  refine ⟨ha0, hb0, ?_⟩
  intro j
  fin_cases j
  · exact hz00
  · exact hz01
  · exact hz02

-- Source/core/bridge triage:
-- * source-facing: the exercise statements about the cyclic-induced part of `R(A₄)` and the four
--   irreducible characters of `A₄`, with degree-`1` characters presented as `A4 →* ℂˣ`.
-- * core/canonical: `Subgroup.cyclicSubgroups A4` for the cyclic subgroup family and
--   `Representation.cyclicInducedCharacterSubmodule A4` for the induced-character owner.
-- * bridge/view: `MonoidHom.toCharacterRing`, which inserts a degree-`1` character into `R(A₄)`,
--   together with the ambient function-space realization
--   `Representation.cyclicInducedCharacterSpan ℤ A4`.
--
-- Primitive data: the source degree-`1` characters `A4 →* ℂˣ`, the source character `ψ`, the
-- canonical cyclic subgroup family `Subgroup.cyclicSubgroups A4`, and the canonical induced
-- character `(V4).characterRingInduction (1 : R(V4))`.
-- Derived API: the positivity predicate below.

-- Proof sketch: compute the inductions from the cyclic subgroups of `A₄` using the character table
-- from Section 5.7. The generator `(V4).characterRingInduction (1 : R(V4))` is the sum of the
-- three degree-`1` irreducible characters, while `MonoidHom.toCharacterRing ρ` ranges over those
-- linear characters individually.
/-- Exercise 9-9.2-3 (1): the additive submonoid of `R(A₄)` generated by characters induced from
cyclic subgroups is generated by `2ψ`, by the induced trivial character of the canonical Klein
four subgroup shifted by `ψ`, and by the three degree-`1` characters of `A₄` shifted by `ψ`. -/
theorem a4_cyclic_induction_add_submonoid_eq_closure_five_characters :
    AddSubmonoid.closure
        { χ : R(A4) |
          ∃ H : Subgroup.cyclicSubgroups A4, ∃ W : FDRep ℂ H.1,
            χ = H.1.characterRingInduction
              ⟨W.character, by
                simpa using rep_character_mem_characterRing (Rep.of W.ρ)⟩ } =
      AddSubmonoid.closure
        { χ : R(A4) |
          χ = 2 • ψ ∨
            χ = (V4).characterRingInduction (1 : R(V4)) + ψ ∨
              ∃ ρ : A4 →* ℂˣ, χ = MonoidHom.toCharacterRing ρ + ψ } := by
  let C : AddSubmonoid (R(A4)) :=
    AddSubmonoid.closure
      { χ : R(A4) |
        χ = 2 • ψ ∨
          χ = (V4).characterRingInduction (1 : R(V4)) + ψ ∨
            ∃ ρ : A4 →* ℂˣ, χ = MonoidHom.toCharacterRing ρ + ψ }
  -- Route correction: use the explicit cyclic-induction formulas already established above and
  -- reduce the theorem to closure bookkeeping on the five textbook generators.
  apply le_antisymm
  · refine AddSubmonoid.closure_le.2 ?_
    intro χ hχ
    rcases hχ with ⟨H, W, rfl⟩
    change H.1.characterRingInduction (a4_fdrepCharacter W) ∈ C
    rcases a4_cyclic_induced_eq_generator_sum H W with ⟨a, b, z, hz⟩
    have hdouble : 2 • ψ ∈ C := by
      exact AddSubmonoid.subset_closure (Or.inl rfl)
    have hshifted_v4 : (V4).characterRingInduction (1 : R(V4)) + ψ ∈ C := by
      exact AddSubmonoid.subset_closure (Or.inr (Or.inl rfl))
    have hlinear_shifted (i : Fin 3) :
        MonoidHom.toCharacterRing
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ ∈ C := by
      exact AddSubmonoid.subset_closure
        (Or.inr (Or.inr ⟨(a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4), rfl⟩))
    have hsum :
        (∑ i : Fin 3,
          z i •
            (MonoidHom.toCharacterRing
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ)) ∈ C := by
      rw [Fin.sum_univ_three]
      exact
        AddSubmonoid.add_mem C
          (AddSubmonoid.add_mem C
            (AddSubmonoid.nsmul_mem C (hlinear_shifted 0) (z 0))
            (AddSubmonoid.nsmul_mem C (hlinear_shifted 1) (z 1)))
          (AddSubmonoid.nsmul_mem C (hlinear_shifted 2) (z 2))
    have hcomb :
        a • (2 • ψ) +
            b • ((V4).characterRingInduction (1 : R(V4)) + ψ) +
              ∑ i : Fin 3,
                z i •
                  (MonoidHom.toCharacterRing
                    ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) ∈ C := by
      exact
        AddSubmonoid.add_mem C
        (AddSubmonoid.add_mem C
          (AddSubmonoid.nsmul_mem C hdouble a)
          (AddSubmonoid.nsmul_mem C hshifted_v4 b))
        hsum
    exact hz.symm ▸ hcomb
  · refine AddSubmonoid.closure_le.2 ?_
    intro χ hχ
    rcases hχ with rfl | hχ | hχ
    · exact AddSubmonoid.subset_closure <| by
        refine ⟨⟨a4_order_two_subgroup, a4_order_two_subgroup_mem_cyclicSubgroups⟩,
          FDRep.of a4_order_two_character.toRepresentation, ?_⟩
        change 2 • ψ =
          a4_order_two_subgroup.characterRingInduction
            (MonoidHom.toCharacterRing a4_order_two_character)
        exact a4_order_two_induced_sign_eq_double_psi.symm
    · rcases hχ with rfl
      exact AddSubmonoid.subset_closure <| by
        let W0 : FDRep ℂ a4_order_two_subgroup :=
          FDRep.of ((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation)
        refine ⟨⟨a4_order_two_subgroup, a4_order_two_subgroup_mem_cyclicSubgroups⟩, W0, ?_⟩
        have htrivRing : a4_fdrepCharacter W0 = (1 : R(a4_order_two_subgroup)) := by
          apply Subtype.ext
          ext h
          change (((1 : a4_order_two_subgroup →* ℂˣ).toRepresentation).character h) = 1
          simp [MonoidHom.toRepresentation_character_apply]
        calc
          (V4).characterRingInduction (1 : R(V4)) + ψ =
              a4_order_two_subgroup.characterRingInduction (1 : R(a4_order_two_subgroup)) := by
                exact a4_order_two_induced_trivial_eq_kleinFour_trivial_plus_psi.symm
          _ =
              a4_order_two_subgroup.characterRingInduction (a4_fdrepCharacter W0) := by
                rw [htrivRing]
    · rcases hχ with ⟨ρ, rfl⟩
      exact AddSubmonoid.subset_closure <| by
        refine ⟨⟨a4_order_three_subgroup, a4_order_three_subgroup_mem_cyclicSubgroups⟩,
          FDRep.of ((ρ.comp a4_order_three_subgroup.subtype).toRepresentation), ?_⟩
        change MonoidHom.toCharacterRing ρ + ψ =
          a4_order_three_subgroup.characterRingInduction
            (MonoidHom.toCharacterRing (ρ.comp a4_order_three_subgroup.subtype))
        exact (a4_order_three_induced_restriction_linear_eq_linear_plus_psi ρ).symm

/-- Helper for Exercise 9-9.2-3: in the explicit irreducible basis
`χ₀, χ₁, χ₂, ψ`, an even-degree virtual character has coefficients satisfying the degree
equation `c₀ + c₁ + c₂ + 3 c₃ = 2 n`. -/
private lemma a4_even_degree_explicit_basis_degree_relation
    (φ : R(A4))
    (hφ : ∃ n : ℤ, (φ : A4 → ℂ) 1 = (2 * n : ℂ)) :
    ∃ n : ℤ,
      let c :=
        (irreducible_characters_basis_of_complete_family
          ℂ (a4_explicitFDRepFamily a4_linearCharacterEquiv)
            (by
              intro i j hij hij_iso
              rcases hij_iso with ⟨e⟩
              exact
                a4_explicit_complex_family_pairwise a4_linearCharacterEquiv hij
                  ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩)
            (a4_explicit_complex_family_complete a4_linearCharacterEquiv)).repr φ
      c 0 + c 1 + c 2 + 3 * c 3 = 2 * n := by
  classical
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic
        (a4_explicitFDRepFamily a4_linearCharacterEquiv) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise a4_linearCharacterEquiv hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete :
      IsCompleteIrreducibleFamily (a4_explicitFDRepFamily a4_linearCharacterEquiv) :=
    a4_explicit_complex_family_complete a4_linearCharacterEquiv
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily a4_linearCharacterEquiv) hpairwise hcomplete
  let c := b.repr φ
  rcases hφ with ⟨n, hn⟩
  have hφ_basis :
      ∑ i, c i •
          ((a4_explicitFDRepFamily a4_linearCharacterEquiv i).character : A4 → ℂ) =
        (φ : A4 → ℂ) := by
    -- Expand `φ` in the explicit irreducible basis `χ₀, χ₁, χ₂, ψ`.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr φ)
  have hdegree_value (i : Fin 4) :
      ((a4_explicitFDRepFamily a4_linearCharacterEquiv i).character : A4 → ℂ) 1 =
        match i with
        | 0 => 1
        | 1 => 1
        | 2 => 1
        | 3 => 3 := by
    -- The explicit family has degrees `1,1,1,3`.
    fin_cases i <;>
      simp [a4_explicitFDRepFamily, a4_explicitComplexFamily, Representation.char_one,
        a4_augmentationRepresentation_finrank_three]
  have hcoeff_relation :
      c 0 + c 1 + c 2 + 3 * c 3 = 2 * n := by
    have hφ_eval := congrFun hφ_basis 1
    rw [hn] at hφ_eval
    rw [Fin.sum_univ_four, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, Pi.smul_apply, Pi.smul_apply] at hφ_eval
    rw [hdegree_value 0, hdegree_value 1, hdegree_value 2, hdegree_value 3] at hφ_eval
    have hφ_eval' :
        (((((c 0 : ℤ) * 1 + (c 1 : ℤ) * 1 + (c 2 : ℤ) * 1) + (c 3 : ℤ) * 3 : ℤ) : ℂ)) =
          (2 * n : ℂ) := by
      simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hφ_eval
    have hcoeff_relation' :
        ((c 0 : ℤ) * 1 + (c 1 : ℤ) * 1 + (c 2 : ℤ) * 1) + (c 3 : ℤ) * 3 = 2 * n := by
      exact_mod_cast hφ_eval'
    simpa [mul_comm] using hcoeff_relation'
  refine ⟨n, ?_⟩
  simpa [b, c] using hcoeff_relation

/-- Helper for Exercise 9-9.2-3: an even-degree virtual character of `A₄` rewrites in `R(A₄)` as
an integral combination of the generators `ρ + ψ` and `2ψ`. -/
private lemma a4_even_degree_generator_rewrite
    (φ : R(A4))
    (hφ : ∃ n : ℤ, (φ : A4 → ℂ) 1 = (2 * n : ℂ)) :
    ∃ z : Fin 3 → ℤ, ∃ t : ℤ,
      φ =
        (∑ i : Fin 3,
          z i •
            (MonoidHom.toCharacterRing
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ)) +
          t • (2 • ψ) := by
  classical
  have hpairwise :
      CategoryTheory.PairwiseNonisomorphic
        (a4_explicitFDRepFamily a4_linearCharacterEquiv) := by
    intro i j hij hij_iso
    rcases hij_iso with ⟨e⟩
    exact
      a4_explicit_complex_family_pairwise a4_linearCharacterEquiv hij
        ⟨(CategoryTheory.forget₂ (FDRep ℂ A4) (Rep ℂ A4)).mapIso e⟩
  have hcomplete :
      IsCompleteIrreducibleFamily (a4_explicitFDRepFamily a4_linearCharacterEquiv) :=
    a4_explicit_complex_family_complete a4_linearCharacterEquiv
  let b :=
    irreducible_characters_basis_of_complete_family
      ℂ (a4_explicitFDRepFamily a4_linearCharacterEquiv) hpairwise hcomplete
  let c := b.repr φ
  rcases a4_even_degree_explicit_basis_degree_relation φ hφ with ⟨n, hdeg⟩
  have hdeg' : c 0 + c 1 + c 2 + 3 * c 3 = 2 * n := by
    simpa [b, c] using hdeg
  have ht :
      ∃ t : ℤ, c 3 - c 0 - c 1 - c 2 = 2 * t := by
    -- The degree relation forces the excess `ψ`-coefficient to be even.
    refine ⟨n - c 3 - c 0 - c 1 - c 2, ?_⟩
    omega
  rcases ht with ⟨t, ht⟩
  have hs :
      c 0 + c 1 + c 2 + 2 * t = c 3 := by
    omega
  have hφ_basis :
      ∑ i, c i • ((a4_explicitFDRepFamily a4_linearCharacterEquiv i).character : A4 → ℂ) =
        (φ : A4 → ℂ) := by
    -- Expand `φ` in the explicit irreducible basis `χ₀, χ₁, χ₂, ψ`.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(A4) ↦ (z : A4 → ℂ)) (b.sum_repr φ)
  let z : Fin 3 → ℤ
    | 0 => c 0
    | 1 => c 1
    | 2 => c 2
  have hs' : z 0 + z 1 + z 2 + 2 * t = c 3 := by
    simpa [z] using hs
  have hslot0_char :
      ((a4_explicitFDRepFamily a4_linearCharacterEquiv 0).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((a4_linearCharacterEquiv 0).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (a4_linearCharacterEquiv 0)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (a4_linearCharacterEquiv 0)
  have hslot1_char :
      ((a4_explicitFDRepFamily a4_linearCharacterEquiv 1).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((a4_linearCharacterEquiv 1).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (a4_linearCharacterEquiv 1)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (a4_linearCharacterEquiv 1)
  have hslot2_char :
      ((a4_explicitFDRepFamily a4_linearCharacterEquiv 2).character : A4 → ℂ) =
        (((MonoidHom.toCharacterRing
          ((a4_linearCharacterEquiv 2).comp (QuotientGroup.mk' V4)) : R(A4)) : A4 → ℂ)) := by
    change (((a4_linearCharacterFamily (a4_linearCharacterEquiv 2)).ρ).character : A4 → ℂ) = _
    exact a4_linearCharacterFamily_character_eq (a4_linearCharacterEquiv 2)
  have hslot3_char :
      ((a4_explicitFDRepFamily a4_linearCharacterEquiv 3).character : A4 → ℂ) = (ψ : A4 → ℂ) := by
    simpa [a4_explicitFDRepFamily, a4_explicitComplexFamily] using
      a4_psi_eq_augmentation_character.symm
  have hdouble_psi_smul : ((2 * t : ℤ) • ψ) = t • (2 • ψ) := by
    calc
      ((2 * t : ℤ) • ψ) = ((t * 2 : ℤ) • ψ) := by rw [mul_comm]
      _ = t • (2 • ψ) := by
            simpa using (smul_assoc t (2 : ℤ) ψ)
  have hrewrite_ring :
      (∑ i : Fin 3,
        (z i : ℤ) •
          (MonoidHom.toCharacterRing
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4))) +
        (c 3 : ℤ) • ψ =
      (∑ i : Fin 3,
        (z i : ℤ) •
          (MonoidHom.toCharacterRing
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ)) +
        t • (2 • ψ) := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hs']
    simp only [zsmul_add, add_zsmul, two_zsmul, smul_smul]
    rw [hdouble_psi_smul]
    abel_nf
  refine ⟨z, t, ?_⟩
  apply Subtype.ext
  calc
    (φ : A4 → ℂ) =
        ∑ i, c i • ((a4_explicitFDRepFamily a4_linearCharacterEquiv i).character : A4 → ℂ) := by
          simpa using hφ_basis.symm
    _ =
        (∑ i : Fin 3,
          (z i : ℤ) •
            (((MonoidHom.toCharacterRing
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) : R(A4)) :
                A4 → ℂ))) +
          (c 3 : ℤ) • (ψ : A4 → ℂ) := by
            rw [Fin.sum_univ_four]
            rw [Fin.sum_univ_three]
            simp [z, hslot0_char, hslot1_char, hslot2_char, hslot3_char]
    _ =
        (∑ i : Fin 3,
          (z i : ℤ) •
            (((MonoidHom.toCharacterRing
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ : R(A4)) :
                A4 → ℂ))) +
          (t : ℤ) • (((2 • ψ : R(A4)) : A4 → ℂ)) := by
            simpa using congrArg (fun χ : R(A4) ↦ (χ : A4 → ℂ)) hrewrite_ring

-- Proof sketch: identify `cyclicInducedCharacterSubmodule A4` with the `ℤ`-span of the generators
-- in part `(1)`. Writing a virtual character in the irreducible basis of `A₄`, the unique
-- congruence condition is that the degree `χ(1)` be even.
/-- Exercise 9-9.2-3 (2): a virtual character of `A₄` belongs to the image of induction from cyclic
subgroups if and only if it belongs to the canonical cyclic-induced submodule of `R(A₄)`,
equivalently if its value at `1` is an even integer. -/
theorem mem_a4_cyclic_induction_submodule_iff_value_at_one_even
    (φ : R(A4)) :
    φ ∈ cyclicInducedCharacterSubmodule A4 ↔
      ∃ n : ℤ, (φ : A4 → ℂ) 1 = (2 * n : ℂ) := by
  constructor
  · -- The verified direction is that every cyclic induction piece has even degree.
    intro hφ
    exact a4_even_value_at_one_of_mem_cyclicInducedCharacterSubmodule φ hφ
  · -- Route correction: expand `φ` in the explicit irreducible basis and rewrite the `ψ`
    -- coefficient using the evenness of `φ(1)`.
    intro hφ
    rcases a4_even_degree_generator_rewrite φ hφ with ⟨z, t, rfl⟩
    -- The generator rewrite lands directly in the cyclic-induced submodule because both building
    -- blocks `ρ + ψ` and `2ψ` were already shown to lie there.
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_mem _ ?_
      intro i hi
      change
        z i •
            (MonoidHom.toCharacterRing
              ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)) + ψ) ∈
          cyclicInducedCharacterSubmodule A4
      exact
        Submodule.smul_mem (cyclicInducedCharacterSubmodule A4) (z i)
          (a4_linear_plus_psi_mem_cyclicInducedCharacterSubmodule
            ((a4_linearCharacterEquiv i).comp (QuotientGroup.mk' V4)))
    · change t • (2 • ψ) ∈ cyclicInducedCharacterSubmodule A4
      exact
        Submodule.smul_mem (cyclicInducedCharacterSubmodule A4) t
          a4_double_psi_mem_cyclicInducedCharacterSubmodule

-- Proof sketch: express any positive rational combination of cyclically induced characters in the
-- generators from part `(1)`, evaluate at `1`, and compare irreducible coefficients. The fact that
-- the source-facing linear characters `ρ : A4 →* ℂˣ` factor through the abelian quotient
-- `A₄ ⧸ V₄` remains internal proof scaffolding rather than public API.
/-- Exercise 9-9.2-3 (3-5): a degree-`1` character of `A₄` is not a positive rational combination
of characters induced from cyclic subgroups. -/
theorem a4_linear_character_not_positive_rat_combination_of_cyclic_inductions
    (ρ : A4 →* ℂˣ) :
    ¬ a4PositiveRatCombinationOfCyclicInductions (MonoidHom.toCharacterRing ρ) := by
  intro hpos
  rcases hpos with ⟨s, c, hcpos, hEq⟩
  choose a b z hz using
    fun i : s ↦ by
      rcases i.1 with ⟨H, W⟩
      simpa using a4_cyclic_induced_eq_generator_sum H W
  let N : s → ℕ := fun i ↦ 2 * a i + b i + ∑ j : Fin 3, z i j
  have hEq_rewrite :
      (MonoidHom.toCharacterRing ρ : A4 → ℂ) =
        ∑ i : s,
          (c i : ℂ) •
            (((match i.1 with
                | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
              A4 → ℂ)) := by
    calc
      (MonoidHom.toCharacterRing ρ : A4 → ℂ) =
          ∑ i : s,
            match i.1 with
            | ⟨H, W⟩ => (c i : ℂ) • Ind[H.1](W.character) := hEq
      _ =
          ∑ i : s,
            (c i : ℂ) •
              (((match i.1 with
                  | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
                A4 → ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rcases i.1 with ⟨H, W⟩
            rw [a4_induced_fdrep_character_eq_characterRingInduction_fun H W]
  have hpair_rhs :
      ⟪(∑ i : s,
          (c i : ℂ) •
            (((match i.1 with
                | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
              A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ =
        ∑ i : s, (c i : ℂ) * ((N i : ℕ) : ℂ) := by
    calc
      ⟪(∑ i : s,
          (c i : ℂ) •
            (((match i.1 with
                | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
              A4 → ℂ)),
        (ψ : A4 → ℂ)⟫ =
          ∑ i : s,
            (c i : ℂ) *
              ⟪(((match i.1 with
                    | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
                  A4 → ℂ),
                (ψ : A4 → ℂ)⟫ := by
            simpa using
              groupFunctionPairing_sum_smul_left_complex
                (s := s)
                (a := fun i : s ↦ (c i : ℂ))
                (χ := fun i : s ↦
                  (((match i.1 with
                      | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
                    A4 → ℂ)))
                (psiFun := (ψ : A4 → ℂ))
      _ = ∑ i : s, (c i : ℂ) * ((N i : ℕ) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rcases i.1 with ⟨H, W⟩
            rw [hz i]
            simpa [N] using a4_generator_sum_pairing_psi_eq (a i) (b i) (z i)
  have hpair_zero :
      ∑ i : s, (c i : ℂ) * ((N i : ℕ) : ℂ) = 0 := by
    have hpair_eq :=
      congrArg (fun f : A4 → ℂ ↦ ⟪f, (ψ : A4 → ℂ)⟫) hEq_rewrite
    rw [a4_linear_character_pairing_psi_eq_zero, hpair_rhs] at hpair_eq
    simpa using hpair_eq.symm
  have hpair_zero_rat :
      ∑ i : s, c i * (N i : ℚ) = 0 := by
    have hcast :
        (((∑ i : s, c i * (N i : ℚ) : ℚ) : ℂ)) = 0 := by
      simpa using hpair_zero
    exact_mod_cast hcast
  have hterm_nonneg (i : s) : 0 ≤ c i * (N i : ℚ) := by
    exact mul_nonneg (le_of_lt (hcpos i)) (Nat.cast_nonneg _)
  have hterm_zero (i : s) : c i * (N i : ℚ) = 0 := by
    have hsum_zero :
        ∑ i in (Finset.univ : Finset s), c i * (N i : ℚ) = 0 := by
      simpa using hpair_zero_rat
    have hall_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi ↦ hterm_nonneg i)).1 hsum_zero
    exact hall_zero i (by simp)
  have hN_zero (i : s) : N i = 0 := by
    have hc_ne : c i ≠ 0 := ne_of_gt (hcpos i)
    have hNq : (N i : ℚ) = 0 := by
      exact (mul_eq_zero.mp (hterm_zero i)).resolve_left hc_ne
    exact Nat.cast_eq_zero.mp hNq
  have hind_zero (i : s) :
      match i.1 with
      | ⟨H, W⟩ => (((H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) : A4 → ℂ))
          = 0 := by
    rcases i.1 with ⟨H, W⟩
    have hweights :
        a i = 0 ∧ b i = 0 ∧ ∀ j : Fin 3, z i j = 0 := by
      apply a4_generator_weight_eq_zero (a i) (b i) (z i)
      simpa [N] using hN_zero i
    rcases hweights with ⟨ha, hb, hz0⟩
    have hring_zero :
        H.1.characterRingInduction (a4_fdrepCharacter W) = 0 := by
      rw [hz i, ha, hb, Fin.sum_univ_three]
      simp [hz0 0, hz0 1, hz0 2]
    simpa using congrArg (fun χ : R(A4) ↦ (χ : A4 → ℂ)) hring_zero
  have hEq_zero :
      (MonoidHom.toCharacterRing ρ : A4 → ℂ) = 0 := by
    calc
      (MonoidHom.toCharacterRing ρ : A4 → ℂ) =
          ∑ i : s,
            (c i : ℂ) •
              (((match i.1 with
                  | ⟨H, W⟩ => H.1.characterRingInduction (a4_fdrepCharacter W) : R(A4)) :
                A4 → ℂ)) := hEq_rewrite
      _ = ∑ i : s, (0 : A4 → ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hind_zero i]
            simp
      _ = 0 := by simp
  have hvalue := congrFun hEq_zero 1
  have : (1 : ℂ) = 0 := by
    simpa [MonoidHom.toCharacterRing_apply] using hvalue
  norm_num at this
