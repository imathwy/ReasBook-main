import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_15_2_Prime_avoidance

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise

private theorem vadd_ideal_subset_iff {R : Type u} [CommRing R] {x : R} {I J : Ideal R} :
    (x +ᵥ (I : Set R)) ⊆ (J : Set R) ↔ x ∈ J ∧ I ≤ J := by
  constructor
  · intro h
    have hxJ : x ∈ J := h <| Set.mem_vadd_set.2 ⟨0, I.zero_mem, by simp⟩
    refine ⟨hxJ, ?_⟩
    intro y hyI
    have hxy : x + y ∈ J := by
      refine h <| Set.mem_vadd_set.2 ⟨y, hyI, ?_⟩
      simp [vadd_eq_add]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using J.sub_mem hxy hxJ
  · rintro ⟨hxJ, hIJ⟩ z hz
    rcases Set.mem_vadd_set.1 hz with ⟨y, hyI, rfl⟩
    simpa [vadd_eq_add] using J.add_mem hxJ (hIJ hyI)

/-- Lemma 10.15.3 (Tag 0EHL): if each prime ideal in a finite family does not contain the coset
`x + I`, then one translate `x + y` with `y ∈ I` avoids all of them simultaneously. -/
-- Proof sketch: argue by induction on the number of prime ideals, as in the textbook proof.
-- Remove redundant inclusions among the primes, separate those that contain `x` from those that do
-- not, choose `y ∈ I` outside the next prime, and multiply it by an element lying in the earlier
-- primes but not in that next prime. This lets one enlarge the set of avoided primes step by step.
@[stacks 0EHL]
theorem exists_mem_ideal_add_not_mem_finset_primes
    {R : Type u} [CommRing R] {ι : Type v} {x : R} {I : Ideal R} (s : Finset ι)
    (p : ι → Ideal R) (hp : ∀ i ∈ s, (p i).IsPrime)
    (hx : ∀ i ∈ s, ¬ (x +ᵥ (I : Set R)) ⊆ (p i : Set R)) :
    ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i := by
  classical
  have havoid : ∀ i ∈ s, x ∈ p i → ¬ I ≤ p i := by
    intro i hi hxi hIp
    exact hx i hi <| (vadd_ideal_subset_iff.2 ⟨hxi, hIp⟩)
  let t : Finset ι := s.filter fun i ↦ ∀ j ∈ s, p i ≤ p j → p j ≤ p i
  let a : Finset ι := t.filter fun i ↦ x ∈ p i
  let b : Finset ι := t.filter fun i ↦ x ∉ p i
  let P : Ideal R := ∏ j ∈ b, p j
  let J : Ideal R := I * P
  have ht_mem : ∀ {i : ι}, i ∈ t → i ∈ s := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have ht_max : ∀ {i : ι}, i ∈ t → ∀ j ∈ s, p i ≤ p j → p j ≤ p i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hs_le_maximal : ∀ i ∈ s, ∃ j ∈ t, p i ≤ p j := by
    intro i hi
    let si : Finset ι := s.filter fun j ↦ p i ≤ p j
    have hsi : si.Nonempty := ⟨i, by simp [si, hi]⟩
    obtain ⟨j, hj⟩ := si.exists_maximalFor p hsi
    refine ⟨j, ?_, (Finset.mem_filter.mp hj.1).2⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hj.1).1
    · intro k hk hjk
      exact hj.2 (Finset.mem_filter.mpr ⟨hk, (Finset.mem_filter.mp hj.1).2.trans hjk⟩) hjk
  have hJ_not_le : ∀ i ∈ a, ¬ J ≤ p i := by
    intro i hi
    have hit : i ∈ t := (Finset.mem_filter.mp hi).1
    have his : i ∈ s := ht_mem hit
    have hxi : x ∈ p i := (Finset.mem_filter.mp hi).2
    obtain ⟨y, hyI, hy_not_mem⟩ : ∃ y ∈ I, y ∉ p i := by
      simpa [SetLike.le_def, Set.not_subset] using havoid i his hxi
    have hwitness : ∃ w ∈ P, w ∉ p i := by
      have hz : ∀ j ∈ b, ∃ z ∈ p j, z ∉ p i := by
        intro j hj
        have hjt : j ∈ t := (Finset.mem_filter.mp hj).1
        have hjs : j ∈ s := ht_mem hjt
        have hxj : x ∉ p j := (Finset.mem_filter.mp hj).2
        have hnot_le : ¬ p j ≤ p i := by
          intro hji
          have hij : p i ≤ p j := ht_max hjt i his hji
          exact hxj (hij hxi)
        simpa [SetLike.le_def, Set.not_subset] using hnot_le
      let z : ι → R := fun j ↦ if hj : j ∈ b then Classical.choose (hz j hj) else 1
      have hz_mem : ∀ j ∈ b, z j ∈ p j := by
        intro j hj
        simp [z, hj, (Classical.choose_spec (hz j hj)).1]
      have hz_not : ∀ j ∈ b, z j ∉ p i := by
        intro j hj
        simp [z, hj, (Classical.choose_spec (hz j hj)).2]
      refine ⟨∏ j ∈ b, z j, ?_, ?_⟩
      · dsimp [P]
        exact Ideal.prod_mem_prod fun j hj ↦ hz_mem j hj
      · have hpi : (p i).IsPrime := hp i his
        letI : (p i).IsPrime := hpi
        intro hprod
        have hprod' : ∏ j ∈ b, z j ∈ p i := by
          simpa using hprod
        have hprod_iff : (∏ j ∈ b, z j ∈ p i) ↔ ∃ j ∈ b, z j ∈ p i := by
          simpa using
            (show (∏ j ∈ b, z j ∈ p i) ↔ ∃ j ∈ b, z j ∈ p i from Ideal.IsPrime.prod_mem_iff)
        rcases hprod_iff.1 hprod' with ⟨j, hj, hzj⟩
        exact hz_not j hj (by simpa using hzj)
    obtain ⟨w, hwP, hw_not_mem⟩ := hwitness
    intro hJle
    have hmul_mem : y * w ∈ J := by
      dsimp [J]
      exact Ideal.mul_mem_mul hyI hwP
    have hmul : y * w ∈ p i := hJle hmul_mem
    have hpi : (p i).IsPrime := hp i his
    letI : (p i).IsPrime := hpi
    exact hpi.mem_or_mem hmul |>.elim hy_not_mem hw_not_mem
  have hy_exists : ∃ y ∈ J, ∀ i ∈ a, y ∉ p i := by
    by_cases ha : a.Nonempty
    · obtain ⟨i₀, hi₀⟩ := ha
      have hnot_subset : ¬ ((J : Set R) ⊆ ⋃ i ∈ (↑a : Set ι), p i) := by
        intro hsubset
        obtain ⟨i, hi, hle⟩ :=
          (Ideal.subset_union_prime i₀ i₀
            fun i hi _ _ ↦ hp i (ht_mem ((Finset.mem_filter.mp hi).1))).mp hsubset
        exact hJ_not_le i hi hle
      obtain ⟨y, hyJ, hyunion⟩ := Set.not_subset.mp hnot_subset
      refine ⟨y, hyJ, ?_⟩
      intro i hi hyi
      exact hyunion <| Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hyi⟩⟩
    · refine ⟨0, J.zero_mem, ?_⟩
      intro i hi
      exact (ha ⟨i, hi⟩).elim
  obtain ⟨y, hyJ, hyavoid⟩ := hy_exists
  have hyI : y ∈ I := by
    have hJI : J ≤ I := by
      dsimp [J]
      exact Ideal.mul_le_right
    exact hJI hyJ
  refine ⟨y, hyI, ?_⟩
  intro i hi
  obtain ⟨j, hjt, hij⟩ := hs_le_maximal i hi
  have hxy_not_j : x + y ∉ p j := by
    by_cases hxj : x ∈ p j
    · have hja : j ∈ a := Finset.mem_filter.mpr ⟨hjt, hxj⟩
      intro hxy
      have hyj : y ∈ p j := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (p j).sub_mem hxy hxj
      exact hyavoid j hja hyj
    · have hjb : j ∈ b := Finset.mem_filter.mpr ⟨hjt, hxj⟩
      have hyP : y ∈ P := by
        have hJP : J ≤ P := by
          dsimp [J]
          exact Ideal.mul_le_left
        exact hJP hyJ
      have hybInf : y ∈ b.inf p := (show P ≤ b.inf p by
          dsimp [P]
          exact Ideal.prod_le_inf) hyP
      have hyj : y ∈ p j := (show b.inf p ≤ p j from Finset.inf_le hjb) hybInf
      intro hxy
      have hxpj : x ∈ p j := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (p j).sub_mem hxy hyj
      exact hxj hxpj
  intro hxy
  exact hxy_not_j (hij hxy)
