import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall tool `lean_leansearch` was unavailable in this environment, so this file
-- follows the local finite-sum and filtered-powerset API directly.

/-- The subsets of `Fin n` whose `a`-weighted subset sum vanishes. -/
noncomputable abbrev zeroSumSubsets {n : ℕ} (a : Fin n → ℂ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powerset).filter (fun S ↦ S.sum a = 0)

/-- The subsets of `Fin n` whose `a`-weighted subset sum is nonzero. -/
noncomputable abbrev nonzeroSumSubsets {n : ℕ} (a : Fin n → ℂ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powerset).filter (fun S ↦ S.sum a ≠ 0)

/-- Helper for Lemma PI-05: the empty subset shows that there is at least one zero subset sum. -/
lemma zeroSumSubsets_card_pos {n : ℕ} (a : Fin n → ℂ) : 0 < (zeroSumSubsets a).card := by
  -- The empty subset belongs to the zero-sum class because its weighted sum is zero.
  refine Finset.card_pos.mpr ?_
  refine ⟨∅, ?_⟩
  simp [zeroSumSubsets]

/-- Helper for Lemma PI-05: the powerset exponential sum splits into zero-sum and nonzero-sum
parts. -/
lemma sum_powerset_exp_split_zero_nonzero {n : ℕ} (a : Fin n → ℂ) :
    (((Finset.univ : Finset (Fin n)).powerset).sum (fun S ↦ Complex.exp (S.sum a))) =
      Finset.sum (zeroSumSubsets a) (fun S ↦ Complex.exp (S.sum a)) +
        Finset.sum (nonzeroSumSubsets a) (fun S ↦ Complex.exp (S.sum a)) := by
  -- Split the powerset by the predicate that the subset sum vanishes.
  simpa [zeroSumSubsets, nonzeroSumSubsets] using
    (Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin n)).powerset)
      (fun S : Finset (Fin n) ↦ S.sum a = 0)
      (fun S ↦ Complex.exp (S.sum a))).symm

/-- Helper for Lemma PI-05: every zero-sum subset contributes `1 = exp 0`, so the zero part of
the split sum is the cardinality of `zeroSumSubsets a`. -/
lemma sum_exp_over_zeroSumSubsets_eq_card {n : ℕ} (a : Fin n → ℂ) :
    Finset.sum (zeroSumSubsets a) (fun S ↦ Complex.exp (S.sum a)) = ((zeroSumSubsets a).card : ℂ) := by
  -- Replace each zero-sum contribution by `exp 0 = 1`.
  calc
    (∑ S ∈ zeroSumSubsets a, Complex.exp (S.sum a)) = (∑ S ∈ zeroSumSubsets a, (1 : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hsum : S.sum a = 0 := (Finset.mem_filter.mp hS).2
      rw [hsum, Complex.exp_zero]
    _ = ((zeroSumSubsets a).card : ℂ) := by
      simp

/-- Helper for Lemma PI-05: the nonzero-sum contribution can be indexed by `Fin` via the canonical
enumeration of the finset `nonzeroSumSubsets a`. -/
lemma nonzeroSumSubsets_reindex_exp_sum {n : ℕ} (a : Fin n → ℂ) :
    let m := (nonzeroSumSubsets a).card
    let e : Fin m ≃ {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a} :=
      (Finset.equivFinOfCardEq (s := nonzeroSumSubsets a) rfl).symm
    Finset.sum (nonzeroSumSubsets a) (fun S ↦ Complex.exp (S.sum a)) =
      ∑ j, Complex.exp ((e j).1.sum a) := by
  classical
  dsimp
  let e' : {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a} ≃ Fin ((nonzeroSumSubsets a).card) :=
    Finset.equivFinOfCardEq (s := nonzeroSumSubsets a) rfl
  -- First rewrite the finset sum as a sum over the subtype of members of `nonzeroSumSubsets a`.
  calc
    (∑ S ∈ nonzeroSumSubsets a, Complex.exp (S.sum a)) =
        (∑ S : {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a}, Complex.exp (S.1.sum a)) := by
      rw [← Finset.sum_attach]
      rw [Finset.attach_eq_univ]
    -- Then transport that subtype sum along the canonical equivalence with `Fin`.
    _ = ∑ j : Fin ((nonzeroSumSubsets a).card), Complex.exp (((e'.symm j).1).sum a) := by
      exact Fintype.sum_equiv e'
        (fun S ↦ Complex.exp (S.1.sum a))
        (fun j ↦ Complex.exp (((e'.symm j).1).sum a))
        (fun S ↦ by simp)

/-- Lemma PI-05: if the total exponential sum over all subset sums of `a : Fin n → ℂ` vanishes,
then one can split off the zero subset sums as a nonzero integer constant `C`, where `C` is
exactly the number of subsets with subset sum zero, and enumerate the remaining nonzero subset
sums by a finite family `β`. -/
theorem exists_integer_and_nonzero_subset_sum_family_of_sum_powerset_exp_eq_zero {n : ℕ}
    (a : Fin n → ℂ)
    (h :
      (((Finset.univ : Finset (Fin n)).powerset).sum (fun S ↦ Complex.exp (S.sum a)) = 0)) :
    ∃ C : ℤ, ∃ m : ℕ, ∃ β : Fin m → ℂ,
      ∃ e : Fin m ≃ {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a},
        C = ((zeroSumSubsets a).card : ℤ) ∧
        C ≠ 0 ∧
        (∀ j, β j = (e j).1.sum a) ∧
        (∀ j, β j ≠ 0) ∧
        (C : ℂ) + ∑ j, Complex.exp (β j) = 0 := by
  classical
  let C : ℤ := ((zeroSumSubsets a).card : ℤ)
  let m : ℕ := (nonzeroSumSubsets a).card
  let e : Fin m ≃ {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a} :=
    (Finset.equivFinOfCardEq (s := nonzeroSumSubsets a) rfl).symm
  let β : Fin m → ℂ := fun j ↦ (e j).1.sum a
  refine ⟨C, m, β, e, ?_⟩
  refine ⟨rfl, ?_⟩
  have hCpos : 0 < (zeroSumSubsets a).card := zeroSumSubsets_card_pos a
  have hC_ne : C ≠ 0 := by
    -- The zero-sum class contains the empty subset, so its cardinality is nonzero.
    simpa [C] using (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hCpos))
  refine ⟨hC_ne, ?_⟩
  refine ⟨?_, ?_⟩
  · -- By definition, `β` records the subset sum attached to the corresponding nonzero subset.
    intro j
    rfl
  refine ⟨?_, ?_⟩
  · -- Membership in `nonzeroSumSubsets a` gives the required nonvanishing of each `β j`.
    intro j
    have hj : (e j).1 ∈ nonzeroSumSubsets a := (e j).2
    simpa [β, nonzeroSumSubsets] using (Finset.mem_filter.mp hj).2
  have hnonzero :
      Finset.sum (nonzeroSumSubsets a) (fun S ↦ Complex.exp (S.sum a)) = ∑ j, Complex.exp (β j) := by
    -- This is the canonical reindexing of the nonzero part by `Fin m`.
    simpa [m, e, β] using nonzeroSumSubsets_reindex_exp_sum a
  -- Assemble the source-faithful partition: zero-sum subsets contribute the constant term and
  -- the remaining subsets contribute the finite exponential family.
  calc
    (C : ℂ) + ∑ j, Complex.exp (β j)
        = ((zeroSumSubsets a).card : ℂ) + ∑ j, Complex.exp (β j) := by
          simp [C]
    _ = ((∑ S ∈ zeroSumSubsets a, Complex.exp (S.sum a)) +
          ∑ S ∈ nonzeroSumSubsets a, Complex.exp (S.sum a)) := by
          rw [← sum_exp_over_zeroSumSubsets_eq_card a, ← hnonzero]
    _ = (((Finset.univ : Finset (Fin n)).powerset).sum (fun S ↦ Complex.exp (S.sum a))) := by
          rw [← sum_powerset_exp_split_zero_nonzero a]
    _ = 0 := h
