import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Finset

/- Domain-style sampling for Lemma 10.115.1:
- primary domain: finite ordered families of multi-indices and weighted sums.
- inspected owner declarations: `Finsupp.weight`, `Finsupp.weight_apply`,
  `Finsupp.equivFunOnFinite`, and `MonomialOrder.lex`.
- best owner abstraction: `Finsupp.weight` on `σ →₀ ℕ`; the tuple model `Fin n → ℕ` is only a
  concrete presentation of the same multi-index data.

Primitive-vs-derived split:
- primitive data: a finite ordered index type `σ`, a finite set `N : Finset (σ →₀ ℕ)` of
  multi-indices, and a weight system `e : σ → ℕ`;
- derived API: the coordinate spread `sup - inf'` and the resulting injectivity statement for the
  canonical weight map. -/

/- Source/core/bridge triage for Lemma 10.115.1:
- `source-facing`: the domination inequalities on coordinates and the conclusion that the weighted
  sums distinguish the multi-indices in `N`;
- `core/canonical`: `Finsupp.weight`;
- `bridge/view`: the finite tuple picture recovered from `Finsupp.equivFunOnFinite`. -/

section

variable {σ : Type*}

/-- The spread of the `i`-th coordinate among the multi-indices in a finite set. It is `0` when
the set is empty. -/
def coordinateSpread (N : Finset (σ →₀ ℕ)) (i : σ) : ℕ :=
  if hN : N.Nonempty then N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) else 0

lemma coordinateSpread_eq (N : Finset (σ →₀ ℕ)) (hN : N.Nonempty) (i : σ) :
    coordinateSpread N i = N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) := by
  simp [coordinateSpread, hN]

variable [LinearOrder σ] [Fintype σ]

omit [LinearOrder σ] in
/-- Helper for Lemma 10.115.1: over a finite index type, the canonical weight is the full
coordinate sum. -/
lemma weight_eq_sum_univ (ν : σ →₀ ℕ) (e : σ → ℕ) :
    ν.weight e = ∑ j : σ, ν j * e j := by
  -- Rewrite the finitely supported sum as a sum over all coordinates.
  simpa [Finsupp.weight_apply, smul_eq_mul] using
    (Finsupp.sum_fintype ν (fun j n ↦ n * e j) fun _ ↦ by simp)

omit [LinearOrder σ] [Fintype σ] in
/-- Helper for Lemma 10.115.1: each coordinate of one multi-index is bounded by the corresponding
coordinate of another multi-index plus the spread of that coordinate in `N`. -/
lemma coordinate_le_add_coordinateSpread
    (N : Finset (σ →₀ ℕ)) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N) (i : σ) :
    ν i ≤ ν' i + coordinateSpread N i := by
  let hN : N.Nonempty := ⟨ν, hν⟩
  -- Compare `ν i` with the largest and smallest `i`-th coordinates occurring in `N`.
  rw [coordinateSpread_eq N hN i]
  have hν_sup : ν i ≤ N.sup (fun ρ ↦ ρ i) := by
    exact Finset.le_sup (s := N) (f := fun ρ : σ →₀ ℕ ↦ ρ i) hν
  have hinf_ν' : N.inf' hN (fun ρ ↦ ρ i) ≤ ν' i := Finset.inf'_le _ hν'
  have hinf_sup : N.inf' hN (fun ρ ↦ ρ i) ≤ N.sup (fun ρ ↦ ρ i) :=
    le_trans (Finset.inf'_le _ hν)
      (Finset.le_sup (s := N) (f := fun ρ : σ →₀ ℕ ↦ ρ i) hν)
  calc
    ν i ≤ N.sup (fun ρ ↦ ρ i) := hν_sup
    _ = N.inf' hN (fun ρ ↦ ρ i) + (N.sup (fun ρ ↦ ρ i) - N.inf' hN (fun ρ ↦ ρ i)) := by
      rw [Nat.add_sub_of_le hinf_sup]
    _ ≤ ν' i + (N.sup (fun ρ ↦ ρ i) - N.inf' hN (fun ρ ↦ ρ i)) :=
      Nat.add_le_add_right hinf_ν' _

/-- Helper for Lemma 10.115.1: the contribution of the coordinates strictly larger than `i` in one
multi-index is controlled by the corresponding contribution of another multi-index plus the tail
spread bound. -/
lemma later_weight_le_add_tail_spread
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N) (i : σ) :
    Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) ≤
      (Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν' j * e j) +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ coordinateSpread N j * e j)) := by
  -- Bound each later coordinate separately, then sum those bounds.
  calc
    Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) ≤
        Finset.sum (univ.filter (fun j : σ ↦ i < j))
          (fun j ↦ (ν' j + coordinateSpread N j) * e j) := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      exact Nat.mul_le_mul_right _ (coordinate_le_add_coordinateSpread N hν hν' j)
    _ = Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν' j * e j) +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ coordinateSpread N j * e j) := by
      simp_rw [Nat.add_mul]
      rw [Finset.sum_add_distrib]

/-- Helper for Lemma 10.115.1: split the weight into the coordinates below `i`, the pivot
coordinate `i`, and the coordinates above `i`. -/
lemma weight_eq_sum_lt_add_self_add_sum_gt (ν : σ →₀ ℕ) (e : σ → ℕ) (i : σ) :
    ν.weight e =
      ((Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν j * e j)) +
        ν i * e i +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j)) := by
  have hsplit :
      Finset.sum (univ.filter (fun j : σ ↦ j ≤ i)) (fun j ↦ ν j * e j) +
          Finset.sum (univ.filter (fun j : σ ↦ ¬ j ≤ i)) (fun j ↦ ν j * e j) =
        Finset.sum univ (fun j ↦ ν j * e j) := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not univ (fun j : σ ↦ j ≤ i) fun j ↦ ν j * e j)
  have hi_mem : i ∈ univ.filter (fun j : σ ↦ j ≤ i) := by
    simp
  -- Isolate the pivot term from the `≤ i` part and identify the remaining coordinates with `< i`.
  calc
    ν.weight e = Finset.sum univ (fun j ↦ ν j * e j) := by
      simpa using weight_eq_sum_univ ν e
    _ = Finset.sum (univ.filter (fun j : σ ↦ j ≤ i)) (fun j ↦ ν j * e j) +
        Finset.sum (univ.filter (fun j : σ ↦ ¬ j ≤ i)) (fun j ↦ ν j * e j) := by
      exact hsplit.symm
    _ = (ν i * e i +
        Finset.sum ((univ.filter (fun j : σ ↦ j ≤ i)) \ {i}) (fun j ↦ ν j * e j)) +
        Finset.sum (univ.filter (fun j : σ ↦ ¬ j ≤ i)) (fun j ↦ ν j * e j) := by
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi_mem]
    _ = (ν i * e i + Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν j * e j)) +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) := by
      have hlt :
          (univ.filter (fun j : σ ↦ j ≤ i)) \ {i} = univ.filter (fun j : σ ↦ j < i) := by
        ext j
        simp [lt_iff_le_and_ne, eq_comm]
      have hgt :
          univ.filter (fun j : σ ↦ ¬ j ≤ i) = univ.filter (fun j : σ ↦ i < j) := by
        ext j
        simp [not_le]
      rw [hlt, hgt]
    _ = Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν j * e j) +
        ν i * e i +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) := by
      ac_rfl

/-- Helper for Lemma 10.115.1: if the first differing coordinate of two multi-indices satisfies
`ν i < ν' i`, then the domination inequality at `i` forces `ν.weight e < ν'.weight e`. -/
lemma weight_lt_of_first_difference
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    {i : σ} (hearlier : ∀ j : σ, j < i → ν j = ν' j) (hi : ν i < ν' i)
    (hi_dom : e i >
      (Finset.sum (univ.filter fun j : σ ↦ i < j) (fun j ↦ coordinateSpread N j * e j))) :
    ν.weight e < ν'.weight e := by
  set earlierWeight := Finset.sum (univ.filter (fun j : σ ↦ j < i))
    (fun j ↦ ν j * e j) with hearlierWeight_def
  set laterWeight := Finset.sum (univ.filter (fun j : σ ↦ i < j))
    (fun j ↦ ν j * e j) with hlaterWeight_def
  set laterWeightPrime := Finset.sum (univ.filter (fun j : σ ↦ i < j))
    (fun j ↦ ν' j * e j) with hlaterWeightPrime_def
  set tailBound := Finset.sum (univ.filter (fun j : σ ↦ i < j))
    (fun j ↦ coordinateSpread N j * e j) with htailBound_def
  have hearlierWeight :
      earlierWeight = Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν' j * e j) := by
    -- The two multi-indices agree on all earlier coordinates by assumption.
    rw [hearlierWeight_def]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    exact congrArg (fun n ↦ n * e j) (hearlier j (by simpa using (Finset.mem_filter.mp hj).2))
  have hlaterWeight :
      laterWeight ≤ laterWeightPrime + tailBound := by
    -- The later coordinates are controlled by the corresponding spreads.
    simpa [hlaterWeight_def, hlaterWeightPrime_def, htailBound_def] using
      later_weight_le_add_tail_spread N e hν hν' i
  have hlaterWeight_lt : laterWeight < laterWeightPrime + e i := by
    -- The domination hypothesis makes the total later error strictly smaller than the pivot weight.
    exact lt_of_le_of_lt hlaterWeight (Nat.add_lt_add_left hi_dom laterWeightPrime)
  have hi_step : ν i + 1 ≤ ν' i := Nat.succ_le_of_lt hi
  have hpivot :
      ν i * e i + e i ≤ ν' i * e i := by
    -- Moving from `ν i` to `ν' i` gains at least one full copy of `e i`.
    calc
      ν i * e i + e i = (ν i + 1) * e i := by
        rw [Nat.add_mul, one_mul]
      _ = e i * (ν i + 1) := by
        rw [Nat.mul_comm]
      _ ≤ e i * ν' i := Nat.mul_le_mul_left (e i) hi_step
      _ = ν' i * e i := by
        rw [Nat.mul_comm]
  -- Compare the split forms of the two weights term-by-term.
  calc
    ν.weight e = earlierWeight + ν i * e i + laterWeight := by
      rw [hearlierWeight_def, hlaterWeight_def]
      exact weight_eq_sum_lt_add_self_add_sum_gt ν e i
    _ < earlierWeight + (ν i * e i + e i) + laterWeightPrime := by
      have :
          earlierWeight + (ν i * e i + laterWeight) <
            earlierWeight + (ν i * e i + (laterWeightPrime + e i)) := by
        exact Nat.add_lt_add_left
          (Nat.add_lt_add_left hlaterWeight_lt (ν i * e i)) earlierWeight
      simpa [add_assoc, add_left_comm, add_comm] using this
    _ ≤ earlierWeight + ν' i * e i + laterWeightPrime := by
      simpa [add_assoc] using
        (Nat.add_le_add_left (Nat.add_le_add_right hpivot laterWeightPrime) earlierWeight)
    _ = ν'.weight e := by
      rw [hearlierWeight, hlaterWeightPrime_def]
      exact (weight_eq_sum_lt_add_self_add_sum_gt ν' e i).symm

/-- Lemma 10.115.1: if each weight `e i` dominates the tail weighted by the coordinate spreads of
`N`, then the canonical weighted sums `ν.weight e` distinguish the multi-indices in `N`. -/
-- Proof sketch: let `i` be the first coordinate where `ν` and `ν'` differ. The domination
-- hypothesis makes the contribution of coordinate `i` larger than the total possible contribution
-- of all later coordinates, so equality of weighted sums forces agreement in coordinate `i`;
-- iterate on the tail.
@[stacks 051M]
lemma weighted_sum_eq_iff_eq_of_dominating_weights
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    (he : ∀ i : σ,
      e i >
        Finset.sum (univ.filter fun j : σ ↦ i < j)
          (fun j ↦ coordinateSpread N j * e j)) :
    ν.weight e = ν'.weight e ↔ ν = ν' := by
  constructor
  · intro hweight
    classical
    by_contra hne
    let S : Finset σ := univ.filter fun j : σ ↦ ν j ≠ ν' j
    have hS : S.Nonempty := by
      -- A nontrivial difference between `ν` and `ν'` produces a first differing coordinate.
      rcases Finsupp.ne_iff.mp hne with ⟨j, hj⟩
      exact ⟨j, by simp [S, hj]⟩
    let i : σ := S.min' hS
    have hi_mem : i ∈ S := Finset.min'_mem S hS
    have hi_ne : ν i ≠ ν' i := by
      simpa [S] using (Finset.mem_filter.mp hi_mem).2
    have hearlier : ∀ j : σ, j < i → ν j = ν' j := by
      -- Minimality of `i` forces agreement on all earlier coordinates.
      intro j hj
      by_contra hj_ne
      have hj_mem : j ∈ S := by
        simp [S, hj_ne]
      have hi_le_j : i ≤ j := Finset.min'_le S j hj_mem
      exact (not_le_of_gt hj) hi_le_j
    rcases lt_or_gt_of_ne hi_ne with hlt | hgt
    · have hlt_weight : ν.weight e < ν'.weight e :=
        weight_lt_of_first_difference N e hν hν' hearlier hlt (he i)
      exact (ne_of_lt hlt_weight) hweight
    · have hgt_weight : ν'.weight e < ν.weight e :=
        weight_lt_of_first_difference N e hν' hν
          (fun j hj ↦ (hearlier j hj).symm) hgt (he i)
      exact (ne_of_gt hgt_weight) hweight
  · intro hEq
    -- The reverse implication is immediate by substitution.
    simpa [hEq]

end
