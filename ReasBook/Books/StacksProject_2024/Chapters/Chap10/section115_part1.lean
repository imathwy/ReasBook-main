import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_115_1 (from Chap10) -/
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

/-! ### Lemma_10_115_2 (from Chap10) -/
open scoped BigOperators
open MvPolynomial

universe u

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

private noncomputable def noetherNormalizationInverseShear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.aeval
    (Fin.snoc (fun i : Fin n ↦ X i.castSucc - X (Fin.last n) ^ e i) (X (Fin.last n)))

/-- The triangular automorphism `x_i ↦ x_i + x_n^(e i)` for `i < n`, with the last variable
`x_n` fixed. Here `MvPolynomial (Fin (n + 1)) R` is viewed as `R[x₁, …, xₙ, x_n]`, and
`Fin.last n` plays the role of `x_n`. -/
noncomputable def noetherNormalizationShear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval
      (Fin.snoc (fun i : Fin n ↦ X i.castSucc + X (Fin.last n) ^ e i) (X (Fin.last n))))
    (noetherNormalizationInverseShear e)
    (by
      ext i
      cases i using Fin.lastCases <;> simp [noetherNormalizationInverseShear])
    (by
      ext i
      cases i using Fin.lastCases <;> simp [noetherNormalizationInverseShear])

/-- The canonical view of `MvPolynomial (Fin (n + 1)) R` as polynomials in the last variable
with coefficients in the first `n` variables. -/
noncomputable def noetherNormalizationLastVariableEquiv :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans (MvPolynomial.optionEquivLeft R (Fin n))

@[simp] theorem noetherNormalizationLastVariableEquiv_X_castSucc (i : Fin n) :
    (noetherNormalizationLastVariableEquiv :
      MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)) (X (Fin.castSucc i)) =
      Polynomial.C (X i) := by
  simp [noetherNormalizationLastVariableEquiv]

@[simp] theorem noetherNormalizationLastVariableEquiv_X_last :
    (noetherNormalizationLastVariableEquiv :
      MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)) (X (Fin.last n)) =
      Polynomial.X := by
  simp [noetherNormalizationLastVariableEquiv]

/-- The sheared polynomial, viewed as a polynomial in the last variable over the first `n`
variables. -/
noncomputable def noetherNormalizationLastVariablePolynomial (e : Fin n → ℕ)
    (g : MvPolynomial (Fin (n + 1)) R) : Polynomial (MvPolynomial (Fin n) R) :=
  noetherNormalizationLastVariableEquiv (noetherNormalizationShear e g)

/-- The weight inequalities expressing `e₁ ≫ e₂ ≫ ⋯ ≫ eₙ₋₁ ≫ 1` relative to the support of
`g`. -/
def noetherNormalizationDominatingWeights (g : MvPolynomial (Fin (n + 1)) R)
    (e : Fin n → ℕ) : Prop :=
  let w : Fin (n + 1) → ℕ := Fin.snoc e 1
  let spread : Fin (n + 1) → ℕ := fun i ↦
    (g.support.product g.support).sup fun m ↦ m.1 i - m.2 i
  g.support.Nonempty ∧
    ∀ i : Fin (n + 1),
      w i >
        Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ i < j)
          (fun j ↦ spread j * w j)

/-- A dominating system of weights can occur only when the support of the polynomial is nonempty. -/
-- Proof sketch: unfold `noetherNormalizationDominatingWeights`; its first component is the
-- nonemptiness of `g.support`.
theorem noetherNormalizationDominatingWeights_support_nonempty
    {g : MvPolynomial (Fin (n + 1)) R} {e : Fin n → ℕ}
    (he : noetherNormalizationDominatingWeights g e) :
    g.support.Nonempty := by
  simpa [noetherNormalizationDominatingWeights] using he.1

/-- Helper for Lemma 10.115.2: the coordinate spread used in Lemma `10.115.1` is bounded by the
pairwise coordinate spread appearing in `noetherNormalizationDominatingWeights`. -/
private lemma coordinateSpread_le_support_pair_spread
    (g : MvPolynomial (Fin (n + 1)) R) (hN : g.support.Nonempty) (i : Fin (n + 1)) :
    coordinateSpread g.support i ≤
      (g.support.product g.support).sup (fun m ↦ m.1 i - m.2 i) := by
  -- Realize the extremal spread as a difference of one support pair.
  rw [coordinateSpread_eq g.support hN i]
  obtain ⟨mMax, hmMax, hmMax_eq⟩ := Finset.exists_mem_eq_sup g.support hN fun m ↦ m i
  obtain ⟨mMin, hmMin, hmMin_eq⟩ :=
    Finset.exists_mem_eq_inf' (s := g.support) hN fun m ↦ m i
  have hpair : (mMax, mMin) ∈ g.support.product g.support := by
    simp [hmMax, hmMin]
  calc
    g.support.sup (fun m ↦ m i) - g.support.inf' hN (fun m ↦ m i) = mMax i - mMin i := by
      rw [hmMax_eq, hmMin_eq]
    _ ≤ (g.support.product g.support).sup (fun m ↦ m.1 i - m.2 i) :=
      Finset.le_sup (f := fun m ↦ m.1 i - m.2 i) hpair

/-- Helper for Lemma 10.115.2: dominating weights are positive on the first `n` coordinates. -/
private lemma dominating_weights_positive
    {g : MvPolynomial (Fin (n + 1)) R} {e : Fin n → ℕ}
    (he : noetherNormalizationDominatingWeights g e) :
    ∀ i : Fin n, 0 < e i := by
  intro i
  -- The domination inequality bounds `e i` below by a nonnegative tail sum.
  have hi := he.2 (Fin.castSucc i)
  exact lt_of_le_of_lt (Nat.zero_le _) (by simpa [noetherNormalizationDominatingWeights] using hi)

/-- Helper for Lemma 10.115.2: among the support monomials there is a unique one of maximal
dominating weight. -/
private lemma exists_unique_max_weight_support_monomial
    (g : MvPolynomial (Fin (n + 1)) R) (e : Fin n → ℕ)
    (he : noetherNormalizationDominatingWeights g e) :
    let w : Fin (n + 1) → ℕ := Fin.snoc e 1
    ∃ m₀ ∈ g.support,
      (∀ m ∈ g.support, m.weight w ≤ m₀.weight w) ∧
        ∀ m ∈ g.support, m.weight w = m₀.weight w → m = m₀ := by
  let w : Fin (n + 1) → ℕ := Fin.snoc e 1
  let hN : g.support.Nonempty := noetherNormalizationDominatingWeights_support_nonempty he
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image g.support (fun m ↦ m.weight w) hN
  refine ⟨m₀, hm₀, hmax, ?_⟩
  intro m hm hEq
  -- Lemma `10.115.1` turns equality of dominating weights into equality of monomials.
  exact
    (weighted_sum_eq_iff_eq_of_dominating_weights g.support w hm hm₀ (fun i ↦ by
      refine lt_of_le_of_lt ?_ (he.2 i)
      refine Finset.sum_le_sum fun j hj ↦ ?_
      exact Nat.mul_le_mul_right _ (coordinateSpread_le_support_pair_spread g hN j))).mp hEq

/-- Helper for Lemma 10.115.2: a nonconstant multivariate polynomial has a nonzero support
monomial. -/
private lemma exists_support_ne_zero_of_not_exists_C
    (g : MvPolynomial (Fin (n + 1)) R) (hg : ¬ ∃ a : R, g = C a) :
    ∃ m ∈ g.support, m ≠ 0 := by
  by_contra h
  have hsupp_zero : ∀ m ∈ g.support, m = 0 := by
    intro m hm
    by_contra hm0
    exact h ⟨m, hm, hm0⟩
  have hconst : g = C (g.coeff 0) := by
    -- If every support monomial is `0`, all nonzero coefficients occur at the constant monomial.
    ext m
    by_cases hm : m = 0
    · subst hm
      simp
    · have hnotmem : m ∉ g.support := by
        intro hm_mem
        exact hm (hsupp_zero m hm_mem)
      have hcoeff : g.coeff m = 0 := by
        exact notMem_support_iff.mp hnotmem
      simpa [MvPolynomial.coeff_C, eq_comm, hm] using hcoeff
  exact hg ⟨g.coeff 0, hconst⟩

/-- Helper for Lemma 10.115.2: after the triangular shear, a support monomial becomes a polynomial
in the last variable whose degree is the weighted sum of its exponents. -/
private lemma noetherNormalizationLastVariablePolynomial_monomial_eq
    (e : Fin n → ℕ) (m : Fin (n + 1) →₀ ℕ) (r : R) :
    noetherNormalizationLastVariablePolynomial e (monomial m r) =
      Polynomial.C (MvPolynomial.C r) *
        (Polynomial.X ^ m (Fin.last n) *
          ∏ i : Fin n, (Polynomial.C (X i) + Polynomial.X ^ e i) ^ m i.castSucc) := by
  rw [noetherNormalizationLastVariablePolynomial, noetherNormalizationShear, monomial_eq,
    Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, map_pow, AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, algebraMap_eq, Fin.prod_univ_castSucc]
    simp [noetherNormalizationLastVariableEquiv, mul_comm]
  · intro i
    simp

/-- Helper for Lemma 10.115.2: a nonzero multi-index has positive weight for any positive
dominating system of weights. -/
private lemma weight_pos_of_ne_zero
    (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) {m : Fin (n + 1) →₀ ℕ} (hm : m ≠ 0) :
    0 < m.weight (Fin.snoc e 1) := by
  let w : Fin (n + 1) → ℕ := Fin.snoc e 1
  rcases Finsupp.ne_iff.mp hm with ⟨i, hi⟩
  have hmi : 0 < m i := Nat.pos_of_ne_zero hi
  have hwi : 0 < w i := by
    cases i using Fin.lastCases with
    | cast j =>
        simpa [w] using he_pos j
    | last =>
        simpa [w]
  have hsingle : m i * w i ≤ m.weight w := by
    rw [weight_eq_sum_univ m w]
    exact Finset.single_le_sum (f := fun j : Fin (n + 1) ↦ m j * w j)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  exact lt_of_lt_of_le (Nat.mul_pos hmi hwi) (by simpa [w] using hsingle)

/-- Helper for Lemma 10.115.2: the product part of the transformed monomial is monic in the last
variable. -/
private lemma monic_noetherNormalizationLastVariablePolynomial_monomial_tail
    (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) :
    (Polynomial.X ^ m (Fin.last n) *
        ∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
          m i.castSucc).Monic := by
  have hbase :
      ∀ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i).Monic := by
    intro i
    rw [add_comm]
    exact Polynomial.monic_X_pow_add_C (MvPolynomial.X (R := R) i) (Nat.ne_of_gt (he_pos i))
  have hprod :
      (∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
          m i.castSucc).Monic := by
    exact Polynomial.monic_prod_of_monic _ _ fun i _ ↦ (hbase i).pow _
  exact (Polynomial.monic_X_pow _).mul hprod

/-- Helper for Lemma 10.115.2: the monic factor in the transformed monomial has weighted degree. -/
private lemma natDegree_noetherNormalizationLastVariablePolynomial_monomial_tail
    [Nontrivial R] (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) :
    (Polynomial.X ^ m (Fin.last n) *
        ∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
          m i.castSucc).natDegree =
      m.weight (Fin.snoc e 1) := by
  have hbase :
      ∀ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i).Monic := by
    intro i
    rw [add_comm]
    exact Polynomial.monic_X_pow_add_C (MvPolynomial.X (R := R) i) (Nat.ne_of_gt (he_pos i))
  have hprod :
      (∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
          m i.castSucc).Monic := by
    exact Polynomial.monic_prod_of_monic _ _ fun i _ ↦ (hbase i).pow _
  have hbase_natDegree :
      ∀ i : Fin n,
        (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i).natDegree = e i := by
    intro i
    rw [add_comm, Polynomial.natDegree_X_pow_add_C]
  rw [(Polynomial.monic_X_pow _).natDegree_mul hprod, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_prod_of_monic]
  · rw [weight_eq_sum_univ m (Fin.snoc e 1), Fin.sum_univ_castSucc]
    have hpow_natDegree :
        ∀ i : Fin n,
          ((Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^ m i.castSucc).natDegree =
            m i.castSucc * e i := by
      intro i
      rw [(hbase i).natDegree_pow (m i.castSucc)]
      rw [hbase_natDegree i]
    simp_rw [hpow_natDegree]
    simp
    ac_rfl
  · intro i hi
    exact (hbase i).pow _

private lemma natDegree_noetherNormalizationLastVariablePolynomial_monomial
    [Nontrivial R] (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) {r : R}
    (hr : r ≠ 0) :
    (noetherNormalizationLastVariablePolynomial e (monomial m r)).natDegree =
      m.weight (Fin.snoc e 1) := by
  rw [noetherNormalizationLastVariablePolynomial_monomial_eq]
  have hCr : MvPolynomial.C (σ := Fin n) r ≠ 0 := by
    simpa using hr
  have htail :
      MvPolynomial.C (σ := Fin n) r *
          (Polynomial.X ^ m (Fin.last n) *
            ∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
              m i.castSucc).leadingCoeff ≠
        0 := by
    simpa [(monic_noetherNormalizationLastVariablePolynomial_monomial_tail e he_pos m).leadingCoeff]
      using hCr
  rw [Polynomial.natDegree_C_mul_of_mul_ne_zero htail]
  exact natDegree_noetherNormalizationLastVariablePolynomial_monomial_tail e he_pos m

/-- Helper for Lemma 10.115.2: the top `x_n`-coefficient of a transformed support monomial is the
original scalar coefficient. -/
private lemma leadingCoeff_noetherNormalizationLastVariablePolynomial_monomial
    (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) {r : R} :
    (noetherNormalizationLastVariablePolynomial e (monomial m r)).leadingCoeff = C r := by
  rw [noetherNormalizationLastVariablePolynomial_monomial_eq]
  simpa using
    (monic_noetherNormalizationLastVariablePolynomial_monomial_tail e he_pos m).leadingCoeff_C_mul
      (MvPolynomial.C (σ := Fin n) r)

/-- Lemma 10.115.2: after the triangular substitution `x_i ↦ x_i + x_n^(e i)` with dominating
weights, a nonconstant polynomial acquires positive degree in `x_n`, and its leading coefficient
is a constant coefficient already occurring in the original polynomial. -/
-- Proof sketch: expand `g` as a finite sum of monomials and compare the resulting `x_n`-degrees
-- after the substitution. The dominating-weight hypothesis, via Lemma `10.115.1`, gives a unique
-- monomial of maximal weighted degree, so the highest `x_n`-term comes from a single support
-- monomial and has coefficient equal to the corresponding coefficient of `g`.
theorem exists_positive_natDegree_and_constant_leadingCoeff_of_noetherNormalizationLastVariablePolynomial
    (g : MvPolynomial (Fin (n + 1)) R) (hg : ¬ ∃ a : R, g = C a)
    (e : Fin n → ℕ) (he : noetherNormalizationDominatingWeights g e) :
    let p := noetherNormalizationLastVariablePolynomial e g
    0 < p.natDegree ∧ ∃ a : R, p.leadingCoeff = C a ∧ ∃ m ∈ g.support, g.coeff m = a := by
  dsimp
  let w : Fin (n + 1) → ℕ := Fin.snoc e 1
  let hmono : (Fin (n + 1) →₀ ℕ) → Polynomial (MvPolynomial (Fin n) R) := fun m ↦
    noetherNormalizationLastVariablePolynomial e (monomial m (g.coeff m))
  let he_pos : ∀ i : Fin n, 0 < e i := dominating_weights_positive he
  obtain ⟨m₀, hm₀, hmax, huniq⟩ := exists_unique_max_weight_support_monomial g e he
  obtain ⟨m₁, hm₁, hm₁_ne_zero⟩ := exists_support_ne_zero_of_not_exists_C g hg
  have hm₀_coeff : g.coeff m₀ ≠ 0 := mem_support_iff.mp hm₀
  letI : Nontrivial R := ⟨⟨0, g.coeff m₀, hm₀_coeff.symm⟩⟩
  have hm₀_natDegree : (hmono m₀).natDegree = m₀.weight w := by
    exact natDegree_noetherNormalizationLastVariablePolynomial_monomial e he_pos m₀ hm₀_coeff
  have hm₀_leadingCoeff : (hmono m₀).leadingCoeff = C (g.coeff m₀) := by
    exact leadingCoeff_noetherNormalizationLastVariablePolynomial_monomial e he_pos m₀
  have hm₀_ne : hmono m₀ ≠ 0 := by
    intro hm₀_zero
    have hzero : MvPolynomial.C (σ := Fin n) (g.coeff m₀) = 0 := by
      simpa [hm₀_leadingCoeff] using congrArg Polynomial.leadingCoeff hm₀_zero
    exact hm₀_coeff (by simpa using hzero)
  have hm₁_pos : 0 < m₁.weight w := weight_pos_of_ne_zero e he_pos hm₁_ne_zero
  have hm₀_pos : 0 < m₀.weight w := lt_of_lt_of_le hm₁_pos (hmax m₁ hm₁)
  have hp_sum :
      noetherNormalizationLastVariablePolynomial e g = ∑ m ∈ g.support, hmono m := by
    have hshear_sum :
        noetherNormalizationShear e g =
          ∑ m ∈ g.support, noetherNormalizationShear e (monomial m (g.coeff m)) := by
      conv_lhs => rw [g.as_sum]
      rw [map_sum]
    simpa [hmono, noetherNormalizationLastVariablePolynomial] using
      congrArg noetherNormalizationLastVariableEquiv hshear_sum
  have hsmaller :
      ∀ x ∈ g.support \ {m₀}, (hmono x).degree < (hmono m₀).degree := by
    intro x hx
    obtain ⟨hx_support, hx_ne⟩ := Finset.mem_sdiff.mp hx
    have hx_coeff : g.coeff x ≠ 0 := mem_support_iff.mp hx_support
    have hx_natDegree : (hmono x).natDegree = x.weight w := by
      exact natDegree_noetherNormalizationLastVariablePolynomial_monomial e he_pos x hx_coeff
    have hx_lt : x.weight w < m₀.weight w := by
      refine lt_of_le_of_ne (hmax x hx_support) ?_
      intro hEq
      exact hx_ne (by simpa using huniq x hx_support hEq)
    have hx_natDegree_lt : (hmono x).natDegree < (hmono m₀).natDegree := by
      simpa [hx_natDegree, hm₀_natDegree] using hx_lt
    exact Polynomial.degree_lt_degree hx_natDegree_lt
  have hdegree_rest :
      (∑ x ∈ g.support \ {m₀}, hmono x).degree < (hmono m₀).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    exact
      (Finset.sup_lt_iff <| Ne.bot_lt fun hx_bot ↦ hm₀_ne <| Polynomial.degree_eq_bot.mp hx_bot).mpr
        hsmaller
  have hp_natDegree :
      (noetherNormalizationLastVariablePolynomial e g).natDegree = (hmono m₀).natDegree := by
    rw [hp_sum, Finset.sum_eq_add_sum_diff_singleton_of_mem hm₀ hmono, add_comm]
    exact Polynomial.natDegree_add_eq_right_of_degree_lt hdegree_rest
  have hp_leadingCoeff :
      (noetherNormalizationLastVariablePolynomial e g).leadingCoeff = (hmono m₀).leadingCoeff := by
    rw [hp_sum, Finset.sum_eq_add_sum_diff_singleton_of_mem hm₀ hmono, add_comm]
    exact Polynomial.leadingCoeff_add_of_degree_lt hdegree_rest
  refine ⟨?_, g.coeff m₀, ?_, ⟨m₀, hm₀, rfl⟩⟩
  · rw [hp_natDegree, hm₀_natDegree]
    exact hm₀_pos
  · rw [hp_leadingCoeff, hm₀_leadingCoeff]

end

/-! ### Lemma_10_115_3 (from Chap10) -/
universe u

open MvPolynomial

section

variable {k : Type u} [Field k] {n : ℕ}

/-- Helper for Lemma 10.115.3: a nonzero element of a non-top ideal cannot be a nonzero
constant polynomial. -/
private lemma not_exists_eq_C_of_mem_ideal_ne_top
    {I : Ideal (MvPolynomial (Fin (n + 1)) k)} (hItop : I ≠ ⊤)
    {f : MvPolynomial (Fin (n + 1)) k} (hf_mem : f ∈ I) (hf_ne_zero : f ≠ 0) :
    ¬ ∃ a : k, f = C a := by
  intro hconst
  rcases hconst with ⟨a, rfl⟩
  have ha_ne_zero : a ≠ 0 := by
    intro ha
    apply hf_ne_zero
    simp [ha]
  have hunit : IsUnit (C a : MvPolynomial (Fin (n + 1)) k) := by
    exact (MvPolynomial.isUnit_iff_eq_C_of_isReduced).2 ⟨a, isUnit_iff_ne_zero.mpr ha_ne_zero, rfl⟩
  exact hItop (I.eq_top_of_isUnit_mem hf_mem hunit)

/-- Helper for Lemma 10.115.3: the sheared generators belong to the `ℤ`-subalgebra generated by
the coordinate variables. -/
private lemma sheared_generator_mem_int_adjoin (e : Fin n → ℕ) (i : Fin n) :
    X i.castSucc - X (Fin.last n) ^ e i ∈
      Algebra.adjoin ℤ (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)) := by
  -- Both terms are built from coordinate variables, so the difference stays in the same adjoin.
  refine Subalgebra.sub_mem _ ?_ ?_
  · exact Algebra.subset_adjoin ⟨i.castSucc, rfl⟩
  · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by exact ⟨Fin.last n, rfl⟩)) _

/-- Helper for Lemma 10.115.3: geometric weights dominate any prescribed tail spread after
normalizing the last weight to `1`. -/
private lemma exists_tail_dominating_weights (spread : Fin (n + 1) → ℕ) :
    ∃ w : Fin (n + 1) → ℕ,
      w (Fin.last n) = 1 ∧
        ∀ i : Fin (n + 1),
          w i >
            Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ i < j)
              (fun j ↦ spread j * w j) := by
  let B : ℕ := Finset.univ.sum spread + 1
  refine ⟨fun i ↦ B ^ (n - i.1), ?_, ?_⟩
  · -- The last coordinate has exponent `0`, so its weight is `1`.
    simp [B]
  · intro i
    cases i using Fin.lastCases with
    | last =>
        -- There are no coordinates larger than the last one.
        have hfilter :
            Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.last n < j = ∅ := by
          ext j
          simp [Fin.not_lt.2 j.le_last]
        simp [B, hfilter]
    | cast i =>
        let d : ℕ := n - (i.1 + 1)
        have hB_pos : 0 < B := Nat.succ_pos _
        have hB_one : 1 ≤ B := Nat.succ_le_of_lt hB_pos
        have hpow_pos : 0 < B ^ d := Nat.pow_pos hB_pos
        have hsum_bound :
            Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.castSucc i < j)
                (fun j ↦ spread j * B ^ (n - j.1)) ≤
              Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.castSucc i < j)
                (fun j ↦ spread j * B ^ d) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          have hij : i.1 < j.1 := by
            simpa using (Finset.mem_filter.mp hj).2
          have hsub : n - j.1 ≤ d := by
            omega
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB_one hsub)
        have hfilter_le :
            Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.castSucc i < j) spread ≤
              Finset.univ.sum spread := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro j _ _
          exact Nat.zero_le _
        have hlt_base :
            (Finset.univ.sum spread) * B ^ d < B * B ^ d := by
          refine Nat.mul_lt_mul_of_pos_right ?_ hpow_pos
          simp [B]
        have hpow_succ : B ^ (n - i.1) = B * B ^ d := by
          have hexp : n - i.1 = d + 1 := by
            omega
          rw [hexp, Nat.pow_succ]
          ring
        -- The tail is bounded by the total spread times the next smaller power of `B`.
        calc
          Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.castSucc i < j)
              (fun j ↦ spread j * B ^ (n - j.1))
              ≤
              Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.castSucc i < j)
                (fun j ↦ spread j * B ^ d) := hsum_bound
          _ = Finset.sum (Finset.univ.filter fun j : Fin (n + 1) ↦ Fin.castSucc i < j) spread *
                B ^ d := by
                rw [← Finset.sum_mul]
          _ ≤ (Finset.univ.sum spread) * B ^ d := Nat.mul_le_mul_right _ hfilter_le
          _ < B * B ^ d := hlt_base
          _ = B ^ (n - i.1) := hpow_succ.symm

/-- Helper for Lemma 10.115.3: a nonzero polynomial admits dominating weights for the triangular
shear used in the source proof. -/
private lemma exists_dominating_weights_of_ne_zero
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f ≠ 0) :
    ∃ e : Fin n → ℕ, noetherNormalizationDominatingWeights f e := by
  let spread : Fin (n + 1) → ℕ := fun i ↦
    (f.support.product f.support).sup fun m ↦ m.1 i - m.2 i
  obtain ⟨w, hw_last, hw_dom⟩ := exists_tail_dominating_weights (n := n) spread
  let e : Fin n → ℕ := fun i ↦ w i.castSucc
  have hsnoc : Fin.snoc e 1 = w := by
    ext i
    cases i using Fin.lastCases with
    | cast i =>
        simp [Fin.snoc, e]
    | last =>
        simpa [Fin.snoc, e] using hw_last.symm
  refine ⟨e, ?_⟩
  -- Route correction: the missing proof ingredient is an explicit dominating weight vector before
  -- invoking Lemma `10.115.2`; the geometric construction above supplies that vector.
  refine ⟨MvPolynomial.support_nonempty.mpr hf, ?_⟩
  intro i
  simpa [noetherNormalizationDominatingWeights, spread, e, hsnoc] using hw_dom i

/-- Helper for Lemma 10.115.3: evaluating the sheared last-variable polynomial at the quotient
classes of the sheared generators and the last coordinate recovers the class of the original
polynomial in the principal quotient. -/
private lemma sheared_last_variable_relation_in_principal_quotient
    (f : MvPolynomial (Fin (n + 1)) k) (e : Fin n → ℕ) :
    let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
    let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
      fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
    let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
      MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
    let xbar : (MvPolynomial (Fin (n + 1)) k) ⧸ J := Ideal.Quotient.mk J (X (Fin.last n))
    Polynomial.eval₂ g.toRingHom xbar (noetherNormalizationLastVariablePolynomial e f) = 0 := by
  -- TODO: prove the shear/evaluation composite equals the principal-quotient map on generators,
  -- then evaluate `f` and use `f ∈ Ideal.span {f}`.
  sorry

/-- Helper for Lemma 10.115.3: in the principal quotient, the class of the last variable is
integral over the range of the map defined by the sheared generators after normalizing the
constant leading coefficient to a monic equation over that range. -/
private lemma range_monic_normalization_of_constant_leadingCoeff
    (f : MvPolynomial (Fin (n + 1)) k) (e : Fin n → ℕ) {a : k}
    (hdeg : 0 < (noetherNormalizationLastVariablePolynomial e f).natDegree)
    (hlead : (noetherNormalizationLastVariablePolynomial e f).leadingCoeff = C a)
    (ha : a ≠ 0) :
    let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
    let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
      fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
    let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
      MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
    let A : Subalgebra k ((MvPolynomial (Fin (n + 1)) k) ⧸ J) := g.range
    let xbar : (MvPolynomial (Fin (n + 1)) k) ⧸ J := Ideal.Quotient.mk J (X (Fin.last n))
    ∃ q : Polynomial A, q.Monic ∧ Polynomial.aeval xbar q = 0 := by
  -- TODO: map the transformed relation into `g.range`, rewrite `val ∘ rangeRestrict = g`,
  -- and rescale by `a⁻¹` to obtain a monic polynomial over `g.range`.
  sorry

/-- Helper for Lemma 10.115.3: in the principal quotient, the class of the last variable is
integral over the range of the map defined by the sheared generators. -/
private lemma last_variable_isIntegral_over_generator_range
    (f : MvPolynomial (Fin (n + 1)) k) (e : Fin n → ℕ) {a : k}
    (hdeg : 0 < (noetherNormalizationLastVariablePolynomial e f).natDegree)
    (hlead : (noetherNormalizationLastVariablePolynomial e f).leadingCoeff = C a)
    (ha : a ≠ 0) :
    let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
    let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
      fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
    let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
      MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
    let A : Subalgebra k ((MvPolynomial (Fin (n + 1)) k) ⧸ J) := g.range
    let xbar : (MvPolynomial (Fin (n + 1)) k) ⧸ J := Ideal.Quotient.mk J (X (Fin.last n))
    IsIntegral A xbar := by
  let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
  let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
    fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
  let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
    MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
  let A : Subalgebra k ((MvPolynomial (Fin (n + 1)) k) ⧸ J) := g.range
  let xbar : (MvPolynomial (Fin (n + 1)) k) ⧸ J := Ideal.Quotient.mk J (X (Fin.last n))
  obtain ⟨q, hq_monic, hq_eval⟩ :=
    range_monic_normalization_of_constant_leadingCoeff
      (f := f) (e := e) (a := a) (hdeg := hdeg) (hlead := hlead) ha
  -- The normalized polynomial over `g.range` is exactly the monic integral equation for `xbar`.
  exact ⟨q, hq_monic, hq_eval⟩

/-- Helper for Lemma 10.115.3: every coordinate class in the principal quotient lies in the
subalgebra obtained by adjoining the last coordinate class to the range of the sheared generator
map. -/
private lemma coordinate_classes_mem_adjoin_last_variable
    (f : MvPolynomial (Fin (n + 1)) k) (e : Fin n → ℕ) :
    let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
    let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
      fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
    let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
      MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
    let A : Subalgebra k ((MvPolynomial (Fin (n + 1)) k) ⧸ J) := g.range
    let xbar : (MvPolynomial (Fin (n + 1)) k) ⧸ J := Ideal.Quotient.mk J (X (Fin.last n))
    ∀ j : Fin (n + 1),
      Ideal.Quotient.mk J (X j) ∈
        (Algebra.adjoin A ({xbar} : Set ((MvPolynomial (Fin (n + 1)) k) ⧸ J))).restrictScalars k := by
  -- TODO: show the last coordinate is the adjoined generator and each earlier coordinate equals
  -- a sheared generator from `g.range` plus a power of that last coordinate.
  sorry

/-- Helper for Lemma 10.115.3: adjoining the last variable class to the range of the sheared
generator map already recovers the whole principal quotient. -/
private lemma principal_quotient_adjoin_last_variable_eq_top
    (f : MvPolynomial (Fin (n + 1)) k) (e : Fin n → ℕ) :
    let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
    let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
      fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
    let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
      MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
    let A : Subalgebra k ((MvPolynomial (Fin (n + 1)) k) ⧸ J) := g.range
    let xbar : (MvPolynomial (Fin (n + 1)) k) ⧸ J := Ideal.Quotient.mk J (X (Fin.last n))
    Algebra.adjoin A ({xbar} : Set ((MvPolynomial (Fin (n + 1)) k) ⧸ J)) = ⊤ := by
  -- TODO: combine the coordinate-membership lemma with surjectivity of the quotient map to show
  -- the quotient is generated over `g.range` by the last coordinate class alone.
  sorry

/-- Helper for Lemma 10.115.3: the principal quotient by a nonconstant polynomial is finite over
the polynomial algebra generated by the sheared coordinates. -/
private lemma principal_quotient_finite_of_sheared_generators
    (f : MvPolynomial (Fin (n + 1)) k) (hf_not_const : ¬ ∃ a : k, f = C a)
    (e : Fin n → ℕ) {a : k}
    (hdeg :
      0 < (noetherNormalizationLastVariablePolynomial e f).natDegree)
    (hlead : (noetherNormalizationLastVariablePolynomial e f).leadingCoeff = C a)
    (ha : a ≠ 0) :
    let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
    let y : Fin n → MvPolynomial (Fin (n + 1)) k :=
      fun i ↦ X i.castSucc - X (Fin.last n) ^ e i
    let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
      MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)
    AlgHom.Finite g := by
  -- TODO: use integrality of the last coordinate over `g.range`, rewrite the simple adjoin as the
  -- whole quotient, and compose the resulting finite map with `g.rangeRestrict`.
  sorry

-- Proof sketch: choose a nonzero polynomial `f ∈ I`, reduce to the principal quotient by `f`,
-- and then use Lemma `10.115.2` to choose polynomial changes of variables so that the image of the
-- last variable is integral over the `k`-subalgebra generated by the images of the other chosen
-- generators; finiteness over that subalgebra follows from adjoining one integral element and then
-- composing with the quotient map from the principal quotient to the original quotient.
/-- Lemma 10.115.3: if `I` is a nonzero ideal of `k[X_0, ..., X_n]`, then the quotient is finite
over the `k`-subalgebra generated by the images of `n` suitable polynomials, and these polynomials
may be chosen in the `Z`-subalgebra generated by the coordinate variables. The source states this
for nonzero proper ideals; the properness hypothesis is redundant for this finiteness conclusion. -/
theorem exists_noether_normalization_generators_quotient_mvPolynomial
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hI : I ≠ ⊥) :
    ∃ y : Fin n → MvPolynomial (Fin (n + 1)) k,
      (∀ i, y i ∈ Algebra.adjoin ℤ (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k))) ∧
      let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
        MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (y i)
      AlgHom.Finite g := by
  classical
  by_cases hItop : I = ⊤
  · -- In the zero quotient, any choice of generators works.
    refine ⟨fun i ↦ X i.castSucc, ?_, ?_⟩
    · intro i
      exact Algebra.subset_adjoin ⟨i.castSucc, rfl⟩
    · let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
        MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (X i.castSucc)
      have hsurj : Function.Surjective g := by
        intro z
        refine ⟨0, ?_⟩
        have hsub : Subsingleton ((MvPolynomial (Fin (n + 1)) k) ⧸ I) := by
          subst hItop
          infer_instance
        exact Subsingleton.elim _ _
      simpa [g] using AlgHom.Finite.of_surjective g hsurj
  · -- Follow the source proof route through one nonzero equation and a triangular shear.
    obtain ⟨f, hf_mem, hf_ne_zero⟩ : ∃ f : MvPolynomial (Fin (n + 1)) k, f ∈ I ∧ f ≠ 0 := by
      by_contra hzero
      apply hI
      ext p
      constructor
      · intro hp
        by_contra hp0
        exact hzero ⟨p, hp, hp0⟩
      · intro hp
        subst hp
        exact I.zero_mem
    have hf_not_const : ¬ ∃ a : k, f = C a := by
      exact not_exists_eq_C_of_mem_ideal_ne_top hItop hf_mem hf_ne_zero
    obtain ⟨e, he⟩ := exists_dominating_weights_of_ne_zero (f := f) hf_ne_zero
    have hnorm :=
      exists_positive_natDegree_and_constant_leadingCoeff_of_noetherNormalizationLastVariablePolynomial
        (g := f) hf_not_const e he
    rcases hnorm with ⟨hdeg, a, hlead, hm⟩
    refine ⟨fun i ↦ X i.castSucc - X (Fin.last n) ^ e i, ?_, ?_⟩
    · intro i
      exact sheared_generator_mem_int_adjoin (e := e) i
    · let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span ({f} : Set _)
      let gJ : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ J) :=
        MvPolynomial.aeval fun i ↦
          Ideal.Quotient.mk J (X i.castSucc - X (Fin.last n) ^ e i)
      have ha : a ≠ 0 := by
        rcases hm with ⟨m, hm_mem, hm_coeff⟩
        rw [← hm_coeff]
        exact mem_support_iff.mp hm_mem
      have hfiniteJ : AlgHom.Finite gJ := by
        simpa [J, gJ] using principal_quotient_finite_of_sheared_generators
          (f := f) (hf_not_const := hf_not_const) (e := e) (hdeg := hdeg) (hlead := hlead) (ha := ha)
      have hJI : J ≤ I := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact hf_mem
      let π : ((MvPolynomial (Fin (n + 1)) k) ⧸ J) →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
        Ideal.quotientMapₐ (I := J) I (AlgHom.id k (MvPolynomial (Fin (n + 1)) k)) hJI
      have hπ_finite : AlgHom.Finite π := by
        refine AlgHom.Finite.of_surjective π ?_
        intro z
        rcases Ideal.Quotient.mk_surjective z with ⟨p, rfl⟩
        refine ⟨Ideal.Quotient.mk J p, ?_⟩
        simp [π]
      let g : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
        MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (X i.castSucc - X (Fin.last n) ^ e i)
      have hg_eq : π.comp gJ = g := by
        -- The quotient map preserves the chosen generators, so the two algebra maps agree.
        ext i
        simp [π, gJ, g]
      have hfinite_comp : AlgHom.Finite (π.comp gJ) := AlgHom.Finite.comp hπ_finite hfiniteJ
      simpa [hg_eq] using hfinite_comp

end

/-! ### Lemma_10_115_4 (from Chap10) -/
universe u

open MvPolynomial

section

variable {k : Type u} [Field k] {n : ℕ}

/-- Helper for Lemma 10.115.4: if an algebra map is finite, then the induced map from its kernel
quotient into the target is finite as well. -/
private lemma kerLiftAlg_finite_of_finite
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (hf : AlgHom.Finite f) :
    AlgHom.Finite (Ideal.kerLiftAlg f) := by
  -- The quotient map is surjective, so finiteness of the composite descends to `kerLiftAlg f`.
  let q : A →ₐ[R] A ⧸ RingHom.ker f := Ideal.Quotient.mkₐ R (RingHom.ker f)
  have hcomp : (Ideal.kerLiftAlg f).comp q = f := by
    -- This is the canonical factorization of `f` through its kernel quotient.
    ext a
    simp [q, Ideal.kerLiftAlg_mk]
  have hfinite_comp : AlgHom.Finite ((Ideal.kerLiftAlg f).comp q) := by
    simpa [hcomp] using hf
  exact AlgHom.Finite.of_comp_finite hfinite_comp

/-- Helper for Lemma 10.115.4: evaluating an integer-coefficient polynomial in generators that
already lie in the ambient coordinate `ℤ`-subalgebra stays inside that same `ℤ`-subalgebra. -/
private lemma aeval_mem_coordinate_int_adjoin {m n : ℕ}
    (y : Fin m → MvPolynomial (Fin n) k)
    (hy :
      ∀ i, y i ∈ Algebra.adjoin ℤ (Set.range (X : Fin n → MvPolynomial (Fin n) k)))
    {p : MvPolynomial (Fin m) k}
    (hp : p ∈ Algebra.adjoin ℤ (Set.range (X : Fin m → MvPolynomial (Fin m) k))) :
    MvPolynomial.aeval y p ∈ Algebra.adjoin ℤ (Set.range (X : Fin n → MvPolynomial (Fin n) k)) := by
  let A : Subalgebra ℤ (MvPolynomial (Fin n) k) :=
    Algebra.adjoin ℤ (Set.range (X : Fin n → MvPolynomial (Fin n) k))
  -- Follow the source proof literally: the target set is a `ℤ`-subalgebra, so it suffices to
  -- check the generators and then close under the ring operations.
  let P :
      (x : MvPolynomial (Fin m) k) →
        x ∈ Algebra.adjoin ℤ (Set.range (X : Fin m → MvPolynomial (Fin m) k)) → Prop :=
    fun x _ ↦ MvPolynomial.aeval y x ∈ A
  change P p hp
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hp
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    change MvPolynomial.aeval y (X i) ∈ A
    simpa [A] using hy i
  · intro z
    change MvPolynomial.aeval y (algebraMap ℤ (MvPolynomial (Fin m) k) z) ∈ A
    simpa [A]
  · intro a b ha hb hpa hpb
    change MvPolynomial.aeval y (a + b) ∈ A
    simpa [P, A, map_add] using A.add_mem hpa hpb
  · intro a b ha hb hpa hpb
    change MvPolynomial.aeval y (a * b) ∈ A
    simpa [P, A, map_mul] using A.mul_mem hpa hpb

/-
Source/core/bridge triage:
* primary domain: Noether normalization and Krull dimension for finite-type algebras over a field;
* sampled owner API:
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether normalization file,
  `exists_noether_normalization_generators_quotient_mvPolynomial` from Lemma `10.115.3`,
  `ringKrullDim_eq_of_injective_algebraMap_of_isIntegral` from Lemma `10.112.4`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing` for polynomial-ring dimension;
* source-facing: the quotient-form normalization statement with the extra `ℤ`-subalgebra choice;
* core/canonical: injective integral/finite polynomial-algebra maps and integral invariance of
  Krull dimension;
* bridge/view: part `(2)` is only the quotient/polynomial specialization of the owner theorem from
  Lemma `10.112.4`, while part `(1)` keeps the stronger source-facing generator choice.

Primitive data here are the chosen normalization polynomials in part `(1)` and the given finite
injective polynomial-algebra map in part `(2)`. The dimension equality in part `(2)` is derived API
from the sampled owner theorems and should be expressed as a thin specialization rather than as a
parallel local owner.
-/

-- Proof sketch: combine the quotient-form Noether normalization argument with the explicit
-- generators produced in the previous step of the induction, and then use the integrality-over-ℤ
-- refinement to choose those generators inside the `ℤ`-subalgebra generated by the coordinate
-- variables.
/-- Lemma 10.115.4 (1): for a proper quotient `S = k[x_1, \ldots, x_n] / I`, there are finitely
many polynomials `y₁, …, yᵣ` in the `ℤ`-subalgebra generated by the coordinate variables such that
the induced map from the polynomial ring on the `yᵢ` into `S` is injective and finite. -/
theorem exists_noether_normalization_polynomials_quotient_mvPolynomial
    (I : Ideal (MvPolynomial (Fin n) k)) (hIproper : I ≠ ⊤) :
    ∃ r : ℕ, ∃ y : Fin r → MvPolynomial (Fin n) k,
      (∀ i, y i ∈ Algebra.adjoin ℤ (Set.range (X : Fin n → MvPolynomial (Fin n) k))) ∧
      let g : MvPolynomial (Fin r) k →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I) :=
        MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (y i)
      Function.Injective g ∧ AlgHom.Finite g := by
  induction n with
  | zero =>
      refine ⟨0, fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · dsimp
        let g : MvPolynomial (Fin 0) k →ₐ[k] ((MvPolynomial (Fin 0) k) ⧸ I) :=
          MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (Fin.elim0 i)
        have hg : g = Ideal.Quotient.mkₐ k I := by
          -- With no variables, `aeval` is the canonical quotient map.
          ext i
          exact Fin.elim0 i
        have hginj : Function.Injective (Ideal.Quotient.mkₐ k I) := by
          intro a b hab
          rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab
          by_contra hne
          have habs : a - b = MvPolynomial.C (coeff 0 (a - b)) := eq_C_of_isEmpty (a - b)
          have hcoeff_ne : coeff 0 (a - b) ≠ 0 := by
            intro hcoeff
            apply hne
            have hsub : a - b = 0 := by
              rw [habs, hcoeff, MvPolynomial.C_0]
            exact sub_eq_zero.mp hsub
          obtain ⟨c, -, hcinv⟩ := isUnit_iff_exists.mp hcoeff_ne.isUnit
          have hone : c • (a - b) = 1 := by
            rw [MvPolynomial.smul_eq_C_mul, habs, ← map_mul, hcinv, MvPolynomial.C_1]
          exact hIproper ((Ideal.eq_top_iff_one I).mpr (hone ▸ I.smul_of_tower_mem c hab))
        have hgfinite : AlgHom.Finite (Ideal.Quotient.mkₐ k I) := by
          exact AlgHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective k I)
        simpa [g, hg] using And.intro hginj hgfinite
  | succ n ih =>
      by_cases hIbot : I = ⊥
      · refine ⟨n + 1, fun i ↦ X i, ?_, ?_⟩
        · intro i
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        · dsimp
          let g : MvPolynomial (Fin (n + 1)) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
            MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (X i)
          have hg : g = Ideal.Quotient.mkₐ k I := by
            -- Evaluating the coordinate tuple is exactly the quotient map.
            ext i
            simp [g]
          have hgbij : Function.Bijective (Ideal.Quotient.mkₐ k I) :=
            (Ideal.Quotient.mk_bijective_iff_eq_bot I).mpr hIbot
          have hgfinite : AlgHom.Finite (Ideal.Quotient.mkₐ k I) := by
            exact AlgHom.Finite.of_surjective _ hgbij.2
          simpa [g, hg] using And.intro hgbij.1 hgfinite
      · have _ : Nontrivial ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
          (Ideal.Quotient.nontrivial_iff).2 hIproper
        obtain ⟨y0, hy0, hg0_raw⟩ :=
          exists_noether_normalization_generators_quotient_mvPolynomial (I := I) hIbot
        let g0 : MvPolynomial (Fin n) k →ₐ[k] ((MvPolynomial (Fin (n + 1)) k) ⧸ I) :=
          MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (y0 i)
        have hg0 : AlgHom.Finite g0 := by
          -- This is the finite map supplied by Lemma `10.115.3`.
          simpa [g0] using hg0_raw
        obtain ⟨r, z, hz_mem, hz_map⟩ := ih (RingHom.ker g0) (RingHom.ker_ne_top g0)
        let h : MvPolynomial (Fin r) k →ₐ[k] (MvPolynomial (Fin n) k ⧸ RingHom.ker g0) :=
          MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk (RingHom.ker g0) (z i)
        have hhinj : Function.Injective h := by
          -- This is the injective map produced by the induction hypothesis on the kernel quotient.
          simpa [h] using hz_map.1
        have hhfinite : AlgHom.Finite h := by
          simpa [h] using hz_map.2
        let w : Fin r → MvPolynomial (Fin (n + 1)) k := fun i ↦ MvPolynomial.aeval y0 (z i)
        have hw_mem :
            ∀ i, w i ∈
              Algebra.adjoin ℤ (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)) := by
          intro i
          -- The induction generators remain inside the ambient coordinate `ℤ`-subalgebra after
          -- substituting the first-step normalization generators.
          exact aeval_mem_coordinate_int_adjoin y0 hy0 (hz_mem i)
        refine ⟨r, w, hw_mem, ?_⟩
        dsimp
        have hcomp :
            (Ideal.kerLiftAlg g0).comp h =
              MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk I (w i) := by
          -- The quotient-kernel presentation is the textbook subring `S'`; on variables this
          -- composite sends `X_i` to the class of the substituted polynomial `w i`.
          ext i
          simpa [h, g0, w, Ideal.kerLiftAlg_mk] using
            (MvPolynomial.comp_aeval_apply
              (f := y0) (φ := Ideal.Quotient.mkₐ k I) (p := z i)).symm
        have hfinal_injective : Function.Injective ((Ideal.kerLiftAlg g0).comp h) :=
          (Ideal.kerLiftAlg_injective g0).comp hhinj
        have hfinal_finite : AlgHom.Finite ((Ideal.kerLiftAlg g0).comp h) :=
          AlgHom.Finite.comp (kerLiftAlg_finite_of_finite g0 hg0) hhfinite
        simpa [hcomp] using And.intro hfinal_injective hfinal_finite

-- Proof sketch: an injective finite map from `k[X₁, ..., Xᵣ]` to the quotient makes the quotient
-- integral over a polynomial ring in `r` variables, so the Krull dimensions agree by invariance
-- under integral extensions; then use the polynomial-ring dimension formula over a field.
/-- Lemma 10.115.4 (2): if a quotient `k[x_1, \ldots, x_n] / I` admits a finite injective map from
the polynomial ring in `r` variables over `k`, then `r` is the Krull dimension of the quotient. -/
theorem ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra
    (I : Ideal (MvPolynomial (Fin n) k)) {r : ℕ}
    (g : MvPolynomial (Fin r) k →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I))
    (hg_injective : Function.Injective g) (hg_finite : AlgHom.Finite g) :
    ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) = r := by
  let _ : Algebra (MvPolynomial (Fin r) k) ((MvPolynomial (Fin n) k) ⧸ I) := g.toAlgebra
  have hg_integral :
      (algebraMap (MvPolynomial (Fin r) k) ((MvPolynomial (Fin n) k) ⧸ I)).IsIntegral := by
    simpa [RingHom.algebraMap_toAlgebra] using
      hg_finite.to_isIntegral
  let _ : Algebra.IsIntegral (MvPolynomial (Fin r) k) ((MvPolynomial (Fin n) k) ⧸ I) :=
    algebraMap_isIntegral_iff.mp hg_integral
  have hdim :
      ringKrullDim (MvPolynomial (Fin r) k) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
      (by simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
  have hpoly : ringKrullDim (MvPolynomial (Fin r) k) = r := by
    simp
  exact hdim.symm.trans hpoly

end

/-! ### Lemma_10_115_5 (from Chap10) -/
universe u v

open TopologicalSpace Topology

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Source/core/bridge triage:
* primary domain: Noether normalization for finite-type algebras over a field, localized on a
  basic open neighborhood of a point of `Spec(S)`;
* sampled owner API:
  `topologicalKrullDimAt` and
  `exists_openNhdsOf_topologicalKrullDimAt_eq` from `Definition 5.10.1`,
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether normalization file,
  `ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra` from
  Lemma `10.115.4`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField` from
  Lemma `10.116.3`;
* source-facing: the existence of a basic open neighborhood of `x` whose coordinate ring realizes
  the local dimension at `x` and admits Noether normalization;
* core/canonical: finite injective polynomial-algebra maps and the local-dimension owner formula;
* bridge/view: this lemma specializes those owners to a localization away from one element
  `g ∉ x.asIdeal`.

Primitive data are the basic-open witness `g` and the finite injective algebra map into
`Localization.Away g`. The polynomial source still needs a literal `ℕ` index, so the statement
keeps the minimal witness `d : ℕ` only to record that the canonical owners
`ringKrullDim (Localization.Away g)` and `topologicalKrullDimAt x` are realized by a finite
number of variables.
-/

/-- A witness that `Localization.Away g` realizes the local dimension at `x` and admits a finite
injective Noether normalization by a polynomial ring in `d` variables. -/
structure IsNoetherNormalizationLocalizationAwayAtPoint
    (x : PrimeSpectrum S) (g : S) (d : ℕ)
    (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g) : Prop where
  not_mem_asIdeal : g ∉ x.asIdeal
  ringKrullDim_eq : ringKrullDim (Localization.Away g) = d
  topologicalKrullDimAt_eq : topologicalKrullDimAt x = d
  injective : Function.Injective f
  finite : AlgHom.Finite f

-- Proof sketch: choose a basic open `D(g)` with `g ∉ x.asIdeal` whose dimension equals the local
-- dimension at `x`. Apply Lemma `10.115.4` to a polynomial presentation of `Localization.Away g`.
-- The number of variables is then the canonical owner `ringKrullDim (Localization.Away g)`, and
-- the local-dimension equality identifies this with `topologicalKrullDimAt x`.
/-- Lemma 10.115.5: for a point `x` of `X = Spec(S)`, where `S` is a finite type `k`-algebra,
there exists `g ∉ x.asIdeal` such that the localization `S_g`, formalized as
`Localization.Away g`, has Krull dimension equal to the local dimension at `x`; writing this
common finite value as `d`, there is a finite injective `k`-algebra map from
`MvPolynomial (Fin d) k` to `Localization.Away g`. -/
lemma exists_noether_normalization_localizationAway_at_point (x : PrimeSpectrum S) :
    ∃ (g : S) (d : ℕ) (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g),
      IsNoetherNormalizationLocalizationAwayAtPoint x g d f := by
  -- First realize the local dimension on an actual open neighborhood of `x`.
  obtain ⟨U, hU⟩ := exists_openNhdsOf_topologicalKrullDimAt_eq x
  have hxU : x ∈ (U : Set (PrimeSpectrum S)) := U.2
  -- Then refine that neighborhood to a basic open through `x`.
  obtain ⟨V, ⟨g, rfl⟩, hxV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.1.2 x hxU
  have hg_not_mem : g ∉ x.asIdeal := by
    simpa using hxV
  have hbasic_le :
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ (U : Set (PrimeSpectrum S)) := hVU
  have hbasic_dim_le :
      topologicalKrullDim (PrimeSpectrum.basicOpen g) ≤ topologicalKrullDim U := by
    -- Compare `D(g)` with its image as a subspace of the minimizing neighborhood `U`.
    let e₁ :
        PrimeSpectrum.basicOpen g ≃ₜ
          (((U : Set (PrimeSpectrum S)) ∩
              (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) :=
      Homeomorph.setCongr <| by
        ext y
        constructor
        · intro hy
          exact ⟨hbasic_le hy, hy⟩
        · intro hy
          exact hy.2
    let e₂ :
        { y : U // y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) } ≃ₜ
          (((U : Set (PrimeSpectrum S)) ∩
              (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) :=
      (Homeomorph.setCongr <| by
          ext y
          constructor
          · intro hy
            exact ⟨y.2, hy⟩
          · intro hy
            exact hy.2).trans
        (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦
          ⟨⟨y, hy.1⟩, rfl⟩)
    have hsubspace :
        topologicalKrullDim
            { y : U // y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) } ≤
          topologicalKrullDim U :=
      topologicalKrullDim_subspace_le U
        { y : U | y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) }
    have heq₁ :
        topologicalKrullDim (PrimeSpectrum.basicOpen g) =
          topologicalKrullDim
            (((U : Set (PrimeSpectrum S)) ∩
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) := by
      simpa [e₁] using
        IsHomeomorph.topologicalKrullDim_eq e₁ e₁.isHomeomorph
    have heq₂ :
        topologicalKrullDim
            { y : U // y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) } =
          topologicalKrullDim
            (((U : Set (PrimeSpectrum S)) ∩
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) := by
      simpa [e₂] using
        IsHomeomorph.topologicalKrullDim_eq e₂ e₂.isHomeomorph
    rw [heq₁, ← heq₂]
    exact hsubspace
  have hdim_basic :
      topologicalKrullDimAt x = topologicalKrullDim (PrimeSpectrum.basicOpen g) := by
    refine le_antisymm ?_ ?_
    · -- Any neighborhood bounds the local dimension from above.
      exact topologicalKrullDimAt_le x ⟨PrimeSpectrum.basicOpen g, hxV⟩
    · -- The chosen neighborhood `U` already realizes the minimum, so the smaller basic open has
      -- the same dimension.
      rw [hU]
      exact hbasic_dim_le
  have hdim_localization :
      topologicalKrullDimAt x = ringKrullDim (Localization.Away g) := by
    -- Identify `D(g)` with `Spec(S_g)` and transport topological Krull dimension across that
    -- homeomorphism.
    have hhomeo :
        topologicalKrullDim (PrimeSpectrum (Localization.Away g)) =
          topologicalKrullDim (PrimeSpectrum.basicOpen g) := by
      simpa using
        IsHomeomorph.topologicalKrullDim_eq
          (primeSpectrum_localizationAway_homeomorph_D g)
          (primeSpectrum_localizationAway_homeomorph_D g).isHomeomorph
    calc
      topologicalKrullDimAt x = topologicalKrullDim (PrimeSpectrum.basicOpen g) := hdim_basic
      _ = topologicalKrullDim (PrimeSpectrum (Localization.Away g)) := hhomeo.symm
      _ = ringKrullDim (Localization.Away g) := by
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  -- Finally apply Noether normalization to the finite type `k`-algebra `Localization.Away g`.
  let xg : PrimeSpectrum (Localization.Away g) :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨x, hxV⟩
  let _ : Nontrivial (Localization.Away g) := PrimeSpectrum.nontrivial xg
  have hfiniteTypeLoc : Algebra.FiniteType k (Localization.Away g) := inferInstance
  obtain ⟨d, f, hf_injective, hf_finite⟩ :=
    exists_finite_inj_algHom_of_fg k (Localization.Away g)
  have hring :
      ringKrullDim (Localization.Away g) = d := by
    let _ : Algebra (MvPolynomial (Fin d) k) (Localization.Away g) := f.toAlgebra
    -- A finite algebra map is integral, hence preserves Krull dimension under injectivity.
    have hf_integral :
        (algebraMap (MvPolynomial (Fin d) k) (Localization.Away g)).IsIntegral := by
      simpa [RingHom.algebraMap_toAlgebra] using hf_finite.to_isIntegral
    let _ : Algebra.IsIntegral (MvPolynomial (Fin d) k) (Localization.Away g) :=
      algebraMap_isIntegral_iff.mp hf_integral
    have hdim :
        ringKrullDim (MvPolynomial (Fin d) k) =
          ringKrullDim (Localization.Away g) :=
      ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
        (by simpa [RingHom.algebraMap_toAlgebra] using hf_injective)
    have hpoly : ringKrullDim (MvPolynomial (Fin d) k) = d := by
      -- Polynomial rings over a field have Krull dimension equal to the number of variables.
      simp
    exact hdim.symm.trans hpoly
  have htop : topologicalKrullDimAt x = d := by
    rw [hdim_localization, hring]
  refine ⟨g, d, f, ?_⟩
  exact
    { not_mem_asIdeal := hg_not_mem
      ringKrullDim_eq := hring
      topologicalKrullDimAt_eq := htop
      injective := hf_injective
      finite := hf_finite }

end
