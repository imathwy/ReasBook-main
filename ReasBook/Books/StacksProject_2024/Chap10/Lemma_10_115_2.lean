import StacksProject_2024.Chap10.Lemma_10_115_1

-- Declarations for this item will be appended below by the statement pipeline.

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
