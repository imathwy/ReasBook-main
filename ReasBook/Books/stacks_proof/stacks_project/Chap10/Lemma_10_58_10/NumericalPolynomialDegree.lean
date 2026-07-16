import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_58_3

open Filter
open scoped BigOperators

noncomputable section

universe u

section

variable {A : Type u} [AddCommGroup A]

/-- Helper for Chap10 Lemma 10 58 10: a source-facing degree bound for numerical
polynomial functions on `ℤ`. -/
def HasNumericalPolynomialDegreeLT (f : ℤ → A) (m : ℤ) : Prop :=
  (f =ᶠ[atTop] fun _ ↦ (0 : A)) ∨
    ∃ r : ℕ, (r : ℤ) < m ∧ ∃ a : Fin (r + 1) → A,
      f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i

/-- Helper for Chap10 Lemma 10 58 10: a source-facing degree bound gives the chapter's
`IsNumericalPolynomial` notion. -/
theorem HasNumericalPolynomialDegreeLT.isNumericalPolynomial
    {f : ℤ → A} {m : ℤ} (hf : HasNumericalPolynomialDegreeLT f m) :
    IsNumericalPolynomial f := by
  rcases hf with hzero | ⟨r, -, a, ha⟩
  · refine ⟨0, fun _ ↦ 0, ?_⟩
    exact hzero.trans <| Filter.EventuallyEq.of_eq <| by
      ext n
      simp
  · exact ⟨r, a, ha⟩

/-- Helper for Chap10 Lemma 10 58 10: degree `< 0` in the source-facing sense is exactly
eventual vanishing. -/
theorem hasNumericalPolynomialDegreeLT_zero_iff {f : ℤ → A} :
    HasNumericalPolynomialDegreeLT f 0 ↔ f =ᶠ[atTop] fun _ ↦ (0 : A) := by
  constructor
  · intro hf
    rcases hf with hzero | ⟨r, hr, -, -⟩
    · exact hzero
    · have hnonneg : (0 : ℤ) ≤ r := by
        exact_mod_cast Nat.zero_le r
      exact (not_lt_of_ge hnonneg hr).elim
  · intro hzero
    exact Or.inl hzero

end

section

variable {d : ℕ}

/-- Helper for Chap10 Lemma 10 58 10: the rational polynomial attached to a
binomial-coefficient expansion. -/
private noncomputable def numericalPolynomialCandidate {r : ℕ} (a : Fin (r + 1) → ℚ) :
    Polynomial ℚ :=
  ∑ i : Fin (r + 1), a i • Polynomial.preHilbertPoly ℚ i i

/-- Helper for Chap10 Lemma 10 58 10: the candidate polynomial evaluates to the expected
binomial-coefficient expansion on the natural-number tail. -/
private theorem numericalPolynomialCandidate_spec_nat {r : ℕ} (a : Fin (r + 1) → ℚ) :
    ∀ᶠ n : ℕ in atTop,
      (numericalPolynomialCandidate a).eval (n : ℚ) =
        ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
  filter_upwards [eventually_ge_atTop r] with n hn
  simp only [numericalPolynomialCandidate, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    zsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add]
  · rw [Nat.sub_add_cancel (le_trans (Nat.lt_succ_iff.mp i.2) hn)]
    simp [Ring.choose_natCast, mul_comm]
  · exact le_trans (Nat.lt_succ_iff.mp i.2) hn

/-- Helper for Chap10 Lemma 10 58 10: `preHilbertPoly` is never the zero polynomial over `ℚ`. -/
private theorem preHilbertPoly_ne_zero (m k : ℕ) :
    Polynomial.preHilbertPoly ℚ m k ≠ 0 := by
  intro hzero
  have hcoeff : (Polynomial.preHilbertPoly ℚ m k).coeff m = 0 := by
    simpa [hzero]
  have hfac : ((m.factorial : ℚ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m)
  rw [Polynomial.coeff_preHilbertPoly_self] at hcoeff
  exact hfac hcoeff

/-- Helper for Chap10 Lemma 10 58 10: coefficients above the natural degree of `preHilbertPoly`
vanish. -/
private theorem preHilbertPoly_coeff_eq_zero_of_lt {m k j : ℕ} (hj : m < j) :
    (Polynomial.preHilbertPoly ℚ m k).coeff j = 0 := by
  have hdeg : (Polynomial.preHilbertPoly ℚ m k).degree < j := by
    rw [Polynomial.degree_eq_natDegree (preHilbertPoly_ne_zero m k),
      Polynomial.natDegree_preHilbertPoly]
    exact_mod_cast hj
  exact (Polynomial.degree_lt_iff_coeff_zero _ j).1 hdeg j le_rfl

/-- Helper for Chap10 Lemma 10 58 10: the top coefficient of a numerical-polynomial candidate is
the last binomial coefficient scaled by `(r!)⁻¹`. -/
private theorem numericalPolynomialCandidate_coeff_top {r : ℕ} (a : Fin (r + 1) → ℚ) :
    (numericalPolynomialCandidate a).coeff r =
      a (Fin.last r) * ((r.factorial : ℚ)⁻¹) := by
  -- Separate the top-degree term from the lower-degree terms and use triangularity of the
  -- `preHilbertPoly` basis.
  rw [numericalPolynomialCandidate, Fin.sum_univ_castSucc, Polynomial.coeff_add]
  have hsum_zero :
      (∑ i : Fin r, a i.castSucc • Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ)).coeff r = 0 := by
    simp [preHilbertPoly_coeff_eq_zero_of_lt]
  simp [hsum_zero, Polynomial.coeff_smul, Polynomial.coeff_preHilbertPoly_self]

/-- Helper for Chap10 Lemma 10 58 10: the source comparison function is represented by an explicit
pre-Hilbert-polynomial difference. -/
private noncomputable def multichooseDifferencePolynomial (d e : ℕ) : Polynomial ℚ :=
  Polynomial.preHilbertPoly ℚ (d - 1) 0 - Polynomial.preHilbertPoly ℚ (d - 1) e

/-- Helper for Chap10 Lemma 10 58 10: the explicit comparison polynomial evaluates to the
multichoose difference on the natural-number tail. -/
private theorem multichooseDifferencePolynomial_spec_nat (d e : ℕ) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (multichooseDifferencePolynomial d e).eval (n : ℚ) =
        (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
  filter_upwards [eventually_ge_atTop e] with n hn
  have hleft :
      (Polynomial.preHilbertPoly ℚ (d - 1) 0).eval (n : ℚ) = (d.multichoose n : ℚ) := by
    have hleft' :
        (Polynomial.preHilbertPoly ℚ (d - 1) 0).eval (n : ℚ) =
          (((n + (d - 1)).choose (d - 1) : ℕ) : ℚ) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) (d - 1) (k := 0) (n := n)
          (by simp))
    calc
      (Polynomial.preHilbertPoly ℚ (d - 1) 0).eval (n : ℚ) =
          (((n + (d - 1)).choose (d - 1) : ℕ) : ℚ) := hleft'
      _ = (((d - 1 + n).choose n : ℕ) : ℚ) := by
          have hchoose_nat : (n + (d - 1)).choose (d - 1) = (d - 1 + n).choose n := by
            rw [Nat.add_comm n (d - 1)]
            exact Nat.choose_symm_add (a := d - 1) (b := n)
          exact_mod_cast hchoose_nat
      _ = (d.multichoose n : ℚ) := by
          rw [Nat.multichoose_eq]
          have hs : d - 1 + n = d + n - 1 := by
            cases d with
            | zero => cases (Nat.lt_asymm hd hd)
            | succ d =>
                simp [Nat.add_comm]
          simp [hs]
  have hright :
      (Polynomial.preHilbertPoly ℚ (d - 1) e).eval (n : ℚ) = (d.multichoose (n - e) : ℚ) := by
    have hright' :
        (Polynomial.preHilbertPoly ℚ (d - 1) e).eval (n : ℚ) =
          ((((n - e) + (d - 1)).choose (d - 1) : ℕ) : ℚ) := by
      simpa [Nat.sub_add_comm hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) (d - 1) (k := e) (n := n) hn)
    calc
      (Polynomial.preHilbertPoly ℚ (d - 1) e).eval (n : ℚ) =
          ((((n - e) + (d - 1)).choose (d - 1) : ℕ) : ℚ) := hright'
      _ = (((d - 1 + (n - e)).choose (n - e) : ℕ) : ℚ) := by
          have hchoose_nat :
              ((n - e) + (d - 1)).choose (d - 1) = (d - 1 + (n - e)).choose (n - e) := by
            rw [Nat.add_comm (n - e) (d - 1)]
            exact Nat.choose_symm_add (a := d - 1) (b := n - e)
          exact_mod_cast hchoose_nat
      _ = (d.multichoose (n - e) : ℚ) := by
          rw [Nat.multichoose_eq]
          have hs : d - 1 + (n - e) = d + (n - e) - 1 := by
            cases d with
            | zero => cases (Nat.lt_asymm hd hd)
            | succ d =>
                simp [Nat.add_comm]
          simp [hs]
  -- Rewrite both pre-Hilbert polynomials by their multichoose evaluations and then cast the
  -- integer subtraction to `ℚ`.
  calc
    (multichooseDifferencePolynomial d e).eval (n : ℚ) =
        (d.multichoose n : ℚ) - (d.multichoose (n - e) : ℚ) := by
          simp [multichooseDifferencePolynomial, hleft, hright]
    _ = (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
          norm_num

/-- Helper for Chap10 Lemma 10 58 10: for `d > 1`, the explicit multichoose-difference
polynomial has degree `< d - 1`. -/
private theorem multichooseDifferencePolynomial_degree_lt (d e : ℕ) (_hd : 1 < d) :
    (multichooseDifferencePolynomial d e).degree < ((d - 1 : ℕ) : WithBot ℕ) := by
  refine (Polynomial.degree_lt_iff_coeff_zero _ (d - 1)).2 ?_
  intro j hj
  by_cases hj_eq : j = d - 1
  · subst hj_eq
    simp [multichooseDifferencePolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_preHilbertPoly_self]
  · have hj_gt : d - 1 < j := lt_of_le_of_ne hj (Ne.symm hj_eq)
    simp [multichooseDifferencePolynomial, Polynomial.coeff_sub,
      preHilbertPoly_coeff_eq_zero_of_lt (k := 0) hj_gt,
      preHilbertPoly_coeff_eq_zero_of_lt (k := e) hj_gt]

/-- Helper for Chap10 Lemma 10 58 10: an eventually nonnegative polynomial bounded above by
another polynomial cannot have larger degree. -/
private theorem degree_le_of_eventually_nonneg_le {E Q : Polynomial ℚ}
    (hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ E.eval (n : ℚ) ∧ E.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    E.degree ≤ Q.degree := by
  by_contra hEQ
  have hQE : Q.degree < E.degree := lt_of_not_ge hEQ
  have hE0 : E ≠ 0 := Polynomial.ne_zero_of_degree_gt hQE
  have hNoRoot :
      ∀ᶠ n : ℕ in atTop, ¬ E.IsRoot (n : ℚ) := by
    exact tendsto_natCast_atTop_atTop.eventually
      (Polynomial.eventually_atTop_not_isRoot (P := E) hE0)
  have hPos :
      ∀ᶠ n : ℕ in atTop, 0 < E.eval (n : ℚ) := by
    -- Eventual nonnegativity plus eventual nonvanishing forces eventual positivity.
    filter_upwards [hbound, hNoRoot] with n hn hnr
    have hne : E.eval (n : ℚ) ≠ 0 := by
      simpa [Polynomial.IsRoot] using hnr
    exact lt_of_le_of_ne hn.1 (Ne.symm hne)
  have hDiv :
      Tendsto (fun n : ℕ ↦ Q.eval (n : ℚ) / E.eval (n : ℚ)) atTop (nhds 0) := by
    exact (Polynomial.div_tendsto_atTop_zero_of_degree_lt (P := Q) (Q := E) hQE).comp
      tendsto_natCast_atTop_atTop
  have hSmall :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) / E.eval (n : ℚ) ∈ Set.Ioo (-1) 1 := by
    exact hDiv.eventually
      (Ioo_mem_nhds (by norm_num : (-1 : ℚ) < 0) (by norm_num : (0 : ℚ) < 1))
  have hFalse : ∀ᶠ n : ℕ in atTop, False := by
    -- The ratio tends to `0`, but the eventual upper bound forces it to be at least `1`.
    filter_upwards [hPos, hSmall, hbound] with n hPosN hSmallN hBoundN
    have hRatioGe : (1 : ℚ) ≤ Q.eval (n : ℚ) / E.eval (n : ℚ) := by
      rw [one_le_div hPosN]
      exact hBoundN.2
    exact (not_le_of_gt hSmallN.2) hRatioGe
  rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
  exact hN N le_rfl

/-- Helper for Chap10 Lemma 10 58 10: if the associated rational polynomial has degree `< m`,
the original binomial-coefficient witness can be trimmed to degree `< m`. -/
private theorem hasNumericalPolynomialDegreeLT_of_choose_witness_degree_lt
    {f : ℤ → ℤ} {m r : ℕ} (hm : 0 < m) (a : Fin (r + 1) → ℤ)
    (ha : f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i)
    (hdeg : (numericalPolynomialCandidate fun i ↦ (a i : ℚ)).degree < m) :
    HasNumericalPolynomialDegreeLT f (m : ℤ) := by
  induction r with
  | zero =>
      exact Or.inr ⟨0, by exact_mod_cast hm, a, ha⟩
  | succ r ih =>
      by_cases hrm : r + 1 < m
      · exact Or.inr ⟨r + 1, by exact_mod_cast hrm, a, ha⟩
      · have hdeg_top :
          (numericalPolynomialCandidate fun i ↦ (a i : ℚ)).degree < r + 1 := by
          exact lt_of_lt_of_le hdeg (by exact_mod_cast Nat.le_of_not_lt hrm)
        have hcoeff_zero :
            (numericalPolynomialCandidate fun i ↦ (a i : ℚ)).coeff (r + 1) = 0 := by
          exact (Polynomial.degree_lt_iff_coeff_zero _ (r + 1)).1 hdeg_top (r + 1) le_rfl
        have hlast_q :
            (a (Fin.last (r + 1)) : ℚ) = 0 := by
          have htop :
              (a (Fin.last (r + 1)) : ℚ) * (((r + 1).factorial : ℚ)⁻¹) = 0 := by
            simpa [numericalPolynomialCandidate_coeff_top] using hcoeff_zero
          have hfac : (((r + 1).factorial : ℚ)⁻¹) ≠ 0 := by
            exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (r + 1))
          exact (mul_eq_zero.mp htop).resolve_right hfac
        have hlast : a (Fin.last (r + 1)) = 0 := by
          exact_mod_cast hlast_q
        let a' : Fin (r + 1) → ℤ := fun i ↦ a i.castSucc
        have ha' :
            f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a' i := by
          -- Drop the vanishing top-degree term from the binomial expansion.
          filter_upwards [ha] with n hn
          rw [hn, Fin.sum_univ_castSucc]
          simp [a', hlast]
        have hdeg' :
            (numericalPolynomialCandidate fun i ↦ (a' i : ℚ)).degree < m := by
          -- The rational polynomial is unchanged after deleting the zero top coefficient.
          simpa [numericalPolynomialCandidate, a', hlast, Fin.sum_univ_castSucc] using hdeg
        exact ih a' ha' hdeg'

/-- Helper for Chap10 Lemma 10 58 10: numerical polynomiality plus the source upper bound by one
fixed multichoose difference forces the Hilbert function to have degree `< d - 1`. -/
theorem hasNumericalPolynomialDegreeLT_of_isNumericalPolynomial_and_eventually_le_multichoose_difference
    {f : ℤ → ℤ} {e : ℕ} (_he : 0 < e) (hd : 1 < d)
    (hnum : IsNumericalPolynomial f)
    (hbound : ∀ᶠ n : ℤ in atTop, 0 ≤ f n ∧
      f n ≤ ((d.multichoose n.toNat : ℤ) - (d.multichoose (n.toNat - e) : ℤ))) :
    HasNumericalPolynomialDegreeLT f (d - 1 : ℤ) := by
  rcases hnum with ⟨r, a, ha⟩
  let P : Polynomial ℚ := numericalPolynomialCandidate fun i ↦ (a i : ℚ)
  let Q : Polynomial ℚ := multichooseDifferencePolynomial d e
  have hPevent :
      ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = (f n : ℚ) := by
    have hNat :
        (fun n : ℕ ↦ f n) =ᶠ[atTop]
          fun n ↦ ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
      simpa using ha.comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop)
    filter_upwards [hNat, numericalPolynomialCandidate_spec_nat (fun i ↦ (a i : ℚ))] with n hn hP
    -- Rewrite the numerical-polynomial witness through the rational candidate.
    calc
      P.eval (n : ℚ) = ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • (a i : ℚ) := by
        simpa [P] using hP
      _ = (f n : ℚ) := by
        simpa [hn, zsmul_eq_mul]
  have hQevent :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) =
        (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
    simpa [Q] using multichooseDifferencePolynomial_spec_nat d e (Nat.lt_trans Nat.zero_lt_one hd)
  have hbound_nat :
      ∀ᶠ n : ℕ in atTop, 0 ≤ (f n : ℚ) ∧ (f n : ℚ) ≤ Q.eval (n : ℚ) := by
    have hbound' :
        ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧
          f n ≤ ((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) := by
      rcases Filter.eventually_atTop.mp hbound with ⟨N, hN⟩
      refine Filter.eventually_atTop.mpr ⟨Int.toNat N, ?_⟩
      intro n hn
      have hN' : N ≤ (n : ℤ) := by
        calc
          N ≤ Int.toNat N := Int.self_le_toNat N
          _ ≤ n := by exact_mod_cast hn
      simpa using hN (n : ℤ) hN'
    filter_upwards [hbound', hQevent] with n hn hQ
    constructor
    · exact_mod_cast hn.1
    · have hcast :
          (f n : ℚ) ≤ (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
          exact_mod_cast hn.2
      calc
        (f n : ℚ) ≤ (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := hcast
        _ = Q.eval (n : ℚ) := hQ.symm
  have hPbound :
      ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ) ∧ P.eval (n : ℚ) ≤ Q.eval (n : ℚ) := by
    -- Replace the Hilbert function by its eventual polynomial representative.
    filter_upwards [hPevent, hbound_nat] with n hP hn
    rw [hP]
    exact hn
  have hQdeg : Q.degree < ((d - 1 : ℕ) : WithBot ℕ) :=
    multichooseDifferencePolynomial_degree_lt d e hd
  have hPdeg : P.degree < ((d - 1 : ℕ) : WithBot ℕ) := by
    exact lt_of_le_of_lt (degree_le_of_eventually_nonneg_le hPbound) hQdeg
  have hm : 0 < d - 1 := Nat.sub_pos_of_lt hd
  -- Convert the degree bound on the rational candidate back to the chapter's source-facing
  -- binomial-coefficient degree notion.
  have hdegInt : (((d - 1 : ℕ) : ℤ)) = (d : ℤ) - 1 := by
    exact Int.ofNat_sub (Nat.one_le_of_lt hd)
  simpa [P, hdegInt] using
    hasNumericalPolynomialDegreeLT_of_choose_witness_degree_lt (m := d - 1) hm a ha hPdeg

end
