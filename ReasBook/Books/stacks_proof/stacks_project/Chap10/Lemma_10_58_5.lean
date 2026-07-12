import StacksProject_2024.Chap10.Definition_10_58_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped BigOperators

section

variable {A : Type u} [AddCommGroup A]

private def numericalPolynomialAntiderivativeCoeffs {r : ℕ} (a : Fin (r + 1) → A) :
    Fin (r + 2) → A :=
  Fin.cons (a 0) <|
    Fin.snoc (fun i : Fin r ↦ a i.castSucc + a i.succ) (a <| Fin.last r)

private def numericalPolynomialCoeffsWithConst {m : ℕ} (c : A) (a : Fin (m + 1) → A) :
    Fin (m + 1) → A :=
  Fin.cons (c + a 0) (Fin.tail a)

private theorem numericalPolynomialExpansion_antiderivativeCoeffs {r : ℕ}
    (a : Fin (r + 1) → A) (n : ℤ) :
    (∑ i : Fin (r + 2), Ring.choose n (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i) =
      ∑ i : Fin (r + 1), Ring.choose (n + 1) ((i : ℕ) + 1) • a i := by
  rw [Fin.sum_univ_succ]
  simp_rw [numericalPolynomialAntiderivativeCoeffs, Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.snoc_castSucc, Fin.snoc_last, smul_add]
  rw [Finset.sum_add_distrib]
  have hcast :
      (∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.castSucc) +
          Ring.choose n ↑(Fin.last r).succ • a (Fin.last r) =
        ∑ i : Fin (r + 1), Ring.choose n ↑i.succ • a i := by
    simpa using
      (Fin.sum_univ_castSucc (fun x : Fin (r + 1) ↦ Ring.choose n ↑x.succ • a x)).symm
  rw [show
    (∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.castSucc) +
        ∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.succ +
        Ring.choose n ↑(Fin.last r).succ • a (Fin.last r) =
      ((∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.castSucc) +
          Ring.choose n ↑(Fin.last r).succ • a (Fin.last r)) +
        ∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.succ by
      abel]
  rw [hcast]
  rw [Fin.sum_univ_succ]
  simp_rw [Ring.choose_succ_succ]
  rw [Fin.sum_univ_succ]
  simp_rw [add_smul]
  simp [Fin.val_castSucc, add_comm, add_left_comm, add_assoc]
  rw [← Finset.sum_add_distrib]

private theorem numericalPolynomialExpansion_coeffsWithConst {m : ℕ}
    (c : A) (a : Fin (m + 1) → A) (n : ℤ) :
    (∑ i : Fin (m + 1), Ring.choose n (i : ℕ) • numericalPolynomialCoeffsWithConst c a i) =
      c + ∑ i : Fin (m + 1), Ring.choose n (i : ℕ) • a i := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [numericalPolynomialCoeffsWithConst, add_assoc]
  abel

private theorem numericalPolynomialExpansion_antiderivativeCoeffs_sub_pred {r : ℕ}
    (a : Fin (r + 1) → A)
    (n : ℤ) :
    (∑ i : Fin (r + 2), Ring.choose n (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i) -
        ∑ i : Fin (r + 2), Ring.choose (n - 1) (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i =
      ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i := by
  rw [numericalPolynomialExpansion_antiderivativeCoeffs,
    numericalPolynomialExpansion_antiderivativeCoeffs, show n - 1 + 1 = n by ring,
    sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← sub_eq_add_neg, ← sub_smul, Ring.choose_succ_succ, add_sub_cancel_right]

private theorem eventuallyEq_const_of_sub_pred_eq_zero (f : ℤ → A)
    (h : ∀ᶠ n : ℤ in atTop, f n - f (n - 1) = 0) :
    ∃ c : A, f =ᶠ[atTop] fun _ ↦ c := by
  rcases Filter.eventually_atTop.mp h with ⟨N, hN⟩
  refine ⟨f (N - 1), Filter.eventually_atTop.mpr ⟨N - 1, ?_⟩⟩
  intro n hn
  induction n, hn using Int.le_induction with
  | base =>
      rfl
  | succ n hn ih =>
      have hstep : f (n + 1) = f n := by
        have hn' : N ≤ n + 1 := by linarith
        simpa using sub_eq_zero.mp (hN (n + 1) hn')
      exact hstep.trans ih

-- Proof sketch: choose a numerical-polynomial description of `n ↦ f n - f (n - 1)`, then
-- antidifferentiate term-by-term using `Δ (choose (n + 1) (i + 1)) = choose n i`. After
-- subtracting this antiderivative from `f`, the resulting function has eventual difference zero,
-- hence is eventually constant, which supplies the missing constant term in the binomial
-- expansion of `f`.
/-- Lemma 10.58.5: if the eventual first difference `n ↦ f(n) - f(n - 1)` is a numerical
polynomial, then `f` itself is a numerical polynomial. -/
@[stacks 00JZ]
theorem IsNumericalPolynomial.of_sub_pred {f : ℤ → A}
    (h : IsNumericalPolynomial (fun n ↦ f n - f (n - 1))) : IsNumericalPolynomial f := by
  rcases h with ⟨r, a, ha⟩
  let g : ℤ → A :=
    fun n ↦ ∑ i : Fin (r + 2), Ring.choose n (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i
  have hzero : ∀ᶠ n : ℤ in atTop, (f n - g n) - (f (n - 1) - g (n - 1)) = 0 := by
    filter_upwards [ha] with n hn
    have hg :
        g n - g (n - 1) = ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i :=
      by
        simpa [g] using numericalPolynomialExpansion_antiderivativeCoeffs_sub_pred a n
    calc
      (f n - g n) - (f (n - 1) - g (n - 1))
          = (f n - f (n - 1)) - (g n - g (n - 1)) := by
            abel
      _ = (∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i) -
            ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i := by
            rw [hn, hg]
      _ = 0 := sub_self _
  rcases eventuallyEq_const_of_sub_pred_eq_zero (fun n ↦ f n - g n) hzero with ⟨c, hc⟩
  refine ⟨r + 1, numericalPolynomialCoeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a), ?_⟩
  filter_upwards [hc] with n hn
  have hg :
      (∑ i : Fin (r + 2), Ring.choose n (i : ℕ) •
          numericalPolynomialCoeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a) i) =
        c + g n :=
    by
      simpa [g] using
        numericalPolynomialExpansion_coeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a) n
  calc
    f n = c + g n := by
      exact sub_eq_iff_eq_add.mp hn
    _ = ∑ i : Fin (r + 2), Ring.choose n (i : ℕ) •
        numericalPolynomialCoeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a) i := by
      symm
      exact hg

end
