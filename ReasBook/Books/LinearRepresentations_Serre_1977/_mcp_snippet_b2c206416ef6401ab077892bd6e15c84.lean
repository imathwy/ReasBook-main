import Mathlib

noncomputable section

universe u

/-- test -/
private def fintypeIdentityMatrix (ι : Type u) [Fintype ι] : Matrix (Fin (Fintype.card ι)) ι ℤ :=
  fun r i => if r = Fintype.equivFin ι i then 1 else 0

/-- test -/
private theorem fintypeIdentityMatrix_transpose_mul
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (fintypeIdentityMatrix ι).transpose * fintypeIdentityMatrix ι = (1 : Matrix ι ι ℤ) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (Fintype.equivFin ι i)]
    · simp [fintypeIdentityMatrix]
    · intro r hr hne
      have : r ≠ Fintype.equivFin ι i := hne
      simp [fintypeIdentityMatrix, this]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_zero]
    · simp [Matrix.one_apply, hij]
    · intro r hr
      by_cases hri : r = Fintype.equivFin ι i
      · have hrj : r ≠ Fintype.equivFin ι j := by
          intro h
          apply hij
          exact (Fintype.equivFin ι).injective (hri.symm.trans h)
        simp [fintypeIdentityMatrix, hri, hrj]
      · simp [fintypeIdentityMatrix, hri]

/-- test -/
private theorem fintypeIdentityMatrix_mulVec_injective
    (ι : Type u) [Fintype ι] :
    Function.Injective (fintypeIdentityMatrix ι).mulVec := by
  intro x y hxy
  ext i
  have hi := congrFun hxy (Fintype.equivFin ι i)
  simpa [Matrix.mulVec, dotProduct, fintypeIdentityMatrix] using hi
