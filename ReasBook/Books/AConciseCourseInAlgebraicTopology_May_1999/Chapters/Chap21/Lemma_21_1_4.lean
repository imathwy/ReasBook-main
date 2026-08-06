import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Ring.Parity

universe u v

namespace LinearMap.BilinForm

/-- Over a field with `2 ≠ 0`, a skew bilinear form is alternating. -/
theorem isAlt_of_eq_neg_flip
    {K : Type u} {V : Type v} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B = -B.flip) : B.IsAlt := by
  intro x
  have hxx : B x x = -B x x := by
    simpa [LinearMap.flip_apply] using congr_fun₂ hB x x
  have hsum : B x x + B x x = 0 := by
    calc
      B x x + B x x = B x x + -B x x := congrArg (fun t ↦ B x x + t) hxx
      _ = 0 := by simp
  have htwo : (2 : K) * B x x = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

end LinearMap.BilinForm

-- Semantic recall: mathlib's canonical bilinear-form API uses `B.Nondegenerate`; we keep
-- skew-symmetry as `B = -B.flip` so the source hypothesis remains explicit over `char K ≠ 2`.

/-- Helper for Lemma 21.1.4: an alternating bilinear form has a skew-symmetric matrix in any
basis. -/
lemma toMatrix_transpose_eq_neg_of_isAlt
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (B : LinearMap.BilinForm K V) (halt : B.IsAlt) :
    Matrix.transpose (LinearMap.BilinForm.toMatrix b B) = -LinearMap.BilinForm.toMatrix b B := by
  -- Compare entries after swapping the basis vectors.
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply]
  simpa using (halt.neg_eq (b i) (b j)).symm

/-- Helper for Lemma 21.1.4: an odd-dimensional skew-symmetric matrix over a field with `2 ≠ 0`
has zero determinant. -/
lemma det_eq_zero_of_odd_transpose_eq_neg
    {K : Type u} [Field K] [NeZero (2 : K)]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hodd : Odd (Fintype.card n)) (hskew : Matrix.transpose A = -A) :
    A.det = 0 := by
  -- Rewrite the determinant through transpose and negation to obtain `det A = - det A`.
  have hdet : A.det = -A.det := by
    calc
      A.det = (Matrix.transpose A).det := by rw [Matrix.det_transpose]
      _ = (-A).det := by rw [hskew]
      _ = (-1 : K) ^ Fintype.card n * A.det := by rw [Matrix.det_neg]
      _ = -A.det := by rw [hodd.neg_one_pow, neg_one_mul]
  -- Convert `a = -a` into `2 * a = 0`, then use `2 ≠ 0`.
  have hsum : A.det + A.det = 0 := by
    calc
      A.det + A.det = A.det + -A.det := by
        exact congrArg (fun t ↦ A.det + t) hdet
      _ = 0 := by simp
  have htwo : (2 : K) * A.det = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- Helper for Lemma 21.1.4: a nondegenerate alternating bilinear form cannot live on an
odd-dimensional finite-dimensional space. -/
lemma not_odd_finrank_of_nondegenerate_alternating
    {K : Type u} {V : Type v} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (halt : B.IsAlt)
    (hB : B.Nondegenerate) : ¬ Odd (Module.finrank K V) := by
  let b : Module.Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
  intro hodd
  -- Pass to the matrix of `B` in the canonical finite basis.
  have hzero : (LinearMap.BilinForm.toMatrix b B).det = 0 := by
    apply det_eq_zero_of_odd_transpose_eq_neg
    · simpa using hodd
    · exact toMatrix_transpose_eq_neg_of_isAlt b B halt
  -- Nondegeneracy of the form forces the Gram determinant to be nonzero.
  have hne : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  exact hne hzero

/-- Lemma 21.1.4 in canonical bilinear-form form: a nonsingular alternating bilinear form over a
field of characteristic not `2` has an even-dimensional underlying vector space. -/
theorem even_finrank_of_nondegenerate_alternating
    {K : Type u} {V : Type v} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (halt : B.IsAlt)
    (hB : B.Nondegenerate) : Even (Module.finrank K V) := by
  -- Route correction: prove the result through the Gram matrix of `B`, not by induction on
  -- dimension, so the nondegeneracy hypothesis is consumed by the determinant criterion.
  rcases Nat.even_or_odd (Module.finrank K V) with hEven | hOdd
  · exact hEven
  · exact False.elim ((not_odd_finrank_of_nondegenerate_alternating B halt hB) hOdd)

/-- Lemma 21.1.4: a nonsingular skew-symmetric bilinear form over a field of characteristic not
`2` has an even-dimensional underlying vector space. -/
theorem even_finrank_of_nondegenerate_skew
    {K : Type u} {V : Type v} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hskew : B = -B.flip)
    (hB : B.Nondegenerate) : Even (Module.finrank K V) :=
  even_finrank_of_nondegenerate_alternating B
    (LinearMap.BilinForm.isAlt_of_eq_neg_flip hskew) hB
