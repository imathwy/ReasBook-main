import stacks_proof.stacks_project.Chap10.Definition_10_70_1
import stacks_proof.stacks_project.Chap10.Lemma_10_70_2

universe u

noncomputable section

open HomogeneousLocalization
open Polynomial
open scoped DirectSum

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.70.8: the scaled ideal `(f) * I` used for the target affine blowup chart. -/
def scaledIdeal (I : Ideal R) (f : R) : Ideal R :=
  Ideal.span ({f} : Set R) * I

/-- Helper for Lemma 10.70.8: the element `f * a` as an element of the scaled ideal `(f) * I`. -/
def scaledElement (I : Ideal R) (a : I) (f : R) : scaledIdeal I f :=
  ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩

/-- Helper for Lemma 10.70.8: an element of the `n`th power of the scaled ideal is exactly a
multiple of `f ^ n` by an element of `I ^ n`. -/
theorem mem_scaledIdeal_pow_iff_exists
    (I : Ideal R) (f : R) (n : ℕ) (x : R) :
    x ∈ scaledIdeal I f ^ n ↔ ∃ y : ↥(I ^ n), f ^ n * y.1 = x := by
  rw [scaledIdeal, mul_pow, Ideal.span_singleton_pow]
  simpa [mul_comm] using
    (Submodule.mem_span_singleton_mul (R := R) (P := (I ^ n : Submodule R R))
      (x := x) (y := f ^ n))

/-- Helper for Lemma 10.70.8: evaluating at `C f * X` multiplies the `n`th coefficient by
`f ^ n`. -/
theorem eval2_C_mul_X_coeff
    (f : R) (p : R[X]) (n : ℕ) :
    (Polynomial.eval₂ C (C f * X) p).coeff n = p.coeff n * f ^ n := by
  -- Polynomial induction reduces the claim to a single monomial calculation.
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq, add_mul]
  | monomial m a =>
      rw [Polynomial.eval₂_monomial, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      by_cases hmn : n = m
      · subst hmn
        simp
      · have hmn' : m ≠ n := by
          exact fun h => hmn h.symm
        simp [hmn, hmn']

/-- Helper for Lemma 10.70.8: evaluating a Rees-algebra polynomial at `fX` stays inside the Rees
algebra of the scaled ideal. -/
theorem scaledReesAlgebra_mem
    (I : Ideal R) (f : R) (x : reesAlgebra I) :
    eval₂RingHom C (C f * X) x.1 ∈
      reesAlgebra (scaledIdeal I f) := by
  -- Check the Rees-algebra condition coefficientwise after evaluation at `fX`.
  rw [mem_reesAlgebra_iff (I := scaledIdeal I f)]
  intro n
  have hxcoeff : x.1.coeff n ∈ I ^ n := (mem_reesAlgebra_iff (I := I) x.1).1 x.2 n
  change (Polynomial.eval₂ C (C f * X) x.1).coeff n ∈ scaledIdeal I f ^ n
  rw [eval2_C_mul_X_coeff]
  exact (mem_scaledIdeal_pow_iff_exists I f n _).2
    ⟨⟨x.1.coeff n, hxcoeff⟩, by simp [mul_comm]⟩

/-- Helper for Lemma 10.70.8: the codomain proof for the scaled Rees-algebra ring homomorphism. -/
theorem scaledReesAlgebraRingHom_mem
    (I : Ideal R) (f : R) (x : (reesAlgebra I).toSubring) :
    ((Polynomial.eval₂RingHom C (C f * X)).comp (reesAlgebra I).toSubring.subtype) x ∈
      (reesAlgebra (scaledIdeal I f)).toSubring := by
  change Polynomial.eval₂RingHom C (C f * X) x.1 ∈ reesAlgebra (scaledIdeal I f)
  exact scaledReesAlgebra_mem I f ⟨x.1, x.2⟩

/-- Helper for Lemma 10.70.8: the Rees-algebra homomorphism induced by evaluating `X` at `f * X`. -/
noncomputable def scaledReesAlgebraRingHom
    (I : Ideal R) (f : R) :
    reesAlgebra I →+* reesAlgebra (scaledIdeal I f) :=
  RingHom.codRestrict
    ((Polynomial.eval₂RingHom C (C f * X)).comp (reesAlgebra I).toSubring.subtype)
    (reesAlgebra (scaledIdeal I f)).toSubring
    (scaledReesAlgebraRingHom_mem I f)

/-- Helper for Lemma 10.70.8: the scaled Rees-algebra map sends a degree-`n` monomial to the
degree-`n` monomial with coefficient multiplied by `f ^ n`. -/
theorem scaledReesAlgebraRingHom_monomial
    (I : Ideal R) (f : R) (n : ℕ) (y : ↥(I ^ n)) :
    scaledReesAlgebraRingHom I f
      (⟨Polynomial.monomial n y.1, (reesAlgebra.monomial_mem).2 y.2⟩ : reesAlgebra I) =
        ⟨Polynomial.monomial n (f ^ n * y.1),
          (reesAlgebra.monomial_mem).2 ((mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨y, rfl⟩)⟩ := by
  apply Subtype.ext
  change Polynomial.eval₂ C (C f * X) (Polynomial.monomial n y.1) = _
  rw [Polynomial.eval₂_monomial, mul_pow, ← Polynomial.C_pow]
  calc
    C y.1 * (C (f ^ n) * X ^ n) = (C y.1 * C (f ^ n)) * X ^ n := by rw [mul_assoc]
    _ = C (y.1 * f ^ n) * X ^ n := by rw [← Polynomial.C_mul]
    _ = Polynomial.monomial n (y.1 * f ^ n) := by rw [Polynomial.C_mul_X_pow_eq_monomial]
    _ = Polynomial.monomial n (f ^ n * y.1) := by simp [mul_comm]

/-- Helper for Lemma 10.70.8: the scaled Rees-algebra map preserves homogeneous degree. -/
theorem scaledReesAlgebra_mem_grade
    (I : Ideal R) (f : R) {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesAlgebraGrade I n) :
    scaledReesAlgebraRingHom I f x ∈ reesAlgebraGrade (scaledIdeal I f) n := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨⟨f ^ n * y.1, (mem_scaledIdeal_pow_iff_exists I f n _).2 ⟨y, rfl⟩⟩, ?_⟩
  simpa using (scaledReesAlgebraRingHom_monomial I f n y).symm

/-- Helper for Lemma 10.70.8: the graded Rees-algebra homomorphism for the scaled ideal `(f) * I`. -/
noncomputable def scaledGradedHom
    (I : Ideal R) (f : R) :
    reesAlgebraGrade I →+*ᵍ reesAlgebraGrade (scaledIdeal I f) where
  toRingHom := scaledReesAlgebraRingHom I f
  map_mem := scaledReesAlgebra_mem_grade I f

/-- Helper for Lemma 10.70.8: the scaled graded map sends `a` in degree one to `f * a`. -/
theorem scaled_degreeOne
    (I : Ideal R) (a : I) (f : R) :
    scaledGradedHom I f (reesAlgebraDegreeOne I a) =
      reesAlgebraDegreeOne (scaledIdeal I f) (scaledElement I a f) := by
  apply Subtype.ext
  simpa [scaledGradedHom, scaledElement, reesAlgebraDegreeOne, pow_one, mul_comm,
    mul_left_comm, mul_assoc] using
    congrArg Subtype.val
      (scaledReesAlgebraRingHom_monomial I f 1 ⟨a.1, by simpa using a.2⟩)

/-- Helper for Lemma 10.70.8: the constant polynomial `r` lies in the degree-zero part of the
Rees algebra. -/
theorem reesAlgebra_zeroDegree_mem (I : Ideal R) (r : R) :
    algebraMap R (reesAlgebra I) r ∈ reesAlgebraGrade I 0 := by
  refine ⟨⟨r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (Polynomial.monomial 0 r : R[X]) = C r
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.8: the constant polynomial `r` also lies in the degree-zero part of
the scaled Rees algebra. -/
theorem scaledReesAlgebra_zeroDegree_mem (I : Ideal R) (f r : R) :
    algebraMap R (reesAlgebra (scaledIdeal I f)) r ∈ reesAlgebraGrade (scaledIdeal I f) 0 := by
  refine ⟨⟨r, by simp⟩, ?_⟩
  apply Subtype.ext
  change (Polynomial.monomial 0 r : R[X]) = C r
  simp [Polynomial.monomial_zero_left]

/-- Helper for Lemma 10.70.8: the degree-zero Rees coefficient determined by `r`. -/
noncomputable def reesAlgebraZeroDegreeCoeff (I : Ideal R) (r : R) :
    reesAlgebraGrade I 0 :=
  ⟨algebraMap R (reesAlgebra I) r, reesAlgebra_zeroDegree_mem I r⟩

/-- Helper for Lemma 10.70.8: the degree-zero coefficient determined by `r` in the scaled Rees
algebra. -/
noncomputable def scaledReesAlgebraZeroDegreeCoeff
    (I : Ideal R) (f r : R) :
    reesAlgebraGrade (scaledIdeal I f) 0 :=
  ⟨algebraMap R (reesAlgebra (scaledIdeal I f)) r, scaledReesAlgebra_zeroDegree_mem I f r⟩

/-- Helper for Lemma 10.70.8: the canonical ring map from `R` into the degree-zero part of the
scaled Rees algebra. -/
noncomputable def scaledReesAlgebraGradeZeroAlgebraMap
    (I : Ideal R) (f : R) :
    R →+* reesAlgebraGrade (scaledIdeal I f) 0 where
  toFun r := scaledReesAlgebraZeroDegreeCoeff I f r
  map_one' := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]
  map_mul' r s := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]
  map_zero' := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]
  map_add' r s := by
    apply Subtype.ext
    simp [scaledReesAlgebraZeroDegreeCoeff]

/-- Helper for Lemma 10.70.8: the scaled graded map is the identity on degree-zero coefficients
coming from the base ring. -/
theorem scaledReesAlgebra_zeroDegree_algebraMap
    (I : Ideal R) (f r : R) :
    (scaledGradedHom I f).gradedAddHom 0 (reesAlgebraZeroDegreeCoeff I r) =
      scaledReesAlgebraZeroDegreeCoeff I f r := by
  -- Both degree-zero elements are represented by the same constant polynomial `C r`.
  apply Subtype.ext
  ext n
  by_cases hn : n = 0
  · subst hn
    simp [scaledGradedHom, scaledReesAlgebraRingHom, reesAlgebraZeroDegreeCoeff,
      scaledReesAlgebraZeroDegreeCoeff]
  · simp [scaledGradedHom, scaledReesAlgebraRingHom, reesAlgebraZeroDegreeCoeff,
      scaledReesAlgebraZeroDegreeCoeff]

end
