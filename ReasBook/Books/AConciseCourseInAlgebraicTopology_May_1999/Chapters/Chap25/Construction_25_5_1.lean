import Mathlib.Algebra.MvPolynomial.Eval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Corollary_25_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_1_3

noncomputable section

universe u w

-- Semantic recall via `lean_leansearch` surfaced `MvPolynomial.aeval` as the canonical
-- polynomial-evaluation API. Repo inspection shows Corollary 25.3.7 already packages `H_*(TO)`
-- as a polynomial `ZMod 2`-algebra on generators `a_i`, while Theorem 25.1.3 packages the
-- abstract algebra `N_* = Z_2[u_i | i > 1, i ≠ 2^r - 1]` through
-- `ThomUnorientedCobordismPolynomialAlgebra`.

/-- The image in the abstract algebra `N_*` of the positive-degree homology generator indexed by
`i`: if its degree is an admissible Thom generator degree, send it to the corresponding abstract
generator `u_i`; otherwise send it to `0`. -/
def thomComparisonGeneratorImage
    (A : ThomUnorientedCobordismPolynomialAlgebra)
    (i : BOHomologyGeneratorIndex) : N_* :=
  by
    classical
    exact
      if h : IsThomUnorientedCobordismGeneratorDegree (boHomologyGeneratorDegree i) then
        A.generators ⟨boHomologyGeneratorDegree i, h⟩
      else
        0

/-- In an admissible degree, `thomComparisonGeneratorImage` returns the corresponding Thom
generator `u_i` of the abstract algebra `N_*`. -/
theorem thomComparisonGeneratorImage_of_admissible
    (A : ThomUnorientedCobordismPolynomialAlgebra)
    (i : BOHomologyGeneratorIndex)
    (h : IsThomUnorientedCobordismGeneratorDegree (boHomologyGeneratorDegree i)) :
    thomComparisonGeneratorImage A i =
      A.generators ⟨boHomologyGeneratorDegree i, h⟩ := by
  classical
  simp [thomComparisonGeneratorImage, h]

/-- In a non-admissible degree, `thomComparisonGeneratorImage` vanishes. -/
theorem thomComparisonGeneratorImage_of_not_admissible
    (A : ThomUnorientedCobordismPolynomialAlgebra)
    (i : BOHomologyGeneratorIndex)
    (h : ¬ IsThomUnorientedCobordismGeneratorDegree (boHomologyGeneratorDegree i)) :
    thomComparisonGeneratorImage A i = 0 := by
  classical
  simp [thomComparisonGeneratorImage, h]

/-- The Chapter 25 comparison recipe attached to a polynomial `ZMod 2`-algebra presentation:
evaluate the polynomial presentation by sending each generator `X i` to the corresponding Thom
generator image in `N_*`. This is the reusable bridge behind Construction 25.5.1. -/
def thomComparisonPolynomialAlgHom
    {R : Type*} [Semiring R] [Algebra (ZMod 2) R]
    (A : ThomUnorientedCobordismPolynomialAlgebra)
    (Ψ : MvPolynomial BOHomologyGeneratorIndex (ZMod 2) ≃ₐ[ZMod 2] R) := by
  letI := A.toCommRing
  letI := A.toAlgebra
  exact (MvPolynomial.aeval fun i ↦ thomComparisonGeneratorImage A i).comp Ψ.symm.toAlgHom

/-- The reusable comparison recipe sends the polynomial variable image `Ψ (X i)` to the
prescribed Thom generator image in `N_*`. -/
@[simp] theorem thomComparisonPolynomialAlgHom_apply_X
    {R : Type*} [Semiring R] [Algebra (ZMod 2) R]
    (A : ThomUnorientedCobordismPolynomialAlgebra)
    (Ψ : MvPolynomial BOHomologyGeneratorIndex (ZMod 2) ≃ₐ[ZMod 2] R)
    (i : BOHomologyGeneratorIndex) :
    thomComparisonPolynomialAlgHom A Ψ (Ψ (MvPolynomial.X i)) =
      thomComparisonGeneratorImage A i := by
  simp [thomComparisonPolynomialAlgHom]

/-- The reusable comparison recipe sends each chosen polynomial generator to the prescribed Thom
generator image in `N_*`. -/
theorem thomComparisonPolynomialAlgHom_apply_generator
    {R : Type*} [Semiring R] [Algebra (ZMod 2) R]
    (A : ThomUnorientedCobordismPolynomialAlgebra)
    (a : BOHomologyGeneratorIndex → R)
    (Ψ : MvPolynomial BOHomologyGeneratorIndex (ZMod 2) ≃ₐ[ZMod 2] R)
    (hX : ∀ i : BOHomologyGeneratorIndex, Ψ (MvPolynomial.X i) = a i)
    (i : BOHomologyGeneratorIndex) :
    thomComparisonPolynomialAlgHom A Ψ (a i) =
      thomComparisonGeneratorImage A i := by
  rw [← hX i]
  exact thomComparisonPolynomialAlgHom_apply_X A Ψ i

section

variable
  (TO : RingPrespectrum.{u, w})
  (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
  (sphereZeroModel : BasedCWComplex)
  [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
  [toTOHomologyAlgebra :
    RingPrespectrumModTwoHomologyModTwoAlgebra
      TO toPresentation sphereZeroModel toTOHomologyRing]
  (A : ThomUnorientedCobordismPolynomialAlgebra)

/-- Construction 25.5.1. Using the polynomial presentation of `H_*(TO)` from Corollary 25.3.7
and the abstract algebra
`N_* = Z_2[u_i | i > 1, i ≠ 2^r - 1]` from Theorem 25.1.3, the comparison map
`f : H_*(TO) → N_*` is the `ZMod 2`-algebra homomorphism obtained by polynomial evaluation,
sending the homology generator `a_i` to the abstract Thom generator `u_i` in the admissible
degrees and to `0` in the excluded degrees. This is the chapter-local formalization of the
textbook formulas modeled on the coaction. -/
def thomComparisonAlgHom
    (Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel) :=
  thomComparisonPolynomialAlgHom A Ψ

/-- The source-facing comparison map from Construction 25.5.1 sends the polynomial variable image
`Ψ (X i)` to the prescribed Thom generator image in `N_*`. -/
@[simp] theorem thomComparisonAlgHom_apply_X
    (Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel)
    (i : BOHomologyGeneratorIndex) :
    thomComparisonAlgHom TO toPresentation sphereZeroModel A Ψ (Ψ (MvPolynomial.X i)) =
      thomComparisonGeneratorImage A i := by
  exact thomComparisonPolynomialAlgHom_apply_X A Ψ i

/-- The comparison algebra map from Construction 25.5.1 sends each chosen polynomial generator
`a_i` of `H_*(TO)` to the prescribed generator image in the abstract algebra `N_*`. -/
theorem thomComparisonAlgHom_apply_generator
    (a : BOHomologyGeneratorIndex →
      ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)
    (Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel)
    (hPresentation :
      IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
        TO toPresentation sphereZeroModel a Ψ)
    (i : BOHomologyGeneratorIndex) :
    thomComparisonAlgHom TO toPresentation sphereZeroModel
        A Ψ (a i) =
      thomComparisonGeneratorImage A i := by
  rw [← isRingPrespectrumModTwoHomologyPolynomialPresentationOn_algEquiv_X hPresentation i]
  exact thomComparisonAlgHom_apply_X TO toPresentation sphereZeroModel A Ψ i

end
