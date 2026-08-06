import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Proposition_25_3_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_3_6

open scoped DirectSum

noncomputable section

universe u v w

-- Semantic recall via `lean_leansearch` surfaced only generic `MvPolynomial` / `AlgEquiv` APIs.
-- Repo inspection shows that Proposition 25.3.5 provides the Thom algebra equivalence `Φ`,
-- while Theorem 25.3.6 packages the target-side polynomial generators `b_i` on `H_*(BO; ZMod 2)`.

/-- A polynomial `ZMod 2`-algebra equivalence from
`MvPolynomial BOHomologyGeneratorIndex (ZMod 2)` to the fixed total mod-`2` homology object
`H_*(TO)` for a chosen ring and `ZMod 2`-algebra structure. -/
abbrev RingPrespectrumModTwoHomologyPolynomialEquiv
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing] :=
  MvPolynomial BOHomologyGeneratorIndex (ZMod 2) ≃ₐ[ZMod 2]
    ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel

/-- A Thom `ZMod 2`-algebra equivalence from `H_*(TO)` to `H_*(BO)` viewed through a chosen
BO-side polynomial presentation `BOPoly`. This is the thin bridge from the source-facing
corollary to the explicit data exported by Proposition 25.3.5 and Theorem 25.3.6. -/
abbrev ThomHomologyPolynomialAlgEquiv
    (BO : Type) [TopologicalSpace BO]
    (BOPoly : BOHomologyPolynomialAlgebra BO)
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing] :=
  ThomHomologyAlgEquiv BO TO toPresentation sphereZeroModel
    toTOHomologyRing toTOHomologyAlgebra BOPoly.toCommRing BOPoly.toAlgebra

/-- The degree-`n` summand in the chosen total mod-`2` homology object `H_*(TO)`. -/
abbrev ringPrespectrumModTwoHomologyDegree
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    (n : ℕ) : Type _ :=
  ((connectivePrespectrumReducedHomology TO.toPrespectrum toPresentation) (n : ℤ)).obj
    sphereZeroModel

/-- Unfolding `ringPrespectrumModTwoHomologyDegree` recovers the degree-`n` reduced homology
group used in the chosen presentation of `H_*(TO)`. -/
theorem ringPrespectrumModTwoHomologyDegree_def
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    (n : ℕ) :
    ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n =
      ((connectivePrespectrumReducedHomology TO.toPrespectrum toPresentation) (n : ℤ)).obj
        sphereZeroModel :=
  rfl

/-- A direct polynomial presentation of the fixed total mod-`2` homology object `H_*(TO)` of a
ring prespectrum consists of homogeneous generators `a_i` indexed by the positive integers, a
polynomial `ZMod 2`-algebra equivalence sending `X i` to `a_i`, and the expected homogeneous
monomial formulas in the total direct sum. -/
def IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    (a : BOHomologyGeneratorIndex → ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)
    (Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel) : Prop :=
  (∀ i, ∃ x :
      ringPrespectrumModTwoHomologyDegree
        TO toPresentation sphereZeroModel (boHomologyGeneratorDegree i),
      a i =
        DirectSum.lof ℤ ℕ
          (fun n ↦ ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n)
          (boHomologyGeneratorDegree i) x) ∧
    (∀ i, Ψ (MvPolynomial.X i) = a i) ∧
      ∀ d : BOHomologyGeneratorIndex →₀ ℕ,
        let totalDegree : ℕ := d.sum fun i e ↦ e * boHomologyGeneratorDegree i
        ∃ x :
          ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel totalDegree,
          Ψ (MvPolynomial.monomial d (1 : ZMod 2)) =
            DirectSum.lof ℤ ℕ
              (fun n ↦ ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n)
              totalDegree x

/-- Unfolding `IsRingPrespectrumModTwoHomologyPolynomialPresentationOn` gives exactly the
homogeneous-generator, variable, and monomial conditions for a polynomial presentation of
`H_*(TO)`. -/
theorem isRingPrespectrumModTwoHomologyPolynomialPresentationOn_iff
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    {a : BOHomologyGeneratorIndex → ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel}
    {Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel} :
    IsRingPrespectrumModTwoHomologyPolynomialPresentationOn TO toPresentation sphereZeroModel a Ψ ↔
      (∀ i, ∃ x :
          ringPrespectrumModTwoHomologyDegree
            TO toPresentation sphereZeroModel (boHomologyGeneratorDegree i),
          a i =
            DirectSum.lof ℤ ℕ
              (fun n ↦ ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n)
              (boHomologyGeneratorDegree i) x) ∧
        (∀ i, Ψ (MvPolynomial.X i) = a i) ∧
          ∀ d : BOHomologyGeneratorIndex →₀ ℕ,
            let totalDegree : ℕ := d.sum fun i e ↦ e * boHomologyGeneratorDegree i
            ∃ x :
              ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel totalDegree,
              Ψ (MvPolynomial.monomial d (1 : ZMod 2)) =
                DirectSum.lof ℤ ℕ
                  (fun n ↦ ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n)
                  totalDegree x :=
  Iff.rfl

/-- In a polynomial presentation of `H_*(TO)`, each generator `a_i` lies in the summand of degree
`boHomologyGeneratorDegree i`. -/
theorem isRingPrespectrumModTwoHomologyPolynomialPresentationOn_generators_homogeneous
    {TO : RingPrespectrum.{u, w}}
    {toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum}
    {sphereZeroModel : BasedCWComplex}
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    {a : BOHomologyGeneratorIndex → ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel}
    {Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel}
    (hPresentation :
      IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
        TO toPresentation sphereZeroModel a Ψ)
    (i : BOHomologyGeneratorIndex) :
    ∃ x :
      ringPrespectrumModTwoHomologyDegree
        TO toPresentation sphereZeroModel (boHomologyGeneratorDegree i),
      a i =
        DirectSum.lof ℤ ℕ
          (fun n ↦ ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n)
          (boHomologyGeneratorDegree i) x := by
  exact hPresentation.1 i

/-- In a polynomial presentation of `H_*(TO)`, the polynomial equivalence sends `X i` to the
chosen generator `a_i`. -/
theorem isRingPrespectrumModTwoHomologyPolynomialPresentationOn_algEquiv_X
    {TO : RingPrespectrum.{u, w}}
    {toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum}
    {sphereZeroModel : BasedCWComplex}
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    {a : BOHomologyGeneratorIndex → ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel}
    {Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel}
    (hPresentation :
      IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
        TO toPresentation sphereZeroModel a Ψ)
    (i : BOHomologyGeneratorIndex) :
    Ψ (MvPolynomial.X i) = a i := by
  exact hPresentation.2.1 i

/-- In a polynomial presentation of `H_*(TO)`, each polynomial monomial maps to a homogeneous
class in the summand of its total degree. -/
theorem isRingPrespectrumModTwoHomologyPolynomialPresentationOn_monomial_homogeneous
    {TO : RingPrespectrum.{u, w}}
    {toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum}
    {sphereZeroModel : BasedCWComplex}
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    {a : BOHomologyGeneratorIndex → ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel}
    {Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel}
    (hPresentation :
      IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
        TO toPresentation sphereZeroModel a Ψ)
    (d : BOHomologyGeneratorIndex →₀ ℕ) :
    let totalDegree : ℕ := d.sum fun i e ↦ e * boHomologyGeneratorDegree i
    ∃ x :
      ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel totalDegree,
      Ψ (MvPolynomial.monomial d (1 : ZMod 2)) =
        DirectSum.lof ℤ ℕ
          (fun n ↦ ringPrespectrumModTwoHomologyDegree TO toPresentation sphereZeroModel n)
          totalDegree x := by
  exact hPresentation.2.2 d

section

variable (BO : Type) [TopologicalSpace BO]

/-- Corollary 25.3.7. If `TO` is the Thom ring prespectrum under consideration,
`Φ : H_*(TO) → H_*(BO)` is a chosen Thom `ZMod 2`-algebra equivalence from Proposition 25.3.5,
and `b_i` is a chosen polynomial generator family for `H_*(BO; ZMod 2)` as in
Theorem 25.3.6, then `H_*(TO)` is likewise a polynomial `ZMod 2`-algebra on generators `a_i`
indexed by the positive integers, with `Φ(a_i) = b_i`. -/
theorem thomPrespectrumModTwoHomology_isPolynomial
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    (BOPoly : BOHomologyPolynomialAlgebra BO)
    (Φ : ThomHomologyPolynomialAlgEquiv BO BOPoly TO toPresentation sphereZeroModel) :
    ∃ a :
        BOHomologyGeneratorIndex →
          ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel,
      ∃ Ψ : RingPrespectrumModTwoHomologyPolynomialEquiv TO toPresentation sphereZeroModel,
        IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
            TO toPresentation sphereZeroModel a Ψ ∧
          ∀ i, Φ (a i) = BOPoly.generators i := sorry

end
