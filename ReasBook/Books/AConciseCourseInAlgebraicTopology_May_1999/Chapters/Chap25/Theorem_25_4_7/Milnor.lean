import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.PNat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_6.DualAlgebra
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_5

noncomputable section

/-- The special admissible Steenrod multiindex `[2^(r - 1), 2^(r - 2), ..., 2, 1]` attached to
the Milnor generator `ξ_r`. -/
def milnorSpecialSteenrodMultiIndex : ℕ → SteenrodMultiIndex
  | 0 => []
  | r + 1 => 2 ^ r :: milnorSpecialSteenrodMultiIndex r

/-- Appending one more leading power of `2` gives the next special Steenrod multiindex. -/
theorem milnorSpecialSteenrodMultiIndex_succ (r : ℕ) :
    milnorSpecialSteenrodMultiIndex (r + 1) =
      2 ^ r :: milnorSpecialSteenrodMultiIndex r :=
  rfl

/-- Milnor's special Steenrod multiindices satisfy the admissibility inequalities from
Theorem 25.4.5. -/
theorem milnorSpecialSteenrodMultiIndex_admissible (r : ℕ+) :
    SteenrodMultiIndex.Admissible (milnorSpecialSteenrodMultiIndex (r : ℕ)) := sorry

/-- The special admissible Steenrod monomial indexed by `r ≥ 1`, viewed in the admissible
multiindex subtype from Theorem 25.4.5. -/
abbrev milnorSpecialAdmissibleSteenrodMonomial
    (r : ℕ+) : AdmissibleSteenrodMonomialIndex :=
  ⟨milnorSpecialSteenrodMultiIndex (r : ℕ), milnorSpecialSteenrodMultiIndex_admissible r⟩

/-- The chosen special admissible monomial for `ξ_r` is represented by the explicit power-of-`2`
multiindex `[2^(r - 1), 2^(r - 2), ..., 2, 1]`. -/
theorem milnorSpecialAdmissibleSteenrodMonomial_spec (r : ℕ+) :
    (milnorSpecialAdmissibleSteenrodMonomial r).1 =
      milnorSpecialSteenrodMultiIndex (r : ℕ) :=
  rfl

/-- The special admissible multiindex `[2^(r - 1), 2^(r - 2), ..., 2, 1]` shifts a degree-`1`
class to degree `2 ^ r`. -/
theorem milnorSpecialSteenrodMultiIndex_targetDegree (r : ℕ) :
    1 + (milnorSpecialSteenrodMultiIndex r).sum = 2 ^ r := sorry

/-- The special admissible basis operation indexed by `r ≥ 1` also shifts a degree-`1` class to
degree `2 ^ r` when viewed in the admissible-monomial subtype. -/
theorem milnorSpecialAdmissibleSteenrodMonomial_targetDegree
    (r : ℕ+) :
    1 + (milnorSpecialAdmissibleSteenrodMonomial r).1.sum = 2 ^ (r : ℕ) := sorry

/-- A commutative multiplication law on a chosen dual Steenrod algebra owner from
Lemma 25.4.6. -/
class ModTwoSteenrodAlgebraDualAlgebra.IsCommutative
    (AStar : ModTwoSteenrodAlgebraDualAlgebra) : Prop where
  /-- The multiplication on the chosen dual Steenrod algebra owner is commutative. -/
  mul_comm :
    let _ : Ring modTwoSteenrodAlgebraGradedDual := AStar.toRing
    ∀ x y : modTwoSteenrodAlgebraGradedDual, x * y = y * x

/-- The type of polynomial `ZMod 2`-algebra equivalences realizing Milnor's presentation on the
fixed dual Steenrod algebra `A_*` for a chosen dual Steenrod algebra owner from Lemma 25.4.6. -/
abbrev ModTwoSteenrodAlgebraDualMilnorAlgEquiv
    (AStar : ModTwoSteenrodAlgebraDualAlgebra) : Type :=
  let _ : Ring modTwoSteenrodAlgebraGradedDual := AStar.toRing
  let _ : Algebra (ZMod 2) modTwoSteenrodAlgebraGradedDual := AStar.toAlgebra
  MvPolynomial ℕ+ (ZMod 2) ≃ₐ[ZMod 2] modTwoSteenrodAlgebraGradedDual

/-- A direct Milnor polynomial presentation on the fixed dual Steenrod algebra `A_*` consists of
the dual Steenrod algebra owner from Lemma 25.4.6 together with generators `ξ_r ∈ A_*` dual to
the admissible Steenrod monomials `admissibleSteenrodMonomial I` from Theorem 25.4.5, and a
polynomial `ZMod 2`-algebra equivalence sending the variables `X_r` to those generators. -/
def IsMilnorPolynomialPresentationOn
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    (ξ : ℕ+ → modTwoSteenrodAlgebraGradedDual)
  (algEquiv : ModTwoSteenrodAlgebraDualMilnorAlgEquiv AStar) : Prop :=
  (∀ r I,
    modTwoSteenrodAlgebraGradedDual.eval (ξ r)
        (admissibleSteenrodMonomial I) =
      if I = milnorSpecialAdmissibleSteenrodMonomial r then 1 else 0) ∧
    ∀ r, algEquiv (MvPolynomial.X r) = ξ r

/-- `IsMilnorPolynomialPresentationOn` is exactly the assertion that the admissible monomial basis
of `A` from Theorem 25.4.5, represented by the admissible monomials
`admissibleSteenrodMonomial I`, has dual generators `ξ_r` indexed by the special
admissible monomials and that these generators polynomially generate `A_*`. -/
theorem isMilnorPolynomialPresentationOn_iff
    {AStar : ModTwoSteenrodAlgebraDualAlgebra}
    {ξ : ℕ+ → modTwoSteenrodAlgebraGradedDual}
    {algEquiv : ModTwoSteenrodAlgebraDualMilnorAlgEquiv AStar} :
    IsMilnorPolynomialPresentationOn AStar ξ algEquiv ↔
      (∀ r I,
        modTwoSteenrodAlgebraGradedDual.eval (ξ r)
            (admissibleSteenrodMonomial I) =
          if I = milnorSpecialAdmissibleSteenrodMonomial r then 1 else 0) ∧
        ∀ r, algEquiv (MvPolynomial.X r) = ξ r :=
  Iff.rfl

/-- A Milnor polynomial presentation on the fixed dual Steenrod algebra `A_*`, extending the
chapter-local dual Steenrod algebra owner from Lemma 25.4.6 by recording commutativity,
Milnor's generators `ξ_r`, and the polynomial algebra equivalence realizing Milnor's theorem. -/
structure ModTwoSteenrodAlgebraDualMilnorPresentation where
  /-- The underlying source-facing dual Steenrod algebra owner from Lemma 25.4.6. -/
  toDualAlgebra : ModTwoSteenrodAlgebraDualAlgebra
  /-- The multiplication on the stored dual Steenrod algebra owner is commutative. -/
  toIsCommutative : ModTwoSteenrodAlgebraDualAlgebra.IsCommutative toDualAlgebra
  /-- Milnor's generators `ξ_r` of the fixed dual Steenrod algebra `A_*`, indexed by `r : ℕ+`. -/
  generators : ℕ+ → modTwoSteenrodAlgebraGradedDual
  /-- The polynomial `ZMod 2`-algebra equivalence realizing Milnor's presentation of `A_*`. -/
  algEquiv : ModTwoSteenrodAlgebraDualMilnorAlgEquiv toDualAlgebra
  /-- Milnor's generators and algebra equivalence satisfy the fixed-object polynomial-presentation
  conditions on the dual Steenrod algebra `A_*`. -/
  isPresentation : IsMilnorPolynomialPresentationOn toDualAlgebra generators algEquiv

/-- A Milnor presentation supplies the chapter-local dual Steenrod algebra owner from
Lemma 25.4.6. -/
abbrev ModTwoSteenrodAlgebraDualMilnorPresentation.toCommRing
    (A : ModTwoSteenrodAlgebraDualMilnorPresentation) :
    CommRing modTwoSteenrodAlgebraGradedDual :=
  { A.toDualAlgebra.toRing with
    mul_comm := A.toIsCommutative.mul_comm }

/-- A Milnor presentation supplies the `ZMod 2`-algebra structure stored by the underlying
dual Steenrod algebra owner from Lemma 25.4.6. -/
abbrev ModTwoSteenrodAlgebraDualMilnorPresentation.toAlgebra
    (A : ModTwoSteenrodAlgebraDualMilnorPresentation) :
    modTwoSteenrodAlgebraGradedDualAlgebraStructure A.toCommRing.toRing :=
  A.toDualAlgebra.toAlgebra

/-- A Milnor presentation carries the additive-compatibility statement from the underlying dual
Steenrod algebra owner. -/
theorem ModTwoSteenrodAlgebraDualMilnorPresentation.addCommGroup_eq
    (A : ModTwoSteenrodAlgebraDualMilnorPresentation) :
    A.toCommRing.toAddCommGroup = modTwoSteenrodAlgebraGradedDualAddCommGroup := by
  simpa [ModTwoSteenrodAlgebraDualMilnorPresentation.toCommRing] using
    A.toDualAlgebra.addCommGroup_eq

/-- A Milnor presentation supplies a commutative ring structure on the fixed dual Steenrod
algebra `A_*`. -/
instance (A : ModTwoSteenrodAlgebraDualMilnorPresentation) :
    CommRing modTwoSteenrodAlgebraGradedDual :=
  A.toCommRing

/-- A Milnor presentation carries the commutativity property on its underlying dual Steenrod
algebra owner. -/
instance (A : ModTwoSteenrodAlgebraDualMilnorPresentation) :
    ModTwoSteenrodAlgebraDualAlgebra.IsCommutative A.toDualAlgebra :=
  A.toIsCommutative

/-- A Milnor presentation supplies a `ZMod 2`-algebra structure on the fixed dual Steenrod
algebra `A_*`. -/
instance (A : ModTwoSteenrodAlgebraDualMilnorPresentation) :
    modTwoSteenrodAlgebraGradedDualAlgebraStructure A.toCommRing.toRing :=
  A.toAlgebra

namespace ModTwoSteenrodAlgebraDualMilnorPresentation

/-- In a Milnor presentation, `ξ_r` evaluates to the Kronecker delta on the admissible basis
monomials from Theorem 25.4.5. -/
theorem generators_apply_admissibleSteenrodMonomial
    (A : ModTwoSteenrodAlgebraDualMilnorPresentation)
    (r : ℕ+) (I : AdmissibleSteenrodMonomialIndex) :
    modTwoSteenrodAlgebraGradedDual.eval (A.generators r)
        (admissibleSteenrodMonomial I) =
      if I = milnorSpecialAdmissibleSteenrodMonomial r then 1 else 0 :=
  A.isPresentation.1 r I

/-- In a Milnor presentation, the polynomial generator `X_r` maps to the Milnor generator
`ξ_r`. -/
theorem algEquiv_X
    (A : ModTwoSteenrodAlgebraDualMilnorPresentation)
    (r : ℕ+) :
    A.algEquiv (MvPolynomial.X r) = A.generators r :=
  A.isPresentation.2 r

end ModTwoSteenrodAlgebraDualMilnorPresentation
