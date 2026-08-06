import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Problem_22_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.SteenrodMultiIndex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_5

open CategoryTheory
open scoped DirectSum

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced no verified `K(ZMod 2, q + 1)` cohomology-ring
-- owner or admissible-Steenrod-monomial presentation in the current environment. The statement is
-- therefore recorded on the local Chapter 22 mod-`2` cohomology owner, using the total direct sum
-- `H^*(X; ZMod 2)` and an explicit polynomial-presentation predicate indexed by admissible
-- Steenrod iterates of a chosen fundamental class.

/-- The total graded mod-`2` cohomology object `H^*(X; ZMod 2)` in the chosen ambient theory
`H2`, realized as the direct sum of the degreewise groups. -/
abbrev modTwoCohomologyStar (H2 : ModTwoCohomologyTheory) (X : TopCat) : Type _ :=
  ⨁ n : ℕ, modTwoCohomologyGroup H2 n X

/-- The direct-sum additive commutative group structure on `modTwoCohomologyStar H2 X`. -/
noncomputable abbrev modTwoCohomologyStarAddCommGroup
    (H2 : ModTwoCohomologyTheory) (X : TopCat) :
    AddCommGroup (modTwoCohomologyStar H2 X) :=
  inferInstance

/-- A commutative ring structure on `H^*(X; ZMod 2)` is the canonical total mod-`2` cohomology
ring when its additive group is the direct-sum one, its unit is `H2.oneClass X` in degree `0`,
and multiplication of homogeneous classes is induced by `H2.cup`. -/
def IsCanonicalModTwoCohomologyRing
    (H2 : ModTwoCohomologyTheory) (X : TopCat)
    (toCommRing : CommRing (modTwoCohomologyStar H2 X)) : Prop :=
  (toCommRing.toRing.toAddCommGroup =
      modTwoCohomologyStarAddCommGroup H2 X) ∧
    (toCommRing.one =
      DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) 0 (H2.oneClass X)) ∧
    ∀ (p q : ℕ) (x : modTwoCohomologyGroup H2 p X) (y : modTwoCohomologyGroup H2 q X),
      toCommRing.mul
          (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) p x)
          (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) q y) =
        DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) (p + q) (H2.cup x y)

namespace SteenrodSquareFamily

/-- Reindexing along the empty multiindex identifies degree `q` with degree `q + [].sum`. -/
theorem applyMultiIndex_nil_degree
    {H2 : ModTwoCohomologyTheory}
    {X : TopCat} (q : ℕ) :
    ((modTwoCohomologyGroup H2 q X) : Type) =
      ((modTwoCohomologyGroup H2 (q + ([] : SteenrodMultiIndex).sum) X) : Type) := by
  simp

/-- Reindexing along `i :: I` identifies the recursive target degree with `q + (i :: I).sum`. -/
theorem applyMultiIndex_cons_degree
    {H2 : ModTwoCohomologyTheory}
    {X : TopCat} (q i : ℕ) (I : SteenrodMultiIndex) :
    ((modTwoCohomologyGroup H2 ((q + i) + I.sum) X) : Type) =
      ((modTwoCohomologyGroup H2 (q + (i :: I).sum) X) : Type) := by
  simp [List.sum_cons, Nat.add_assoc]

/-- Iterating a degreewise Steenrod-square operation family along a multiindex `I` sends a class in
degree `q` to the class obtained by applying the corresponding composite `Sq^I`, which lies in
degree `q + I.sum`. -/
def applyMultiIndex
    {H2 : ModTwoCohomologyTheory}
    (sq : ∀ (n q : ℕ) (X : TopCat),
      modTwoCohomologyGroup H2 q X ⟶ modTwoCohomologyGroup H2 (q + n) X)
    {X : TopCat} :
    ∀ (q : ℕ) (I : SteenrodMultiIndex),
      modTwoCohomologyGroup H2 q X →
        modTwoCohomologyGroup H2 (q + I.sum) X
  | q, [], x =>
      cast (applyMultiIndex_nil_degree q) x
  | q, i :: I, x =>
      cast (applyMultiIndex_cons_degree q i I)
        (applyMultiIndex sq (q + i) I (sq i q X x))

/-- The empty multiindex acts as the identity on mod-`2` cohomology classes. -/
theorem applyMultiIndex_nil
    {H2 : ModTwoCohomologyTheory}
    (sq : ∀ (n q : ℕ) (X : TopCat),
      modTwoCohomologyGroup H2 q X ⟶ modTwoCohomologyGroup H2 (q + n) X)
    {X : TopCat} (q : ℕ) (x : modTwoCohomologyGroup H2 q X) :
    applyMultiIndex sq q [] x = x := by
  simp [applyMultiIndex]

end SteenrodSquareFamily

/-- The admissible Steenrod iterates on a `K(ZMod 2, q + 1)` fundamental class are indexed by
admissible multiindices of excess strictly less than `q + 1`. -/
abbrev EilenbergMacLaneModTwoGeneratorIndex (q : ℕ) :=
  {I : SteenrodMultiIndex // SteenrodMultiIndex.Admissible I ∧ SteenrodMultiIndex.excess I < q + 1}

/-- An index in `EilenbergMacLaneModTwoGeneratorIndex q` carries exactly the admissibility and
excess conditions required for the standard polynomial generators `Sq^I u`. -/
theorem eilenbergMacLaneModTwoGeneratorIndex_spec
    {q : ℕ} (I : EilenbergMacLaneModTwoGeneratorIndex q) :
    SteenrodMultiIndex.Admissible I.1 ∧ SteenrodMultiIndex.excess I.1 < q + 1 := sorry

/-- The cohomological degree of the admissible generator `Sq^I u` attached to a fundamental class
`u ∈ H^(q + 1)(K(ZMod 2, q + 1); ZMod 2)` is `(q + 1) + I.sum`. -/
def eilenbergMacLaneModTwoGeneratorDegree
    (q : ℕ) (I : EilenbergMacLaneModTwoGeneratorIndex q) : ℕ :=
  (q + 1) + I.1.sum

/-- `eilenbergMacLaneModTwoGeneratorDegree q I` is definitionally `(q + 1) + I.sum`. -/
theorem eilenbergMacLaneModTwoGeneratorDegree_def
    (q : ℕ) (I : EilenbergMacLaneModTwoGeneratorIndex q) :
    eilenbergMacLaneModTwoGeneratorDegree q I = (q + 1) + I.1.sum := sorry

/-- The direct-sum generator corresponding to the admissible Steenrod iterate `Sq^I u`. -/
def eilenbergMacLaneModTwoGenerator
    (H2 : ModTwoCohomologyTheory)
    (sq : ∀ (n q : ℕ) (X : TopCat),
      modTwoCohomologyGroup H2 q X ⟶ modTwoCohomologyGroup H2 (q + n) X)
    (q : ℕ) (X : TopCat)
    (fundamentalClass : modTwoCohomologyGroup H2 (q + 1) X) :
    EilenbergMacLaneModTwoGeneratorIndex q → modTwoCohomologyStar H2 X :=
  fun I ↦
    DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X)
      (eilenbergMacLaneModTwoGeneratorDegree q I)
      (SteenrodSquareFamily.applyMultiIndex sq (q + 1) I.1 fundamentalClass)

/-- `eilenbergMacLaneModTwoGenerator` inserts `Sq^I u` into the direct-sum summand of degree
`eilenbergMacLaneModTwoGeneratorDegree q I`. -/
theorem eilenbergMacLaneModTwoGenerator_apply
    (H2 : ModTwoCohomologyTheory)
    (sq : ∀ (n q : ℕ) (X : TopCat),
      modTwoCohomologyGroup H2 q X ⟶ modTwoCohomologyGroup H2 (q + n) X)
    (q : ℕ) (X : TopCat)
    (fundamentalClass : modTwoCohomologyGroup H2 (q + 1) X)
    (I : EilenbergMacLaneModTwoGeneratorIndex q) :
    eilenbergMacLaneModTwoGenerator H2 sq q X fundamentalClass I =
      DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X)
        (eilenbergMacLaneModTwoGeneratorDegree q I)
        (SteenrodSquareFamily.applyMultiIndex sq (q + 1) I.1 fundamentalClass) := by
  rfl

/-- For a based space `K` realizing `K(ZMod 2, q + 1)`, a degree-`q + 1` mod-`2` cohomology class
`u` is fundamental when it is the unique nonzero class in that degree. This records the usual
generator of `H^(q + 1)(K; ZMod 2) ≃ ZMod 2` attached to the chosen `K(ZMod 2, q + 1)` setup. -/
def IsFundamentalClassForAdditiveEilenbergMacLaneSpace
    (H2 : ModTwoCohomologyTheory) (q : ℕ) (K : Under (⊤_ TopCat))
    (u : modTwoCohomologyGroup H2 (q + 1) K.right) : Prop :=
  u ≠ 0 ∧ ∀ v : modTwoCohomologyGroup H2 (q + 1) K.right, v = 0 ∨ v = u

/-- Unfolding `IsFundamentalClassForAdditiveEilenbergMacLaneSpace` says that the chosen class is
the unique nonzero degree-`q + 1` mod-`2` cohomology class on the fixed `K(ZMod 2, q + 1)` model.
-/
theorem isFundamentalClassForAdditiveEilenbergMacLaneSpace_iff
    (H2 : ModTwoCohomologyTheory) (q : ℕ) (K : Under (⊤_ TopCat))
    (u : modTwoCohomologyGroup H2 (q + 1) K.right) :
    IsFundamentalClassForAdditiveEilenbergMacLaneSpace H2 q K u ↔
      u ≠ 0 ∧ ∀ v : modTwoCohomologyGroup H2 (q + 1) K.right, v = 0 ∨ v = u := sorry

/-- The induced `ZMod 2`-algebra structure on a chosen commutative ring structure on
`H^*(X; ZMod 2)`. -/
abbrev modTwoCohomologyStarModTwoAlgebra
    (H2 : ModTwoCohomologyTheory) (X : TopCat)
    (toCommRing : CommRing (modTwoCohomologyStar H2 X)) :=
  @Algebra (ZMod 2) (modTwoCohomologyStar H2 X) inferInstance toCommRing.toSemiring

/-- A chosen canonical `ZMod 2`-algebra structure on the fixed total mod-`2` cohomology object
`H^*(X; ZMod 2)`, carrying both the commutative ring structure and its canonicality witness. -/
structure CanonicalModTwoCohomologyAlgebra
    (H2 : ModTwoCohomologyTheory) (X : TopCat) where
  /-- The commutative ring structure on `H^*(X; ZMod 2)`. -/
  toCommRing : CommRing (modTwoCohomologyStar H2 X)
  /-- The chosen ring structure is the canonical cup-product ring on the fixed direct sum. -/
  isCanonical : IsCanonicalModTwoCohomologyRing H2 X toCommRing
  /-- The induced `ZMod 2`-algebra structure on the canonical total mod-`2` cohomology ring. -/
  toAlgebra : modTwoCohomologyStarModTwoAlgebra H2 X toCommRing

/-- A canonical total mod-`2` cohomology algebra supplies its chosen commutative ring structure. -/
instance {H2 : ModTwoCohomologyTheory} {X : TopCat}
    (A : CanonicalModTwoCohomologyAlgebra H2 X) :
    CommRing (modTwoCohomologyStar H2 X) :=
  A.toCommRing

/-- A canonical total mod-`2` cohomology algebra supplies its chosen `ZMod 2`-algebra structure.
-/
instance {H2 : ModTwoCohomologyTheory} {X : TopCat}
    (A : CanonicalModTwoCohomologyAlgebra H2 X) :
    modTwoCohomologyStarModTwoAlgebra H2 X A.toCommRing := by
  exact A.toAlgebra

/-- A canonical total mod-`2` cohomology algebra carries the canonical cup-product ring
compatibility on the fixed direct sum. -/
theorem CanonicalModTwoCohomologyAlgebra.isCanonicalRing
    {H2 : ModTwoCohomologyTheory} {X : TopCat}
    (A : CanonicalModTwoCohomologyAlgebra H2 X) :
    IsCanonicalModTwoCohomologyRing H2 X A.toCommRing :=
  A.isCanonical

/-- A polynomial `ZMod 2`-algebra equivalence from
`MvPolynomial (EilenbergMacLaneModTwoGeneratorIndex q) (ZMod 2)` to the canonical total mod-`2`
cohomology algebra `H^*(X; ZMod 2)` carried by `A`. -/
abbrev eilenbergMacLaneModTwoPolynomialEquiv
    (H2 : ModTwoCohomologyTheory) (q : ℕ) (X : TopCat)
    (A : CanonicalModTwoCohomologyAlgebra H2 X) :=
  let _ : CommRing (modTwoCohomologyStar H2 X) := A.toCommRing
  let _ : Algebra (ZMod 2) (modTwoCohomologyStar H2 X) := A.toAlgebra
  MvPolynomial (EilenbergMacLaneModTwoGeneratorIndex q) (ZMod 2) ≃ₐ[ZMod 2]
    modTwoCohomologyStar H2 X

/-- A polynomial presentation of the canonical total mod-`2` cohomology ring of `X` on admissible
Steenrod iterates of a chosen degree-`q + 1` class `u`: the polynomial variables map to the
direct-sum generators `Sq^I u`, and monomials land in the corresponding homogeneous summands. -/
def IsEilenbergMacLaneModTwoPolynomialPresentationOn
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (q : ℕ) (X : TopCat)
    (A : CanonicalModTwoCohomologyAlgebra H2 X)
    (fundamentalClass : modTwoCohomologyGroup H2 (q + 1) X)
    (algEquiv : eilenbergMacLaneModTwoPolynomialEquiv H2 q X A) : Prop :=
  (∀ I,
    algEquiv (MvPolynomial.X I) =
      eilenbergMacLaneModTwoGenerator H2 Sq.sq q X fundamentalClass I) ∧
    ∀ d : EilenbergMacLaneModTwoGeneratorIndex q →₀ ℕ,
      ∃ x :
        modTwoCohomologyGroup H2
          (d.sum fun I e ↦ e * eilenbergMacLaneModTwoGeneratorDegree q I) X,
        algEquiv (MvPolynomial.monomial d (1 : ZMod 2)) =
          DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X)
            (d.sum fun I e ↦ e * eilenbergMacLaneModTwoGeneratorDegree q I) x

/-- Unfolding `IsEilenbergMacLaneModTwoPolynomialPresentationOn` gives the variable formulas and
the homogeneous-monomial condition for the admissible Steenrod generators. -/
theorem isEilenbergMacLaneModTwoPolynomialPresentationOn_iff
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    {Sq : SteenrodSquareFamily H2 suspension suspensionIso}
    {q : ℕ} {X : TopCat}
    {A : CanonicalModTwoCohomologyAlgebra H2 X}
    {fundamentalClass : modTwoCohomologyGroup H2 (q + 1) X}
    {algEquiv : eilenbergMacLaneModTwoPolynomialEquiv H2 q X A} :
    IsEilenbergMacLaneModTwoPolynomialPresentationOn
        H2 Sq q X A fundamentalClass algEquiv ↔
      (∀ I,
        algEquiv (MvPolynomial.X I) =
          eilenbergMacLaneModTwoGenerator H2 Sq.sq q X fundamentalClass I) ∧
      ∀ d : EilenbergMacLaneModTwoGeneratorIndex q →₀ ℕ,
        ∃ x :
          modTwoCohomologyGroup H2
            (d.sum fun I e ↦ e * eilenbergMacLaneModTwoGeneratorDegree q I) X,
          algEquiv (MvPolynomial.monomial d (1 : ZMod 2)) =
            DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X)
              (d.sum fun I e ↦ e * eilenbergMacLaneModTwoGeneratorDegree q I) x :=
  Iff.rfl

/-- In an Eilenberg-MacLane polynomial presentation, each polynomial variable `X_I` maps to the
corresponding admissible Steenrod iterate `Sq^I u`. -/
theorem isEilenbergMacLaneModTwoPolynomialPresentationOn_X
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    {Sq : SteenrodSquareFamily H2 suspension suspensionIso}
    {q : ℕ} {X : TopCat}
    {A : CanonicalModTwoCohomologyAlgebra H2 X}
    {fundamentalClass : modTwoCohomologyGroup H2 (q + 1) X}
    {algEquiv : eilenbergMacLaneModTwoPolynomialEquiv H2 q X A}
    (h :
      IsEilenbergMacLaneModTwoPolynomialPresentationOn
        H2 Sq q X A fundamentalClass algEquiv)
    (I : EilenbergMacLaneModTwoGeneratorIndex q) :
    algEquiv (MvPolynomial.X I) =
      eilenbergMacLaneModTwoGenerator H2 Sq.sq q X fundamentalClass I :=
  h.1 I

/-- In an Eilenberg-MacLane polynomial presentation, each monomial maps to a homogeneous class in
the summand of the expected total degree. -/
theorem isEilenbergMacLaneModTwoPolynomialPresentationOn_monomial
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    {Sq : SteenrodSquareFamily H2 suspension suspensionIso}
    {q : ℕ} {X : TopCat}
    {A : CanonicalModTwoCohomologyAlgebra H2 X}
    {fundamentalClass : modTwoCohomologyGroup H2 (q + 1) X}
    {algEquiv : eilenbergMacLaneModTwoPolynomialEquiv H2 q X A}
    (h :
      IsEilenbergMacLaneModTwoPolynomialPresentationOn
        H2 Sq q X A fundamentalClass algEquiv)
    (d : EilenbergMacLaneModTwoGeneratorIndex q →₀ ℕ) :
    ∃ x :
      modTwoCohomologyGroup H2
        (d.sum fun I e ↦ e * eilenbergMacLaneModTwoGeneratorDegree q I) X,
      algEquiv (MvPolynomial.monomial d (1 : ZMod 2)) =
        DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X)
          (d.sum fun I e ↦ e * eilenbergMacLaneModTwoGeneratorDegree q I) x :=
  h.2 d

/-- Theorem 22.5.6. For a based space `K` realizing `K(ZMod 2, q)` with `q > 0` and a chosen
Steenrod square family `Sq` from Theorem 22.5.5, there exist a canonical total mod-`2`
cohomology algebra `A` on `H^*(K; ZMod 2)`, a fundamental class `u ∈ H^q(K; ZMod 2)`, and a
polynomial `ZMod 2`-algebra equivalence whose variables map to the admissible Steenrod iterates
`Sq^I u` with `SteenrodMultiIndex.excess I < q`. The implementation uses the index `q.natPred`,
so the distinguished class has degree `q.natPred + 1 = q`. -/
theorem eilenbergMacLaneModTwoCohomology_isPolynomial
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (q : ℕ+) (K : Under (⊤_ TopCat))
    (hK : IsAdditiveEilenbergMacLaneSpace (ZMod 2) q.natPred K) :
    ∃ (A : CanonicalModTwoCohomologyAlgebra H2 K.right)
      (fundamentalClass : modTwoCohomologyGroup H2 (q.natPred + 1) K.right)
      (algEquiv : eilenbergMacLaneModTwoPolynomialEquiv H2 q.natPred K.right A),
      IsFundamentalClassForAdditiveEilenbergMacLaneSpace
          H2 q.natPred K fundamentalClass ∧
        IsEilenbergMacLaneModTwoPolynomialPresentationOn
          H2 Sq q.natPred K.right A fundamentalClass algEquiv := sorry
