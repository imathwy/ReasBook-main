import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Lemma_20_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v w

-- Chapter 25 already uses the explicit stagewise data `BO(n)`, `γ n`, the stabilization maps,
-- and the compatible inclusions `BO(n) → BO` as the source-facing interface for the stable real
-- classifying space. This file keeps that same surface and refines only the target-side homology
-- algebra API.

/-- The total mod-`2` singular homology object `H_*(BO)` of a chosen space `BO`, realized as the
direct sum of the degreewise homology groups. -/
abbrev boModTwoHomology (BO : Type) [TopologicalSpace BO] : Type _ :=
  ⨁ n : ℕ, rSingularHomology (ZMod 2) n (TopCat.of BO)

/-- The polynomial generators `b_i` in Theorem 25.3.6 are indexed by the positive integers
`i ≥ 1`. -/
abbrev BOHomologyGeneratorIndex :=
  ℕ+

/-- The homological degree of the generator `b_i` is the underlying natural number `i`. -/
def boHomologyGeneratorDegree (i : BOHomologyGeneratorIndex) : ℕ :=
  i

/-- Unfolding `boHomologyGeneratorDegree` recovers the underlying positive integer index. -/
theorem boHomologyGeneratorDegree_def (i : BOHomologyGeneratorIndex) :
    boHomologyGeneratorDegree i = (i : ℕ) :=
  rfl

/-- A `ZMod 2`-algebra structure on the fixed total homology object `H_*(BO; ZMod 2)` for a
chosen commutative ring structure. -/
abbrev BOHomologyModTwoAlgebra
    (BO : Type) [TopologicalSpace BO]
    (toCommRing : CommRing (boModTwoHomology BO)) :=
  letI := toCommRing
  Algebra (ZMod 2) (boModTwoHomology BO)

/-- A polynomial `ZMod 2`-algebra equivalence from
`MvPolynomial BOHomologyGeneratorIndex (ZMod 2)` to `H_*(BO; ZMod 2)`, for a chosen commutative
ring and `ZMod 2`-algebra structure on the fixed total homology object. -/
abbrev BOHomologyPolynomialEquiv
    (BO : Type) [TopologicalSpace BO]
    (toCommRing : CommRing (boModTwoHomology BO))
    (toAlgebra : BOHomologyModTwoAlgebra BO toCommRing) :=
  letI := toCommRing
  letI := toAlgebra
  MvPolynomial BOHomologyGeneratorIndex (ZMod 2) ≃ₐ[ZMod 2] boModTwoHomology BO

/-- A direct polynomial presentation of `H_*(BO; ZMod 2)` consists of homogeneous generators
`b_i` in positive degrees together with a polynomial `ZMod 2`-algebra equivalence sending `X i`
to `b_i`. The monomial clause records that products of the generators remain homogeneous in the
expected total degree. -/
def IsBOHomologyPolynomialPresentationOn
    (BO : Type) [TopologicalSpace BO]
    (toCommRing : CommRing (boModTwoHomology BO))
    (toAlgebra : BOHomologyModTwoAlgebra BO toCommRing)
    (b : BOHomologyGeneratorIndex → boModTwoHomology BO)
    (algEquiv : BOHomologyPolynomialEquiv BO toCommRing toAlgebra) : Prop :=
  (∀ i, ∃ x : rSingularHomology (ZMod 2) (boHomologyGeneratorDegree i) (TopCat.of BO),
    b i =
      DirectSum.lof ℤ ℕ
        (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
        (boHomologyGeneratorDegree i) x) ∧
    (∀ i, algEquiv (MvPolynomial.X i) = b i) ∧
      ∀ d : BOHomologyGeneratorIndex →₀ ℕ,
        ∃ x :
          rSingularHomology (ZMod 2)
            (d.sum fun i e ↦ e * boHomologyGeneratorDegree i)
            (TopCat.of BO),
          algEquiv (MvPolynomial.monomial d (1 : ZMod 2)) =
            DirectSum.lof ℤ ℕ
              (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
              (d.sum fun i e ↦ e * boHomologyGeneratorDegree i) x

/-- Unfolding `IsBOHomologyPolynomialPresentationOn` gives exactly the homogeneous-generator and
polynomial-algebra conditions for the classes `b_i ∈ H_i(BO; ZMod 2)`. -/
theorem isBOHomologyPolynomialPresentationOn_iff
    {BO : Type} [TopologicalSpace BO]
    {toCommRing : CommRing (boModTwoHomology BO)}
    {toAlgebra : BOHomologyModTwoAlgebra BO toCommRing}
    {b : BOHomologyGeneratorIndex → boModTwoHomology BO}
    {algEquiv : BOHomologyPolynomialEquiv BO toCommRing toAlgebra} :
    IsBOHomologyPolynomialPresentationOn BO toCommRing toAlgebra b algEquiv ↔
      (∀ i, ∃ x : rSingularHomology (ZMod 2) (boHomologyGeneratorDegree i) (TopCat.of BO),
        b i =
          DirectSum.lof ℤ ℕ
            (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
            (boHomologyGeneratorDegree i) x) ∧
        (∀ i, algEquiv (MvPolynomial.X i) = b i) ∧
          ∀ d : BOHomologyGeneratorIndex →₀ ℕ,
            ∃ x :
              rSingularHomology (ZMod 2)
                (d.sum fun i e ↦ e * boHomologyGeneratorDegree i)
                (TopCat.of BO),
              algEquiv (MvPolynomial.monomial d (1 : ZMod 2)) =
                DirectSum.lof ℤ ℕ
                  (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
                  (d.sum fun i e ↦ e * boHomologyGeneratorDegree i) x :=
  Iff.rfl

/-- The additive commutative group underlying a candidate commutative ring structure on
`H_*(BO; ZMod 2)` agrees with the canonical direct-sum additive commutative group. -/
def BOHomologyAdditiveCompatibility
    (BO : Type) [TopologicalSpace BO]
    (toCommRing : CommRing (boModTwoHomology BO)) : Prop :=
  let existingAddCommGroup : AddCommGroup (boModTwoHomology BO) := inferInstance
  letI := toCommRing
  (inferInstance : AddCommGroup (boModTwoHomology BO)) = existingAddCommGroup

/-- A polynomial `ZMod 2`-algebra presentation of `H_*(BO; ZMod 2)`, carrying the commutative
ring and algebra structures on the fixed homology object together with the degree-`0` unit class,
the degreewise homogeneous product maps, the generators `b_i`, and the polynomial algebra
equivalence realizing the presentation. -/
structure BOHomologyPolynomialAlgebra (BO : Type) [TopologicalSpace BO] where
  /-- The commutative ring structure on `H_*(BO; ZMod 2)`. -/
  toCommRing : CommRing (boModTwoHomology BO)
  /-- The ring addition, zero, and negation agree with the direct-sum additive commutative group
  structure already carried by `H_*(BO; ZMod 2)`. -/
  addCommGroup_eq : BOHomologyAdditiveCompatibility BO toCommRing
  /-- The `ZMod 2`-algebra structure in the chosen polynomial presentation of `H_*(BO; ZMod 2)`.
  -/
  toAlgebra : BOHomologyModTwoAlgebra BO toCommRing
  /-- The degree-`0` homology class representing the multiplicative unit. -/
  oneClass : rSingularHomology (ZMod 2) 0 (TopCat.of BO)
  /-- The chosen degree-`0` class maps to the ring unit in `H_*(BO; ZMod 2)`. -/
  one_eq :
    letI := toCommRing
    DirectSum.lof ℤ ℕ
        (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
        0 oneClass =
      (1 : boModTwoHomology BO)
  /-- The chosen homogeneous product maps on degreewise mod-`2` homology classes of `BO`. -/
  mulHomogeneous :
    ∀ p q : ℕ,
      rSingularHomology (ZMod 2) p (TopCat.of BO) →
        rSingularHomology (ZMod 2) q (TopCat.of BO) →
          rSingularHomology (ZMod 2) (p + q) (TopCat.of BO)
  /-- Multiplication in the total homology ring is induced on homogeneous classes by the chosen
  degreewise product maps. -/
  lof_mul_eq :
    letI := toCommRing
    ∀ p q : ℕ,
      ∀ x : rSingularHomology (ZMod 2) p (TopCat.of BO),
      ∀ y : rSingularHomology (ZMod 2) q (TopCat.of BO),
        DirectSum.lof ℤ ℕ
            (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
            p x *
          DirectSum.lof ℤ ℕ
            (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
            q y =
            DirectSum.lof ℤ ℕ
              (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
              (p + q) (mulHomogeneous p q x y)
  /-- The homogeneous generators `b_i ∈ H_i(BO; ZMod 2)` indexed by the positive integers. -/
  generators : BOHomologyGeneratorIndex → boModTwoHomology BO
  /-- The polynomial `ZMod 2`-algebra equivalence sending `X i` to the generator `b_i`. -/
  algEquiv : BOHomologyPolynomialEquiv BO toCommRing toAlgebra
  /-- The generators and algebra equivalence satisfy the homogeneous polynomial-presentation
  conditions for `H_*(BO; ZMod 2)`. -/
  isPresentation :
    IsBOHomologyPolynomialPresentationOn BO toCommRing toAlgebra generators algEquiv

/-- A polynomial algebra presentation of `H_*(BO; ZMod 2)` supplies a commutative ring structure
on the fixed homology object. -/
instance {BO : Type} [TopologicalSpace BO] (A : BOHomologyPolynomialAlgebra BO) :
    CommRing (boModTwoHomology BO) :=
  A.toCommRing

/-- A polynomial algebra presentation of `H_*(BO; ZMod 2)` supplies the corresponding
`ZMod 2`-algebra structure on the fixed homology object. -/
instance {BO : Type} [TopologicalSpace BO] (A : BOHomologyPolynomialAlgebra BO) :
    BOHomologyModTwoAlgebra BO A.toCommRing :=
  A.toAlgebra

/-- The data carried by `BOHomologyPolynomialAlgebra BO` identifies the ring unit and
multiplication on `H_*(BO; ZMod 2)` with a degree-`0` class and degreewise homogeneous products.
-/
theorem boHomologyPolynomialAlgebra_ringSpec
    {BO : Type} [TopologicalSpace BO] (A : BOHomologyPolynomialAlgebra BO) :
    letI := A.toCommRing
    DirectSum.lof ℤ ℕ
        (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
        0 A.oneClass =
      (1 : boModTwoHomology BO) ∧
      ∀ p q : ℕ,
        ∀ x : rSingularHomology (ZMod 2) p (TopCat.of BO),
        ∀ y : rSingularHomology (ZMod 2) q (TopCat.of BO),
          DirectSum.lof ℤ ℕ
              (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
              p x *
            DirectSum.lof ℤ ℕ
              (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
              q y =
              DirectSum.lof ℤ ℕ
                (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
                (p + q) (A.mulHomogeneous p q x y) := by
  exact ⟨A.one_eq, A.lof_mul_eq⟩

/-- The data carried by `BOHomologyPolynomialAlgebra BO` satisfies the explicit homogeneous
polynomial-presentation predicate on `H_*(BO; ZMod 2)`. -/
theorem boHomologyPolynomialAlgebra_spec
    {BO : Type} [TopologicalSpace BO] (A : BOHomologyPolynomialAlgebra BO) :
    IsBOHomologyPolynomialPresentationOn
      BO A.toCommRing A.toAlgebra A.generators A.algEquiv :=
  A.isPresentation

/-- The map on total homology induced by the source inclusion
`i : RP^∞ = BO(1) → BO`, evaluated on a degree-`i` class. -/
abbrev stableBOGeneratorImage
    {BO : Type} [TopologicalSpace BO]
    (BOStage : ℕ → Type)
    [∀ n, TopologicalSpace (BOStage n)]
    (stageInclusion : ∀ n : ℕ, ContinuousMap (BOStage n) BO)
    (stageOneIso : TopCat.of RealProjectiveInfinity ≅ TopCat.of (BOStage 1))
    (i : BOHomologyGeneratorIndex)
    (x : rSingularHomology
      (ZMod 2) (boHomologyGeneratorDegree i) (TopCat.of RealProjectiveInfinity)) :
    boModTwoHomology BO :=
  DirectSum.lof ℤ ℕ
    (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
    (boHomologyGeneratorDegree i)
    (rSingularHomologyMap
      (ZMod 2) (boHomologyGeneratorDegree i)
      (stageOneIso.hom ≫ TopCat.ofHom (stageInclusion 1)) x)

/-- A class `x_i ∈ H_i(RP^∞; ZMod 2)` is the source's distinguished generator exactly when it
is the unique nonzero class in that degree. -/
def IsRPInfinityHomologyGenerator
    (i : BOHomologyGeneratorIndex)
    (x : rSingularHomology
      (ZMod 2) (boHomologyGeneratorDegree i) (TopCat.of RealProjectiveInfinity)) : Prop :=
  x ≠ 0 ∧ ∀ y, y ≠ 0 → y = x

section

/-- Theorem 25.3.6. Let `i : RP^∞ = BO(1) → BO` be the stable inclusion and let `x_i` be the
unique nonzero class in `H_i(RP^∞; ZMod 2)`.  Then the classes `b_i = i_*(x_i)` are homogeneous
polynomial generators and
`H_*(BO; ZMod 2) = ZMod 2[b_i | i ≥ 1]`.  The finite-stage data below fixes the source's stable
`BO`, while `stageOneIso` identifies its first stage with `RP^∞`; unlike the previous statement,
the polynomial generators in the conclusion are explicitly the images of that inclusion. -/
theorem boHomologyPolynomialAlgebra_exists
    (BO : Type) [TopologicalSpace BO]
    (BOStage : ℕ → Type)
    [∀ n, TopologicalSpace (BOStage n)]
    (stageInclusion : ∀ n : ℕ, ContinuousMap (BOStage n) BO)
    (stageOneIso : TopCat.of RealProjectiveInfinity ≅ TopCat.of (BOStage 1))
    (stabilization : ∀ n : ℕ, ContinuousMap (BOStage n) (BOStage (n + 1)))
    (stageInclusion_comp_stabilization :
      ∀ n : ℕ, stageInclusion n = (stageInclusion (n + 1)).comp (stabilization n))
    (γ : ∀ n : ℕ, BOStage n → Type)
    [∀ n, TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) (γ n))]
    [∀ n, (b : BOStage n) → TopologicalSpace (γ n b)]
    [∀ n, FiberBundle (Fin n → ℝ) (γ n)]
    [∀ n, (b : BOStage n) → AddCommGroup (γ n b)]
    [∀ n, (b : BOStage n) → Module ℝ (γ n b)]
    [∀ n, RealPlaneBundleClassifyingSpace n (BOStage n) (γ n)] :
    ∃ (x : ∀ i : BOHomologyGeneratorIndex,
        rSingularHomology
          (ZMod 2) (boHomologyGeneratorDegree i) (TopCat.of RealProjectiveInfinity))
      (toCommRing : CommRing (boModTwoHomology BO))
      (toAlgebra : BOHomologyModTwoAlgebra BO toCommRing)
      (oneClass : rSingularHomology (ZMod 2) 0 (TopCat.of BO))
      (mulHomogeneous :
        ∀ p q : ℕ,
          rSingularHomology (ZMod 2) p (TopCat.of BO) →
            rSingularHomology (ZMod 2) q (TopCat.of BO) →
              rSingularHomology (ZMod 2) (p + q) (TopCat.of BO))
      (generators : BOHomologyGeneratorIndex → boModTwoHomology BO)
      (algEquiv : BOHomologyPolynomialEquiv BO toCommRing toAlgebra),
      (∀ i, IsRPInfinityHomologyGenerator i (x i)) ∧
        BOHomologyAdditiveCompatibility BO toCommRing ∧
        (letI := toCommRing
         DirectSum.lof ℤ ℕ
             (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
             0 oneClass =
           (1 : boModTwoHomology BO)) ∧
        (letI := toCommRing
         ∀ p q : ℕ,
           ∀ x : rSingularHomology (ZMod 2) p (TopCat.of BO),
           ∀ y : rSingularHomology (ZMod 2) q (TopCat.of BO),
             DirectSum.lof ℤ ℕ
                 (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
                 p x *
               DirectSum.lof ℤ ℕ
                 (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
                 q y =
                 DirectSum.lof ℤ ℕ
                 (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
                 (p + q) (mulHomogeneous p q x y)) ∧
        IsBOHomologyPolynomialPresentationOn BO toCommRing toAlgebra generators algEquiv ∧
        ∀ i,
          generators i =
            stableBOGeneratorImage BOStage stageInclusion stageOneIso i (x i) := by
  sorry

end
