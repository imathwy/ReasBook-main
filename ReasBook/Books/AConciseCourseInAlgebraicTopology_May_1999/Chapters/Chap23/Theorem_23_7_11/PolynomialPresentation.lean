import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.PNat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_7_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_7_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Proposition_23_7_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_2

noncomputable section

open scoped DirectSum

-- Repository precedent in Chapters 22 and 23 packages polynomial cohomology statements on the
-- fixed total cohomology object `H^*(X; R)`, not on an arbitrary chosen carrier with degreewise
-- comparison maps. This module keeps that owner layer for singular cohomology with coefficients
-- in a general commutative ring `R`, while exposing the source-facing universal Pontryagin and
-- Euler classes on `BO(n)` and `BSO(n)` as reusable API for Theorem 23.7.11 and later items.

/-- The total graded singular cohomology object `H^*(X; R)`, realized as the direct sum of the
degreewise groups `H^q(X; R)`. -/
abbrev singularCohomologyStar (R : Type) [CommRing R] (X : TopCat) : Type _ :=
  ⨁ n : ℕ, singularCohomologyClasses R X n

namespace SingularCohomologyNotation

/-- Lean notation for the total singular cohomology object `H^*(X; R)`. -/
scoped notation "H^*(" X "; " R ")" => singularCohomologyStar R X

end SingularCohomologyNotation

open scoped SingularCohomologyNotation

/-- Each graded summand `H^q(X; R)` of `H^*(X; R)` is an additive commutative
monoid via the degreewise singular cohomology group structure. -/
instance singularCohomologyStarSummandAddCommMonoid
    (R : Type) [CommRing R] (X : TopCat) :
    ∀ n : ℕ, AddCommMonoid (singularCohomologyClasses R X n) :=
  fun _ ↦ inferInstance

/-- The direct-sum additive commutative group structure on `H^*(X; R)`. -/
noncomputable abbrev singularCohomologyStarAddCommGroup
    (R : Type) [CommRing R] (X : TopCat) :
    AddCommGroup (H^*(X; R)) :=
  inferInstance

/-- The canonical inclusion of the degree-`q` summand `H^q(X; R)` into `H^*(X; R)`. -/
abbrev singularCohomologyStarLof
    (R : Type) [CommRing R] (X : TopCat) (q : ℕ) :
    singularCohomologyClasses R X q → H^*(X; R) :=
  DirectSum.lof ℤ ℕ (fun n ↦ singularCohomologyClasses R X n) q

/-- The constant singular `0`-cochain with value `r`. -/
def singularZeroCochain
    (R : Type) [CommRing R] (X : TopCat) (r : R) :
    singularCochains R X 0 :=
  fun _ ↦ r

/-- The constant singular `0`-cochain with value `r` is closed. -/
theorem singularZeroCochain_closed
    (R : Type) [CommRing R] (X : TopCat) (r : R) :
    singularCochains.coboundary (singularZeroCochain R X r) = 0 := by
  sorry

/-- The degree-`0` singular cohomology class determined by the constant `0`-cochain with value
`r`. -/
def singularCohomologyCoefficientClass
    (R : Type) [CommRing R] (X : TopCat) (r : R) :
    singularCohomologyClasses R X 0 :=
  Quotient.mk (singularCohomologySetoid R X 0)
    ⟨singularZeroCochain R X r, singularZeroCochain_closed R X r⟩

/-- An ambient commutative ring structure on `H^*(X; R)` is canonical when its additive
structure is the direct-sum one, its unit is the degree-`0` unit class, and multiplication of
homogeneous classes is induced by the cup product. -/
class IsCanonicalSingularCohomologyRing
    (R : Type) [CommRing R] (X : TopCat) [CommRing (H^*(X; R))] : Prop where
  /-- The additive group structure is the direct-sum one. -/
  toAddCommGroup_eq :
    (inferInstance : AddCommGroup (H^*(X; R))) = singularCohomologyStarAddCommGroup R X
  /-- The multiplicative unit is the degree-`0` cohomology unit class. -/
  one_eq :
    (1 : H^*(X; R)) =
      singularCohomologyStarLof R X 0 (singularCohomologyOneClass R X)
  /-- Multiplication of homogeneous classes is induced by the cup product. -/
  mul_lof_eq (p q : ℕ) (x : singularCohomologyClasses R X p)
      (y : singularCohomologyClasses R X q) :
    singularCohomologyStarLof R X p x * singularCohomologyStarLof R X q y =
      singularCohomologyStarLof R X (p + q) (singularCohomologyCup R X p q x y)

/-- An ambient `R`-algebra structure on `H^*(X; R)` is canonical when it is built on the
canonical cup-product ring and its scalar map sends `r : R` to the degree-`0`
coefficient class of `r`. -/
class IsCanonicalSingularCohomologyAlgebra
    (R : Type) [CommRing R] (X : TopCat)
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))] : Prop
    extends IsCanonicalSingularCohomologyRing R X where
  /-- The coefficient action is the standard degree-`0` coefficient-class map. -/
  algebraMap_eq (r : R) :
    algebraMap R (H^*(X; R)) r =
      singularCohomologyStarLof R X 0 (singularCohomologyCoefficientClass R X r)

/-- The polynomial generators corresponding to Pontryagin classes on `BO(n)` or `BSO(n)` are
indexed by the positive integers `i` with `i ≤ ⌊n / 2⌋`. -/
abbrev PontryaginClassIndex (n : ℕ) :=
  {i : ℕ // 0 < i ∧ i ≤ n / 2}

/-- In even oriented rank `2m`, the polynomial generators coming from Pontryagin classes below the
top index are indexed by the positive integers `i < m`. -/
abbrev LowerPontryaginClassIndex (m : ℕ+) :=
  {i : ℕ // 0 < i ∧ i < m}

/-- The index type for the polynomial generators of `H^*(BSO(2m); R)`: the lower Pontryagin
classes `p_i` for `0 < i < m` together with the Euler class `e`. -/
abbrev EvenOrientedGeneratorIndex (m : ℕ+) :=
  LowerPontryaginClassIndex m ⊕ PUnit

/-- A lower Pontryagin index in even oriented rank `2m` also determines a Pontryagin index for
the full range `1 ≤ i ≤ m`. -/
abbrev lowerPontryaginClassIndexToPontryaginClassIndex
    {m : ℕ+} (i : LowerPontryaginClassIndex m) :
    PontryaginClassIndex (2 * (m : ℕ)) :=
  ⟨i.1, ⟨i.2.1, by
    have hi : i.1 ≤ (m : ℕ) := Nat.le_of_lt i.2.2
    simpa [Nat.mul_comm] using hi⟩⟩

/-- The top Pontryagin index in even oriented rank `2m` is the index `i = m`. -/
abbrev topPontryaginClassIndex (m : ℕ+) :
    PontryaginClassIndex (2 * (m : ℕ)) :=
  ⟨m, ⟨m.2, by
    simp⟩⟩

/-- The odd oriented rank attached to `m`, namely `2 * m + 1`. -/
abbrev oddOrientedRank (m : ℕ) : ℕ :=
  2 * m + 1

/-- The even oriented rank attached to `m`, namely `2 * m`. -/
abbrev evenOrientedRank (m : ℕ+) : ℕ :=
  2 * (m : ℕ)

/-- A chosen family of universal Pontryagin classes on `X`, one in each degree `4 * i` for
`1 ≤ i ≤ ⌊n / 2⌋`. -/
abbrev UniversalPontryaginFamily
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :=
  ∀ i : PontryaginClassIndex n, singularCohomologyClasses R X (4 * i.1)

/-- A chosen universal Euler class on `X` in degree `2 * m`. -/
abbrev UniversalEulerClass
    (R : Type) [CommRing R] (X : TopCat) (m : ℕ+) :=
  singularCohomologyClasses R X (2 * (m : ℕ))

/-- A chosen bridge from Chapter 20 ordinary integral singular cohomology to the displayed
`R`-coefficient quotient-model singular cohomology of `X`. -/
abbrev integralToSingularCohomologyComparison
    (R : Type) [CommRing R] (X : TopCat) :=
  ∀ q : ℕ, integralSingularCohomology X q → singularCohomologyClasses R X q

/-- The degree-`4 * i` universal Pontryagin class, viewed as a homogeneous element of the total
singular cohomology object `H^*(X; R)`. -/
def pontryaginGenerator
    (R : Type) [CommRing R] (X : TopCat) {n : ℕ}
    (universalPontryagin : UniversalPontryaginFamily R X n) :
    PontryaginClassIndex n → H^*(X; R) :=
  fun i ↦ singularCohomologyStarLof R X (4 * i.1) (universalPontryagin i)

/-- `pontryaginGenerator` inserts the universal class `p_i` into the total cohomology direct sum
in degree `4 * i`. -/
theorem pontryaginGenerator_apply
    (R : Type) [CommRing R] (X : TopCat) {n : ℕ}
    (universalPontryagin : UniversalPontryaginFamily R X n)
    (i : PontryaginClassIndex n) :
    pontryaginGenerator R X universalPontryagin i =
      singularCohomologyStarLof R X (4 * i.1) (universalPontryagin i) :=
  rfl

/-- The universal Euler class, viewed as a homogeneous element of the total singular cohomology
object `H^*(X; R)`. -/
def eulerGenerator
    (R : Type) [CommRing R] (X : TopCat) (m : ℕ+)
    (universalEuler : UniversalEulerClass R X m) :
    H^*(X; R) :=
  singularCohomologyStarLof R X (2 * (m : ℕ)) universalEuler

/-- `eulerGenerator` inserts the universal Euler class into the total cohomology direct sum in
degree `2 * m`. -/
theorem eulerGenerator_apply
    (R : Type) [CommRing R] (X : TopCat)
    (m : ℕ+) (universalEuler : UniversalEulerClass R X m) :
    eulerGenerator R X m universalEuler =
      singularCohomologyStarLof R X (2 * (m : ℕ)) universalEuler :=
  rfl

/-- A family of classes on `BO(n)` is the universal Pontryagin family when it is obtained by
evaluating the Chapter 23 Pontryagin-class owner from Definition 23.7.7 on the universal real
`n`-plane bundle and transporting those integral classes to `R`-coefficient singular cohomology
through a chosen comparison. -/
def IsUniversalBOPontryaginFamily
    (R : Type) [CommRing R] {n : ℕ}
    (BO : Type) [TopologicalSpace BO] (γ : BO → Type)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace n BO γ]
    (universalPontryagin : UniversalPontryaginFamily R (TopCat.of BO) n) : Prop :=
  ∃ comparison : integralToSingularCohomologyComparison R (TopCat.of BO),
    ∃ normalizationData : StandardChernNormalization.{0},
      ∃ c : ChernClassFamily.{0},
        ∃ complexification : RealBundleComplexification.{0, 0, 0} n,
          ∃ hComplexification : RealBundleComplexification.IsNatural complexification,
            IsChernTheory integralSingularCohomologyTheory
              normalizationData.toChernNormalization c ∧
            ∀ i : PontryaginClassIndex n,
              let _ : RealBundleComplexification.IsNatural complexification := hComplexification
              universalPontryagin i =
                comparison (4 * i.1)
                  ((pontryaginClass c complexification i.1)
                    (universalRealPlaneBundleClass n γ))

/-- Unfolding `IsUniversalBOPontryaginFamily` recovers the comparison from the Chapter 23
Pontryagin-class owner on the universal real bundle to the displayed `R`-coefficient universal
family. -/
theorem isUniversalBOPontryaginFamily_iff
    {R : Type} [CommRing R] {n : ℕ}
    {BO : Type} [TopologicalSpace BO] {γ : BO → Type}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace n BO γ]
    {universalPontryagin : UniversalPontryaginFamily R (TopCat.of BO) n} :
    IsUniversalBOPontryaginFamily R BO γ universalPontryagin ↔
      ∃ comparison : integralToSingularCohomologyComparison R (TopCat.of BO),
        ∃ normalizationData : StandardChernNormalization.{0},
          ∃ c : ChernClassFamily.{0},
            ∃ complexification : RealBundleComplexification.{0, 0, 0} n,
              ∃ hComplexification : RealBundleComplexification.IsNatural complexification,
                IsChernTheory integralSingularCohomologyTheory
                  normalizationData.toChernNormalization c ∧
                ∀ i : PontryaginClassIndex n,
                  let _ : RealBundleComplexification.IsNatural complexification :=
                    hComplexification
                  universalPontryagin i =
                    comparison (4 * i.1)
                      ((pontryaginClass c complexification i.1)
                        (universalRealPlaneBundleClass n γ)) :=
  Iff.rfl

/-- Pull back an `R`-coefficient universal Pontryagin family on `BO(n)` along a chosen comparison
map `BSO(n) ⟶ BO(n)`. -/
def pullbackUniversalPontryaginFamily
    (R : Type) [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {BO : Type} [TopologicalSpace BO]
    (comparisonMap : C(BSO[n, ESO], BO))
    (universalBO : UniversalPontryaginFamily R (TopCat.of BO) n) :
    UniversalPontryaginFamily R (TopCat.of BSO[n, ESO]) n :=
  fun i ↦
    singularCohomologyPullback R (TopCat.ofHom comparisonMap) (4 * i.1) (universalBO i)

/-- `pullbackUniversalPontryaginFamily` evaluates degreewise by functoriality of
`H^*(-; R)` along the chosen comparison map `BSO(n) ⟶ BO(n)`. -/
theorem pullbackUniversalPontryaginFamily_apply
    (R : Type) [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {BO : Type} [TopologicalSpace BO]
    (comparisonMap : C(BSO[n, ESO], BO))
    (universalBO : UniversalPontryaginFamily R (TopCat.of BO) n)
    (i : PontryaginClassIndex n) :
    pullbackUniversalPontryaginFamily R comparisonMap universalBO i =
      singularCohomologyPullback R (TopCat.ofHom comparisonMap) (4 * i.1) (universalBO i) :=
  rfl

/-- A family on `BSO(n)` is the pullback of a Chapter 23 universal Pontryagin family on a real
rank-`n` classifying space `BO(n)` when it arises along a chosen comparison map `BSO(n) ⟶ BO(n)`.
The `BO(n)` family itself is required to come from the actual Pontryagin-class owner of
Definition 23.7.7. -/
def IsPullbackOfUniversalBOPontryaginFamily
    (R : Type) [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    (universalPontryagin : UniversalPontryaginFamily R (TopCat.of BSO[n, ESO]) n) :
    Prop :=
  ∃ (BO : Type) (_ : TopologicalSpace BO) (γ : BO → Type 0),
    ∃ (_ : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ))
      (_ : ∀ b, TopologicalSpace (γ b))
      (_ : FiberBundle (Fin n → ℝ) γ)
      (_ : ∀ b, AddCommGroup (γ b))
      (_ : ∀ b, Module ℝ (γ b))
      (_ : RealPlaneBundleClassifyingSpace.{0, 0, 0} n BO γ)
      (universalBO : UniversalPontryaginFamily R (TopCat.of BO) n)
      (comparisonMap : C(BSO[n, ESO], BO)),
      IsUniversalBOPontryaginFamily R BO γ universalBO ∧
        universalPontryagin =
          pullbackUniversalPontryaginFamily R comparisonMap universalBO

/-- Unfolding `IsPullbackOfUniversalBOPontryaginFamily` recovers a Chapter 23 classifying space
`BO(n)`, its universal real bundle, its universal Pontryagin family, and the comparison map
`BSO(n) ⟶ BO(n)`. -/
theorem isPullbackOfUniversalBOPontryaginFamily_iff
    {R : Type} [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {universalPontryagin : UniversalPontryaginFamily R (TopCat.of BSO[n, ESO]) n} :
    IsPullbackOfUniversalBOPontryaginFamily R universalPontryagin ↔
      ∃ (BO : Type) (_ : TopologicalSpace BO) (γ : BO → Type 0),
        ∃ (_ : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ))
          (_ : ∀ b, TopologicalSpace (γ b))
          (_ : FiberBundle (Fin n → ℝ) γ)
          (_ : ∀ b, AddCommGroup (γ b))
          (_ : ∀ b, Module ℝ (γ b))
          (_ : RealPlaneBundleClassifyingSpace.{0, 0, 0} n BO γ)
          (universalBO : UniversalPontryaginFamily R (TopCat.of BO) n)
          (comparisonMap : C(BSO[n, ESO], BO)),
          IsUniversalBOPontryaginFamily R BO γ universalBO ∧
            universalPontryagin =
              pullbackUniversalPontryaginFamily R comparisonMap universalBO :=
  Iff.rfl

/-- A family on the quotient-model space `BSO(n)` is the universal Pontryagin family when it is
the pullback of a Chapter 23 universal Pontryagin family on some real rank-`n` classifying space
`BO(n)`. This keeps the `BSO(n)` classes tied to the actual Pontryagin owner of
Definition 23.7.7 through a thin comparison-map bridge. -/
def IsUniversalBSOPontryaginFamily
    (R : Type) [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    (universalPontryagin :
      UniversalPontryaginFamily R (TopCat.of BSO[n, ESO]) n) : Prop :=
  IsPullbackOfUniversalBOPontryaginFamily R universalPontryagin

/-- Unfolding `IsUniversalBSOPontryaginFamily` recovers the Chapter 23 `BO(n)` bridge carrying
the actual universal Pontryagin classes. -/
theorem isUniversalBSOPontryaginFamily_iff
    {R : Type} [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {universalPontryagin : UniversalPontryaginFamily R (TopCat.of BSO[n, ESO]) n} :
    IsUniversalBSOPontryaginFamily R universalPontryagin ↔
      ∃ (BO : Type) (_ : TopologicalSpace BO) (γ : BO → Type 0),
        ∃ (_ : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ))
          (_ : ∀ b, TopologicalSpace (γ b))
          (_ : FiberBundle (Fin n → ℝ) γ)
          (_ : ∀ b, AddCommGroup (γ b))
          (_ : ∀ b, Module ℝ (γ b))
          (_ : RealPlaneBundleClassifyingSpace.{0, 0, 0} n BO γ)
          (universalBO : UniversalPontryaginFamily R (TopCat.of BO) n)
          (comparisonMap : C(BSO[n, ESO], BO)),
          IsUniversalBOPontryaginFamily R BO γ universalBO ∧
            universalPontryagin =
              pullbackUniversalPontryaginFamily R comparisonMap universalBO :=
  Iff.rfl

/-- A universal `BSO(n)` Pontryagin family comes from a Chapter 23 `BO(n)` pullback bridge. -/
theorem isUniversalBSOPontryaginFamily_toPullback
    {R : Type} [CommRing R] {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {universalPontryagin : UniversalPontryaginFamily R (TopCat.of BSO[n, ESO]) n}
    (hUniversalPontryagin : IsUniversalBSOPontryaginFamily R universalPontryagin) :
    IsPullbackOfUniversalBOPontryaginFamily R universalPontryagin :=
  hUniversalPontryagin

/-- The Pontryagin and Euler classes on `BSO(2m)` are the universal classes when they are
given by the Chapter 23 owners: the Pontryagin classes are the pullbacks of universal Pontryagin
classes on a real rank-`2m` classifying space `BO(2m)`, and the Euler class is the image of the
universal Euler class from Proposition 23.7.10 under a chosen comparison to `R`-coefficient
singular cohomology. -/
def IsUniversalBSOPontryaginEulerFamily
    (R : Type) [CommRing R] (m : ℕ+)
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(evenOrientedRank m)) ESO]
    [ContinuousSMul (SO(evenOrientedRank m)) ESO]
    (universalPontryagin :
      UniversalPontryaginFamily
        R (TopCat.of BSO[evenOrientedRank m, ESO]) (evenOrientedRank m))
    (universalEuler :
      UniversalEulerClass R (TopCat.of BSO[evenOrientedRank m, ESO]) m) : Prop :=
  IsUniversalBSOPontryaginFamily R universalPontryagin ∧
    ∃ comparison :
        integralToSingularCohomologyComparison
          R (TopCat.of BSO[evenOrientedRank m, ESO]),
      ∃ (EU : Type) (_ : TopologicalSpace EU)
        (_ : MulAction (U m) EU) (_ : ContinuousSMul (U m) EU)
        (γBU : BU[m, EU] → Type),
        ∃
          (_ : TopologicalSpace (Bundle.TotalSpace (Fin m → ℂ) γBU))
          (_ : ∀ b, TopologicalSpace (γBU b))
          (_ : FiberBundle (Fin m → ℂ) γBU)
          (_ : ∀ b, AddCommGroup (γBU b))
          (_ : ∀ b, Module ℂ (γBU b))
          (_ : VectorBundle ℂ (Fin m → ℂ) γBU)
          (_ : ContractibleSpace EU)
          (_ : IsPrincipalBundleMap (U m) (Quotient.mk'' : EU → BU[m, EU]))
          (_ : ComplexPlaneBundleQuotientModel m EU γBU)
          (restrictionMap :
            TopCat.of BSO[evenOrientedRank m, ESO] ⟶ TopCat.of BU[m, EU])
          (universalChern : UniversalChernClassFamily m EU),
          IsUniversalChernClassFamily γBU universalChern ∧
            universalEuler =
              comparison (2 * (m : ℕ))
                (universalEulerClass restrictionMap universalChern)

/-- Unfolding `IsUniversalBSOPontryaginEulerFamily` recovers the comparison from the chosen
universal Euler class of Proposition 23.7.10 and the `BO(2m)` Pontryagin pullback bridge to the
displayed `R`-coefficient universal classes. -/
theorem isUniversalBSOPontryaginEulerFamily_iff
    {R : Type} [CommRing R] {m : ℕ+}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(evenOrientedRank m)) ESO]
    [ContinuousSMul (SO(evenOrientedRank m)) ESO]
    {universalPontryagin :
      UniversalPontryaginFamily
        R (TopCat.of BSO[evenOrientedRank m, ESO]) (evenOrientedRank m)}
    {universalEuler :
      UniversalEulerClass R (TopCat.of BSO[evenOrientedRank m, ESO]) m} :
    IsUniversalBSOPontryaginEulerFamily
        R m universalPontryagin universalEuler ↔
      IsUniversalBSOPontryaginFamily R universalPontryagin ∧
        ∃ comparison :
            integralToSingularCohomologyComparison
              R (TopCat.of BSO[evenOrientedRank m, ESO]),
          ∃ (EU : Type) (_ : TopologicalSpace EU)
            (_ : MulAction (U m) EU) (_ : ContinuousSMul (U m) EU)
            (γBU : BU[m, EU] → Type),
            ∃
              (_ : TopologicalSpace (Bundle.TotalSpace (Fin m → ℂ) γBU))
              (_ : ∀ b, TopologicalSpace (γBU b))
              (_ : FiberBundle (Fin m → ℂ) γBU)
              (_ : ∀ b, AddCommGroup (γBU b))
              (_ : ∀ b, Module ℂ (γBU b))
              (_ : VectorBundle ℂ (Fin m → ℂ) γBU)
              (_ : ContractibleSpace EU)
              (_ : IsPrincipalBundleMap (U m) (Quotient.mk'' : EU → BU[m, EU]))
              (_ : ComplexPlaneBundleQuotientModel m EU γBU)
              (restrictionMap :
                TopCat.of BSO[evenOrientedRank m, ESO] ⟶ TopCat.of BU[m, EU])
              (universalChern : UniversalChernClassFamily m EU),
              IsUniversalChernClassFamily γBU universalChern ∧
                universalEuler =
                  comparison (2 * (m : ℕ))
                    (universalEulerClass restrictionMap universalChern) :=
  Iff.rfl

/-- A universal even-oriented Pontryagin-Euler family carries the universal Pontryagin family. -/
theorem isUniversalBSOPontryaginEulerFamily_toPontryagin
    {R : Type} [CommRing R] {m : ℕ+}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(evenOrientedRank m)) ESO]
    [ContinuousSMul (SO(evenOrientedRank m)) ESO]
    {universalPontryagin :
      UniversalPontryaginFamily
        R (TopCat.of BSO[evenOrientedRank m, ESO]) (evenOrientedRank m)}
    {universalEuler :
      UniversalEulerClass R (TopCat.of BSO[evenOrientedRank m, ESO]) m}
    (hUniversalPontryaginEuler :
      IsUniversalBSOPontryaginEulerFamily R m universalPontryagin universalEuler) :
    IsUniversalBSOPontryaginFamily R universalPontryagin :=
  hUniversalPontryaginEuler.1

/-- A universal even-oriented Pontryagin-Euler family carries the universal Euler comparison
data from Proposition 23.7.10. -/
theorem isUniversalBSOPontryaginEulerFamily_toEuler
    {R : Type} [CommRing R] {m : ℕ+}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(evenOrientedRank m)) ESO]
    [ContinuousSMul (SO(evenOrientedRank m)) ESO]
    {universalPontryagin :
      UniversalPontryaginFamily
        R (TopCat.of BSO[evenOrientedRank m, ESO]) (evenOrientedRank m)}
    {universalEuler :
      UniversalEulerClass R (TopCat.of BSO[evenOrientedRank m, ESO]) m}
    (hUniversalPontryaginEuler :
      IsUniversalBSOPontryaginEulerFamily R m universalPontryagin universalEuler) :
    ∃ comparison :
        integralToSingularCohomologyComparison
          R (TopCat.of BSO[evenOrientedRank m, ESO]),
      ∃ (EU : Type) (_ : TopologicalSpace EU)
        (_ : MulAction (U m) EU) (_ : ContinuousSMul (U m) EU)
        (γBU : BU[m, EU] → Type),
        ∃
          (_ : TopologicalSpace (Bundle.TotalSpace (Fin m → ℂ) γBU))
          (_ : ∀ b, TopologicalSpace (γBU b))
          (_ : FiberBundle (Fin m → ℂ) γBU)
          (_ : ∀ b, AddCommGroup (γBU b))
          (_ : ∀ b, Module ℂ (γBU b))
          (_ : VectorBundle ℂ (Fin m → ℂ) γBU)
          (_ : ContractibleSpace EU)
          (_ : IsPrincipalBundleMap (U m) (Quotient.mk'' : EU → BU[m, EU]))
          (_ : ComplexPlaneBundleQuotientModel m EU γBU)
          (restrictionMap :
            TopCat.of BSO[evenOrientedRank m, ESO] ⟶ TopCat.of BU[m, EU])
          (universalChern : UniversalChernClassFamily m EU),
          IsUniversalChernClassFamily γBU universalChern ∧
            universalEuler =
              comparison (2 * (m : ℕ))
                (universalEulerClass restrictionMap universalChern) :=
  hUniversalPontryaginEuler.2

/-- A polynomial `R`-algebra equivalence from
`MvPolynomial (PontryaginClassIndex n) R` to the fixed total singular cohomology algebra
`H^*(X; R)` equipped with its chosen canonical structure. -/
abbrev pontryaginPolynomialEquiv
    (R : Type) [CommRing R] (n : ℕ) (X : TopCat)
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X] :=
  MvPolynomial (PontryaginClassIndex n) R ≃ₐ[R] H^*(X; R)

/-- A polynomial presentation of the fixed total singular cohomology ring of `X` by the
universal Pontryagin classes: each variable `X i` maps to the corresponding homogeneous generator
in degree `4 * i`. -/
def IsPontryaginPolynomialPresentationOn
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ)
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    (universalPontryagin : UniversalPontryaginFamily R X n)
    (algEquiv : pontryaginPolynomialEquiv R n X) : Prop :=
  ∀ i : PontryaginClassIndex n,
    algEquiv (MvPolynomial.X i) =
      pontryaginGenerator R X universalPontryagin i

/-- Unfolding `IsPontryaginPolynomialPresentationOn` gives exactly the `MvPolynomial` variable
formulas for the universal Pontryagin generators. -/
theorem isPontryaginPolynomialPresentationOn_iff
    {R : Type} [CommRing R] {X : TopCat} {n : ℕ}
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    {universalPontryagin : UniversalPontryaginFamily R X n}
    {algEquiv : pontryaginPolynomialEquiv R n X} :
    IsPontryaginPolynomialPresentationOn
        R X n universalPontryagin algEquiv ↔
      (∀ i : PontryaginClassIndex n,
        algEquiv (MvPolynomial.X i) =
          pontryaginGenerator R X universalPontryagin i) :=
  Iff.rfl

/-- In a Pontryagin polynomial presentation, each polynomial variable `X i` maps to the
corresponding universal Pontryagin generator in the total cohomology ring. -/
theorem isPontryaginPolynomialPresentationOn_X
    {R : Type} [CommRing R] {X : TopCat} {n : ℕ}
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    {universalPontryagin : UniversalPontryaginFamily R X n}
    {algEquiv : pontryaginPolynomialEquiv R n X}
    (h : IsPontryaginPolynomialPresentationOn
      R X n universalPontryagin algEquiv)
    (i : PontryaginClassIndex n) :
    algEquiv (MvPolynomial.X i) =
      pontryaginGenerator R X universalPontryagin i :=
  h i

/-- A polynomial `R`-algebra equivalence from
`MvPolynomial (EvenOrientedGeneratorIndex m) R` to the fixed total singular cohomology ring
`H^*(X; R)` equipped with its chosen canonical structure. -/
abbrev evenOrientedPontryaginEulerPolynomialEquiv
    (R : Type) [CommRing R] (m : ℕ+) (X : TopCat)
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X] :=
  MvPolynomial (EvenOrientedGeneratorIndex m) R ≃ₐ[R] H^*(X; R)

/-- A polynomial presentation of the fixed total singular cohomology ring of `X = BSO(2m)`
by the lower Pontryagin classes and the Euler class: the variables map to the corresponding
homogeneous universal generators, and the top Pontryagin generator satisfies `p_m = e * e`. -/
def IsEvenOrientedPontryaginEulerPresentationOn
    (R : Type) [CommRing R] (X : TopCat) (m : ℕ+)
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    (universalPontryagin : UniversalPontryaginFamily R X (2 * (m : ℕ)))
    (universalEuler : UniversalEulerClass R X m)
    (algEquiv : evenOrientedPontryaginEulerPolynomialEquiv R m X) : Prop :=
  (∀ i : LowerPontryaginClassIndex m,
      algEquiv (MvPolynomial.X (Sum.inl i)) =
        pontryaginGenerator R X universalPontryagin
          (lowerPontryaginClassIndexToPontryaginClassIndex i)) ∧
    algEquiv (MvPolynomial.X (Sum.inr PUnit.unit)) =
      eulerGenerator R X m universalEuler ∧
    pontryaginGenerator R X universalPontryagin (topPontryaginClassIndex m) =
      eulerGenerator R X m universalEuler * eulerGenerator R X m universalEuler

/-- Unfolding `IsEvenOrientedPontryaginEulerPresentationOn` gives the universal-class
generator formulas and the relation `p_m = e * e` in the fixed total cohomology ring. -/
theorem isEvenOrientedPontryaginEulerPresentationOn_iff
    {R : Type} [CommRing R] {X : TopCat} {m : ℕ+}
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    {universalPontryagin : UniversalPontryaginFamily R X (2 * (m : ℕ))}
    {universalEuler : UniversalEulerClass R X m}
    {algEquiv : evenOrientedPontryaginEulerPolynomialEquiv R m X} :
    IsEvenOrientedPontryaginEulerPresentationOn
        R X m universalPontryagin universalEuler algEquiv ↔
      (∀ i : LowerPontryaginClassIndex m,
          algEquiv (MvPolynomial.X (Sum.inl i)) =
            pontryaginGenerator R X universalPontryagin
              (lowerPontryaginClassIndexToPontryaginClassIndex i)) ∧
        algEquiv (MvPolynomial.X (Sum.inr PUnit.unit)) =
          eulerGenerator R X m universalEuler ∧
        pontryaginGenerator R X universalPontryagin (topPontryaginClassIndex m) =
          eulerGenerator R X m universalEuler * eulerGenerator R X m universalEuler :=
  Iff.rfl

/-- In an even oriented Pontryagin-Euler presentation, the variables indexed by lower Pontryagin
classes map to the corresponding universal generators. -/
theorem isEvenOrientedPontryaginEulerPresentationOn_lower_X
    {R : Type} [CommRing R] {X : TopCat} {m : ℕ+}
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    {universalPontryagin : UniversalPontryaginFamily R X (2 * (m : ℕ))}
    {universalEuler : UniversalEulerClass R X m}
    {algEquiv : evenOrientedPontryaginEulerPolynomialEquiv R m X}
    (h : IsEvenOrientedPontryaginEulerPresentationOn
      R X m universalPontryagin universalEuler algEquiv)
    (i : LowerPontryaginClassIndex m) :
    algEquiv (MvPolynomial.X (Sum.inl i)) =
      pontryaginGenerator R X universalPontryagin
        (lowerPontryaginClassIndexToPontryaginClassIndex i) :=
  h.1 i

/-- In an even oriented Pontryagin-Euler presentation, the Euler variable maps to the chosen
Euler generator. -/
theorem isEvenOrientedPontryaginEulerPresentationOn_euler_X
    {R : Type} [CommRing R] {X : TopCat} {m : ℕ+}
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    {universalPontryagin : UniversalPontryaginFamily R X (2 * (m : ℕ))}
    {universalEuler : UniversalEulerClass R X m}
    {algEquiv : evenOrientedPontryaginEulerPolynomialEquiv R m X}
    (h : IsEvenOrientedPontryaginEulerPresentationOn
      R X m universalPontryagin universalEuler algEquiv) :
    algEquiv (MvPolynomial.X (Sum.inr PUnit.unit)) =
      eulerGenerator R X m universalEuler :=
  h.2.1

/-- In an even oriented Pontryagin-Euler presentation, the top Pontryagin class satisfies the
Euler relation `p_m = e * e`. -/
theorem isEvenOrientedPontryaginEulerPresentationOn_top
    {R : Type} [CommRing R] {X : TopCat} {m : ℕ+}
    [CommRing (H^*(X; R))] [Algebra R (H^*(X; R))]
    [IsCanonicalSingularCohomologyAlgebra R X]
    {universalPontryagin : UniversalPontryaginFamily R X (2 * (m : ℕ))}
    {universalEuler : UniversalEulerClass R X m}
    {algEquiv : evenOrientedPontryaginEulerPolynomialEquiv R m X}
    (h : IsEvenOrientedPontryaginEulerPresentationOn
      R X m universalPontryagin universalEuler algEquiv) :
    pontryaginGenerator R X universalPontryagin (topPontryaginClassIndex m) =
      eulerGenerator R X m universalEuler * eulerGenerator R X m universalEuler :=
  h.2.2
