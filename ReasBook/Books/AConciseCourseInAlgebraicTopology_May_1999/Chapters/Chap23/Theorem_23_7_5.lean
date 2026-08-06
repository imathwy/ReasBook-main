import Mathlib.Topology.Homotopy.Contractible
import Mathlib.LinearAlgebra.UnitaryGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_8_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_8_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_7_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_2

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` did not surface a ready-made `BSO(n)` mod-`2`
-- cohomology-ring presentation in the imported environment. Local Chapter 23 precedent already
-- packages `BSO(n)` itself through `orientedRealPlaneBundleClassifyingSpace` / `BSO[...]` in
-- `Theorem_23_7_2`, and packages the actual universal Stiefel-Whitney classes on `BO(n)` through
-- `UniversalStiefelWhitneyFamily` / `IsUniversalBOStiefelWhitneyFamily`, while
-- `Theorem_22_5_6` packages polynomial `ZMod 2`-algebra presentations on the canonical total
-- cohomology ring. This file uses that Chapter 23 owner directly and records the `BSO(n)` classes
-- on the chosen quotient-model classifying space `BSO[n, ESO]` by combining the actual universal
-- oriented bundle `hBSO` with the canonical `BO(n)` universal-family owner from
-- `Theorem_23_3_2`.

/-- The generator indices for the polynomial presentation of `H^*(BSO(n); ZMod 2)`: precisely
the integers `i` with `2 ≤ i ≤ n`, corresponding to the universal Stiefel-Whitney classes
`w_i`. -/
abbrev orientedStiefelWhitneyClassIndex (n : ℕ) :=
  {i : ℕ // 2 ≤ i ∧ i ≤ n}

/-- An index in `orientedStiefelWhitneyClassIndex n` is exactly a degree `i` satisfying
`2 ≤ i ≤ n`. -/
theorem orientedStiefelWhitneyClassIndex_spec
    {n : ℕ} (i : orientedStiefelWhitneyClassIndex n) :
    2 ≤ i.1 ∧ i.1 ≤ n :=
  i.2

/-- A family of degree-`i` Stiefel-Whitney classes on `X`, indexed by the source-facing
generator range `2 ≤ i ≤ n`. -/
abbrev OrientedStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (n : ℕ) (X : TopCat) :=
  ∀ i : orientedStiefelWhitneyClassIndex n, modTwoCohomologyGroup H2 i.1 X

/-- The degree-`i` universal Stiefel-Whitney class, viewed as a homogeneous element of the
canonical total mod-`2` cohomology ring `H^*(X; ZMod 2)`. -/
def orientedStiefelWhitneyGenerator
    (H2 : ModTwoCohomologyTheory) (X : TopCat) {n : ℕ}
    (universalW : OrientedStiefelWhitneyFamily H2 n X) :
    orientedStiefelWhitneyClassIndex n → modTwoCohomologyStar H2 X :=
  fun i ↦
    DirectSum.lof ℤ ℕ (fun q ↦ modTwoCohomologyGroup H2 q X) i.1 (universalW i)

/-- `orientedStiefelWhitneyGenerator` inserts the degree-`i` class `w_i` into the total
cohomology direct sum in degree `i`. -/
theorem orientedStiefelWhitneyGenerator_apply
    (H2 : ModTwoCohomologyTheory) (X : TopCat) {n : ℕ}
    (universalW : OrientedStiefelWhitneyFamily H2 n X)
    (i : orientedStiefelWhitneyClassIndex n) :
    orientedStiefelWhitneyGenerator H2 X universalW i =
      DirectSum.lof ℤ ℕ (fun q ↦ modTwoCohomologyGroup H2 q X) i.1 (universalW i) :=
  rfl

/-- Restrict a universal Stiefel-Whitney family on a real rank-`n` classifying space `BO(n)` to
the generator range `2 ≤ i ≤ n` after pulling back along a chosen map
`BSO(n) ⟶ BO(n)`. -/
def pullbackUniversalStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {BO : Type} [TopologicalSpace BO]
    (comparisonMap : C(BSO[n, ESO], BO))
    (universalBO : UniversalStiefelWhitneyFamily H2 BO) :
    OrientedStiefelWhitneyFamily H2 n (TopCat.of BSO[n, ESO]) :=
  fun i ↦ (H2.cohomology i.1).map (TopCat.ofHom comparisonMap).op (universalBO i.1)

/-- A family of universal Stiefel-Whitney classes on `BSO(n)`, indexed by the generator degrees
`2 ≤ i ≤ n`. -/
abbrev UniversalBSOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (n : ℕ) (ESO : Type)
    [TopologicalSpace ESO] [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO] :=
  OrientedStiefelWhitneyFamily H2 n (TopCat.of BSO[n, ESO])

/-- A family on `BSO(n)` is the pullback of a Chapter 23 universal Stiefel-Whitney family on a
real rank-`n` classifying space `BO(n)` with universal bundle `γ` when it arises from a
comparison map
`BSO(n) ⟶ BO(n)`. -/
def IsPullbackOfUniversalBOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ} {ESO : Type}
    [TopologicalSpace ESO] [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    (universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO) : Prop :=
  ∃ (BO : Type) (_ : TopologicalSpace BO) (γ : BO → Type 0),
    ∃ (_ : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ))
      (_ : ∀ b, TopologicalSpace (γ b))
      (_ : FiberBundle (Fin n → ℝ) γ)
      (_ : ∀ b, AddCommGroup (γ b))
      (_ : ∀ b, Module ℝ (γ b))
      (_ : RealPlaneBundleClassifyingSpace.{0, 0, 0} n BO γ)
      (universalBO : UniversalStiefelWhitneyFamily H2 BO)
      (comparisonMap : C(BSO[n, ESO], BO)),
      IsUniversalBOStiefelWhitneyFamily
          H2 normalizationData.toStiefelWhitneyNormalization n BO γ universalBO ∧
        universalW = pullbackUniversalStiefelWhitneyFamily H2 comparisonMap universalBO

/-- `pullbackUniversalStiefelWhitneyFamily` evaluates degreewise by functoriality of
`H^*(-; ZMod 2)` along the chosen comparison map `BSO(n) ⟶ BO(n)`. -/
theorem pullbackUniversalStiefelWhitneyFamily_apply
    (H2 : ModTwoCohomologyTheory) {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    {BO : Type} [TopologicalSpace BO]
    (comparisonMap : C(BSO[n, ESO], BO))
    (universalBO : UniversalStiefelWhitneyFamily H2 BO)
    (i : orientedStiefelWhitneyClassIndex n) :
    pullbackUniversalStiefelWhitneyFamily H2 comparisonMap universalBO i =
      (H2.cohomology i.1).map (TopCat.ofHom comparisonMap).op (universalBO i.1) :=
  rfl

/-- A family on the chosen quotient-model classifying space `BSO(n)` is universal, relative to
the chosen universal oriented bundle `hBSO`, when it is realized on that actual universal
oriented bundle by oriented characteristic-class owners and also identified with the pullback of a
Chapter 23 universal family on a real rank-`n` classifying space `BO(n)` using the fixed standard
Stiefel-Whitney normalization data. This keeps the source-facing `BSO(n)` classes tied to `hBSO`
while reusing the canonical `BO(n)` owner from `Theorem_23_3_2` through a thin bridge. -/
def IsUniversalBSOStiefelWhitneyFamily
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    (universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO) : Prop :=
  ∃ orientedW :
      ∀ i : orientedStiefelWhitneyClassIndex n,
        OrientedCharacteristicClass n i.1 H2.cohomology,
    (∀ i : orientedStiefelWhitneyClassIndex n,
      universalW i =
        orientedCharacteristicClassEvalOnUniversalBundle hBSO (orientedW i)) ∧
      IsPullbackOfUniversalBOStiefelWhitneyFamily H2 normalizationData universalW

/-- Unfolding `IsPullbackOfUniversalBOStiefelWhitneyFamily` recovers a Chapter 23 classifying
space `BO(n)`, its universal bundle `γ`, its universal family, and the comparison map
`BSO(n) ⟶ BO(n)`, all stated directly through the canonical
`RealPlaneBundleClassifyingSpace n BO γ` owner. -/
theorem isPullbackOfUniversalBOStiefelWhitneyFamily_iff
    {H2 : ModTwoCohomologyTheory}
    {normalizationData : StandardStiefelWhitneyNormalization H2} {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    {universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO} :
    IsPullbackOfUniversalBOStiefelWhitneyFamily H2 normalizationData universalW ↔
      ∃ (BO : Type) (_ : TopologicalSpace BO) (γ : BO → Type 0),
        ∃ (_ : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ))
          (_ : ∀ b, TopologicalSpace (γ b))
          (_ : FiberBundle (Fin n → ℝ) γ)
          (_ : ∀ b, AddCommGroup (γ b))
          (_ : ∀ b, Module ℝ (γ b))
          (_ : RealPlaneBundleClassifyingSpace.{0, 0, 0} n BO γ)
          (universalBO : UniversalStiefelWhitneyFamily H2 BO)
          (comparisonMap : C(BSO[n, ESO], BO)),
          IsUniversalBOStiefelWhitneyFamily
              H2 normalizationData.toStiefelWhitneyNormalization n BO γ universalBO ∧
            universalW = pullbackUniversalStiefelWhitneyFamily H2 comparisonMap universalBO :=
  Iff.rfl

/-- Unfolding `IsUniversalBSOStiefelWhitneyFamily` recovers the chosen `BO(n)` bridge and the
realization of the displayed classes on the actual universal oriented bundle `hBSO`. -/
theorem isUniversalBSOStiefelWhitneyFamily_iff
    {H2 : ModTwoCohomologyTheory}
    {normalizationData : StandardStiefelWhitneyNormalization H2} {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    {hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO])}
    {universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO} :
    IsUniversalBSOStiefelWhitneyFamily H2 normalizationData hBSO universalW ↔
      ∃ orientedW :
          ∀ i : orientedStiefelWhitneyClassIndex n,
            OrientedCharacteristicClass n i.1 H2.cohomology,
        (∀ i : orientedStiefelWhitneyClassIndex n,
          universalW i =
            orientedCharacteristicClassEvalOnUniversalBundle hBSO (orientedW i)) ∧
          IsPullbackOfUniversalBOStiefelWhitneyFamily H2 normalizationData universalW :=
  Iff.rfl

/-- A universal `BSO(n)` Stiefel-Whitney family is realized by oriented characteristic classes on
the actual universal oriented bundle determined by `hBSO`. -/
theorem isUniversalBSOStiefelWhitneyFamily_eq_evalOnUniversalBundle
    {H2 : ModTwoCohomologyTheory}
    {normalizationData : StandardStiefelWhitneyNormalization H2} {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    {hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO])}
    {universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO}
    (hUniversalW : IsUniversalBSOStiefelWhitneyFamily H2 normalizationData hBSO universalW) :
    ∃ orientedW :
        ∀ i : orientedStiefelWhitneyClassIndex n,
          OrientedCharacteristicClass n i.1 H2.cohomology,
      ∀ i : orientedStiefelWhitneyClassIndex n,
        universalW i =
          orientedCharacteristicClassEvalOnUniversalBundle hBSO (orientedW i) := by
  rcases hUniversalW with ⟨orientedW, hOriented, -⟩
  exact ⟨orientedW, hOriented⟩

/-- A universal `BSO(n)` Stiefel-Whitney family comes from pulling back a Chapter 23 universal
family on a Chapter 23 classifying space `BO(n)` along a comparison map `BSO(n) ⟶ BO(n)`. -/
theorem isUniversalBSOStiefelWhitneyFamily_eq_pullback
    {H2 : ModTwoCohomologyTheory}
    {normalizationData : StandardStiefelWhitneyNormalization H2} {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    {hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO])}
    {universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO}
    (hUniversalW : IsUniversalBSOStiefelWhitneyFamily H2 normalizationData hBSO universalW) :
    IsPullbackOfUniversalBOStiefelWhitneyFamily H2 normalizationData universalW := by
  rcases hUniversalW with ⟨-, -, hPullback⟩
  exact hPullback

/-- Pulling back a universal Stiefel-Whitney family on `BO(n)` along a comparison map
`BSO(n) ⟶ BO(n)` produces a universal Stiefel-Whitney family on `BSO(n)` once one also records
that the resulting classes are the evaluations of oriented characteristic classes on the actual
universal oriented bundle `hBSO`. -/
theorem isUniversalBSOStiefelWhitneyFamily_of_pullback
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO] [ContinuousSMul (SO(n)) ESO]
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    (BO : Type) [TopologicalSpace BO] (γ : BO → Type 0)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)]
    [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)]
    [∀ b, Module ℝ (γ b)]
    [RealPlaneBundleClassifyingSpace.{0, 0, 0} n BO γ]
    (comparisonMap : C(BSO[n, ESO], BO))
    (universalBO : UniversalStiefelWhitneyFamily H2 BO)
    (orientedW :
      ∀ i : orientedStiefelWhitneyClassIndex n,
        OrientedCharacteristicClass n i.1 H2.cohomology)
    (hOriented :
      ∀ i : orientedStiefelWhitneyClassIndex n,
        pullbackUniversalStiefelWhitneyFamily H2 comparisonMap universalBO i =
          orientedCharacteristicClassEvalOnUniversalBundle hBSO (orientedW i))
    (hUniversalBO :
      IsUniversalBOStiefelWhitneyFamily
        H2 normalizationData.toStiefelWhitneyNormalization n BO γ universalBO) :
    IsUniversalBSOStiefelWhitneyFamily H2 normalizationData hBSO
      (pullbackUniversalStiefelWhitneyFamily H2 comparisonMap universalBO) := by
  refine ⟨orientedW, hOriented, ?_⟩
  exact
    ⟨BO, inferInstance, γ, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, universalBO, comparisonMap, hUniversalBO, rfl⟩

/-- A polynomial presentation of the canonical total mod-`2` cohomology ring of `X` by the
universal oriented Stiefel-Whitney classes: the chosen generators are the homogeneous classes
`w_i` for `2 ≤ i ≤ n`, viewed in the total direct sum. -/
abbrev orientedStiefelWhitneyPolynomialEquiv
    (H2 : ModTwoCohomologyTheory) (n : ℕ) (X : TopCat)
    (A : CanonicalModTwoCohomologyAlgebra H2 X) :=
  let _ : CommRing (modTwoCohomologyStar H2 X) := A.toCommRing
  let _ : Algebra (ZMod 2) (modTwoCohomologyStar H2 X) := A.toAlgebra
  MvPolynomial (orientedStiefelWhitneyClassIndex n) (ZMod 2) ≃ₐ[ZMod 2]
    modTwoCohomologyStar H2 X

/-- A polynomial presentation of the canonical total mod-`2` cohomology ring of `X` by the
universal oriented Stiefel-Whitney classes sends the variable `X_i` to the homogeneous generator
represented by the universal class `w_i`. -/
def IsBSOStiefelWhitneyPolynomialPresentationOn
    (H2 : ModTwoCohomologyTheory) (n : ℕ) (X : TopCat)
    (A : CanonicalModTwoCohomologyAlgebra H2 X)
    (universalW : OrientedStiefelWhitneyFamily H2 n X)
    (algEquiv : orientedStiefelWhitneyPolynomialEquiv H2 n X A) : Prop :=
  ∀ i : orientedStiefelWhitneyClassIndex n,
    algEquiv (MvPolynomial.X i) =
      orientedStiefelWhitneyGenerator H2 X universalW i

/-- Unfolding `IsBSOStiefelWhitneyPolynomialPresentationOn` gives the direct-sum realization of
the `MvPolynomial` variable formulas. -/
theorem isBSOStiefelWhitneyPolynomialPresentationOn_iff
    {H2 : ModTwoCohomologyTheory} {n : ℕ} {X : TopCat}
    {A : CanonicalModTwoCohomologyAlgebra H2 X}
    {universalW : OrientedStiefelWhitneyFamily H2 n X}
    {algEquiv : orientedStiefelWhitneyPolynomialEquiv H2 n X A} :
    IsBSOStiefelWhitneyPolynomialPresentationOn
        H2 n X A universalW algEquiv ↔
      (∀ i : orientedStiefelWhitneyClassIndex n,
        algEquiv (MvPolynomial.X i) =
          orientedStiefelWhitneyGenerator H2 X universalW i) :=
  Iff.rfl

/-- In a Stiefel-Whitney polynomial presentation, each polynomial variable `X_i` maps to the
corresponding homogeneous generator coming from the universal class `w_i`. -/
theorem isBSOStiefelWhitneyPolynomialPresentationOn_X
    {H2 : ModTwoCohomologyTheory} {n : ℕ} {X : TopCat}
    {A : CanonicalModTwoCohomologyAlgebra H2 X}
    {universalW : OrientedStiefelWhitneyFamily H2 n X}
    {algEquiv : orientedStiefelWhitneyPolynomialEquiv H2 n X A}
    (h : IsBSOStiefelWhitneyPolynomialPresentationOn H2 n X A universalW algEquiv)
    (i : orientedStiefelWhitneyClassIndex n) :
    algEquiv (MvPolynomial.X i) =
      orientedStiefelWhitneyGenerator H2 X universalW i :=
  h i

/-- For a fixed universal Stiefel-Whitney family on `BSO(n)`, the canonical total mod-`2`
cohomology algebra of `BSO(n)` admits a polynomial presentation on the classes `w_i` for
`2 ≤ i ≤ n`. -/
theorem bsoStiefelWhitneyPolynomialPresentation
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of BSO[n, ESO]))
    (universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO)
    (hUniversalW : IsUniversalBSOStiefelWhitneyFamily H2 normalizationData hBSO universalW) :
    ∃ algEquiv :
      orientedStiefelWhitneyPolynomialEquiv
        H2 n (TopCat.of BSO[n, ESO]) A,
      IsBSOStiefelWhitneyPolynomialPresentationOn
        H2 n (TopCat.of BSO[n, ESO]) A universalW algEquiv := sorry

/-- Theorem 23.7.5. For the classifying space `BSO(n)` of oriented real `n`-plane bundles, the
canonical total mod-`2` cohomology algebra `H^*(BSO(n); Z_2)` is a polynomial `ZMod 2`-algebra
on universal Stiefel-Whitney classes `w_i` in degrees `2 ≤ i ≤ n`. The source-facing universal
classes on `BSO(n)` are recorded by `UniversalBSOStiefelWhitneyFamily`, and their universality is
expressed by `IsUniversalBSOStiefelWhitneyFamily` relative to the chosen principal
`SO(n)`-bundle `hBSO` and the chosen standard normalization data, reusing the Chapter 23 `BO(n)`
owner as a bridge. -/
theorem bsoModTwoCohomology_isPolynomial
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2)
    {n : ℕ}
    {ESO : Type} [TopologicalSpace ESO]
    [MulAction (SO(n)) ESO]
    [ContinuousSMul (SO(n)) ESO]
    [ContractibleSpace ESO]
    (hBSO : IsPrincipalBundleMap (SO(n)) (Quotient.mk'' : ESO → BSO[n, ESO]))
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of BSO[n, ESO])) :
    ∃ universalW : UniversalBSOStiefelWhitneyFamily H2 n ESO,
      IsUniversalBSOStiefelWhitneyFamily H2 normalizationData hBSO universalW ∧
        ∃ algEquiv :
          orientedStiefelWhitneyPolynomialEquiv
            H2 n (TopCat.of BSO[n, ESO]) A,
          IsBSOStiefelWhitneyPolynomialPresentationOn
            H2 n (TopCat.of BSO[n, ESO]) A universalW algEquiv := sorry
