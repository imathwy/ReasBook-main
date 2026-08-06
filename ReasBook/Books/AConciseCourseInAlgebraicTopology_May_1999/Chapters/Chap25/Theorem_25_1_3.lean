import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_1_2
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic

open scoped DirectSum

/-- The total direct sum of the degreewise unoriented cobordism groups. -/
abbrev NStar : Type 1 := ⨁ n : ℕ, N_(n)

notation "N_*" => NStar

-- Semantic recall: `lean_leansearch` surfaced the graded-algebra/direct-sum API around
-- `GradedAlgebra`, `DirectSum.decomposeAlgEquiv`, and `MvPolynomial`. Repo inspection then showed
-- that the current Chapter 25 development still has no fixed canonical cobordism multiplication or
-- `ZMod 2`-algebra owner on `N_*`, so this file records Thom's theorem through an explicit
-- current-file owner carrying the ring/algebra/generator/`AlgEquiv` data on `N_*`.

/-- A degree is allowed as a Thom generator degree for `N_*` precisely when it is greater than `1`
and is not of the form `2^r - 1`. -/
def IsThomUnorientedCobordismGeneratorDegree (i : ℕ) : Prop :=
  1 < i ∧ ∀ r : ℕ, i ≠ 2 ^ r - 1

/-- Companion to `IsThomUnorientedCobordismGeneratorDegree`: the defining conditions are exactly
`1 < i` and the exclusion of all Mersenne degrees `2^r - 1`. -/
theorem isThomUnorientedCobordismGeneratorDegree_iff {i : ℕ} :
    IsThomUnorientedCobordismGeneratorDegree i ↔
      1 < i ∧ ∀ r : ℕ, i ≠ 2 ^ r - 1 :=
  Iff.rfl

/-- The index type of Thom's polynomial generators for the total unoriented cobordism object
`N_*`. -/
abbrev ThomUnorientedCobordismGeneratorDegree :=
  {i : ℕ // IsThomUnorientedCobordismGeneratorDegree i}

/-- Each admissible Thom generator degree carries its defining dimension constraints. -/
theorem thomUnorientedCobordismGeneratorDegree_spec
    (i : ThomUnorientedCobordismGeneratorDegree) :
    1 < i.1 ∧ ∀ r : ℕ, i.1 ≠ 2 ^ r - 1 :=
  i.2

/-- A `ZMod 2`-algebra structure on the fixed cobordism object `N_*` for a chosen commutative ring
structure. -/
abbrev ThomUnorientedCobordismModTwoAlgebra (toCommRing : CommRing N_*) :=
  letI := toCommRing
  Algebra (ZMod 2) N_*

/-- A polynomial `ZMod 2`-algebra equivalence from
`MvPolynomial ThomUnorientedCobordismGeneratorDegree (ZMod 2)` to `N_*`, for a chosen
commutative ring and `ZMod 2`-algebra structure on `N_*`. -/
abbrev ThomUnorientedCobordismPolynomialEquiv
    (toCommRing : CommRing N_*)
    (toAlgebra : ThomUnorientedCobordismModTwoAlgebra toCommRing) :=
  letI := toCommRing
  letI := toAlgebra
  MvPolynomial ThomUnorientedCobordismGeneratorDegree (ZMod 2) ≃ₐ[ZMod 2] N_*

/-- The additive commutative group underlying a candidate commutative ring structure on `N_*`
agrees with the canonical direct-sum additive commutative group. -/
def ThomUnorientedCobordismAdditiveCompatibility (toCommRing : CommRing N_*) : Prop :=
  toCommRing.toAddCommGroup =
    DirectSum.instAddCommGroup (fun n ↦ N_(n))

/-- A direct Thom polynomial presentation on the fixed total unoriented cobordism object `N_*`
consists of homogeneous generators in the admissible degrees and a polynomial `ZMod 2`-algebra
equivalence whose monomials land in the summand prescribed by the sum of the generator degrees. -/
def IsThomUnorientedCobordismPolynomialPresentationOn
    (toCommRing : CommRing N_*)
    (toAlgebra : ThomUnorientedCobordismModTwoAlgebra toCommRing)
    (u : ThomUnorientedCobordismGeneratorDegree → N_*)
    (φ : ThomUnorientedCobordismPolynomialEquiv toCommRing toAlgebra) : Prop :=
  (∀ i, ∃ x : N_(i.1),
    u i = DirectSum.lof ℤ ℕ (fun n ↦ N_(n)) i.1 x) ∧
    (∀ i, φ (MvPolynomial.X i) = u i) ∧
      ∀ d : ThomUnorientedCobordismGeneratorDegree →₀ ℕ,
        ∃ x : N_(d.sum fun i e ↦ e * i.1),
          φ (MvPolynomial.monomial d (1 : ZMod 2)) =
            DirectSum.lof ℤ ℕ (fun n ↦ N_(n))
              (d.sum fun i e ↦ e * i.1) x

/-- Companion to `IsThomUnorientedCobordismPolynomialPresentationOn`: it is exactly the data of
homogeneous generators in the admissible degrees together with a polynomial `ZMod 2`-algebra
equivalence carrying variables and monomials to the expected homogeneous summands of `N_*`. -/
theorem isThomUnorientedCobordismPolynomialPresentationOn_iff
    {toCommRing : CommRing N_*}
    {toAlgebra : ThomUnorientedCobordismModTwoAlgebra toCommRing}
    {u : ThomUnorientedCobordismGeneratorDegree → N_*}
    {φ : ThomUnorientedCobordismPolynomialEquiv toCommRing toAlgebra} :
    IsThomUnorientedCobordismPolynomialPresentationOn
        toCommRing toAlgebra u φ ↔
      (∀ i, ∃ x : N_(i.1),
        u i = DirectSum.lof ℤ ℕ (fun n ↦ N_(n)) i.1 x) ∧
        (∀ i, φ (MvPolynomial.X i) = u i) ∧
          ∀ d : ThomUnorientedCobordismGeneratorDegree →₀ ℕ,
            ∃ x : N_(d.sum fun i e ↦ e * i.1),
              φ (MvPolynomial.monomial d (1 : ZMod 2)) =
                DirectSum.lof ℤ ℕ (fun n ↦ N_(n))
                  (d.sum fun i e ↦ e * i.1) x :=
  Iff.rfl

/-- A packaged Thom polynomial `ZMod 2`-algebra presentation on the fixed total unoriented
cobordism object `N_*`, together with compatibility of its ring addition with the existing
direct-sum additive commutative group structure on `N_*`. -/
structure ThomUnorientedCobordismPolynomialAlgebra where
  /-- The commutative ring structure on `N_*` appearing in Thom's polynomial presentation. -/
  toCommRing : CommRing N_*
  /-- The ring addition, zero, and negation agree with the direct-sum additive commutative group
  structure already carried by `N_*`. -/
  addCommGroup_eq : ThomUnorientedCobordismAdditiveCompatibility toCommRing
  /-- The `ZMod 2`-algebra structure in Thom's polynomial presentation of `N_*`. -/
  toAlgebra : ThomUnorientedCobordismModTwoAlgebra toCommRing
  /-- Thom's chosen generator family on `N_*`, indexed by the admissible degrees. -/
  generators : ThomUnorientedCobordismGeneratorDegree → N_*
  /-- The polynomial `ZMod 2`-algebra equivalence realizing Thom's presentation of `N_*`. -/
  algEquiv : ThomUnorientedCobordismPolynomialEquiv toCommRing toAlgebra
  /-- Thom's generators and algebra equivalence satisfy the stated polynomial-presentation
  conditions on the fixed cobordism object `N_*`. -/
  isPresentation :
    IsThomUnorientedCobordismPolynomialPresentationOn
      toCommRing toAlgebra generators algEquiv

/-- A Thom polynomial algebra structure supplies a commutative ring structure on `N_*`. -/
instance (A : ThomUnorientedCobordismPolynomialAlgebra) : CommRing N_* :=
  A.toCommRing

/-- A Thom polynomial algebra structure supplies a `ZMod 2`-algebra structure on `N_*`. -/
instance (A : ThomUnorientedCobordismPolynomialAlgebra) :
    ThomUnorientedCobordismModTwoAlgebra A.toCommRing :=
  A.toAlgebra

/-- The presentation data carried by `ThomUnorientedCobordismPolynomialAlgebra` satisfies the
explicit polynomial-presentation predicate on `N_*`. -/
theorem thomUnorientedCobordismPolynomialAlgebra_spec
    (A : ThomUnorientedCobordismPolynomialAlgebra) :
    IsThomUnorientedCobordismPolynomialPresentationOn
      A.toCommRing A.toAlgebra A.generators A.algEquiv :=
  A.isPresentation

/-- Theorem 25.1.3. Thom: the fixed total unoriented cobordism object `N_*` admits a polynomial
`ZMod 2`-algebra presentation, with a commutative ring structure compatible with its existing
additive commutative group on generators `u_i` in each degree `i > 1` that is not of the form
`2^r - 1`. -/
theorem thomUnorientedCobordismPolynomialAlgebra_exists :
    ∃ (toCommRing : CommRing N_*)
      (toAlgebra : ThomUnorientedCobordismModTwoAlgebra toCommRing)
      (generators : ThomUnorientedCobordismGeneratorDegree → N_*)
      (algEquiv : ThomUnorientedCobordismPolynomialEquiv toCommRing toAlgebra),
      ThomUnorientedCobordismAdditiveCompatibility toCommRing ∧
        IsThomUnorientedCobordismPolynomialPresentationOn
          toCommRing toAlgebra generators algEquiv := by
  sorry

/-- Companion to Theorem 25.1.3: the same source-facing existence statement can be packaged as a
single `ThomUnorientedCobordismPolynomialAlgebra` owner together with its presentation predicate.
-/
theorem exists_thomUnorientedCobordismPolynomialAlgebra :
    ∃ A : ThomUnorientedCobordismPolynomialAlgebra,
      IsThomUnorientedCobordismPolynomialPresentationOn
        A.toCommRing A.toAlgebra A.generators A.algEquiv := by
  rcases thomUnorientedCobordismPolynomialAlgebra_exists with
    ⟨toCommRing, toAlgebra, generators, algEquiv, addCommGroup_eq, isPresentation⟩
  refine ⟨
    { toCommRing := toCommRing
      addCommGroup_eq := addCommGroup_eq
      toAlgebra := toAlgebra
      generators := generators
      algEquiv := algEquiv
      isPresentation := isPresentation },
    ?_⟩
  exact isPresentation
