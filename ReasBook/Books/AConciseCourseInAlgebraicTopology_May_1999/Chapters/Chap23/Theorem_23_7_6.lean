import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.ComplexPlaneBundleWhitneySum
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_7_3

open CategoryTheory Bundle
open scoped BigOperators LinearAlgebra.Projectivization

noncomputable section

universe u v

namespace singularCohomologyClasses

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {n : ℕ}

/-- Addition of singular cohomology classes is induced by pointwise addition of cocycle
representatives. -/
def add (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularCohomologyClasses R X n →
      singularCohomologyClasses R X n →
        singularCohomologyClasses R X n :=
  Quotient.map₂
    (fun φ ψ ↦
      ⟨φ.1 + ψ.1, by
        simp [map_add, φ.2, ψ.2]⟩)
    (fun _ _ hφ _ _ hψ ↦ by
      sorry)

/-- Negation of singular cohomology classes is induced by negation of cocycle representatives. -/
def neg (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularCohomologyClasses R X n →
      singularCohomologyClasses R X n :=
  Quotient.map
    (fun φ ↦
      ⟨-φ.1, by
        simp [map_neg, φ.2]⟩)
    (fun _ _ h ↦ by
      sorry)

/-- Subtraction on singular cohomology classes is addition of the negative. -/
def sub (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularCohomologyClasses R X n →
      singularCohomologyClasses R X n →
        singularCohomologyClasses R X n :=
  fun α β ↦ add R X n α (neg R X n β)

end singularCohomologyClasses

/-- The zero quotient-model singular cohomology class. -/
instance instZeroSingularCohomologyClasses
    {R : Type u} [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    Zero (singularCohomologyClasses R X n) where
  zero := singularCohomologyZeroClass R X n

/-- Addition on quotient-model singular cohomology classes. -/
instance instAddSingularCohomologyClasses
    {R : Type u} [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    Add (singularCohomologyClasses R X n) where
  add := singularCohomologyClasses.add R X n

/-- Negation on quotient-model singular cohomology classes. -/
instance instNegSingularCohomologyClasses
    {R : Type u} [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    Neg (singularCohomologyClasses R X n) where
  neg := singularCohomologyClasses.neg R X n

/-- Subtraction on quotient-model singular cohomology classes. -/
instance instSubSingularCohomologyClasses
    {R : Type u} [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    Sub (singularCohomologyClasses R X n) where
  sub := singularCohomologyClasses.sub R X n

/-- Quotient-model singular cohomology classes form an additive commutative group degreewise. -/
instance singularCohomologyClassesAddCommGroup
    {R : Type u} [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    AddCommGroup (singularCohomologyClasses R X n) where
  toAddGroup :=
    AddGroup.ofRightAxioms
      (fun a b c ↦ by
        sorry)
      (fun a ↦ by
        sorry)
      (fun a ↦ by
        sorry)
  add_comm := by
    sorry

-- Chapter 20 owns the canonical ordinary integral cohomology groups
-- `integralSingularCohomology X n`. This file adds only the thin degreewise
-- `AddCommGrpCat` bridge needed by `ComplexCharacteristicClass`, together with the
-- source-facing Chern-theory and universal-class surfaces.

/-- Quotient-model integral singular cohomology classes, viewed as a degreewise
`AddCommGrpCat`-valued contravariant functor on spaces. -/
abbrev singularCohomologyClassesFunctor (n : ℕ) : TopCatᵒᵖ ⥤ AddCommGrpCat where
  obj X :=
    AddCommGrpCat.of (singularCohomologyClasses ℤ (Opposite.unop X) n)
  map f :=
    AddCommGrpCat.ofHom
      { toFun := singularCohomologyPullback ℤ (Opposite.unop f) n
        map_zero' := by
          sorry
        map_add' := by
          sorry }
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The degree-`n` ordinary integral cohomology groups, viewed as a `ModuleCat ℤ`-valued
contravariant functor on spaces. -/
abbrev integralSingularCohomologyModuleFunctor (n : ℕ) : TopCatᵒᵖ ⥤ ModuleCat ℤ where
  obj X :=
    integralSingularCohomology (Opposite.unop X) n
  map f := rSingularCohomology.map ℤ (Opposite.unop f) n
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The degree-`n` ordinary integral cohomology groups, viewed as an `AddCommGrpCat`-valued
contravariant functor on spaces. -/
abbrev integralSingularCohomologyFunctor (n : ℕ) : TopCatᵒᵖ ⥤ AddCommGrpCat :=
  integralSingularCohomologyModuleFunctor n ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat

/-- Pullback on the canonical Chapter 20 owner `integralSingularCohomology`. -/
abbrev integralSingularCohomologyPullback
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    integralSingularCohomology Y n ⟶ integralSingularCohomology X n :=
  rSingularCohomology.map ℤ f n

/-- An ordinary integral cohomology theory on spaces, presented degreewise as an
`AddCommGrpCat`-valued contravariant functor equipped with its degree-zero unit class and cup
product. -/
structure IntegralCohomologyTheory where
  /-- The degreewise cohomology functor. -/
  cohomology : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat
  /-- The degree-zero unit class. -/
  oneClass : ∀ B : TopCat, (cohomology 0).obj (Opposite.op B)
  /-- The cup product. -/
  cup :
    ∀ {p q : ℕ} {B : TopCat},
      (cohomology p).obj (Opposite.op B) →
        (cohomology q).obj (Opposite.op B) →
          (cohomology (p + q)).obj (Opposite.op B)

/-- The canonical Chapter 20 ordinary integral cohomology theory on spaces. -/
abbrev integralSingularCohomologyTheory : IntegralCohomologyTheory where
  cohomology := integralSingularCohomologyFunctor
  oneClass := integralSingularCohomologyOneClass
  cup := fun {p q} {B} α β ↦ integralSingularCohomologyCup B p q α β

/-- The quotient-model integral singular cohomology theory on spaces. -/
abbrev singularCohomologyClassesTheory : IntegralCohomologyTheory where
  cohomology := singularCohomologyClassesFunctor
  oneClass := singularCohomologyOneClass ℤ
  cup := fun {p q} {B} ↦ singularCohomologyCup ℤ B p q

/-- A family of degree-`2 * i` Chern characteristic classes for complex `n`-plane bundles with
values in the chosen integral cohomology theory `H`. -/
abbrev ChernClassFamily
    (H : IntegralCohomologyTheory := integralSingularCohomologyTheory) :=
  ∀ n i : ℕ, ComplexCharacteristicClass.{0, v, 0} n (2 * i)
    H.cohomology

/-- The cup-product term in the Whitney sum formula for the degree-`i` Chern class lands in
cohomological degree `2 * i`. -/
theorem chernWhitneyDegree_eq (i : ℕ) (p : Fin (i + 1)) :
    2 * (p : ℕ) + 2 * (i - (p : ℕ)) = 2 * i := sorry

/-- A chosen `CP^∞` normalization datum for integral Chern classes in the cohomology theory `H`:
the tautological complex line bundle over `ComplexProjectiveInfinity` together with the
distinguished degree-`2` class used in the normalization axiom. -/
structure ChernNormalization
    (H : IntegralCohomologyTheory := integralSingularCohomologyTheory) where
  /-- The tautological complex line bundle over the canonical projective-space base
  `ComplexProjectiveInfinity`. -/
  tautologicalLineBundle : ComplexPlaneBundle 1 (TopCat.of ComplexProjectiveInfinity)
  /-- The chosen bundle fibers are exactly the canonical projective-space tautological complex
  lines, up to the ambient universe lift used by this file's bundle conventions. -/
  tautologicalLineBundle_spec :
    tautologicalLineBundle.fiber =
      fun ℓ : TopCat.of ComplexProjectiveInfinity ↦
        ULift.{v} (Projectivization.submodule ℓ)
  /-- The distinguished degree-`2` normalization class on `ComplexProjectiveInfinity`. -/
  degreeTwoGenerator : (H.cohomology 2).obj (Opposite.op (TopCat.of ComplexProjectiveInfinity))

/-- A degree-`2` integral singular cohomology class on `ComplexProjectiveInfinity` is standard
when it corresponds to `1 : ℤ` under some chosen identification
`H²(ComplexProjectiveInfinity; ℤ) ≃ ℤ`. -/
def IsStandardComplexProjectiveGenerator
    (α : integralSingularCohomology (TopCat.of ComplexProjectiveInfinity) 2) : Prop :=
  ∃ e : integralSingularCohomology (TopCat.of ComplexProjectiveInfinity) 2 ≅
      ModuleCat.of ℤ ℤ,
    e.hom α = 1

/-- A `CP^∞` normalization datum in Chapter 20 ordinary integral cohomology whose degree-`2`
class is the standard generator of `H²(ComplexProjectiveInfinity; ℤ)`. -/
structure StandardChernNormalization
    extends ChernNormalization integralSingularCohomologyTheory where
  /-- The chosen normalization class is the standard generator of
  `H²(ComplexProjectiveInfinity; ℤ)`. -/
  degreeTwoGenerator_spec :
    IsStandardComplexProjectiveGenerator toChernNormalization.degreeTwoGenerator

/-- A `CP^∞` normalization datum in quotient-model integral singular cohomology whose degree-`2`
class maps to the standard generator of `H²(ComplexProjectiveInfinity; ℤ)` in the Chapter 20
owner. -/
structure StandardIntegralChernNormalization
    extends ChernNormalization singularCohomologyClassesTheory where
  /-- The chosen quotient-model degree-`2` class maps to the standard generator in the Chapter 20
  integral owner. -/
  degreeTwoGenerator_spec :
    IsStandardComplexProjectiveGenerator
      (singularCohomologyClassToIntegralSingularCohomology
        (TopCat.of ComplexProjectiveInfinity) 2 toChernNormalization.degreeTwoGenerator)

namespace StandardChernNormalization

/-- The ambient degree-`2` normalization class of a standard normalization datum is the standard
generator of `H²(ComplexProjectiveInfinity; ℤ)`. -/
theorem degreeTwoGenerator_isStandard
    (normalizationData : StandardChernNormalization) :
    IsStandardComplexProjectiveGenerator
      normalizationData.toChernNormalization.degreeTwoGenerator :=
  normalizationData.degreeTwoGenerator_spec

end StandardChernNormalization

namespace StandardIntegralChernNormalization

/-- The quotient-model degree-`2` normalization class of a standard integral normalization datum
maps to the standard generator of `H²(ComplexProjectiveInfinity; ℤ)` in the Chapter 20 owner. -/
theorem degreeTwoGenerator_isStandard
    (normalizationData : StandardIntegralChernNormalization) :
    IsStandardComplexProjectiveGenerator
      (singularCohomologyClassToIntegralSingularCohomology
        (TopCat.of ComplexProjectiveInfinity) 2
        normalizationData.toChernNormalization.degreeTwoGenerator) :=
  normalizationData.degreeTwoGenerator_spec

end StandardIntegralChernNormalization

/-- The Chern axioms for a family of characteristic classes with values in ordinary integral
cohomology. Naturality is built into `ComplexCharacteristicClass`. The normalization on line
bundles is encoded by the chosen tautological complex line bundle over
`ComplexProjectiveInfinity`, and the Whitney-sum clause is stated for a chosen
`Fin (n + m) → ℂ`-modeled structure on `E₁.fiber ×ᵇ E₂.fiber`. -/
structure IsChernTheory
    (H : IntegralCohomologyTheory := integralSingularCohomologyTheory)
    (normalizationData : ChernNormalization H) (c : ChernClassFamily H) : Prop where
  /-- The degree-`0` class of the chosen tautological complex line bundle is the unit class on
  `ComplexProjectiveInfinity`. -/
  tautologicalZeroClass :
    (c 1 0)
        (ComplexPlaneBundle.classOf normalizationData.tautologicalLineBundle) =
      H.oneClass (TopCat.of ComplexProjectiveInfinity)
  /-- The degree-`1` class of the chosen tautological complex line bundle is the distinguished
  normalization generator. -/
  normalization :
    (c 1 1)
        (ComplexPlaneBundle.classOf normalizationData.tautologicalLineBundle) =
      normalizationData.degreeTwoGenerator
  /-- The degree-`i` class of an `n`-plane bundle vanishes for `i > n`. -/
  dimension :
    ∀ {n i : ℕ} {B : TopCat} (E : ComplexPlaneBundle n B),
      n < i →
        (c n i) ((ComplexPlaneBundle.classOf E) : ComplexPlaneBundle.classes n B) = 0
  /-- The classes of a Whitney sum are given by the cup-product expansion of the summand classes
  on the chosen bundled Whitney sum of `E₁` and `E₂`. -/
  whitneySum :
    ∀ {n m i : ℕ} {B : TopCat}
      (E₁ : ComplexPlaneBundle n B) (E₂ : ComplexPlaneBundle m B)
      [TopologicalSpace (Bundle.TotalSpace (Fin (n + m) → ℂ) (E₁.fiber ×ᵇ E₂.fiber))]
      [FiberBundle (Fin (n + m) → ℂ) (E₁.fiber ×ᵇ E₂.fiber)]
      [VectorBundle ℂ (Fin (n + m) → ℂ) (E₁.fiber ×ᵇ E₂.fiber)],
      (c (n + m) i)
          ((ComplexPlaneBundle.classOf
            (complexPlaneBundleWhitneySum E₁ E₂)) :
              ComplexPlaneBundle.classes (n + m) B) =
        ∑ p : Fin (i + 1),
          (chernWhitneyDegree_eq i p) ▸
            H.cup
              ((c n p)
                ((ComplexPlaneBundle.classOf E₁) : ComplexPlaneBundle.classes n B))
              ((c m (i - (p : ℕ)))
                ((ComplexPlaneBundle.classOf E₂) : ComplexPlaneBundle.classes m B))

section

variable {n : ℕ}
variable {EU : Type} [TopologicalSpace EU]
variable [MulAction (U n) EU] [ContinuousSMul (U n) EU]
variable (γBU : BU[n, EU] → Type _)
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
variable [∀ b, TopologicalSpace (γBU b)]
variable [FiberBundle (Fin n → ℂ) γBU]
variable [∀ b, AddCommGroup (γBU b)]
variable [∀ b, Module ℂ (γBU b)]
variable [VectorBundle ℂ (Fin n → ℂ) γBU]

/-- The ordinary integral singular cohomology group `H^{2 * i}(BU(n); ℤ)` of the quotient-model
classifying space `BU(n)`. -/
abbrev universalChernClassGroup
    (n : ℕ) (EU : Type) [TopologicalSpace EU] [MulAction (U n) EU] [ContinuousSMul (U n) EU]
    (i : ℕ) :=
  integralSingularCohomology (TopCat.of BU[n, EU]) (2 * i)

/-- A chosen family of universal Chern classes on `BU(n)`, one in each degree `2 * i`. -/
abbrev UniversalChernClassFamily
    (n : ℕ) (EU : Type) [TopologicalSpace EU] [MulAction (U n) EU] [ContinuousSMul (U n) EU] :=
  ∀ i : ℕ, universalChernClassGroup n EU i

/-- The degree-`i` universal Chern class on `BU(n)` obtained by evaluating the degree-`i` Chern
class owner on the quotient-model universal bundle `γBU`. -/
abbrev universalChernClass
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    (c : ChernClassFamily) (i : ℕ) :
    integralSingularCohomology (TopCat.of BU[n, EU]) (2 * i) :=
  complexCharacteristicClassEvalOnUniversalBundle γBU (c n i)

/-- A family `u` of classes in ordinary integral cohomology `H^{2 * i}(BU(n); ℤ)` is universal
when it is obtained by evaluating a Chern theory on the quotient-model universal bundle and the
chosen normalization class on `ComplexProjectiveInfinity` is the standard generator of
`H²(ComplexProjectiveInfinity; ℤ)`. -/
def IsUniversalChernClassFamily
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    (u : UniversalChernClassFamily n EU) : Prop :=
  ∃ normalizationData : StandardChernNormalization,
    ∃ c : ChernClassFamily,
      IsChernTheory integralSingularCohomologyTheory
        normalizationData.toChernNormalization c ∧
        ∀ i : ℕ, universalChernClass γBU c i = u i

/-- Unfolding `IsUniversalChernClassFamily` recovers the chosen standard normalization datum, the
realizing Chern theory, and evaluation on the quotient-model universal bundle. -/
theorem isUniversalChernClassFamily_iff
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    {u : UniversalChernClassFamily n EU} :
    IsUniversalChernClassFamily γBU u ↔
    ∃ normalizationData : StandardChernNormalization,
      ∃ c : ChernClassFamily,
        IsChernTheory integralSingularCohomologyTheory
          normalizationData.toChernNormalization c ∧
          ∀ i : ℕ, universalChernClass γBU c i = u i :=
  Iff.rfl

/-- Any Chern theory with standard normalization yields its universal Chern classes on `BU(n)` by
evaluation on the quotient-model universal bundle. -/
theorem isUniversalChernClassFamily_of_isChernTheory
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    (normalizationData : StandardChernNormalization) (c : ChernClassFamily)
    (hc : IsChernTheory integralSingularCohomologyTheory
      normalizationData.toChernNormalization c) :
    IsUniversalChernClassFamily γBU
      (fun i ↦ universalChernClass γBU c i) :=
  ⟨normalizationData, c, hc, fun _ ↦ rfl⟩

/-- Theorem 23.7.6 (1). For a chosen quotient-model universal complex `n`-plane bundle `γBU` over
`BU(n)`, there exists a family of universal Chern classes
`u : ∀ i, H^{2 * i}(BU(n); ℤ)` that is characterized by naturality, dimension, normalization on
line bundles by the standard generator of `H²(ComplexProjectiveInfinity; ℤ)`, and the Whitney
sum formula. -/
theorem exists_universalChernClasses [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU] :
    ∃ u : UniversalChernClassFamily n EU,
      IsUniversalChernClassFamily γBU u := sorry

/-- Theorem 23.7.6 (2). For a chosen quotient-model universal complex `n`-plane bundle `γBU` over
`BU(n)`, the family of universal Chern classes in ordinary integral cohomology
`u : ∀ i, H^{2 * i}(BU(n); ℤ)` characterized by naturality, dimension, normalization on line
bundles by the standard generator of `H²(ComplexProjectiveInfinity; ℤ)`, and the Whitney sum
formula is unique. -/
theorem subsingleton_universalChernClasses [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU] :
    Subsingleton
      { u : UniversalChernClassFamily n EU //
        IsUniversalChernClassFamily γBU u } := sorry

instance instSubsingletonUniversalChernClasses [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n) (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU] :
    Subsingleton
      { u : UniversalChernClassFamily n EU //
        IsUniversalChernClassFamily γBU u } :=
  subsingleton_universalChernClasses γBU

end
