import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_5_4.Comparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Problem_19_6_2

noncomputable section

universe u

/-- A multiplicative pair cohomology theory with coefficients in `R`. Besides the Eilenberg--
Steenrod axioms bundled by `PairCohomologyTheory`, it records the absolute and relative cup
products, their compatibility, and the coefficient-module structure used by the Thom map. -/
structure MultiplicativePairCohomologyTheory (R : Type u) [CommRing R] where
  toPairCohomologyTheory : PairCohomologyTheory R
  absoluteCup : AbsoluteCupProduct toPairCohomologyTheory
  relativeCup : PairCohomologyTheory.RelativeCupProductMap toPairCohomologyTheory
  relativeCup_compatible : absoluteCup.IsCompatibleWithRelativeCup relativeCup
  relativeCohomologyModule :
    ∀ q : ℤ, ∀ X : TopCat.{u}, ∀ A : Set X,
      Module R (toPairCohomologyTheory.relativeCohomology q X A)

/-- The relative groups underlying a multiplicative pair cohomology theory. -/
abbrev MultiplicativePairCohomologyTheory.relativeCohomology
    {R : Type u} [CommRing R] (H : MultiplicativePairCohomologyTheory R) :
    ℤ → ∀ X : TopCat.{u}, Set X → Type u :=
  H.toPairCohomologyTheory.relativeCohomology

instance {R : Type u} [CommRing R] :
    CoeFun (MultiplicativePairCohomologyTheory R)
      (fun _ ↦ ℤ → ∀ X : TopCat.{u}, Set X → Type u) where
  coe H := H.relativeCohomology

instance {R : Type u} [CommRing R] (H : MultiplicativePairCohomologyTheory R)
    (q : ℤ) (X : TopCat.{u}) (A : Set X) : Module R (H q X A) :=
  H.relativeCohomologyModule q X A

-- The reusable comparison-presentation layer for Theorem 23.5.4 lives in the item-owned
-- foundation module `Theorem_23_5_4.Comparison`; this file keeps only the source-facing Thom map
-- and the labeled theorem.

section

variable {R : Type u} [CommRing R]
variable {B : Type u} {n : ℕ} {E : B → Type u}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]
variable (H : MultiplicativePairCohomologyTheory R)

/-- The source-facing Thom comparison map in degree `q` determined by the canonical pullback-then-
cup comparison `Φ` attached to the Thom class `μ`. -/
abbrev thomIsomorphismMap
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (comparison : ThomComparison H q μ) :
    H q (TopCat.of B) (∅ : Set B) →ₗ[R]
      thomReducedCohomology n E H ((n : ℤ) + q) :=
  comparison.toLinearMap

/-- Unfolding `thomIsomorphismMap` recovers the pullback-then-cup formula for a canonical Thom
comparison `Φ` attached to `μ`. -/
@[simp] theorem thomIsomorphismMap_apply
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (comparison : ThomComparison H q μ)
    (α : H q (TopCat.of B) (∅ : Set B)) :
    thomIsomorphismMap H q μ comparison α =
      (Classical.choose comparison.isCanonical).thomCup.cup q
        (TensorProduct.tmul R μ.toReducedCohomology
          ((Classical.choose comparison.isCanonical).baseToThom α)) := by
  rcases Classical.choose_spec comparison.isCanonical with ⟨_, hcomparison⟩
  change comparison.toLinearMap α = _
  calc
    comparison.toLinearMap α =
        thomIsomorphismMapFromPresentation H q μ
          (Classical.choose comparison.isCanonical) α :=
      congrArg (fun f ↦ f α) hcomparison
    _ =
        (Classical.choose comparison.isCanonical).thomCup.cup q
          (TensorProduct.tmul R μ.toReducedCohomology
            ((Classical.choose comparison.isCanonical).baseToThom α)) :=
      thomIsomorphismMapFromPresentation_apply
        (R := R) (B := B) (n := n) (E := E) (H := H)
        (q := q) (μ := μ) (presentation := Classical.choose comparison.isCanonical) (α := α)

/-- Helper for Theorem 23.5.4: the Thom comparison map attached to `μ` is bijective. The
multiplicative pair-cohomology structure on `H` supplies the dimension, exactness, excision,
additivity, weak-equivalence, and cup-product axioms used in the standard proof. -/
theorem thomIsomorphismMap_bijective
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (comparison : ThomComparison H q μ) :
    Function.Bijective
      (thomIsomorphismMap H q μ comparison) := sorry

/-- Theorem 23.5.4::statement_repair::1 If `μ` is a Thom class for the real `n`-plane bundle `ξ`,
then the canonical Thom comparison `Φ : H^q(B; R) → H̃^(n + q)(Tξ; R)` attached to `μ` is a linear
isomorphism. -/
theorem thom_isomorphism_theorem
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (comparison : ThomComparison H q μ) :
    ∃ thomEquiv :
        H q (TopCat.of B) (∅ : Set B) ≃ₗ[R]
          thomReducedCohomology n E H ((n : ℤ) + q),
      thomEquiv.toLinearMap = thomIsomorphismMap H q μ comparison := sorry

end
