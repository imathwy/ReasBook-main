import Mathlib.LinearAlgebra.TensorProduct.Map
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_3

open scoped TensorProduct

noncomputable section

universe u w

open CategoryTheory Limits
open Bundle

-- This item-owned foundation keeps Theorem 23.5.4 on the actual Thom-space cohomology owner
-- `H^*(ThomSpace n E, thomInfinitySubset n E)` from Definition 23.5.3, without routing the
-- source-facing theorem through Proposition 23.5.5's fallback indiscrete-topology placeholder.

section

variable {R : Type w} [CommRing R]
variable {B : Type u} {n : ℕ} {E : B → Type u}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]
variable (H : ℤ → ∀ X : TopCat.{u}, Set X → Type w)
variable [∀ q : ℤ, ∀ X : TopCat.{u}, ∀ A : Set X, AddCommGroup (H q X A)]
variable [∀ q : ℤ, ∀ X : TopCat.{u}, ∀ A : Set X, Module R (H q X A)]

/-- The absolute cohomology of the Thom space, recorded on the same abstract Chapter 23 owner
surface as `thomReducedCohomology`. -/
abbrev thomAbsoluteCohomology
    (n : ℕ) (E : B → Type u)
    [TopologicalSpace B]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E]
    (H : ℤ → ∀ X : TopCat.{u}, Set X → Type w)
    (q : ℤ) : Type w :=
  H q (TopCat.of (ThomSpace n E)) (∅ : Set (ThomSpace n E))

/-- Thom-space absolute cohomology inherits its additive-group structure from the ambient
cohomology group. -/
instance thomAbsoluteCohomologyAddCommGroup (q : ℤ) :
    AddCommGroup (thomAbsoluteCohomology n E H q) := by
  unfold thomAbsoluteCohomology
  infer_instance

/-- Thom-space absolute cohomology inherits its `R`-module structure from the ambient cohomology
group. -/
instance thomAbsoluteCohomologyModule (q : ℤ) :
    Module R (thomAbsoluteCohomology n E H q) := by
  unfold thomAbsoluteCohomology
  infer_instance

/-- A source-facing cup-product presentation on the Thom space, sufficient to write the comparison
map `H^q(B; R) → H̃^(n + q)(Tξ; R)` obtained by multiplying with a Thom class. -/
structure ThomSpaceCupProduct where
  /-- Cup product with left factor in reduced degree `n` on the Thom space. -/
  cup :
    ∀ q : ℤ,
      thomReducedCohomology n E H (n : ℤ) ⊗[R]
          thomAbsoluteCohomology n E H q →ₗ[R]
        thomReducedCohomology n E H ((n : ℤ) + q)
  /-- The degree-`0` unit class on the Thom-space absolute cohomology owner. -/
  oneClass : thomAbsoluteCohomology n E H 0
  /-- The degree-`0` unit acts as a right unit on reduced degree-`n` classes. -/
  right_unit :
    ∀ α : thomReducedCohomology n E H (n : ℤ),
      cup 0 (TensorProduct.tmul R α oneClass) = α

/-- A source-facing presentation of the pullback and cup-product data used to write the Thom
comparison attached to a Thom class on the actual Thom-space owner used in Theorem 23.5.4. -/
structure ThomComparisonPresentation
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction) where
  /-- Pull back a degree-`q` class on the base to absolute degree `q` on the Thom space. -/
  baseToThom :
    H q (TopCat.of B) (∅ : Set B) →ₗ[R]
      thomAbsoluteCohomology n E H q
  /-- Cup product on the Thom-space cohomology used in the Thom comparison. -/
  thomCup :
    ThomSpaceCupProduct (R := R) (B := B) (n := n) (E := E) (H := H)

/-- The pullback-then-cup Thom comparison map in degree `q`, obtained from a chosen presentation
of the source-facing comparison data attached to `μ`. This helper isolates the presentation-level
formula; the source-facing owner `ThomComparison` below records the resulting canonical
comparison. -/
def thomIsomorphismMapFromPresentation
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (presentation :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ) :
    H q (TopCat.of B) (∅ : Set B) →ₗ[R]
      thomReducedCohomology n E H ((n : ℤ) + q) :=
  (presentation.thomCup.cup q).comp <|
    TensorProduct.mk R _ _ μ.toReducedCohomology |>.comp presentation.baseToThom

/-- A chosen presentation is canonical when it yields the unique Thom comparison map determined
by the given Thom class, i.e. every other source-facing presentation induces the same linear map.
This records the source's "the Thom comparison" on the actual Thom-space cohomology owner. -/
def IsCanonicalThomComparison
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (presentation :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ) : Prop :=
  ∀ presentation' :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ,
    thomIsomorphismMapFromPresentation H q μ presentation' =
      thomIsomorphismMapFromPresentation H q μ presentation

/-- A chosen canonical Thom-comparison presentation. The existence witness restores the missing
"previous setup" assumption that the textbook theorem uses to talk about the canonical comparison
`Φ` rather than an arbitrary package of maps. -/
noncomputable def thomIsomorphismPresentation
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (hcomparison :
      ∃ presentation :
          ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
            (H := H) (fiberRestriction := fiberRestriction) q μ,
        IsCanonicalThomComparison H q μ presentation) :
    ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
      (H := H) (fiberRestriction := fiberRestriction) q μ :=
  Classical.choose hcomparison

/-- The source-facing Thom comparison map in degree `q`, obtained from a chosen witness that the
Thom-space presentation data determines a canonical pullback-then-cup comparison. -/
noncomputable def thomIsomorphismMapOfWitness
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (hcomparison :
      ∃ presentation :
          ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
            (H := H) (fiberRestriction := fiberRestriction) q μ,
        IsCanonicalThomComparison H q μ presentation) :
    H q (TopCat.of B) (∅ : Set B) →ₗ[R]
      thomReducedCohomology n E H ((n : ℤ) + q) :=
  thomIsomorphismMapFromPresentation H q μ
    (thomIsomorphismPresentation H q μ hcomparison)

/-- Unfolding `thomIsomorphismMapFromPresentation` recovers the pullback-then-cup formula from
the chosen Thom comparison presentation. -/
@[simp] theorem thomIsomorphismMapFromPresentation_apply
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (presentation :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ)
    (α : H q (TopCat.of B) (∅ : Set B)) :
    thomIsomorphismMapFromPresentation H q μ presentation α =
      presentation.thomCup.cup q
        (TensorProduct.tmul R μ.toReducedCohomology (presentation.baseToThom α)) := by
  rfl

/-- When the canonical fallback presentation witness exists, unfolding
`thomIsomorphismMapOfWitness` recovers the pullback-then-cup formula from that chosen
presentation. -/
@[simp] theorem thomIsomorphismMapOfWitness_apply
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (hcomparison :
      ∃ presentation :
          ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
            (H := H) (fiberRestriction := fiberRestriction) q μ,
        IsCanonicalThomComparison H q μ presentation)
    (α : H q (TopCat.of B) (∅ : Set B)) :
    thomIsomorphismMapOfWitness H q μ hcomparison α =
      (thomIsomorphismPresentation H q μ hcomparison).thomCup.cup q
        (TensorProduct.tmul R μ.toReducedCohomology
          ((thomIsomorphismPresentation H q μ hcomparison).baseToThom α)) := by
  rfl

/-- Any canonical presentation of the Thom comparison yields the same presentation-level linear
map. -/
theorem thomIsomorphismMapFromPresentation_eq_of_isCanonical
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    {presentation presentation' :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ}
    (hcanonical : IsCanonicalThomComparison H q μ presentation) :
    thomIsomorphismMapFromPresentation H q μ presentation' =
      thomIsomorphismMapFromPresentation H q μ presentation :=
  hcanonical presentation'

/-- The witness-selected Thom comparison map agrees with every presented comparison once a
canonical presentation witness has fixed the underlying comparison. -/
theorem thomIsomorphismMapOfWitness_eq_of_isCanonical
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (hcomparison :
      ∃ presentation :
          ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
            (H := H) (fiberRestriction := fiberRestriction) q μ,
        IsCanonicalThomComparison H q μ presentation)
    {presentation :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ} :
    thomIsomorphismMapOfWitness H q μ hcomparison =
      thomIsomorphismMapFromPresentation H q μ presentation := by
  simpa [hcomparison, thomIsomorphismMapOfWitness, thomIsomorphismPresentation] using
    (Classical.choose_spec hcomparison presentation).symm

/-- A packaged Thom comparison `Φ` in degree `q` for the Thom class `μ`. It consists of the
comparison map together with a presentation-level witness that it is the canonical pullback-then-
cup map attached to `μ`. -/
structure ThomComparison
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction) where
  /-- The comparison map `Φ : H^q(B; R) → H̃^(n + q)(Tξ; R)`. -/
  toLinearMap :
    H q (TopCat.of B) (∅ : Set B) →ₗ[R]
      thomReducedCohomology n E H ((n : ℤ) + q)
  /-- `Φ` is the canonical pullback-then-cup comparison attached to `μ`. -/
  isCanonical :
    ∃ presentation :
        ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
          (H := H) (fiberRestriction := fiberRestriction) q μ,
      IsCanonicalThomComparison H q μ presentation ∧
        toLinearMap = thomIsomorphismMapFromPresentation H q μ presentation

/-- A canonical presentation of the Thom comparison determines a source-facing comparison owner. -/
def ThomComparison.fromPresentation
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[R]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (q : ℤ)
    (μ : ThomClass H fiberRestriction)
    (presentation :
      ThomComparisonPresentation (R := R) (B := B) (n := n) (E := E)
        (H := H) (fiberRestriction := fiberRestriction) q μ)
    (hcanonical : IsCanonicalThomComparison H q μ presentation) :
    ThomComparison H q μ where
  toLinearMap := thomIsomorphismMapFromPresentation H q μ presentation
  isCanonical := ⟨presentation, hcanonical, rfl⟩

end
