import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ProjectiveBundleTopologicalKTheory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped LinearAlgebra.Projectivization
open scoped ProjectiveBundleNotation

-- Semantic recall via `lean_leansearch` did not surface a canonical imported projective-bundle
-- theorem for topological `K`-theory, so this file follows Chapter 24 precedent and states the
-- theorem directly on the actual `complexKTheory` classes of `P(E)`. Honest presentation families
-- remain bridge/view API via bundle isomorphisms to the actual exterior-power presentations
-- `[Λ^i E]`.

section

variable {X : Type} [TopologicalSpace X]
variable {n : ℕ} {E : ComplexPlaneBundle n X}

/-- The fiberwise exterior power bundle `x ↦ ⋀[ℂ]^i (E x)` over `X`. -/
abbrev projectiveBundleExteriorPowerBundle (E : ComplexPlaneBundle n X) (i : ℕ) : X → Type :=
  fun x ↦ ⋀[ℂ]^i (E.fiber x)

/-- The projective-bundle relation polynomial over `K(X)` determined by a family of classes
playing the role of the coefficients `[Λ^i E]`. -/
noncomputable abbrev projectiveBundleKTheoryRelationPolynomial
    (exteriorPowerClass : Fin (n + 1) → complexKTheory X) :
    Polynomial (complexKTheory X) :=
  ∑ i : Fin (n + 1),
    Polynomial.C
        (((-1 : complexKTheory X) ^ (i : ℕ)) *
          exteriorPowerClass i) *
      Polynomial.X ^ (i : ℕ)

/-- `projectiveBundleKTheoryRelationPolynomial` is the polynomial
`∑ i : Fin (n + 1), C (((-1 : K(X)) ^ i) * [Λ^i E]) * X ^ i`. -/
theorem projectiveBundleKTheoryRelationPolynomial_def
    (exteriorPowerClass : Fin (n + 1) → complexKTheory X) :
    projectiveBundleKTheoryRelationPolynomial exteriorPowerClass =
      ∑ i : Fin (n + 1),
        Polynomial.C
            (((-1 : complexKTheory X) ^ (i : ℕ)) *
              exteriorPowerClass i) *
          Polynomial.X ^ (i : ℕ) := rfl

private theorem projectiveBundleExteriorPowerPresentation_iso_of_bundle_eq
    {V W : ComplexVectorBundle.Presentation X} (hVW : V.bundle = W.bundle) :
    Nonempty (ComplexVectorBundle.Iso V W) := by
  sorry

/-- Two exact presentations of the actual `i`th exterior power of `E` determine the same
`K`-theory class. -/
theorem projectiveBundleExteriorPowerClass_eq_of_bundle_eq
    (i : Fin (n + 1))
    (exteriorPowerPresentation exteriorPowerPresentation' :
      ComplexVectorBundle.Presentation X)
    (hExteriorPowerPresentation :
      exteriorPowerPresentation.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ))
    (hExteriorPowerPresentation' :
      exteriorPowerPresentation'.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ)) :
    ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation =
      ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation' := by
  have hIso :
      Nonempty (ComplexVectorBundle.Iso exteriorPowerPresentation exteriorPowerPresentation') :=
    projectiveBundleExteriorPowerPresentation_iso_of_bundle_eq
      (hExteriorPowerPresentation.trans hExteriorPowerPresentation'.symm)
  exact ComplexVectorBundle.toVirtualPresentation_eq_of_iso hIso

/-- Any two chosen presentations of the actual `i`th exterior power determine the same
`K`-theory class once both are isomorphic to an exact presentation of `Λ^i E`. -/
theorem projectiveBundleExteriorPowerClass_eq_of_iso
    (i : Fin (n + 1))
    (actualExteriorPowerPresentation :
      ComplexVectorBundle.Presentation X)
    (exteriorPowerPresentation exteriorPowerPresentation' :
      ComplexVectorBundle.Presentation X)
    (hActualExteriorPowerPresentation :
      actualExteriorPowerPresentation.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ))
    (hExteriorPowerPresentation :
      Nonempty (ComplexVectorBundle.Iso exteriorPowerPresentation actualExteriorPowerPresentation))
    (hExteriorPowerPresentation' :
      Nonempty
        (ComplexVectorBundle.Iso exteriorPowerPresentation' actualExteriorPowerPresentation)) :
    ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation =
      ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation' := by
  sorry

/-- A class `α ∈ K(X)` is the actual class `[Λ^i E]` when it is the virtual class of some exact
honest presentation of the actual exterior-power bundle `Λ^i E`. Chosen isomorphic presentations
are handled by bridge theorems rather than by a second public owner. -/
def IsProjectiveBundleExteriorPowerClass
    (E : ComplexPlaneBundle n X) (i : Fin (n + 1))
    (α : complexKTheory X) : Prop :=
  ∃ exteriorPowerPresentation : ComplexVectorBundle.Presentation X,
    exteriorPowerPresentation.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ) ∧
      α = ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation

/-- Any exact presentation of `Λ^i E` computes the source-facing actual class `[Λ^i E]`. -/
theorem isProjectiveBundleExteriorPowerClass_of_bundle_eq
    (i : Fin (n + 1))
    (exteriorPowerPresentation : ComplexVectorBundle.Presentation X)
    (hExteriorPowerPresentation :
      exteriorPowerPresentation.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ)) :
    IsProjectiveBundleExteriorPowerClass E i
      (ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation) := by
  exact ⟨exteriorPowerPresentation, hExteriorPowerPresentation, rfl⟩

/-- Any chosen presentation isomorphic to an exact presentation of `Λ^i E` computes the same
source-facing actual class `[Λ^i E]`. -/
theorem isProjectiveBundleExteriorPowerClass_of_presentation
    (i : Fin (n + 1))
    (actualExteriorPowerPresentation exteriorPowerPresentation :
      ComplexVectorBundle.Presentation X)
    (hActualExteriorPowerPresentation :
      actualExteriorPowerPresentation.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ))
    (hExteriorPowerPresentation :
      Nonempty
        (ComplexVectorBundle.Iso exteriorPowerPresentation actualExteriorPowerPresentation)) :
    IsProjectiveBundleExteriorPowerClass E i
      (ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation) := by
  exact ⟨actualExteriorPowerPresentation, hActualExteriorPowerPresentation,
    ComplexVectorBundle.toVirtualPresentation_eq_of_iso hExteriorPowerPresentation⟩

/-- A source-facing actual exterior-power class is represented by some exact presentation of the
actual bundle `Λ^i E`. -/
theorem IsProjectiveBundleExteriorPowerClass.exists_eq_toVirtualPresentation
    {i : Fin (n + 1)}
    {α : complexKTheory X}
    (hα : IsProjectiveBundleExteriorPowerClass E i α) :
    ∃ exteriorPowerPresentation : ComplexVectorBundle.Presentation X,
      exteriorPowerPresentation.bundle = projectiveBundleExteriorPowerBundle E (i : ℕ) ∧
        α = ComplexVectorBundle.toVirtualPresentation exteriorPowerPresentation := hα

/-- The actual class `[Λ^i E]` in `K(X)` is independent of the honest presentation choices used
to compute it. -/
theorem projectiveBundleExteriorPowerClass_eq_of_isProjectiveBundleExteriorPowerClass
    {i : Fin (n + 1)}
    {α α' : complexKTheory X}
    (hα : IsProjectiveBundleExteriorPowerClass E i α)
    (hα' : IsProjectiveBundleExteriorPowerClass E i α') :
    α = α' := by
  rcases hα with ⟨exteriorPowerPresentation, hExteriorPowerPresentation, rfl⟩
  rcases hα' with ⟨exteriorPowerPresentation', hExteriorPowerPresentation', hα'⟩
  rw [hα']
  exact projectiveBundleExteriorPowerClass_eq_of_bundle_eq
    i exteriorPowerPresentation exteriorPowerPresentation'
    hExteriorPowerPresentation hExteriorPowerPresentation'

/-- Pointwise-equal exterior-power coefficient families determine the same relation polynomial. -/
theorem projectiveBundleKTheoryRelationPolynomial_eq_of_eq
    {exteriorPowerClass exteriorPowerClass' :
      Fin (n + 1) → complexKTheory X}
    (hExteriorPowerClass :
      ∀ i : Fin (n + 1), exteriorPowerClass i = exteriorPowerClass' i) :
    projectiveBundleKTheoryRelationPolynomial exteriorPowerClass =
      projectiveBundleKTheoryRelationPolynomial exteriorPowerClass' := by
  unfold projectiveBundleKTheoryRelationPolynomial
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hExteriorPowerClass i]

/-- The relation polynomial computed from chosen presentation families is independent of the
chosen family once both bridge by bundle isomorphisms to the same actual exterior-power
presentation family. -/
theorem projectiveBundleKTheoryRelationPolynomial_eq_of_presentation
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ComplexVectorBundle.Presentation X)
    (hActualExteriorPowerPresentation :
      ∀ i : Fin (n + 1),
        (actualExteriorPowerPresentation i).bundle =
          projectiveBundleExteriorPowerBundle E (i : ℕ))
    (exteriorPowerPresentation exteriorPowerPresentation' :
      (i : Fin (n + 1)) → ComplexVectorBundle.Presentation X)
    (hExteriorPowerPresentation :
      ∀ i : Fin (n + 1),
        Nonempty (ComplexVectorBundle.Iso
          (exteriorPowerPresentation i)
          (actualExteriorPowerPresentation i)))
    (hExteriorPowerPresentation' :
      ∀ i : Fin (n + 1),
        Nonempty (ComplexVectorBundle.Iso
          (exteriorPowerPresentation' i)
          (actualExteriorPowerPresentation i))) :
    projectiveBundleKTheoryRelationPolynomial
        (fun i ↦ ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i)) =
      projectiveBundleKTheoryRelationPolynomial
        (fun i ↦ ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation' i)) := by
  apply projectiveBundleKTheoryRelationPolynomial_eq_of_eq
  intro i
  exact projectiveBundleExteriorPowerClass_eq_of_iso
    i
    (actualExteriorPowerPresentation i)
    (exteriorPowerPresentation i)
    (exteriorPowerPresentation' i)
    (hActualExteriorPowerPresentation i)
    (hExteriorPowerPresentation i)
    (hExteriorPowerPresentation' i)

/-- The projective-bundle relation polynomial depends only on the actual exterior-power classes
`[Λ^i E] ∈ K(X)`, not on how those classes are represented by chosen honest bundles. -/
theorem projectiveBundleKTheoryRelationPolynomial_eq_of_isProjectiveBundleExteriorPowerClass
    {exteriorPowerClass exteriorPowerClass' :
      Fin (n + 1) → complexKTheory X}
    (hExteriorPowerClass :
      ∀ i : Fin (n + 1),
        IsProjectiveBundleExteriorPowerClass E i (exteriorPowerClass i))
    (hExteriorPowerClass' :
      ∀ i : Fin (n + 1),
        IsProjectiveBundleExteriorPowerClass E i (exteriorPowerClass' i)) :
    projectiveBundleKTheoryRelationPolynomial exteriorPowerClass =
      projectiveBundleKTheoryRelationPolynomial exteriorPowerClass' := by
  apply projectiveBundleKTheoryRelationPolynomial_eq_of_eq
  intro i
  exact projectiveBundleExteriorPowerClass_eq_of_isProjectiveBundleExteriorPowerClass
    (hExteriorPowerClass i) (hExteriorPowerClass' i)

variable [CompactSpace X]
variable [CompactSpace (P(E))]
variable [TopologicalSpace (Bundle.TotalSpace ℂ (projectiveBundleTautologicalLine E))]
variable [Fact (0 < n)]
variable [FiberBundle ℂ (projectiveBundleTautologicalLine E)]
variable [VectorBundle ℂ ℂ (projectiveBundleTautologicalLine E)]

/- Theorem 24.3.6 (1). For the projective bundle `P(E)`, the topological-`K`-theory ring
`K(P(E))` is free as a `K(X)`-module on `1, [H], …, [H]^(n - 1)`, where `0 < n`, `[H]` is the
actual tautological class on `P(E)`, and the
`K(X)`-module structure is the actual one induced by the ambient `K(X)`-algebra structure on
`K(P(E))`. -/
theorem projectiveBundleKTheory_freeOnPowers
    [ProjectiveBundleTopologicalKTheory E] :
    ∃ b : Module.Basis
        (Fin n)
        (complexKTheory X)
        (complexKTheory (P(E))),
      ∀ i : Fin n,
        b i =
          (projectiveBundleTautologicalClass :
            complexKTheory (P(E))) ^
            (i : ℕ) := sorry

/-- Theorem 24.3.6 (2). If `exteriorPowerClass i ∈ K(X)` is the actual class `[Λ^i E]` for each
`i = 0, ..., n`, then the corresponding projective-bundle relation polynomial over `K(X)`
annihilates the actual tautological class `[H]` on `P(E)`. The theorem
`projectiveBundleKTheoryRelationPolynomial_eq_of_isProjectiveBundleExteriorPowerClass` shows this
polynomial depends only on the actual exterior-power classes of `E` and not on any chosen honest
presentation family used to compute them. -/
theorem projectiveBundleKTheory_exteriorPowerRelation
    [ProjectiveBundleTopologicalKTheory E]
    (exteriorPowerClass : Fin (n + 1) → complexKTheory X)
    (hExteriorPowerClass :
      ∀ i : Fin (n + 1),
        IsProjectiveBundleExteriorPowerClass E i (exteriorPowerClass i)) :
    Polynomial.aeval
      (projectiveBundleTautologicalClass :
        complexKTheory (P(E)))
      (projectiveBundleKTheoryRelationPolynomial exteriorPowerClass :
        Polynomial (complexKTheory X)) =
      (0 : complexKTheory (P(E))) := sorry

/-- Any chosen presentation family bridging to an actual exterior-power presentation family
computes coefficient classes satisfying Theorem 24.3.6 (2). -/
theorem projectiveBundleKTheory_exteriorPowerRelation_of_presentation
    [ProjectiveBundleTopologicalKTheory E]
    (actualExteriorPowerPresentation :
      (i : Fin (n + 1)) → ComplexVectorBundle.Presentation X)
    (hActualExteriorPowerPresentation :
      ∀ i : Fin (n + 1),
        (actualExteriorPowerPresentation i).bundle =
          projectiveBundleExteriorPowerBundle E (i : ℕ))
    (exteriorPowerPresentation :
      (i : Fin (n + 1)) → ComplexVectorBundle.Presentation X)
    (hExteriorPowerPresentation :
      ∀ i : Fin (n + 1),
        Nonempty (ComplexVectorBundle.Iso
          (exteriorPowerPresentation i)
          (actualExteriorPowerPresentation i))) :
    Polynomial.aeval
      (projectiveBundleTautologicalClass :
        complexKTheory (P(E)))
      (projectiveBundleKTheoryRelationPolynomial
          (fun i ↦ ComplexVectorBundle.toVirtualPresentation (exteriorPowerPresentation i)) :
        Polynomial (complexKTheory X)) =
      (0 : complexKTheory (P(E))) := by
  apply projectiveBundleKTheory_exteriorPowerRelation
  intro i
  exact isProjectiveBundleExteriorPowerClass_of_presentation
    i
    (actualExteriorPowerPresentation i)
    (exteriorPowerPresentation i)
    (hActualExteriorPowerPresentation i)
    (hExteriorPowerPresentation i)

end
