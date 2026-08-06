import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_1_8

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle
open CategoryTheory

universe u v w

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a canonical mathlib splitting-principle
-- owner for this vector-bundle statement, so this file keeps the explicit Chapter 24 owner.

/-- The fiberwise finite Whitney product of a family of line bundles, used to model the bundle
that the pullback of `E` splits into over the splitting space. -/
abbrev whitneyProductLineBundle {Y : Type u} (n : ℕ) (lineBundle : Fin n → Y → Type v) :
    Y → Type v :=
  fun y ↦ (i : Fin n) → lineBundle i y

section

variable (X : Type) [TopologicalSpace X]
variable (n : ℕ) (E : X → Type v)
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
variable [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
variable [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
variable [VectorBundle ℂ (Fin n → ℂ) E]

/-- A chosen splitting-principle space for a rank-`n` complex vector bundle `E`, together with a
bundle-level decomposition of the pullback bundle into line bundles. -/
structure SplittingPrinciple where
  /-- The space `F(E)` to which `E` is pulled back. -/
  splittingSpace : TopCat
  /-- The projection `F(E) → X`. -/
  projection : splittingSpace ⟶ TopCat.of X
  /-- The line-bundle summands of the pulled-back bundle on `F(E)`. -/
  lineBundle : Fin n → splittingSpace → Type v
  /-- The topology on the total space of each line-bundle summand. -/
  totalSpaceTopologicalSpace :
    ∀ i : Fin n, TopologicalSpace (Bundle.TotalSpace (Fin 1 → ℂ) (lineBundle i))
  /-- The topology on each fiber of the line-bundle summands. -/
  fiberTopologicalSpace : ∀ i : Fin n, (y : splittingSpace) → TopologicalSpace (lineBundle i y)
  /-- Each summand is a complex line bundle. -/
  fiberBundle : ∀ i : Fin n, FiberBundle (Fin 1 → ℂ) (lineBundle i)
  /-- The additive-group structure on each summand fiber. -/
  addCommGroup : ∀ i : Fin n, (y : splittingSpace) → AddCommGroup (lineBundle i y)
  /-- The complex-vector-space structure on each summand fiber. -/
  module : ∀ i : Fin n, (y : splittingSpace) → Module ℂ (lineBundle i y)
  /-- The vector-bundle structure on each line-bundle summand. -/
  vectorBundle : ∀ i : Fin n, VectorBundle ℂ (Fin 1 → ℂ) (lineBundle i)
  /-- The total space of the finite Whitney product of the chosen line bundles carries its chosen
  topology. -/
  whitneyProductTotalSpaceTopologicalSpace :
    TopologicalSpace
      (Bundle.TotalSpace (Fin n → ℂ) (whitneyProductLineBundle n lineBundle))
  /-- The pullback bundle `projection *ᵖ E` is identified over `F(E)` with the finite Whitney
  product of the chosen line bundles by a homeomorphism of total spaces. -/
  splitTotalSpaceHomeomorph :
    Bundle.TotalSpace (Fin n → ℂ) (projection *ᵖ E) ≃ₜ
      Bundle.TotalSpace (Fin n → ℂ) (whitneyProductLineBundle n lineBundle)
  /-- Over each `y : F(E)`, the total-space identification restricts to a complex-linear
  equivalence of fibers. -/
  splitFiberLinear :
    ∀ y : splittingSpace, (projection *ᵖ E) y ≃ₗ[ℂ] ((i : Fin n) → lineBundle i y)
  /-- On each fiber, the total-space identification is given by the specified complex-linear
  equivalence. -/
  splitTotalSpaceHomeomorph_mk :
    ∀ (y : splittingSpace) (v : (projection *ᵖ E) y),
      splitTotalSpaceHomeomorph (Bundle.TotalSpace.mk y v) =
        Bundle.TotalSpace.mk y (splitFiberLinear y v)

/-- A `SplittingPrinciple X n E` datum exhibits an explicit splitting space, projection, a finite
family of complex line bundles on that space, and a bundle-level splitting of the pulled-back
bundle. -/
theorem SplittingPrinciple.spec (S : SplittingPrinciple X n E) :
    ∃ (F : TopCat) (projection : F ⟶ TopCat.of X) (L : Fin n → F → Type v)
      (totalSpaceTopologicalSpace :
        ∀ i : Fin n, TopologicalSpace (Bundle.TotalSpace (Fin 1 → ℂ) (L i)))
      (fiberTopologicalSpace :
        ∀ i : Fin n, (y : F) → TopologicalSpace (L i y))
      (fiberBundle : ∀ i : Fin n, FiberBundle (Fin 1 → ℂ) (L i))
      (addCommGroup : ∀ i : Fin n, (y : F) → AddCommGroup (L i y))
      (module : ∀ i : Fin n, (y : F) → Module ℂ (L i y))
      (vectorBundle : ∀ i : Fin n, VectorBundle ℂ (Fin 1 → ℂ) (L i))
      (whitneyTotalSpaceTopology :
        TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) (whitneyProductLineBundle n L)))
      (splitTotalSpaceHomeomorph :
        Bundle.TotalSpace (Fin n → ℂ) (projection *ᵖ E) ≃ₜ
          Bundle.TotalSpace (Fin n → ℂ) (whitneyProductLineBundle n L))
      (splitFiberLinear :
        ∀ y : F, (projection *ᵖ E) y ≃ₗ[ℂ] ((i : Fin n) → L i y)),
      ∀ (y : F) (v : (projection *ᵖ E) y),
        splitTotalSpaceHomeomorph (Bundle.TotalSpace.mk y v) =
          Bundle.TotalSpace.mk y (splitFiberLinear y v) := sorry

namespace SplittingPrinciple

variable {X : Type} [TopologicalSpace X]
variable {n : ℕ} {E : X → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
variable [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
variable [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
variable [VectorBundle ℂ (Fin n → ℂ) E]

/-- A ring homomorphism `K(X) → K(F(E))` is a compact splitting-principle pullback for `S` when
`F(E)` is compact and the map is the canonical presentation-level pullback induced by
`S.projection`. -/
def IsTopologicalKTheoryPullback
    (S : SplittingPrinciple X n E)
    (pullback : complexKTheory X →+* complexKTheory S.splittingSpace) : Prop :=
  ∃ splittingSpaceCompact : CompactSpace S.splittingSpace,
    letI := splittingSpaceCompact
    IsComplexKTheoryPresentationPullback S.projection pullback

end SplittingPrinciple

/-- Theorem 24.3.3 (1): there exists a splitting-principle datum for `E` whose pullback bundle
splits as a finite Whitney sum of complex line bundles over a suitable space `F(E)`. -/
theorem exists_splittingPrinciple :
    Nonempty (SplittingPrinciple X n E) := sorry

/-- Theorem 24.3.3 (2): there exists a suitable splitting-principle space `F(E)` for which
pullback on integral singular cohomology is injective in every degree. -/
theorem exists_splittingPrincipleCohomologyPullback_injective :
    ∃ S : SplittingPrinciple X n E,
      ∀ q : ℕ, Function.Injective (singularCohomologyPullback ℤ S.projection q) := sorry

section

variable [CompactSpace X]

/-- Theorem 24.3.3 (3): if `X` is compact, then there exists a suitable compact splitting space
`F(E)` such that pullback along its splitting-principle projection is injective on integral
singular cohomology in every degree and on topological `K`-theory. -/
theorem exists_splittingPrincipleTopologicalKTheoryPullback_injective :
    ∃ S : SplittingPrinciple X n E,
      ∃ pullback : complexKTheory X →+* complexKTheory S.splittingSpace,
        S.IsTopologicalKTheoryPullback pullback ∧
          Function.Injective pullback ∧
          ∀ q : ℕ, Function.Injective (singularCohomologyPullback ℤ S.projection q) := sorry

end

end
