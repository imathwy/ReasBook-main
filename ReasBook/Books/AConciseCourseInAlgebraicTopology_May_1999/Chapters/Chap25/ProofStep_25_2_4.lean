import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_2_2

open scoped Manifold

noncomputable section

universe u v

-- Chapter 25 already fixes the source-facing cobordism relation `cobordant` and the canonical
-- collapse-map owner `PontryaginThomConstruction.collapseMap`, so this proof step records their
-- textbook correspondence directly on those owners.

section

variable {n q : ℕ}
variable {BO : Type u} [TopologicalSpace BO]
variable {γ : BO → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)]
variable [FiberBundle (Fin q → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)]
variable [∀ b, Module ℝ (γ b)]
variable [∀ b, NormedAddCommGroup (γ b)]
variable [∀ b, NormedSpace ℝ (γ b)]
variable [RealPlaneBundleClassifyingSpace q BO γ]
variable {M N : ClosedSmoothManifold n}
variable {eM : M.M → AmbientEuclideanSpace n q}
variable {eN : N.M → AmbientEuclideanSpace n q}

/-- Proof step 25.2.4 (1). If two closed smooth `n`-manifolds are cobordant, then any chosen
Pontryagin-Thom constructions for embeddings of them into the same Euclidean space
`AmbientEuclideanSpace n q = ℝ^(n + q)` have homotopic collapse maps into the same Thom space
`TO q BO γ`. -/
theorem pontryaginThomCollapseMap_homotopic_of_cobordant
    (hMN : cobordant n M N)
    (ptM : PontryaginThomConstruction n q BO γ M eM)
    (ptN : PontryaginThomConstruction n q BO γ N eN) :
    ContinuousMap.Homotopic ptM.collapseMap ptN.collapseMap := sorry

/-- Proof step 25.2.4 (2). Conversely, if chosen Pontryagin-Thom constructions for two closed
smooth `n`-manifolds have homotopic collapse maps in the same codimension `q`, then the
manifolds are cobordant. -/
theorem cobordant_of_pontryaginThomCollapseMap_homotopic
    (ptM : PontryaginThomConstruction n q BO γ M eM)
    (ptN : PontryaginThomConstruction n q BO γ N eN)
    (hpt : ContinuousMap.Homotopic ptM.collapseMap ptN.collapseMap) :
    cobordant n M N := sorry

/-- Proof step 25.2.4. For fixed Pontryagin-Thom constructions in codimension `q`, two closed
smooth `n`-manifolds are cobordant exactly when their collapse maps into `TO q BO γ` are
homotopic. -/
theorem cobordant_iff_pontryaginThomCollapseMap_homotopic
    (ptM : PontryaginThomConstruction n q BO γ M eM)
    (ptN : PontryaginThomConstruction n q BO γ N eN) :
    cobordant n M N ↔ ContinuousMap.Homotopic ptM.collapseMap ptN.collapseMap := by
  constructor
  · intro hMN
    exact pontryaginThomCollapseMap_homotopic_of_cobordant hMN ptM ptN
  · intro hpt
    exact cobordant_of_pontryaginThomCollapseMap_homotopic ptM ptN hpt

end
