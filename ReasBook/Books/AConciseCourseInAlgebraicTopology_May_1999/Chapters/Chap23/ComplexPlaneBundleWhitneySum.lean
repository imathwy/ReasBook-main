import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1

open Bundle

noncomputable section

universe u v

/-- A chosen `Fin (n + m) → ℂ`-modeled Whitney sum of two bundled complex plane bundles over the
same base. -/
def complexPlaneBundleWhitneySum
    {n m : ℕ} {B : Type u} [TopologicalSpace B]
    (E₁ : ComplexPlaneBundle.{u, v} n B) (E₂ : ComplexPlaneBundle.{u, v} m B)
    [TopologicalSpace (Bundle.TotalSpace (Fin (n + m) → ℂ) (E₁.fiber ×ᵇ E₂.fiber))]
    [FiberBundle (Fin (n + m) → ℂ) (E₁.fiber ×ᵇ E₂.fiber)]
    [VectorBundle ℂ (Fin (n + m) → ℂ) (E₁.fiber ×ᵇ E₂.fiber)] :
    ComplexPlaneBundle (n + m) B where
  fiber := E₁.fiber ×ᵇ E₂.fiber
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance
