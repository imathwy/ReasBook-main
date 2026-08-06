import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.ComplexPlaneBundleWhitneySum
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexKTheoryAdams
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ProjectiveBundleTopologicalKTheory

open Bundle
open scoped ProjectiveBundleNotation

noncomputable section

universe u v

-- This file specializes the Chapter 24 projective-bundle API to a bundled complex line bundle
-- `L : ComplexPlaneBundle 1 X`, using the canonical repository owner and a bridge to `L ⊕ ε`.

section BundleSide

variable {X : Type u} [TopologicalSpace X]
variable (L : ComplexPlaneBundle 1 X)

/-- The trivial complex line bundle over `X`, viewed as a rank-`1` bundled complex plane bundle.
This is the thin bridge needed to form the Chapter 23 bundled Whitney sum `L ⊕ ε`. -/
def trivialComplexLineBundle (X : Type u) [TopologicalSpace X] : ComplexPlaneBundle 1 X where
  fiber := Bundle.Trivial X (Fin 1 → ℂ)
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

variable [TopologicalSpace
  (Bundle.TotalSpace
    (Fin 2 → ℂ)
    (L.fiber ×ᵇ (trivialComplexLineBundle X).fiber))]
variable [FiberBundle
  (Fin 2 → ℂ)
  (L.fiber ×ᵇ (trivialComplexLineBundle X).fiber)]
variable [VectorBundle
  ℂ
  (Fin 2 → ℂ)
  (L.fiber ×ᵇ (trivialComplexLineBundle X).fiber)]

end BundleSide
section Formula

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
variable (L : ComplexPlaneBundle 1 X)
variable [TopologicalSpace
  (Bundle.TotalSpace
    (Fin 2 → ℂ)
    (L.fiber ×ᵇ (trivialComplexLineBundle X).fiber))]
variable [FiberBundle
  (Fin 2 → ℂ)
  (L.fiber ×ᵇ (trivialComplexLineBundle X).fiber)]
variable [VectorBundle
  ℂ
  (Fin 2 → ℂ)
  (L.fiber ×ᵇ (trivialComplexLineBundle X).fiber)]
variable [CompactSpace (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))]
variable [TopologicalSpace
  (Bundle.TotalSpace
    ℂ
    (projectiveBundleTautologicalLine
      (complexPlaneBundleWhitneySum L (trivialComplexLineBundle X))))]
variable [FiberBundle
  ℂ
  (projectiveBundleTautologicalLine
    (complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))]
variable [VectorBundle
  ℂ
  ℂ
  (projectiveBundleTautologicalLine
    (complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))]

/-- Theorem 24.3.2 (1). For a complex line bundle `L` over the compact space `X`, the actual
tautological class `[H]` on `P(L ⊕ ε)` satisfies
`([H] - 1) * ((π^*[L]) * [H] - 1) = 0` in `K(P(L ⊕ ε))`, where the coefficients are taken over
`K(X)` via `π^* : K(X) → K(P(L ⊕ ε))`. -/
theorem projectiveBundleOfLinePlusTrivialKTheory_relation
    [topologicalKTheory :
      ProjectiveBundleTopologicalKTheory
        (complexPlaneBundleWhitneySum L (trivialComplexLineBundle X))] :
    ((projectiveBundleTautologicalClass :
        complexKTheory (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))) - 1) *
      (topologicalKTheory.pullback
          (lineBundleKTheoryClass L) *
          (projectiveBundleTautologicalClass :
            complexKTheory (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))) -
        1) =
      (0 :
        complexKTheory (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))) := sorry

/-- Theorem 24.3.2 (2). For a complex line bundle `L` over the compact space `X`, the explicit
classes `1` and `[H]` generate `K(P(L ⊕ ε))` over `K(X)` via `π^*` and are linearly independent,
where `[H]` is the actual tautological class on `P(L ⊕ ε)`. -/
theorem projectiveBundleOfLinePlusTrivialKTheory_freeOnOneAndTautological
    [ProjectiveBundleTopologicalKTheory
      (complexPlaneBundleWhitneySum L (trivialComplexLineBundle X))] :
    Submodule.span
        (complexKTheory X)
        (Set.range
          (![1, (projectiveBundleTautologicalClass :
              complexKTheory
                (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X))))] :
            Fin 2 →
              complexKTheory
                (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X))))) = ⊤ ∧
      LinearIndependent
        (complexKTheory X)
        (![1, (projectiveBundleTautologicalClass :
            complexKTheory
              (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X))))] :
          Fin 2 →
            complexKTheory
              (P(complexPlaneBundleWhitneySum L (trivialComplexLineBundle X)))) := sorry

end Formula
