import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifolds_Lee_2012.Chap01.Sec01_04.Example_1_26
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Proposition_4_6
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Proposition_4_8
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this session; local precedent here uses the chapter owner
-- `IsEmbeddedSubmanifold` together with `IsEmbeddedSubmanifold.codimension`.

open TopologicalSpace
open scoped Manifold

universe u

noncomputable section

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- The underlying subtype of an open subset carries the canonical restricted charted-space
structure. -/
instance instChartedSpaceUnderlyingOpenSet (U : Opens M) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ((U : Set M)) :=
  (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin n)) U)

/-- The underlying subtype of an open subset of a smooth manifold carries the canonical inherited
smooth structure. -/
instance instIsManifoldUnderlyingOpenSet (U : Opens M) :
    IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) ((U : Set M)) :=
  (inferInstance : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) U)

/-- Proposition 5.1 (1): an open submanifold of a smooth manifold is an embedded submanifold via
the canonical subtype inclusion. -/
theorem open_submanifold_isEmbeddedSubmanifold (U : Opens M) :
    IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (U : Set M) := sorry

/-- The canonical `Opens`-typed open submanifold inherits the embedded-submanifold structure from
`open_submanifold_isEmbeddedSubmanifold`. -/
instance instIsEmbeddedSubmanifoldOpens (U : Opens M) :
    IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (U : Set M) :=
  open_submanifold_isEmbeddedSubmanifold U

/-- Helper: an open submanifold has codimension `0` in its ambient smooth manifold. -/
theorem open_submanifold_codimension_zero (U : Opens M) :
    ((show IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (U : Set M) from
        open_submanifold_isEmbeddedSubmanifold U)).codimension = 0 := sorry

/-- Proposition 5.1 (2): a codimension-`0` embedded submanifold of a smooth manifold is an open
subset of the ambient manifold. -/
theorem isOpen_of_codimension_zero_embedded_submanifold {S : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S)
    (hcodim : hS.codimension = 0) :
    IsOpen S := sorry

end
