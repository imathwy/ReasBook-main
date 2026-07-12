import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace Seminorm

/-- Proposition 3.6, stated at the intrinsic owner level: on any finite-dimensional real normed
space, every seminorm defines a closed convex `WithTop ℝ`-valued function. The textbook `ℝⁿ`
statement is the specialization to `E = EuclideanSpace ℝ (Fin n)`, and separation still plays no
role in convexity or closedness of the epigraph. -/
-- Proof sketch: `Seminorm.convexOn` gives convexity on all of `E`, and then the finite-dimensional
-- continuity theorem for convex functions upgrades this to continuity on `univ`. The chapter lemma
-- `closedConvexFunction_coe_of_convexOn_continuous` then packages the epigraph closedness.
theorem closedConvexFunction
    (p : Seminorm ℝ E) :
    ClosedConvexFunction (fun x : E ↦ (p x : WithTop ℝ)) := by
  -- Route correction: the textbook reverse-triangle argument proves continuity when the seminorm
  -- is itself the ambient norm. For the intrinsic owner theorem, `p` is an arbitrary seminorm on
  -- a normed space, so we use finite-dimensional convex-function continuity instead.
  -- Package the textbook route: convexity plus continuity implies a closed epigraph.
  apply closedConvexFunction_coe_of_convexOn_continuous
  · -- Convexity is the standard seminorm inequality from triangle inequality and homogeneity.
    simpa using p.convexOn
  · -- On a finite-dimensional real space, a convex function is continuous on the open set `univ`.
    simpa [continuousOn_univ] using p.convexOn.continuousOn isOpen_univ

end Seminorm
