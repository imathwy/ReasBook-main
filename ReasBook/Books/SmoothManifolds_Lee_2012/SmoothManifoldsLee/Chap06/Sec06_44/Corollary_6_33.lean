import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_44.Theorem_6_32

open TopologicalSpace
open scoped ContDiff Manifold

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` surfaced local-diffeomorphism API results, and this
-- file keeps the Chapter 6 owner `graphFirstProjection` from `Theorem_6_32` for the restricted
-- first projection.

section LocalGraphs

universe uEM uEN uHM uHN uM uN

open Manifold

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]

/-- A neighborhood of `x` in an immersed submanifold is the graph of a smooth map over a
neighborhood of `p` in the first factor. -/
def isLocalGraphAt
    (S : ImmersedSubmanifold (IM.prod IN) (M × N))
    (x : S) (p : M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
    ∃ V : Set S, IsOpen V ∧ x ∈ V ∧
      ∃ f : M → N,
        ContMDiffOn IM IN ∞ f U ∧
          S.inclusion '' V = U.graphOn f

/-- Corollary 6.33 (Local Characterization of Graphs): suppose `S` is an immersed submanifold of
`M × N`, and let `x : S` map to `(p, q)`. If `S` intersects the vertical slice `{p} × N`
transversely at `(p, q)` and the derivative of the restricted first projection at `x` is
injective, then there exist a neighborhood of `p` in `M` and a neighborhood of `x` in `S` such
that the latter is the graph of a smooth map to `N`. Since transversality gives surjectivity of
that derivative, these hypotheses encode the source proof's local-isomorphism condition. -/
theorem exists_local_graph_of_immersedSubmanifold_of_verticalSliceMeetsTransverselyAt
    (S : ImmersedSubmanifold (IM.prod IN) (M × N))
    (x : S)
    (htrans : verticalSliceMeetsTransverselyAt S x)
    (hinj :
      Function.Injective
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) IM (graphFirstProjection S) x)) :
    isLocalGraphAt S x (S.inclusion x).1 := sorry

end LocalGraphs
