import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_37 (from Chap05/Sec05_35) -/
open scoped ContDiff Manifold
open Manifold Set

universe uE uE' uH uH' uM

section SubmanifoldTangentSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E H}
variable {I : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I ∞ M]
variable (S : Set M) [ChartedSpace H S] [IsManifold J ∞ S]

-- Proof sketch: for the forward implication, compose a tangent vector in the range of the
-- inclusion differential with a smooth function whose restriction to `S` is zero. For the
-- converse, use the local normal-form characterization of a smooth embedding and test against
-- coordinate functions transverse to `S`.
/-- Proposition 5.37: if `S ⊆ M` is given a smooth manifold structure for which the inclusion
`S ↪ M` is a smooth embedding, then an ambient tangent vector at `p ∈ S` is tangent to `S`
exactly when it annihilates every smooth real-valued function on `M` whose restriction to `S`
vanishes. -/
theorem tangentVector_mem_submanifold_iff_forall_smooth_eq_zero
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (p : S) (v : TangentSpace I (p : M)) :
    v ∈ T[J; p] ↔
      ∀ f : C^∞⟮I, M; ℝ⟯, EqOn f 0 S → mfderiv% f (p : M) v = 0 := sorry

end SubmanifoldTangentSpace
