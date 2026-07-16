import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_30.Theorem_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section SubmersionLevelSets

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

-- Semantic search note: the owner abstraction here is the chapter-level constant-rank level-set
-- theorem `constant_rank_level_set_has_embedded_submanifold_structure`, specialized to the
-- source-facing smooth-submersion hypothesis.
-- Proof sketch: a smooth submersion has full rank at every point, hence constant rank equal to the
-- target dimension; apply Theorem 5.12 to the fiber `Φ ⁻¹' {y}`.
/-- Corollary 5.13 (1): the level set of a smooth submersion carries a smooth embedded submanifold
structure whose codimension is the dimension of the target manifold. -/
theorem smooth_submersion_level_set_has_embedded_submanifold_structure {Φ : M → N}
    (hΦ : Manifold.IsSmoothSubmersion I J Φ) (y : N) :
    let k : ℕ := Module.finrank ℝ E - Module.finrank ℝ E'
    let S : Set M := Φ ⁻¹' {y}
    let K := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        ∃ hS : IsEmbeddedSubmanifold I K S,
          hS.codimension = Module.finrank ℝ E' := by
  simpa using
    (constant_rank_level_set_has_embedded_submanifold_structure
      hΦ.contMDiff hΦ.hasConstantRank y)

-- Proof sketch: specialize the proper-embedding part of Theorem 5.12 to the constant-rank value
-- `Module.finrank ℝ E'` furnished by the smooth-submersion hypothesis.
/-- Corollary 5.13 (2): each level set of a smooth submersion is properly embedded in the ambient
manifold. -/
theorem smooth_submersion_level_set_isProperlyEmbedded [T1Space N] {Φ : M → N}
    (hΦ : Manifold.IsSmoothSubmersion I J Φ) (y : N) :
    (Φ ⁻¹' {y}).IsProperlyEmbedded := by
  simpa using
    (constant_rank_level_set_isProperlyEmbedded
      hΦ.contMDiff hΦ.hasConstantRank y)

end SubmersionLevelSets
