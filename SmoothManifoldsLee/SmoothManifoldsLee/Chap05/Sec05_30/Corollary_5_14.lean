import Mathlib
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section RegularLevelSets

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

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against the local regular-value owner in `Definition_5_36_extra_3` and the
-- preceding submersion-level-set corollary in `Corollary_5_13`.

/-- Corollary 5.14 (1) (Regular Level Set Theorem): if `Φ : M → N` is smooth and `c` is a regular
value of `Φ`, then the level set `Φ ⁻¹' {c}` carries a smooth embedded submanifold structure whose
codimension is the dimension of the codomain manifold. -/
theorem regular_level_set_has_embedded_submanifold_structure {Φ : M → N} {c : N}
    (hΦ : ContMDiff I J ∞ Φ) (hc : IsRegularValue I J Φ c) :
    let k : ℕ := Module.finrank ℝ E - Module.finrank ℝ E'
    let S : Set M := Φ ⁻¹' {c}
    let K := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        ∃ hS : IsEmbeddedSubmanifold I K S,
          hS.codimension = Module.finrank ℝ E' := sorry

/-- Corollary 5.14 (2) (Regular Level Set Theorem): if `Φ : M → N` is smooth and `c` is a regular
value of `Φ`, then the level set `Φ ⁻¹' {c}` is properly embedded in `M`. -/
theorem regular_level_set_isProperlyEmbedded [T1Space N] {Φ : M → N} {c : N}
    (hΦ : ContMDiff I J ∞ Φ) (hc : IsRegularValue I J Φ c) :
    (Φ ⁻¹' {c}).IsProperlyEmbedded := sorry

end RegularLevelSets
