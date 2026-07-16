import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Exercise_4_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.HasConstantRank`, `Theorem_4_5`, and nearby manifold Euclidean-space item files.

noncomputable section

open Set
open scoped ContDiff Manifold

universe uM uN

section RankTheorem

variable {m n r : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The Euclidean normal form for a rank-`r` map keeps the first `r` source coordinates and sends
all remaining target coordinates to `0`. -/
def rank_normal_form (m n r : ℕ) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
  fun x ↦
    WithLp.toLp 2 <| fun i : Fin n ↦
        if i.1 < r then
          if hmi : i.1 < m then
            x ⟨i.1, hmi⟩
          else
            0
        else
          0

/-- On a target coordinate with index `< r` and `< m`, `rank_normal_form` returns the matching
source coordinate. -/
-- Proof sketch: unfold `rank_normal_form` and evaluate the nested `if` expressions using the two
-- index inequalities.
theorem rank_normal_form_apply_of_lt {i : Fin n} (hri : i.1 < r) (hmi : i.1 < m)
    (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = x ⟨i.1, hmi⟩ := sorry

/-- A local coordinate normal form for `F` at `p` consists of centered smooth charts on the source
and target in which the coordinate representative of `F` agrees with a prescribed Euclidean model
map. -/
structure LocalCoordinateNormalFormAt (F : M → N) (p : M)
    (normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) where
  domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m))
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas I_m ∞ M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n ∞ N
  domChart_centered : p ∈ domChart.source ∧ domChart p = 0
  codChart_centered : F p ∈ codChart.source ∧ codChart (F p) = 0
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) normalForm domChart.target

namespace LocalCoordinateNormalFormAt

/-- Any local coordinate normal form carries the source chart domain into the target chart
domain. -/
-- Proof sketch: this is exactly the `mapsTo` field of the structure.
theorem mapsTo_source {F : M → N} {p : M}
    {normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (h : LocalCoordinateNormalFormAt F p normalForm) :
    MapsTo F h.domChart.source h.codChart.source := sorry

end LocalCoordinateNormalFormAt

/-- Theorem 4.12: a smooth map of constant rank `r` has centered smooth local coordinates in which
its coordinate representative is the standard rank-`r` normal form. -/
-- Proof sketch: use the inverse function theorem on the first `r` output coordinates to build a
-- centered source chart in which the map looks like `(x, y) ↦ (x, R_tilde (x, y))`; the
-- constant-rank hypothesis forces `R_tilde` to be independent of `y`, and a final centered target
-- chart subtracts the
-- resulting graph term to obtain `rank_normal_form m n r`.
theorem constant_rank_local_coordinate_normal_form {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r) (p : M) :
    ∃ h : LocalCoordinateNormalFormAt F p (rank_normal_form m n r), True := sorry

/-- A smooth submersion admits centered local coordinates in which it becomes projection onto the
first `n` coordinates. -/
-- Proof sketch: specialize the rank theorem to the full target rank `r = n`; a smooth
-- submersion has surjective manifold derivative at every point, so the rank normal form becomes
-- the projection form of equation `(4.2)`.
theorem smooth_submersion_local_projection_form {F : M → N}
    (hF : Manifold.IsSmoothSubmersion
      I_m I_n F) (p : M) :
    ∃ h : LocalCoordinateNormalFormAt F p (rank_normal_form m n n), True := sorry

/-- A smooth immersion admits centered local coordinates in which it becomes the standard
coordinate inclusion into the first `m` target coordinates. -/
-- Proof sketch: specialize the rank theorem to the full source rank `r = m`; in that case the
-- rank normal form is the inclusion form of equation `(4.3)`.
theorem smooth_immersion_local_inclusion_form {F : M → N}
    (hF : Manifold.IsImmersion
      I_m I_n ∞ F) (p : M) :
    ∃ h : LocalCoordinateNormalFormAt F p (rank_normal_form m n m), True := sorry

end RankTheorem
