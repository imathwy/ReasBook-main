import Mathlib
import SmoothManifoldsLee.Chap04.Sec04_23.Theorem_4_12

open scoped ContDiff Manifold

noncomputable section

universe uM uN

namespace LocalNormalFormAPI

section

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- Helper for Theorem 5.8: the Euclidean normal form that keeps the first `r` source coordinates
and sets the remaining target coordinates to `0`. -/
abbrev rank_normal_form (m n r : ℕ) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
  _root_.rank_normal_form m n r

/-- Helper for Theorem 5.8: on a target coordinate with index `< r` and `< m`,
`rank_normal_form` returns the matching source coordinate. -/
theorem rank_normal_form_apply_of_lt {r : ℕ} {i : Fin n} (hri : i.1 < r) (hmi : i.1 < m)
    (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = x ⟨i.1, hmi⟩ := by
  simpa using _root_.rank_normal_form_apply_of_lt (m := m) (n := n) (r := r) hri hmi x

/-- Helper for Theorem 5.8: a local coordinate normal form packages centered charts in which a map
agrees with a prescribed Euclidean model. -/
abbrev LocalCoordinateNormalFormAt (F : M → N) (p : M)
    (normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) :=
  _root_.LocalCoordinateNormalFormAt F p normalForm

namespace LocalCoordinateNormalFormAt

/-- Helper for Theorem 5.8: a local coordinate normal form carries the source chart domain into
the target chart domain. -/
theorem mapsTo_source {F : M → N} {p : M}
    {normalForm : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (h : LocalCoordinateNormalFormAt F p normalForm) :
    Set.MapsTo F h.domChart.source h.codChart.source := by
  exact h.mapsTo

end LocalCoordinateNormalFormAt

/-- Helper for Theorem 5.8: a smooth immersion admits centered local coordinates in which it is
the standard coordinate inclusion into the first `m` ambient coordinates. -/
theorem smooth_immersion_local_inclusion_form {F : M → N}
    (hF : Manifold.IsImmersion I_m I_n ∞ F) (p : M) :
    ∃ _ : LocalCoordinateNormalFormAt F p (rank_normal_form m n m), True := by
  simpa using _root_.smooth_immersion_local_inclusion_form (m := m) (n := n) hF p

end

end LocalNormalFormAPI
