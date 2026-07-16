import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_29.Theorem_5_8.Common
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_29.Theorem_5_8.LocalSliceAtlas
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_4

-- Declarations for Euclidean half-slice helper geometry used by Theorem 5.51.

open Set ChartedSpace
open scoped Manifold

noncomputable section

section

variable {n k : ℕ}

/-- Helper for Theorem 5.51: the last projected coordinate of `ℝ^k` is the boundary coordinate in
Lee's half-slice convention. -/
private def projected_last_coordinate (hk : 0 < k) : Fin k :=
  ⟨k - 1, Nat.pred_lt (Nat.ne_of_gt hk)⟩

/-- Helper for Theorem 5.51: the distinguished nonnegative coordinate of a Euclidean half-slice,
viewed in ambient `ℝ^n`. -/
private def euclidean_half_slice_ambient_last_coordinate (hk : 0 < k) (hkn : k ≤ n) : Fin n :=
  ⟨k - 1, lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hk)) hkn⟩

/-- Helper for Theorem 5.51: projecting to the first `k` coordinates carries the last free
half-slice coordinate to the last coordinate of `ℝ^k`. -/
private theorem euclidean_slice_projection_last_coordinate
    (hk : 0 < k) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    euclidean_slice_projection hkn x (projected_last_coordinate hk) =
      x (euclidean_half_slice_ambient_last_coordinate hk hkn) := by
  rfl

/-- Helper for Theorem 5.51: swap the last coordinate of `ℝ^k` into slot `0`, matching mathlib's
half-space convention. -/
private def half_slice_boundary_coordinate_swap [NeZero k] (hk : 0 < k) : Fin k ≃ Fin k :=
  Equiv.swap 0 (projected_last_coordinate hk)

/-- Helper for Theorem 5.51: Lee's “last coordinate nonnegative” convention is homeomorphic to the
standard Euclidean half-space by swapping coordinates `0` and `k - 1`. -/
private noncomputable def half_slice_last_coordinate_homeomorph
    [NeZero k]
    (hk : 0 < k) :
    {u : EuclideanSpace ℝ (Fin k) | 0 ≤ u (projected_last_coordinate hk)} ≃ₜ
      EuclideanHalfSpace k := by
  let e : EuclideanSpace ℝ (Fin k) ≃ₜ EuclideanSpace ℝ (Fin k) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (half_slice_boundary_coordinate_swap hk)).toHomeomorph
  exact e.subtype fun u ↦ by
    simpa [e, half_slice_boundary_coordinate_swap, projected_last_coordinate]

/-- Helper for Theorem 5.51: projecting a Euclidean half-slice to its free coordinates and then
moving the constrained last coordinate into slot `0` identifies it with a subtype of `ℍ^k`. -/
private noncomputable def euclidean_half_slice_projection_homeomorph
    [NeZero k]
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hk : 0 < k) (hkn : k ≤ n) (c : Fin (n - k) → ℝ) :
    Set.euclideanHalfSlice U k hk hkn c ≃ₜ
      {z : EuclideanHalfSpace k |
        euclidean_slice_inclusion hkn c
          ((half_slice_last_coordinate_homeomorph hk).symm z).1 ∈ U} := by
  let sourceAsSlice :
      Set.euclideanHalfSlice U k hk hkn c ≃ₜ
        {x : Set.euclideanSlice U k hkn c |
          0 ≤ x.1 (euclidean_half_slice_ambient_last_coordinate hk hkn)} := by
    simpa [Set.euclideanHalfSlice, euclidean_half_slice_ambient_last_coordinate] using
      (subtype_patch_intersection_homeomorph
        (Set.euclideanSlice U k hkn c)
        {y : EuclideanSpace ℝ (Fin n) |
          0 ≤ y (euclidean_half_slice_ambient_last_coordinate hk hkn)}).symm
  let projectedAsNested :
      {x : Set.euclideanSlice U k hkn c |
          0 ≤ x.1 (euclidean_half_slice_ambient_last_coordinate hk hkn)} ≃ₜ
        {u : {u : EuclideanSpace ℝ (Fin k) |
            euclidean_slice_inclusion hkn c u ∈ U} |
          0 ≤ u.1 (projected_last_coordinate hk)} :=
    (euclidean_slice_projection_homeomorph U hkn c).subtype fun x ↦ by
      change
        0 ≤ x.1 (euclidean_half_slice_ambient_last_coordinate hk hkn) ↔
          0 ≤ (euclidean_slice_projection hkn x.1) (projected_last_coordinate hk)
      rw [euclidean_slice_projection_last_coordinate hk hkn x.1]
  let reorderTarget :
      {u : {u : EuclideanSpace ℝ (Fin k) |
            euclidean_slice_inclusion hkn c u ∈ U} |
          0 ≤ u.1 (projected_last_coordinate hk)} ≃ₜ
        {u : {u : EuclideanSpace ℝ (Fin k) |
            0 ≤ u (projected_last_coordinate hk)} |
          euclidean_slice_inclusion hkn c u.1 ∈ U} := by
    let leftFlatten :
        {u : {u : EuclideanSpace ℝ (Fin k) |
              euclidean_slice_inclusion hkn c u ∈ U} |
            0 ≤ u.1 (projected_last_coordinate hk)} ≃ₜ
          ({u : EuclideanSpace ℝ (Fin k) |
              euclidean_slice_inclusion hkn c u ∈ U} ∩
            {u : EuclideanSpace ℝ (Fin k) |
              0 ≤ u (projected_last_coordinate hk)} : Set (EuclideanSpace ℝ (Fin k))) :=
      subtype_patch_intersection_homeomorph
        {u : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hkn c u ∈ U}
        {u : EuclideanSpace ℝ (Fin k) | 0 ≤ u (projected_last_coordinate hk)}
    let rightFlatten :
        {u : {u : EuclideanSpace ℝ (Fin k) |
              0 ≤ u (projected_last_coordinate hk)} |
            euclidean_slice_inclusion hkn c u.1 ∈ U} ≃ₜ
          ({u : EuclideanSpace ℝ (Fin k) |
              0 ≤ u (projected_last_coordinate hk)} ∩
            {u : EuclideanSpace ℝ (Fin k) |
              euclidean_slice_inclusion hkn c u ∈ U} : Set (EuclideanSpace ℝ (Fin k))) :=
      subtype_patch_intersection_homeomorph
        {u : EuclideanSpace ℝ (Fin k) | 0 ≤ u (projected_last_coordinate hk)}
        {u : EuclideanSpace ℝ (Fin k) | euclidean_slice_inclusion hkn c u ∈ U}
    exact leftFlatten.trans <|
      (Homeomorph.setCongr <| by
        ext u
        constructor <;> intro hu
        · exact ⟨hu.2, hu.1⟩
        · exact ⟨hu.2, hu.1⟩).trans rightFlatten.symm
  let halfSpaceAsNested :
      {u : {u : EuclideanSpace ℝ (Fin k) |
            0 ≤ u (projected_last_coordinate hk)} |
          euclidean_slice_inclusion hkn c u.1 ∈ U} ≃ₜ
        {z : EuclideanHalfSpace k |
          euclidean_slice_inclusion hkn c
            ((half_slice_last_coordinate_homeomorph hk).symm z).1 ∈ U} :=
    (half_slice_last_coordinate_homeomorph hk).subtype fun u ↦ by
      have hu :
          ((half_slice_last_coordinate_homeomorph hk).symm
            ((half_slice_last_coordinate_homeomorph hk) u)) = u :=
        (half_slice_last_coordinate_homeomorph hk).left_inv u
      change
        euclidean_slice_inclusion hkn c u.1 ∈ U ↔
          euclidean_slice_inclusion hkn c
            (((half_slice_last_coordinate_homeomorph hk).symm
              ((half_slice_last_coordinate_homeomorph hk) u)).1) ∈ U
      exact hu.symm ▸ Iff.rfl
  exact sourceAsSlice.trans <| projectedAsNested.trans <| reorderTarget.trans halfSpaceAsNested

/-- Helper for Theorem 5.51: a Euclidean `k`-dimensional half-slice carries the standard
boundary-model chart obtained by projecting the free coordinates and moving the constrained
coordinate to the half-space boundary coordinate. -/
noncomputable def euclidean_half_slice_projection_partial_homeomorph
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hk : 0 < k) (hkn : k ≤ n) (c : Fin (n - k) → ℝ)
    (x : Set.euclideanHalfSlice U k hk hkn c) :
    OpenPartialHomeomorph (Set.euclideanHalfSlice U k hk hkn c) (ℍ^{k}) := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k =>
      let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 1)) :=
        ⟨{z : EuclideanHalfSpace (k + 1) |
            euclidean_slice_inclusion hkn c
              ((half_slice_last_coordinate_homeomorph hk).symm z).1 ∈ U}, by
          have hcoord :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                ((half_slice_last_coordinate_homeomorph hk).symm z).1 :=
            continuous_subtype_val.comp
              (half_slice_last_coordinate_homeomorph hk).symm.continuous
          have hmap :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                euclidean_slice_inclusion hkn c
                  (((half_slice_last_coordinate_homeomorph hk).symm z).1) :=
            (euclidean_slice_inclusion_continuous hkn c).comp hcoord
          simpa [Set.preimage, Function.comp] using hU.preimage hmap⟩
      let xProjected :
          {u : EuclideanSpace ℝ (Fin (k + 1)) |
            0 ≤ u (projected_last_coordinate hk)} :=
        ⟨euclidean_slice_projection hkn x.1, by
          simpa [euclidean_slice_projection_last_coordinate hk hkn x.1] using x.2.2⟩
      let targetNonempty : Nonempty targetOpen := by
        refine ⟨⟨half_slice_last_coordinate_homeomorph hk xProjected, ?_⟩⟩
        have hxPerm :
            ((half_slice_last_coordinate_homeomorph hk).symm
              (half_slice_last_coordinate_homeomorph hk xProjected)) = xProjected :=
          (half_slice_last_coordinate_homeomorph hk).left_inv xProjected
        have hxInU : euclidean_slice_inclusion hkn c xProjected.1 ∈ U := by
          simpa [xProjected, euclidean_slice_inclusion_projection hkn c x.2.1] using x.2.1.1
        change euclidean_slice_inclusion hkn c
          (((half_slice_last_coordinate_homeomorph hk).symm
              (half_slice_last_coordinate_homeomorph hk xProjected)).1) ∈ U
        exact hxPerm.symm ▸ hxInU
      exact
        OpenPartialHomeomorph.trans'
          ((euclidean_half_slice_projection_homeomorph
            U hk hkn c).toOpenPartialHomeomorph)
          (targetOpen.openPartialHomeomorphSubtypeCoe targetNonempty)
          rfl

/-- Helper for Theorem 5.51: the distinguished center point used to build the Euclidean
half-slice chart lies in that chart's source. -/
theorem euclidean_half_slice_projection_partial_homeomorph_center_mem_source
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hk : 0 < k) (hkn : k ≤ n) (c : Fin (n - k) → ℝ)
    (x : Set.euclideanHalfSlice U k hk hkn c) :
    x ∈ (euclidean_half_slice_projection_partial_homeomorph U hU hk hkn c x).source := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k =>
      let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace (k + 1)) :=
        ⟨{z : EuclideanHalfSpace (k + 1) |
            euclidean_slice_inclusion hkn c
              ((half_slice_last_coordinate_homeomorph hk).symm z).1 ∈ U}, by
          have hcoord :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                ((half_slice_last_coordinate_homeomorph hk).symm z).1 :=
            continuous_subtype_val.comp
              (half_slice_last_coordinate_homeomorph hk).symm.continuous
          have hmap :
              Continuous fun z : EuclideanHalfSpace (k + 1) ↦
                euclidean_slice_inclusion hkn c
                  (((half_slice_last_coordinate_homeomorph hk).symm z).1) :=
            (euclidean_slice_inclusion_continuous hkn c).comp hcoord
          simpa [Set.preimage, Function.comp] using hU.preimage hmap⟩
      let xProjected :
          {u : EuclideanSpace ℝ (Fin (k + 1)) |
            0 ≤ u (projected_last_coordinate hk)} :=
        ⟨euclidean_slice_projection hkn x.1, by
          simpa [euclidean_slice_projection_last_coordinate hk hkn x.1] using x.2.2⟩
      let targetNonempty : Nonempty targetOpen := by
        refine ⟨⟨half_slice_last_coordinate_homeomorph hk xProjected, ?_⟩⟩
        have hxPerm :
            ((half_slice_last_coordinate_homeomorph hk).symm
              (half_slice_last_coordinate_homeomorph hk xProjected)) = xProjected :=
          (half_slice_last_coordinate_homeomorph hk).left_inv xProjected
        have hxInU : euclidean_slice_inclusion hkn c xProjected.1 ∈ U := by
          simpa [xProjected, euclidean_slice_inclusion_projection hkn c x.2.1] using x.2.1.1
        change euclidean_slice_inclusion hkn c
          (((half_slice_last_coordinate_homeomorph hk).symm
              (half_slice_last_coordinate_homeomorph hk xProjected)).1) ∈ U
        exact hxPerm.symm ▸ hxInU
      simpa [euclidean_half_slice_projection_partial_homeomorph, targetOpen, xProjected,
        targetNonempty]

end
