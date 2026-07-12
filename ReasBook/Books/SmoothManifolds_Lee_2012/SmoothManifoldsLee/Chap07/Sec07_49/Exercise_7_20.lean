import Mathlib
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Example_7_19
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Theorem_7_21

-- Declarations for this item will be appended below by the statement pipeline.

open Topology Manifold
open scoped LieGroup Manifold ContDiff Torus

noncomputable section

local notation "T3Model" => ModelWithCorners.pi (fun _ : Fin 3 ↦ 𝓡 1)

-- `lean_leansearch` was unavailable in this session, so the statement surfaces below were fixed by
-- local inspection of `Example_7_19`, the local `LieSubgroup` owner, `Theorem_7_21`, and the
-- set-level owner `Set.IsProperlyEmbedded`.

/-- The coordinate-plane embedding `𝕋² ↪ 𝕋³` obtained by fixing the third circle coordinate to
`1`. -/
def torus_coordinate_plane_embedding : 𝕋^{2} → 𝕋^{3} :=
  fun z ↦ ![z 0, z 1, 1]

/-- The image of the dense torus curve in `𝕋³`, obtained by composing with the coordinate-plane
embedding. -/
def torusSlopeCurveInT3 (α : ℝ) : ℝ → 𝕋^{3} :=
  fun t ↦ torus_coordinate_plane_embedding (torusSlopeCurve α t)

/-- The coordinate two-torus in `𝕋³` cut out by the equation `z₂ = 1`. -/
def torus_coordinate_plane : Set (𝕋^{3}) :=
  { z | z 2 = 1 }

/-- The identity element of `𝕋³` lies in the coordinate two-torus `z₂ = 1`. -/
theorem one_mem_torus_coordinate_plane :
    (1 : 𝕋^{3}) ∈ torus_coordinate_plane := sorry

/-- The coordinate two-torus `z₂ = 1` is closed under multiplication. -/
theorem mul_mem_torus_coordinate_plane {z w : 𝕋^{3}}
    (hz : z ∈ torus_coordinate_plane) (hw : w ∈ torus_coordinate_plane) :
    z * w ∈ torus_coordinate_plane := sorry

/-- The coordinate two-torus `z₂ = 1` is closed under inversion. -/
theorem inv_mem_torus_coordinate_plane {z : 𝕋^{3}} (hz : z ∈ torus_coordinate_plane) :
    z⁻¹ ∈ torus_coordinate_plane := sorry

/-- The coordinate two-torus `z₂ = 1` is a subgroup of `𝕋³`. -/
def torus_coordinate_plane_subgroup : Subgroup (𝕋^{3}) where
  carrier := torus_coordinate_plane
  one_mem' := one_mem_torus_coordinate_plane
  mul_mem' := fun {_ _} ↦ mul_mem_torus_coordinate_plane
  inv_mem' := fun {_} ↦ inv_mem_torus_coordinate_plane

/-- Exercise 7.20 (1): for irrational `α`, the image `S` of the subgroup from Example 7.19 under
the obvious embedding `𝕋² ↪ 𝕋³` is an immersed Lie subgroup of `𝕋³`. -/
theorem torusSlopeCurveInT3_range_has_immersed_lie_subgroup_structure
    (α : ℝ) (hα : Irrational α) :
    ∃ K : LieSubgroup T3Model,
      (K.carrier : Set (𝕋^{3})) = Set.range (torusSlopeCurveInT3 α) := sorry

/-- Exercise 7.20 (2): for irrational `α`, the image `S ⊆ 𝕋³` of the dense torus curve from
Example 7.19 is not closed in `𝕋³`. -/
theorem torusSlopeCurveInT3_range_not_closed (α : ℝ) (hα : Irrational α) :
    ¬ IsClosed (Set.range (torusSlopeCurveInT3 α) : Set (𝕋^{3})) := sorry

/-- Exercise 7.20 (3): for irrational `α`, any Lie subgroup structure on the carrier `S` from
part (1) is not embedded; equivalently, its inclusion into `𝕋³` is not a smooth embedding. -/
theorem torusSlopeCurveInT3_range_not_embedded
    (α : ℝ) (hα : Irrational α)
    (K : LieSubgroup T3Model)
    (hK : (K.carrier : Set (𝕋^{3})) = Set.range (torusSlopeCurveInT3 α)) :
    ¬ IsSmoothEmbedding (modelWithCornersSelf ℝ K.ModelSpace) T3Model ∞
      (Subtype.val : K.carrier → 𝕋^{3}) :=
  sorry

/-- Exercise 7.20 (4): for irrational `α`, the image `S ⊆ 𝕋³` is not dense in `𝕋³`. -/
theorem torusSlopeCurveInT3_range_not_dense (α : ℝ) (hα : Irrational α) :
    ¬ Dense (Set.range (torusSlopeCurveInT3 α) : Set (𝕋^{3})) := sorry

/-- Exercise 7.20 (5): for irrational `α`, the closure of `S` in `𝕋³` is the coordinate two-torus
`{z : 𝕋³ | z 2 = 1}`. -/
theorem closure_torusSlopeCurveInT3_range_eq_torus_coordinate_plane
    (α : ℝ) (hα : Irrational α) :
    closure (Set.range (torusSlopeCurveInT3 α)) =
      (torus_coordinate_plane_subgroup : Set (𝕋^{3})) := sorry

/-- Exercise 7.20 (6): the closure of `S` is a properly embedded Lie subgroup of `𝕋³`; more
precisely, the coordinate two-torus `z₂ = 1` admits a Lie-group structure whose inclusion into
`𝕋³` is a smooth embedding and hence properly embedded. -/
theorem torus_coordinate_plane_subgroup_has_properly_embedded_lie_subgroup_structure :
    ∃ K : LieSubgroup T3Model,
      K.carrier = torus_coordinate_plane_subgroup ∧
        IsSmoothEmbedding (modelWithCornersSelf ℝ K.ModelSpace) T3Model ∞
          (Subtype.val : K.carrier → 𝕋^{3}) ∧
        (torus_coordinate_plane_subgroup : Set (𝕋^{3})).IsProperlyEmbedded := sorry
