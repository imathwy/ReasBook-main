module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Affine

public section

open Set

/-- An oriented nondegenerate line segment, specified by its ordered endpoints. -/
structure OrientedSegment (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  initial : E
  final : E
  ne : initial ≠ final

namespace OrientedSegment

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The underlying unoriented geometric segment. -/
@[expose]
def carrier (L : OrientedSegment E) : Set E :=
  segment ℝ L.initial L.final

/-- The initial endpoint belongs to the oriented segment. -/
theorem initial_mem (L : OrientedSegment E) : L.initial ∈ L.carrier := by
  -- The initial endpoint is the left endpoint of the underlying segment.
  exact left_mem_segment ℝ L.initial L.final

/-- The final endpoint belongs to the oriented segment. -/
theorem final_mem (L : OrientedSegment E) : L.final ∈ L.carrier := by
  -- The final endpoint is the right endpoint of the underlying segment.
  exact right_mem_segment ℝ L.initial L.final

/-- The same geometric segment with the opposite orientation. -/
def reverse (L : OrientedSegment E) : OrientedSegment E where
  initial := L.final
  final := L.initial
  ne := L.ne.symm

/-- Reversal exchanges the initial and final endpoints. -/
theorem reverse_initial (L : OrientedSegment E) : L.reverse.initial = L.final := by
  -- This projection is fixed by the definition of reversal.
  rfl

/-- Reversal exchanges the final and initial endpoints. -/
theorem reverse_final (L : OrientedSegment E) : L.reverse.final = L.initial := by
  -- This projection is fixed by the definition of reversal.
  rfl

/-- Reversing an oriented segment twice returns the original orientation. -/
theorem reverse_reverse (L : OrientedSegment E) : L.reverse.reverse = L := by
  -- Both endpoint swaps cancel; proof irrelevance identifies the nondegeneracy fields.
  cases L
  rfl

/-- Reversal does not change the underlying geometric segment. -/
theorem carrier_reverse (L : OrientedSegment E) : L.reverse.carrier = L.carrier := by
  -- The unoriented segment is symmetric in its endpoints.
  exact segment_symm ℝ L.final L.initial

/-- Helper for Definition 74.2: affine interpolation stays in the segment carrier. -/
lemma lineMap_mem_carrier (L : OrientedSegment E) (s : unitInterval) :
    AffineMap.lineMap L.initial L.final (s : ℝ) ∈ L.carrier := by
  -- Unit-interval membership is exactly the side condition for `lineMap_mem_segment`.
  exact lineMap_mem_segment ℝ L.initial L.final s.property

/-- The point of an oriented segment with affine parameter `s ∈ unitInterval`. -/
-- The preceding membership lemma supplies the construction's proof field.
def point (L : OrientedSegment E) (s : unitInterval) : L.carrier :=
  ⟨AffineMap.lineMap L.initial L.final (s : ℝ), L.lineMap_mem_carrier s⟩

/-- The underlying point of `L.point s` is the usual affine interpolation. -/
theorem point_coe (L : OrientedSegment E) (s : unitInterval) :
    (L.point s : E) = AffineMap.lineMap L.initial L.final (s : ℝ) := by
  -- Coercing the subtype construction exposes its affine interpolation value.
  rfl

/-- Helper for Definition 74.2: normalized distance recovers the affine parameter. -/
lemma normalizedDistance_lineMap (L : OrientedSegment E) (s : ℝ) (hs : s ∈ unitInterval) :
    ‖AffineMap.lineMap L.initial L.final s - L.initial‖ /
      ‖L.final - L.initial‖ = s := by
  -- Nondegenerate endpoints make the normalization denominator nonzero.
  have hdisplacement : L.final - L.initial ≠ 0 := sub_ne_zero.mpr L.ne.symm
  have hnorm : ‖L.final - L.initial‖ ≠ 0 := norm_ne_zero_iff.mpr hdisplacement
  -- The line-map displacement is scalar multiplication by `s`, so its norm cancels.
  rw [← vsub_eq_sub, AffineMap.lineMap_vsub_left, vsub_eq_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs.1, mul_div_cancel_right₀ _ hnorm]

/-- Helper for Definition 74.2: normalized distance of a segment point lies in `unitInterval`. -/
lemma normalizedDistance_mem_unitInterval (L : OrientedSegment E) (x : L.carrier) :
    ‖(x : E) - L.initial‖ / ‖L.final - L.initial‖ ∈ unitInterval := by
  -- Segment membership supplies an affine parameter in the unit interval.
  have hx : (x : E) ∈
      AffineMap.lineMap L.initial L.final '' Set.Icc (0 : ℝ) 1 := by
    rw [← segment_eq_image_lineMap ℝ L.initial L.final]
    exact x.property
  obtain ⟨s, hs, hsx⟩ := hx
  -- The normalized-distance formula transfers the witness's interval bounds.
  rw [← hsx, L.normalizedDistance_lineMap s hs]
  exact hs

/-- The affine parameter of a point of an oriented segment. -/
-- The interval-bound helper supplies the construction's proof field.
noncomputable def parameter (L : OrientedSegment E) (x : L.carrier) : unitInterval :=
  ⟨‖(x : E) - L.initial‖ / ‖L.final - L.initial‖,
    L.normalizedDistance_mem_unitInterval x⟩

/-- The affine parameter is the normalized distance from the initial endpoint. -/
theorem parameter_coe (L : OrientedSegment E) (x : L.carrier) :
    (L.parameter x : ℝ) = ‖(x : E) - L.initial‖ / ‖L.final - L.initial‖ := by
  -- Coercing the subtype construction exposes its normalized-distance value.
  rfl

/-- Recovering the parameter of an affinely parameterized point is the identity. -/
theorem parameter_point (L : OrientedSegment E) (s : unitInterval) :
    L.parameter (L.point s) = s := by
  -- Equality in `unitInterval` follows from the normalized-distance computation.
  apply Subtype.ext
  rw [L.parameter_coe, L.point_coe,
    L.normalizedDistance_lineMap (s : ℝ) s.property]

/-- Helper for Definition 74.2: every carrier point has an affine unit-interval parameter. -/
lemma point_surjective (L : OrientedSegment E) : Function.Surjective L.point := by
  intro x
  -- Rewrite carrier membership as membership in the image of the line map.
  have hx : (x : E) ∈
      AffineMap.lineMap L.initial L.final '' Set.Icc (0 : ℝ) 1 := by
    rw [← segment_eq_image_lineMap ℝ L.initial L.final]
    exact x.property
  obtain ⟨s, hs, hsx⟩ := hx
  let t : unitInterval := ⟨s, hs⟩
  refine ⟨t, ?_⟩
  -- Subtype extensionality reduces the claim to the affine witness equation.
  apply Subtype.ext
  rw [L.point_coe]
  exact hsx

/-- Reconstructing a segment point from its affine parameter is the identity. -/
theorem point_parameter (L : OrientedSegment E) (x : L.carrier) :
    L.point (L.parameter x) = x := by
  -- Surjectivity reduces to a parameterized point, where the left inverse applies.
  obtain ⟨s, rfl⟩ := L.point_surjective x
  rw [L.parameter_point]

/-- Affine parameterization is continuous. -/
theorem continuous_point (L : OrientedSegment E) : Continuous L.point := by
  -- It suffices to check continuity after coercing from the segment subtype.
  refine continuous_induced_rng.2 ?_
  have hline : Continuous (fun s : unitInterval ↦
      AffineMap.lineMap L.initial L.final (s : ℝ)) :=
    ((AffineMap.lineMap_continuous :
      Continuous (AffineMap.lineMap L.initial L.final)).comp continuous_subtype_val)
  -- Pointwise identification with the coercion of `point` finishes the subtype bridge.
  exact hline.congr fun s ↦ (L.point_coe s).symm

/-- The affine parameter varies continuously along a nondegenerate segment. -/
theorem continuous_parameter (L : OrientedSegment E) : Continuous L.parameter := by
  -- The ambient normalized-distance function is a composition of continuous operations.
  refine continuous_induced_rng.2 ?_
  have hnormalized : Continuous (fun x : L.carrier ↦
      ‖(x : E) - L.initial‖ / ‖L.final - L.initial‖) :=
    (continuous_norm.comp (continuous_subtype_val.sub continuous_const)).div_const
      ‖L.final - L.initial‖
  -- Pointwise identification with the coercion of `parameter` finishes the subtype bridge.
  exact hnormalized.congr fun x ↦ (L.parameter_coe x).symm

/-- The canonical homeomorphism from the unit interval to an oriented segment. -/
noncomputable def paramHomeomorph (L : OrientedSegment E) :
    unitInterval ≃ₜ L.carrier where
  toEquiv :=
    { toFun := L.point
      invFun := L.parameter
      left_inv := L.parameter_point
      right_inv := L.point_parameter }
  continuous_toFun := L.continuous_point
  continuous_invFun := L.continuous_parameter

/-- The canonical parameter homeomorphism agrees with affine interpolation. -/
theorem paramHomeomorph_apply (L : OrientedSegment E) (s : unitInterval) :
    (L.paramHomeomorph s : E) = AffineMap.lineMap L.initial L.final (s : ℝ) := by
  -- Unfold this owner-side specification once to expose the affine point map.
  unfold paramHomeomorph
  exact L.point_coe s


end OrientedSegment
