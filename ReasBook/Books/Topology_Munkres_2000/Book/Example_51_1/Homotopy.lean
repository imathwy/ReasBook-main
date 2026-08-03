module

public import Mathlib.Topology.Homotopy.Affine

@[expose] public section

open Set unitInterval

universe u

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]

namespace Path.Homotopy

variable {x₀ x₁ : E} (p q : Path x₀ x₁)

/-- The affine homotopy between paths with common endpoints is fixed on those endpoints. -/
theorem affine_fixed (t : unitInterval) (x : unitInterval)
    (hx : x ∈ ({0, 1} : Set unitInterval)) :
    ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap (t, x) = p x := by
  -- Split the distinguished path parameter into the source and target cases.
  rcases hx with hx | hx
  · subst x
    simp only [ContinuousMap.Homotopy.affine_apply, Path.coe_toContinuousMap,
      Path.source, AffineMap.lineMap_same_apply]
  · rw [Set.mem_singleton_iff] at hx
    subst x
    simp only [ContinuousMap.Homotopy.affine_apply, Path.coe_toContinuousMap,
      Path.target, AffineMap.lineMap_same_apply]

/-- The straight-line homotopy between two paths with common endpoints. -/
def affine : p.Homotopy q where
  toHomotopy := ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap
  prop' := affine_fixed p q

/-- The value of the straight-line homotopy between two paths. -/
theorem affine_apply (z : unitInterval × unitInterval) :
    affine p q z = AffineMap.lineMap (p z.2) (q z.2) (z.1 : ℝ) := by
  -- Expose the computation rule inherited from the ambient affine homotopy.
  exact ContinuousMap.Homotopy.affine_apply p.toContinuousMap q.toContinuousMap z

end Path.Homotopy

namespace Convex

variable {s : Set E} (hconv : Convex ℝ s) {x₀ x₁ : s} (p q : Path x₀ x₁)

include hconv

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The ambient affine interpolation point of two paths in a convex set lies in the set. -/
theorem pathHomotopy_mem (z : unitInterval × unitInterval) :
    AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ) ∈ s := by
  -- Apply convexity to the two path values and the unit-interval coefficient.
  exact hconv.lineMap_mem (p z.2).property (q z.2).property z.1.property

/-- The subtype-valued affine interpolation between two paths in a convex set is continuous. -/
theorem continuous_pathHomotopy : Continuous fun z : unitInterval × unitInterval ↦
    (⟨AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ),
      pathHomotopy_mem hconv p q z⟩ : s) := by
  -- Lift continuity of the ambient line-map formula to the convex subtype.
  apply Continuous.subtype_mk
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- At time zero, affine interpolation in a convex set equals the first path. -/
theorem pathHomotopy_zero (x : unitInterval) :
    (⟨AffineMap.lineMap (p x).1 (q x).1 (0 : ℝ),
      pathHomotopy_mem hconv p q (0, x)⟩ : s) = p x := by
  -- Equality in the subtype follows from the time-zero line-map computation.
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero (p x).1 (q x).1

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- At time one, affine interpolation in a convex set equals the second path. -/
theorem pathHomotopy_one (x : unitInterval) :
    (⟨AffineMap.lineMap (p x).1 (q x).1 (1 : ℝ),
      pathHomotopy_mem hconv p q (1, x)⟩ : s) = q x := by
  -- Equality in the subtype follows from the time-one line-map computation.
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one (p x).1 (q x).1

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Affine interpolation between paths in a convex set fixes their common endpoints. -/
theorem pathHomotopy_fixed (t : unitInterval) (x : unitInterval)
    (hx : x ∈ ({0, 1} : Set unitInterval)) :
    (⟨AffineMap.lineMap (p x).1 (q x).1 (t : ℝ),
      pathHomotopy_mem hconv p q (t, x)⟩ : s) = p x := by
  -- At either path endpoint, both input paths have the same subtype value.
  rcases hx with hx | hx
  · subst x
    apply Subtype.ext
    simp only [Path.source, AffineMap.lineMap_same_apply]
  · rw [Set.mem_singleton_iff] at hx
    subst x
    apply Subtype.ext
    simp only [Path.target, AffineMap.lineMap_same_apply]

/-- The straight-line homotopy between two paths in a convex set. -/
def pathHomotopy : p.Homotopy q where
  toHomotopy :=
    { toFun := fun z ↦
        ⟨AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ),
          pathHomotopy_mem hconv p q z⟩
      continuous_toFun := continuous_pathHomotopy hconv p q
      map_zero_left := pathHomotopy_zero hconv p q
      map_one_left := pathHomotopy_one hconv p q }
  prop' := pathHomotopy_fixed hconv p q

/-- The ambient value of the straight-line homotopy inside a convex set. -/
theorem pathHomotopy_apply (z : unitInterval × unitInterval) :
    (pathHomotopy hconv p q z).1 =
      AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ) := by
  -- Projecting the constructed subtype-valued homotopy gives its ambient formula.
  rfl

end Convex
