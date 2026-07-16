import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_49
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_54

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

/-
Lemma 3.2.6 lies in the measure-theoretic convex-geometry domain of centroid halfspace cuts in a
real inner-product space.

Sampled owner-style declarations:
- `setAverage` / `setAverage_eq` in mathlib, the canonical normalized-average owner for centroids;
- `Convex.set_average_mem` in mathlib, the canonical centroid-membership lemma;
- `cuttingHalfspace` in `Definition_3_49`, the chapter owner for affine halfspace cuts.

Best owner abstraction:
- source-facing: the centroid-cut volume estimate for `S`;
- core/canonical: `setAverage`;
- bridge/view: `S ∩ cuttingHalfspace (⨍ x in S, x) g`.

Primitive data:
- a set `S : Set E`;
- a direction `g : E`.

Derived API:
- the centroid `⨍ x in S, x`;
- the centroid cut `S ∩ cuttingHalfspace (⨍ x in S, x) g`;
- textbook membership descriptions obtained directly from the owner theorem
  `mem_cuttingHalfspace_iff`.

The present item stays at the intrinsic finite-dimensional owner level rather than at the
coordinate model `EuclideanSpace ℝ (Fin n)`: the centroid itself is expressed directly through the
canonical set-average owner, while the theorem surface is the chapter's centroid-cut volume
estimate. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local instance instMeasurableSpaceLemma326 : MeasurableSpace E := borel E
local instance instBorelSpaceLemma326 : BorelSpace E := ⟨rfl⟩

/-- Lemma 3.2.6 at the intrinsic owner level: if `S ⊆ E` is convex with positive finite volume in
a finite-dimensional real inner-product space and `g` is nonzero, then the centroid cut
`S₊ = S ∩ cuttingHalfspace (⨍ x in S, x) g = {x ∈ S | ⟨g, (⨍ x in S, x) - x⟩ ≥ 0}` has relative
volume at most `1 - 1 / e`. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook
`ℝⁿ` statement. -/
-- Proof sketch: this is Grünbaum's centroid halfspace inequality for convex bodies. Apply the
-- centroid-cut volume estimate to the convex set `S` and the nonzero direction `g`, then rewrite
-- the conclusion using the owner membership theorem `mem_cuttingHalfspace_iff` and real-valued
-- Lebesgue volumes.
theorem centerOfGravityCut_volumeRatio_le_one_sub_inv_e
    (S : Set E) (g : E) (hS_convex : Convex ℝ S) (hS_finite : volume S ≠ ⊤)
    (hS_pos : volume S ≠ 0) (hg : g ≠ 0) :
    (volume (S ∩ cuttingHalfspace (⨍ x in S, x) g)).toReal / (volume S).toReal ≤
      1 - 1 / Real.exp 1 := sorry

end
