import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Example_4_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Torus

noncomputable section

/- Problem 4-4 is a bridge/view item, not a new owner: Example 4.20 already proved the canonical
topological statement that the torus curve has dense range, and `DenseRange f` is definitionally
the dense-image-set statement `Dense (Set.range f)`. -/
recall denseTorusCurve_denseRange (α : ℝ) (hα : Irrational α) :
    DenseRange (denseTorusCurve α)

section

variable (α : ℝ) (hα : Irrational α)

/- In the source wording, Problem 4-4 asks for density of the image subset itself; this is exactly
the set-valued view of the recalled dense-range theorem above. -/
#check (denseTorusCurve_denseRange α hα : Dense (Set.range (denseTorusCurve α) : Set (𝕋^{2})))

end
