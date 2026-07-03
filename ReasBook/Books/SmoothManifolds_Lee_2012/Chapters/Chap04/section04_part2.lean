import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_4_4 (from Chap04/Sec04_27) -/
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
