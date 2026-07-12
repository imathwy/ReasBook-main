import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

/-- The vector field `d/dt` on `ℝ`, represented by the constant unit tangent vector under the
canonical identification `Tₜℝ ≃ ℝ`. -/
def example_8_17_d_dt (t : ℝ) : TangentSpace 𝓘(ℝ) t :=
  (fromTangentSpace t).symm 1
