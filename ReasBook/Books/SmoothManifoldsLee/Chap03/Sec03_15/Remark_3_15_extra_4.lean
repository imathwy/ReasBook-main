import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle
open scoped Manifold

section

universe u_𝕜 u_E u_H u_M

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type u_H} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/- Remark 3.15-extra-4: in mathlib, the change-of-coordinates rule for tangent vectors is packaged
by `tangentCoordChange I x y z`. The theorem `tangentCoordChange_def` identifies this linear map
with the derivative of the chart transition map `extChartAt I y ∘ (extChartAt I x).symm`, which is
the basis-free form of equation (3.11); applying this linear map to a coordinate vector gives the
component transformation law (3.12). -/
#check tangentCoordChange_def

/-- Changing tangent coordinates from the chart centered at `x` to the chart centered at `y` is
given by the tangent coordinate change linear map. -/
  theorem tangent_coordinates_change
    {x y z : M} (hxy : z ∈ (chartAt H x).source ∩ (chartAt H y).source) :
    (trivializationAt E (TangentSpace I) x).coordChangeL 𝕜
        (trivializationAt E (TangentSpace I) y) z =
      tangentCoordChange I x y z := by
  ext v
  simpa [tangentCoordChange] using
    (tangentBundleCore I M).trivializationAt_coordChange_eq hxy v

end
