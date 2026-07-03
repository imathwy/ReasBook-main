import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_16_extra_1 (from Chap03/Sec03_16) -/
open Bundle

section

universe u_𝕜 u_E u_H u_M

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type u_H} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M]

/- Definition 3.16-extra-1: the tangent bundle `TM` of a manifold `M` modeled by `I` is the
canonical bundle total space `TangentBundle I M`, i.e. `Bundle.TotalSpace` specialized to the
family `p ↦ TangentSpace I p`; an element is written as a pair `⟨p, v⟩` with
`v : TangentSpace I p`. -/
recall TangentBundle (I : ModelWithCorners 𝕜 E H) (M : Type u_M)
    [TopologicalSpace M] [ChartedSpace H M] : Type _

/- The tangent-bundle projection is the generic bundle projection `TotalSpace.proj`. -/
#check (TotalSpace.proj : TangentBundle I M → M)

end

/-! ### Definition_3_16_extra_3 (from Chap03/Sec03_16) -/
section

universe u_𝕜 u_E u_E' u_H u_H' u_M u_M'

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type u_E'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type u_H} [TopologicalSpace H]
variable {H' : Type u_H'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type u_M'} [TopologicalSpace M'] [ChartedSpace H' M']

/- Definition 3.16-extra-3: the global differential of a map `F : M → M'` is the canonical map
between tangent bundles `tangentMap I I' F : TangentBundle I M → TangentBundle I' M'`, whose
restriction to each tangent space `TangentSpace I p` is the differential at `p`. -/
#check (tangentMap I I' : (M → M') → TangentBundle I M → TangentBundle I' M')

/- The pointwise evaluation formula expresses that for `v ∈ TangentSpace I p`, applying the global
map `tangentMap I I' F` to `⟨p, v⟩` gives the vector `(mfderiv I I' F p) v` in the tangent space at
`F p`. -/
#check tangentMap_snd

end

/-! ### Example_3_16 (from Chap03/Sec03_15) -/
/-- Example 3.16: at the polar point `(2, π / 2)`, the polar-coordinate tangent vector
`3 ∂/∂r - ∂/∂θ` has standard-coordinate components `(2, 3)`. -/
-- Proof sketch: unfold mathlib's owner `fderivPolarCoordSymm`, evaluate the resulting matrix on
-- `(3, -1)`, and simplify using `Real.cos_pi_div_two` and `Real.sin_pi_div_two`.
theorem polar_vector_in_standard_coordinates :
    fderivPolarCoordSymm (2, Real.pi / 2) (3, -1) = (2, 3) := by
  -- Expand the derivative into the explicit Jacobian action on pairs.
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  -- Evaluate the trigonometric entries at `π / 2` and simplify the resulting coordinates.
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
