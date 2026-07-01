import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- Declarations for this item will be appended below by the statement pipeline.

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
