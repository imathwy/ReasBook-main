import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this environment; the canonical owners below were verified
-- directly against mathlib's `MulAction.orbit`, `MulAction.stabilizer`,
-- `MulAction.mem_stabilizer_iff`, and `ContMDiffSMul` APIs. The source-facing primitive data here
-- is the orbit map itself, which only needs the action map `SMul G M`; the orbit subset,
-- stabilizer, and smoothness statements are derived at the stronger canonical `MulAction` and
-- `ContMDiffSMul` layers.

open scoped ContDiff Manifold

universe u𝕜 uE uH uG uE' uH' uM

/-- Definition 7.50-extra-4. For a left `G`-action on `M` and a point `p : M`, the orbit map at
`p` is the map `g ↦ g • p` from `G` to `M`. The ambient group is an explicit owner parameter
because it is not recoverable from `p` alone. -/
abbrev orbit_map (G : Type uG) {M : Type uM} [SMul G M] (p : M) : G → M :=
  fun g ↦ g • p

section OrbitMapRange

variable {G : Type uG} {M : Type uM} [SMul G M]

/-- The image of the orbit map at `p` is exactly the orbit of `p`. -/
theorem range_orbit_map (p : M) :
    Set.range (orbit_map G p) = MulAction.orbit G p := rfl

end OrbitMapRange

section OrbitMapStabilizer

variable {G : Type uG} [Group G]
variable {M : Type uM} [MulAction G M]

/-- The preimage of `{p}` under the orbit map at `p` is the isotropy group (stabilizer) of `p`,
viewed as a subset of `G`. -/
theorem preimage_singleton_orbit_map_eq_stabilizer (p : M) :
    orbit_map G p ⁻¹' ({p} : Set M) = (MulAction.stabilizer G p : Set G) := by
  ext g
  simp [orbit_map, MulAction.mem_stabilizer_iff]

end OrbitMapStabilizer

section SmoothOrbitMap

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H}
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {J : ModelWithCorners 𝕜 E' H'}
variable [SMul G M]

/-- For a `C^∞` left action, each orbit map is smooth. -/
theorem orbitMap_contMDiff [ContMDiffSMul I J ∞ G M] (p : M) :
    ContMDiff I J ∞ (orbit_map G p) := by
  have h : ContMDiff I J ∞ (fun g : G ↦ g • p) :=
    contMDiff_id.smul contMDiff_const
  simpa [orbit_map] using h

end SmoothOrbitMap
