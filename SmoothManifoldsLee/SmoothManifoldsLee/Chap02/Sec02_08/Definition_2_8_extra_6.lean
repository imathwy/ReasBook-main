import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

-- Declarations for this item will be appended below by the statement pipeline.

open Set

/- Definition 2.8-extra-6 (source-facing recall): for charts `φ` on the source and `ψ` on the
target, the coordinate representation of `F` is the chart-written map `ψ ∘ F ∘ φ.symm`; when one
uses model-with-corners extensions to express smoothness, the canonical owner is
`ψ.extend J ∘ F ∘ (φ.extend I).symm`, with owner theorems
`OpenPartialHomeomorph.continuousOn_writtenInExtend_iff` and
`OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff`. -/
section

universe u𝕜 uE uE' uM uN uH uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {M : Type uM} [TopologicalSpace M]
variable {N : Type uN} [TopologicalSpace N]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}

/-- Definition 2.8-extra-6: the coordinate representation of a map `F : M → N` in charts `φ`
and `ψ` is the chart-written map `ψ ∘ F ∘ φ.symm`. -/
abbrev coordinate_representation (F : M → N) (φ : OpenPartialHomeomorph M H)
    (ψ : OpenPartialHomeomorph N G) : H → G :=
  ψ ∘ F ∘ φ.symm

/-- Helper for Definition 2.8-extra-6: on the overlap of the chart domains, evaluating the
coordinate representation at the chart coordinate `φ x` recovers `ψ (F x)`. -/
lemma coordinate_representation_apply_chart
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G)
    {x : M} (hx : x ∈ φ.source ∩ F ⁻¹' ψ.source) :
    coordinate_representation F φ ψ (φ x) = ψ (F x) := by
  -- Unfold the conjugated map and use that `φ.symm` inverts `φ` on the chart source.
  rcases hx with ⟨hxφ, _⟩
  simp [coordinate_representation, φ.left_inv hxφ]

/-- Helper for Definition 2.8-extra-6: the coordinate representation sends the chart image of
`φ.source ∩ F ⁻¹' ψ.source` into the chart image `ψ '' ψ.source`. -/
lemma coordinate_representation_mapsTo_image
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G) :
    MapsTo (coordinate_representation F φ ψ)
      (φ '' (φ.source ∩ F ⁻¹' ψ.source)) (ψ '' ψ.source) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Rewrite the written-in-coordinates value back to the concrete point `F x`.
  refine ⟨F x, hx.2, ?_⟩
  simpa using (coordinate_representation_apply_chart F φ ψ hx).symm

/-- Helper for Definition 2.8-extra-6: rewriting the codomain image as the chart target gives the
usual `MapsTo` formulation for the coordinate representation. -/
lemma coordinate_representation_mapsTo_target
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G) :
    MapsTo (coordinate_representation F φ ψ)
      (φ '' (φ.source ∩ F ⁻¹' ψ.source)) ψ.target := by
  intro y hy
  -- First land in `ψ '' ψ.source`, then rewrite that image as the chart target.
  have hy' := coordinate_representation_mapsTo_image F φ ψ hy
  simpa [ψ.image_source_eq_target] using hy'

/-- Helper for Definition 2.8-extra-6: the extended coordinate representation used by the
manifold smoothness API sends the same overlap to the extended target chart. -/
lemma extended_coordinate_representation_mapsTo
    (F : M → N) (φ : OpenPartialHomeomorph M H) (ψ : OpenPartialHomeomorph N G) :
    MapsTo (ψ.extend J ∘ F ∘ (φ.extend I).symm)
      ((φ.extend I) '' (φ.source ∩ F ⁻¹' ψ.source)) (ψ.extend J).target := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Route correction: rewrite through the extended source inverse before applying the target chart.
  have hFx : F x ∈ (ψ.extend J).source := by
    simpa [ψ.extend_source (I := J)] using hx.2
  have hxchart : φ.symm (φ x) = x :=
    φ.left_inv hx.1
  -- After reducing the source-side extension, the target-side extension maps into its target.
  simpa [Function.comp_apply, hxchart] using
    (ψ.extend J).mapsTo hFx

end
