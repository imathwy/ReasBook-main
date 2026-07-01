import Mathlib
import cartan.VI.section26.«0001_Definition_VI_5_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe u v

-- Domain sampling: the primary domain here is one-dimensional complex manifolds together with
-- local-homeomorphism / covering-space maps over a base surface. The relevant owner declarations
-- inspected before this refinement were:
-- * the chapter-local owner `RiemannSurfaceOver` from `0001_Definition_VI_5_extra_1.lean`,
--   which already packages the genuine Riemann-surface semantics over a base;
-- * mathlib's `IsLocalHomeomorph.localInverseAt`, which provides the local inverse used to pull
--   back the base charts to the total space;
-- * mathlib's `IsCoveringMap.isLocalHomeomorph`, which shows that covering maps live naturally in
--   the same topological primitive data.
-- Primitive data in this file is only the total-space topology and the local-homeomorphism
-- projection to the base, packaged as `UnramifiedSurfaceOver`. The connected Hausdorff
-- refinement is the source-facing owner `ConnectedHausdorffUnramifiedSurfaceOver`; the genuine
-- Riemann-surface semantics are derived from that owner through its induced manifold instances and
-- the canonical bridge `ConnectedHausdorffUnramifiedSurfaceOver.toRiemannSurfaceOver`, whose
-- nonconstancy field is derived from the local-homeomorphism/chart data rather than stored as
-- extra primitive input.

/-- A surface over `Y` is represented by a topological space equipped with a projection to `Y`
that is locally a homeomorphism. This is the primitive topological owner used by the local
unramified-surface API in this chapter. -/
structure UnramifiedSurfaceOver (Y : Type v) [TopologicalSpace Y] where
  carrier : Type u
  topology : TopologicalSpace carrier
  projection : carrier → Y
  isLocalHomeomorph : IsLocalHomeomorph projection

namespace UnramifiedSurfaceOver

/-- An unramified surface over `Y` coerces to its total space. -/
instance {Y : Type v} [TopologicalSpace Y] :
    CoeSort (UnramifiedSurfaceOver Y) (Type u) where
  coe X := X.carrier

attribute [instance] topology

/-- Pull back the base complex charts along the local homeomorphism `projection`. -/
noncomputable instance chartedSpace
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] (X : UnramifiedSurfaceOver Y) :
    ChartedSpace ℂ X where
  atlas := {e | ∃ x : X,
    e = (X.isLocalHomeomorph.localInverseAt x).symm.trans (chartAt ℂ (X.projection x))}
  chartAt x := (X.isLocalHomeomorph.localInverseAt x).symm.trans (chartAt ℂ (X.projection x))
  mem_chart_source x := by
    simp [X.isLocalHomeomorph.self_mem_localInverseAt_target]
  chart_mem_atlas x := ⟨x, rfl⟩

-- The next helpers implement the pulled-back atlas argument for Definition VI.5-extra-2.
/-- Helper for Definition VI.5-extra-2: overlap maps between two local inverse branches of the
projection are restrictions of the identity on their common source. -/
lemma localInverse_transition_eqOnSource_ofSet
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (X : UnramifiedSurfaceOver Y) (x x' : X) :
    let e := X.isLocalHomeomorph.localInverseAt x
    let e' := X.isLocalHomeomorph.localInverseAt x'
    e.trans e'.symm ≈
      OpenPartialHomeomorph.ofSet (e.trans e'.symm).source (e.trans e'.symm).open_source := by
  intro e e'
  -- The transition is `projection ∘ localInverseAt`, so it is the identity wherever it is defined.
  refine ⟨rfl, ?_⟩
  intro y hy
  change e'.symm (e y) = y
  simpa [e', X.isLocalHomeomorph.localInverseAt_symm] using
    X.isLocalHomeomorph.apply_localInverseAt_of_mem (x := x) hy.1

/-- Helper for Definition VI.5-extra-2: every pulled-back chart transition is a `C^1`
coordinate change because it is a restriction of the corresponding base-chart transition. -/
lemma pulled_back_chart_transition_mem_contDiffGroupoid
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : UnramifiedSurfaceOver Y) {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X) :
    e.symm.trans e' ∈ contDiffGroupoid 1 𝓘(ℂ) := by
  rcases he with ⟨x, rfl⟩
  rcases he' with ⟨x', rfl⟩
  let lx := X.isLocalHomeomorph.localInverseAt x
  let lx' := X.isLocalHomeomorph.localInverseAt x'
  let cy := chartAt ℂ (X.projection x)
  let cy' := chartAt ℂ (X.projection x')
  have hbase : cy.symm.trans cy' ∈ contDiffGroupoid 1 𝓘(ℂ) :=
    HasGroupoid.compatible (chart_mem_atlas ℂ (X.projection x)) (chart_mem_atlas ℂ (X.projection x'))
  have hmid : lx.trans lx'.symm ≈
      OpenPartialHomeomorph.ofSet (lx.trans lx'.symm).source (lx.trans lx'.symm).open_source :=
    X.localInverse_transition_eqOnSource_ofSet x x'
  have hleft : cy.symm.trans (lx.trans lx'.symm) ≈
      cy.symm.trans
        (OpenPartialHomeomorph.ofSet (lx.trans lx'.symm).source (lx.trans lx'.symm).open_source) :=
    OpenPartialHomeomorph.EqOnSource.trans'
      (OpenPartialHomeomorph.eqOnSource_refl (e := cy.symm)) hmid
  have hcomp : (cy.symm.trans (lx.trans lx'.symm)).trans cy' ≈
      (cy.symm.trans
        (OpenPartialHomeomorph.ofSet (lx.trans lx'.symm).source (lx.trans lx'.symm).open_source)).trans
          cy' :=
    OpenPartialHomeomorph.EqOnSource.trans'
      hleft (OpenPartialHomeomorph.eqOnSource_refl (e := cy'))
  have hofset :
      (OpenPartialHomeomorph.ofSet (lx.trans lx'.symm).source (lx.trans lx'.symm).open_source).trans cy' =
        cy'.restr (lx.trans lx'.symm).source := by
    simpa using
      (OpenPartialHomeomorph.ofSet_trans (e := cy') (s := (lx.trans lx'.symm).source)
        (lx.trans lx'.symm).open_source)
  have hrestr0 : cy.symm.trans (cy'.restr (lx.trans lx'.symm).source) ≈
      (cy.symm.trans cy').restr (cy.target ∩ cy.symm ⁻¹' (lx.trans lx'.symm).source) := by
    simpa using (cy'.symm_trans_restr cy (lx.trans lx'.symm).open_source)
  have hrestr : (cy.symm.trans
      (OpenPartialHomeomorph.ofSet (lx.trans lx'.symm).source (lx.trans lx'.symm).open_source)).trans cy' ≈
      (cy.symm.trans cy').restr (cy.target ∩ cy.symm ⁻¹' (lx.trans lx'.symm).source) := by
    rw [OpenPartialHomeomorph.trans_assoc, hofset]
    exact hrestr0
  have hrestrict_mem :
      (cy.symm.trans cy').restr (cy.target ∩ cy.symm ⁻¹' (lx.trans lx'.symm).source) ∈
        contDiffGroupoid 1 𝓘(ℂ) :=
    closedUnderRestriction' hbase (cy.isOpen_inter_preimage_symm (lx.trans lx'.symm).open_source)
  -- The transition on `X` is equivalent to the restriction of the base transition to the overlap.
  have hchain : (cy.symm.trans (lx.trans lx'.symm)).trans cy' ≈
      (cy.symm.trans cy').restr (cy.target ∩ cy.symm ⁻¹' (lx.trans lx'.symm).source) :=
    Setoid.trans hcomp hrestr
  have hsimp : ((lx.symm.trans cy).symm.trans (lx'.symm.trans cy')) ≈
      (cy.symm.trans (lx.trans lx'.symm)).trans cy' := by
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
      using OpenPartialHomeomorph.eqOnSource_refl (e := (cy.symm.trans (lx.trans lx'.symm)).trans cy')
  apply StructureGroupoid.mem_of_eqOnSource (G := contDiffGroupoid 1 𝓘(ℂ)) hrestrict_mem
  exact Setoid.trans hsimp hchain

/-- An unramified surface over a Riemann surface is canonically a one-dimensional complex
manifold. -/
instance
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : UnramifiedSurfaceOver Y) : IsManifold 𝓘(ℂ) 1 X := by
  -- The pulled-back atlas is compatible because each transition is a restriction of a base
  -- chart transition, hence inherits the base `C^1` compatibility.
  letI := ({
    compatible := fun he he' ↦ X.pulled_back_chart_transition_mem_contDiffGroupoid he he'
  } : HasGroupoid X (contDiffGroupoid 1 𝓘(ℂ)))
  exact IsManifold.mk' 𝓘(ℂ) 1 X

-- The next helpers turn the chart computation for `projection` into pointwise holomorphicity.
/-- Helper for Definition VI.5-extra-2: in the preferred pulled-back chart at `x`, the projection
has coordinate expression `id`. -/
lemma writtenInExtChartAt_projection_eq_id
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : UnramifiedSurfaceOver Y) (x : X) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) x).target) :
    writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x X.projection z = z := by
  let e := X.isLocalHomeomorph.localInverseAt x
  let c := chartAt ℂ (X.projection x)
  have hchart : chartAt ℂ x = e.symm.trans c := by
    rfl
  have hz' := hz
  rw [extChartAt_target, hchart, OpenPartialHomeomorph.trans_target] at hz'
  simp [Set.mem_preimage, e, c, mfld_simps] at hz'
  have htarget : z ∈ c.target := hz'.1
  have hsource : c.symm z ∈ e.source := hz'.2
  have hchart_symm : (chartAt ℂ x).symm z = e (c.symm z) := by
    rw [hchart]
    rfl
  -- In coordinates, `projection` cancels the chosen local inverse branch.
  calc
    writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x X.projection z
        = c (X.projection ((chartAt ℂ x).symm z)) := by
            simp [writtenInExtChartAt, extChartAt, c, mfld_simps]
    _ = c (X.projection (e (c.symm z))) := by rw [hchart_symm]
    _ = c (c.symm z) := by rw [X.isLocalHomeomorph.apply_localInverseAt_of_mem hsource]
    _ = z := c.right_inv htarget

/-- Helper for Definition VI.5-extra-2: the projection is holomorphic at every point of the
pulled-back complex manifold. -/
lemma mdifferentiableAt_projection
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : UnramifiedSurfaceOver Y) (x : X) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) X.projection x := by
  rw [mdifferentiableAt_iff]
  refine ⟨X.isLocalHomeomorph.continuous.continuousAt, ?_⟩
  have hwritten :
      writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x X.projection
        =ᶠ[nhdsWithin (extChartAt 𝓘(ℂ) x x) (Set.range (𝓘(ℂ)))] id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓘(ℂ)) x] with z hz
    exact X.writtenInExtChartAt_projection_eq_id x hz
  have hxwritten :
      writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x X.projection (extChartAt 𝓘(ℂ) x x) =
        id (extChartAt 𝓘(ℂ) x x) :=
    X.writtenInExtChartAt_projection_eq_id x (mem_extChartAt_target (I := 𝓘(ℂ)) x)
  -- After rewriting the coordinate expression to `id`, the derivative is the usual identity map.
  let hId : DifferentiableWithinAt ℂ id (Set.range (𝓘(ℂ))) (extChartAt 𝓘(ℂ) x x) :=
    differentiableWithinAt_id
  exact hId.congr_of_eventuallyEq hwritten hxwritten

/-- With the pulled-back complex structure, the projection of an unramified surface is
holomorphic. -/
theorem mdifferentiable_projection
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : UnramifiedSurfaceOver Y) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X.projection := by
  -- Holomorphicity is pointwise, and each point uses the same identity-in-charts computation.
  intro x
  exact X.mdifferentiableAt_projection x

end UnramifiedSurfaceOver

namespace ChartedSpace

/-- A complex charted space has no open singleton. -/
theorem not_isOpen_singleton_complex
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] (y : Y) :
    ¬ IsOpen ({y} : Set Y) := by
  intro hy
  have hsubset : ({y} : Set Y) ⊆ (chartAt ℂ y).source := by
    intro z hz
    simpa [Set.mem_singleton_iff] using hz ▸ mem_chart_source ℂ y
  have himage : IsOpen ((chartAt ℂ y) '' ({y} : Set Y)) :=
    (chartAt ℂ y).isOpen_image_of_subset_source hy hsubset
  have : IsOpen ({chartAt ℂ y y} : Set ℂ) := by
    simpa using himage
  exact not_isOpen_singleton (chartAt ℂ y y) this

end ChartedSpace

/-- Definition VI.5-extra-2: a connected Hausdorff unramified surface over `Y` is a connected,
Hausdorff local-homeomorphism surface over `Y`. -/
structure ConnectedHausdorffUnramifiedSurfaceOver (Y : Type v) [TopologicalSpace Y]
    extends UnramifiedSurfaceOver Y where
  connected : ConnectedSpace carrier
  t2Space : T2Space carrier

namespace ConnectedHausdorffUnramifiedSurfaceOver

/-- A connected Hausdorff unramified surface over `Y` coerces to its total space. -/
instance {Y : Type v} [TopologicalSpace Y] :
    CoeSort (ConnectedHausdorffUnramifiedSurfaceOver Y) (Type u) where
  coe X := X.carrier

instance {Y : Type v} [TopologicalSpace Y] (X : ConnectedHausdorffUnramifiedSurfaceOver Y) :
    TopologicalSpace X :=
  X.toUnramifiedSurfaceOver.topology

attribute [instance] connected t2Space

/-- A connected Hausdorff unramified surface inherits the pulled-back complex charts from its
underlying unramified surface. -/
noncomputable instance chartedSpace
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (X : ConnectedHausdorffUnramifiedSurfaceOver Y) : ChartedSpace ℂ X :=
  UnramifiedSurfaceOver.chartedSpace X.toUnramifiedSurfaceOver

/-- A connected Hausdorff unramified surface over a one-dimensional complex manifold is itself a
one-dimensional complex manifold. -/
instance
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : ConnectedHausdorffUnramifiedSurfaceOver Y) : IsManifold 𝓘(ℂ) 1 X := by
  simpa using (inferInstance : IsManifold 𝓘(ℂ) 1 X.toUnramifiedSurfaceOver)

/-- The projection of a connected Hausdorff unramified surface is holomorphic. -/
theorem mdifferentiable_projection
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (X : ConnectedHausdorffUnramifiedSurfaceOver Y) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X.projection := by
  simpa using X.toUnramifiedSurfaceOver.mdifferentiable_projection

/-- Package a connected Hausdorff local homeomorphism `X → Y` as the source-facing owner of
Definition VI.5-extra-2. When `Y` is a Riemann surface, the induced `ChartedSpace` and
`IsManifold` instances are then provided by `UnramifiedSurfaceOver`. -/
def ofIsLocalHomeomorph
    {Y : Type v} [TopologicalSpace Y]
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    (φ : X → Y) (hφ : IsLocalHomeomorph φ) : ConnectedHausdorffUnramifiedSurfaceOver Y where
  carrier := X
  topology := inferInstance
  projection := φ
  isLocalHomeomorph := hφ
  connected := inferInstance
  t2Space := inferInstance

/-- A covering space over `Y` gives a connected Hausdorff unramified surface over `Y` in the
topological sense of Definition VI.5-extra-2. -/
def ofIsCoveringMap
    {Y : Type v} [TopologicalSpace Y]
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    (φ : X → Y) (hφ : IsCoveringMap φ) : ConnectedHausdorffUnramifiedSurfaceOver Y :=
  ofIsLocalHomeomorph φ hφ.isLocalHomeomorph

/-- If the projection of a connected Hausdorff unramified surface were constant, its image would
be an open singleton in the base. -/
theorem isOpen_singleton_projection
    {Y : Type v} [TopologicalSpace Y]
    (X : ConnectedHausdorffUnramifiedSurfaceOver Y) (x : X)
    (hconst : ∀ x' : X, X.projection x' = X.projection x) :
    IsOpen ({X.projection x} : Set Y) := by
  obtain ⟨U, hU, hEmb⟩ :=
    isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp X.isLocalHomeomorph x
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hrange : Set.range (U.restrict X.projection) = ({X.projection x} : Set Y) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      simp [hconst u]
    · intro hy
      refine ⟨⟨x, hxU⟩, ?_⟩
      simpa using hy.symm
  simpa [hrange] using hEmb.isOpen_range

/-- The projection of a connected Hausdorff unramified surface over a complex charted base is
automatically nonconstant. -/
theorem nonconstant_projection
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (X : ConnectedHausdorffUnramifiedSurfaceOver Y) :
    ∃ x₁ x₂ : X, X.projection x₁ ≠ X.projection x₂ := by
  classical
  by_contra hnonconstant
  have hconst : ∀ x₁ x₂ : X, X.projection x₁ = X.projection x₂ := by
    simpa using hnonconstant
  obtain ⟨x⟩ := X.connected.toNonempty
  exact ChartedSpace.not_isOpen_singleton_complex (X.projection x) <|
    X.isOpen_singleton_projection x fun x' ↦ hconst x' x

/-- Definition VI.5-extra-2, expressed through the chapter-local covering owner: a connected
Hausdorff unramified surface over a Riemann surface base is canonically a Riemann surface over
that base. -/
noncomputable def toRiemannSurfaceOver
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space Y]
    (X : ConnectedHausdorffUnramifiedSurfaceOver Y) :
    RiemannSurfaceOver 𝓘(ℂ) Y where
  carrier := X
  topology := inferInstance
  t2Space := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  connected := inferInstance
  projection := X.projection
  mdiff_projection := X.toUnramifiedSurfaceOver.mdifferentiable_projection
  nonconstant_projection := X.nonconstant_projection

end ConnectedHausdorffUnramifiedSurfaceOver
