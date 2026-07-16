import DifferentialForms_Cartan_1970.cartan.VI.section25.«0005_Definition_VI_4_extra_5»
import DifferentialForms_Cartan_1970.cartan.VI.section25.«0016_Theorem_VI_4_extra_13».OpenSphereUniformization
import DifferentialForms_Cartan_1970.cartan.VI.section25.«0016_Theorem_VI_4_extra_13».SeededSphereContinuationSurface
import DifferentialForms_Cartan_1970.cartan.VI.section25.«0016_Theorem_VI_4_extra_13».SphereNeighborhoodSourceContinuation

universe u

open scoped Complex.UnitDisc Manifold

section

/-- Helper for Theorem VI.4-extra-13: along a fixed path, the parameter values already covered by
seeded continuation charts form an open subset of `unitInterval`. -/
lemma seededSphereNeighborhoodChart_pathCoveredTimes_isOpen
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexManifold X]
    {c₀ : SphereNeighborhoodChart X} {x₀ x : X} (γ : Path x₀ x) :
    IsOpen {t : unitInterval | ∃ c : SeededSphereNeighborhoodChart c₀, γ t ∈ c.chart.source} := by
  refine isOpen_iff_mem_nhds.2 ?_
  intro t ht
  rcases ht with ⟨c, hct⟩
  -- Once one seeded chart covers `γ t`, the path stays in that chart on a time neighborhood.
  exact Filter.mem_of_superset
    (γ.continuous.continuousAt.preimage_mem_nhds (c.chart.source.isOpen.mem_nhds hct))
    (by
      intro s hs
      exact ⟨c, hs⟩)

/-- Helper for Theorem VI.4-extra-13: starting from one seed sphere chart, path continuation
through the local sphere charts covers every point of a simply connected complex manifold. -/
lemma seededSphereNeighborhoodChart_covers_of_simplyConnected
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexManifold X]
    [SimplyConnectedSpace X]
    {c₀ : SphereNeighborhoodChart X} {x₀ : X} (hx₀ : x₀ ∈ c₀.source) :
    ∀ x : X, ∃ c : SeededSphereNeighborhoodChart c₀, x ∈ c.chart.source := by
  intro x
  rcases Cartan.seededSphereChart_gluedProjection_hasSeedPreimage (c₀ := c₀) hx₀ with
    ⟨y0, _hy0⟩
  let Y : Type u := connectedComponentIn
    (Set.univ : Set ((Cartan.seededSphereChart_liftedGlueData (c₀ := c₀)).glued)) y0
  let π : Y → X := fun y ↦ Cartan.seededSphereChart_gluedProjection (c₀ := c₀) y.1
  have hπSurj : Function.Surjective π := by
    -- Route correction: use the already packaged connected-component projection surjectivity,
    -- instead of reopening the older clopen-on-`unitInterval` propagation proof.
    simpa [π, Y] using
      Cartan.seededSphereChart_gluedComponentProjection_surjective (c₀ := c₀) y0
  rcases hπSurj x with ⟨y, hy⟩
  rcases TopCat.GlueData.ι_jointly_surjective
      (D := Cartan.seededSphereChart_liftedGlueData (c₀ := c₀)) y.1 with ⟨c, z, hcz⟩
  refine ⟨c, ?_⟩
  have hx_branch :
      Cartan.seededSphereChart_liftedBranch (c₀ := c₀) c z = x := by
    -- Evaluate the restricted projection at the chosen glued representative and compare with `x`.
    calc
      Cartan.seededSphereChart_liftedBranch (c₀ := c₀) c z =
          Cartan.seededSphereChart_gluedProjection (c₀ := c₀)
            ((Cartan.seededSphereChart_liftedGlueData (c₀ := c₀)).ι c z) := by
              rw [Cartan.seededSphereChart_gluedProjection_apply_ι (c₀ := c₀) c z]
      _ = Cartan.seededSphereChart_gluedProjection (c₀ := c₀) y.1 := by rw [hcz]
      _ = x := by simpa [π] using hy
  -- The represented point in the chosen chart source is exactly `x`.
  simpa [Cartan.seededSphereChart_liftedBranch] using
    hx_branch.symm ▸ c.chart.branch_mem_source
      ((Cartan.seededSphereChart_targetSpace c).uliftFunctorObjHomeo.symm z)

/-- Theorem VI.4-extra-13. Fundamental theorem: any simply connected complex manifold `X` is
isomorphic, as a complex manifold, to the canonical Riemann sphere, the complex plane, or the
unit disc `𝔻`. -/
theorem simply_connected_complex_manifold_uniformization
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexManifold X]
    [SimplyConnectedSpace X] :
    Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere) ∨
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ 𝔻) := by
  letI : Nonempty X := inferInstance
  let x₀ : X := Classical.choice inferInstance
  rcases point_has_sphereNeighborhoodChart (X := X) x₀ with ⟨c₀, hx₀⟩
  rcases Cartan.seededSphereContinuationCoverOfSeedPoint (c₀ := c₀) (x₀ := x₀) hx₀ with
    ⟨Y, hTopY, hChartY, hManY, hT2Y, hConnY, hNonemptyY, π, hπCover, hπLocal, V, hYV⟩
  letI : TopologicalSpace Y := hTopY
  letI : ChartedSpace ℂ Y := hChartY
  letI : IsManifold 𝓘(ℂ) 1 Y := hManY
  letI : T2Space Y := hT2Y
  letI : ConnectedSpace Y := hConnY
  letI : Nonempty Y := hNonemptyY
  let eYX : Y ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ X :=
    IsLocalDiffeomorph.diffeomorphOfBijective hπLocal
      (coveringMap_bijective_of_simplyConnected hπCover)
  rcases hYV with ⟨eYV⟩
  let eXV : X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V := eYX.symm.trans eYV
  haveI : SimplyConnectedSpace Y :=
    eYX.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  haveI : SimplyConnectedSpace V :=
    eYV.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  rcases simplyConnectedOpenSubset_riemannSphere_uniformization V with
    hsphere | hplane | hdisc
  · rcases hsphere with ⟨eVR⟩
    -- Compose the continuation-surface model of `X` with the sphere case on the open subset `V`.
    exact Or.inl ⟨eXV.trans eVR⟩
  · rcases hplane with ⟨eVC⟩
    -- The plane case is obtained by the same composition through the canonical open subset `V`.
    exact Or.inr <| Or.inl ⟨eXV.trans eVC⟩
  · rcases hdisc with ⟨eVD⟩
    -- Likewise for the unit-disc case.
    exact Or.inr <| Or.inr ⟨eXV.trans eVD⟩

end
