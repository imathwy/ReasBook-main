import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Covering.Basic
import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Proposition_4_40

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u v

section

variable {n : ℕ} {M : Type u} {E : Type v}
variable [TopologicalSpace M] [SmoothManifoldWithBoundary n M]
variable [TopologicalSpace E] (π : E → M)

local notation "I" => leeBoundaryModelWithCorners n

/-- Helper for Proposition 4.41: the total space of a covering over a Hausdorff base is
Hausdorff. -/
theorem t2Space_of_isCoveringMap [T2Space M] (hπ : IsCoveringMap π) : T2Space E := by
  -- Separate points either by distinct images in the Hausdorff base or, over one fiber, by the
  -- separated-map property of a covering projection.
  refine ⟨fun x y hxy ↦ ?_⟩
  by_cases hxy' : π x = π y
  · exact hπ.isSeparatedMap x y hxy' hxy
  · rcases t2_separation hxy' with ⟨u, v, hu, hv, hx, hy, huv⟩
    refine ⟨π ⁻¹' u, π ⁻¹' v, hu.preimage hπ.continuous, hv.preimage hπ.continuous,
      hx, hy, huv.preimage π⟩

namespace SmoothManifoldWithBoundary

variable {π : E → M}
variable [SmoothManifoldWithBoundary n E]

/-- Helper for Proposition 4.41: a smooth boundary covering map is, by definition, a smooth local
diffeomorphism. This is the bridge from the source-facing covering hypothesis to the canonical
boundary API used below. -/
theorem isLocalDiffeomorph (hπ : Manifold.IsSmoothCoveringMap I I π) :
    IsLocalDiffeomorph I I ∞ π := by
  -- Route correction: the false `ContMDiff + IsCoveringMap` bridge is replaced by the actual
  -- local-diffeomorphism field carried by `IsSmoothCoveringMap`.
  exact hπ.isLocalDiffeomorph

/-- Helper for Proposition 4.41: re-export the smooth covering hypothesis inside the boundary
namespace. -/
theorem isSmoothCoveringMap (hπ : Manifold.IsSmoothCoveringMap I I π) :
    Manifold.IsSmoothCoveringMap I I π := by
  -- No extra packaging is needed once the source-facing smooth covering structure is given.
  exact hπ

end SmoothManifoldWithBoundary

-- Proof sketch: In evenly covered neighborhoods, `π` is a local homeomorphism identifying the
-- lifted charts on `E` with the boundary charts on `M`. This preserves whether a chart point lies
-- in the frontier of the model boundary, so boundary points of `E` are exactly the points lying
-- over boundary points of `M`.
/-- Proposition 4.41 (2): For any lifted smooth manifold-with-boundary structure on the covering
space, the boundary of the total space is the preimage of the boundary of the base. -/
theorem preimage_boundary_eq_boundary_of_smooth_boundary_covering_structure
    [SmoothManifoldWithBoundary n E] (hπ : Manifold.IsSmoothCoveringMap I I π) :
    π ⁻¹' (leeBoundaryModelWithCorners n).boundary M =
      (leeBoundaryModelWithCorners n).boundary E := by
  -- Boundary preservation is the standard local-diffeomorphism theorem once `π` is known to be a
  -- smooth covering map.
  simpa using
    (SmoothManifoldWithBoundary.isLocalDiffeomorph hπ).preimage_boundary (by simp)

section Existence

variable [ConnectedSpace M]

/-- Helper for Proposition 4.41: every transition between canonical lifted covering charts is
analytic because it is the restriction of the corresponding base-chart transition. -/
theorem lifted_covering_chart_transition_mem_groupoid_omega
    (hπ : IsCoveringMap π) (p q : E) :
    (lifted_covering_chart (H := ℍ^{n}) π hπ p).symm.trans
      (lifted_covering_chart (H := ℍ^{n}) π hπ q) ∈ contDiffGroupoid ω I := by
  -- The lifted transition agrees on its source with a restricted base transition.
  have hbase :
      (chartAt (ℍ^{n}) (π p)).symm.trans (chartAt (ℍ^{n}) (π q)) ∈ contDiffGroupoid ω I := by
    exact HasGroupoid.compatible
      (chart_mem_atlas (ℍ^{n}) (π p)) (chart_mem_atlas (ℍ^{n}) (π q))
  have hrestr :
      ((chartAt (ℍ^{n}) (π p)).symm.trans (chartAt (ℍ^{n}) (π q))).restr
        ((lifted_covering_chart (H := ℍ^{n}) π hπ p).symm.trans
          (lifted_covering_chart (H := ℍ^{n}) π hπ q)).source ∈ contDiffGroupoid ω I := by
    exact closedUnderRestriction' hbase
      ((lifted_covering_chart (H := ℍ^{n}) π hπ p).symm.trans
        (lifted_covering_chart (H := ℍ^{n}) π hπ q)).open_source
  -- Replace the lifted transition by the equivalent restricted base transition.
  exact (contDiffGroupoid ω I).mem_of_eqOnSource hrestr
    (lifted_covering_chart_transition_eqOnSource (H := ℍ^{n}) π hπ p q)

/-- Helper for Proposition 4.41: the canonical lifted covering atlas is analytic, so it gives the
`ω`-smooth structure needed for a smooth manifold with boundary. -/
theorem smooth_covering_structure_isManifold_omega
    (hπ : IsCoveringMap π) :
    let _ : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
    IsManifold I ω E := by
  -- Route correction: prove `ω`-compatibility directly for the canonical lifted atlas, instead of
  -- trying to upgrade an arbitrary `C^∞` witness.
  let cs : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
  have hgroupoid : HasGroupoid E (contDiffGroupoid ω I) := by
    let _ : ChartedSpace (ℍ^{n}) E := cs
    exact
      { compatible := by
          intro e e' he he'
          rcases he with ⟨p, rfl⟩
          rcases he' with ⟨q, rfl⟩
          exact lifted_covering_chart_transition_mem_groupoid_omega (π := π) hπ p q }
  let _ : ChartedSpace (ℍ^{n}) E := cs
  let _ : HasGroupoid E (contDiffGroupoid ω I) := hgroupoid
  exact IsManifold.mk' I ω E

/-- Helper for Proposition 4.41: the canonical lifted covering atlas already makes the covering
projection a smooth covering map. -/
theorem canonical_lifted_covering_structure_isSmoothCoveringMap
    (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    let _ : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
    Manifold.IsSmoothCoveringMap I I π := by
  have h_infty_lift :
      (let _ : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
       IsManifold I ∞ E) := by
    exact lifted_covering_chartedSpace_isManifold I (H := ℍ^{n}) π hπ
  let _ : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
  let _ : IsManifold I ∞ E :=
    by
      simpa using h_infty_lift
  refine ⟨hπ, h_surj, ?_⟩
  intro p
  -- The local inverse branch through `p` is a partial diffeomorphism that agrees with `π`.
  rcases lifted_projection_partial_diffeomorph I (H := ℍ^{n}) π hπ p with
    ⟨Φ, hp, hEq, -⟩
  exact ⟨Φ, hp, hEq⟩

/-- Helper for Proposition 4.41: two smooth manifold-with-boundary structures on the same covering
space that make the projection a smooth covering map induce the same maximal smooth atlas. -/
lemma smooth_boundary_covering_same_smooth_structure
    (s s' : SmoothManifoldWithBoundary n E)
    (hπs : let _ : SmoothManifoldWithBoundary n E := s
      Manifold.IsSmoothCoveringMap I I π)
    (hπs' : let _ : SmoothManifoldWithBoundary n E := s'
      Manifold.IsSmoothCoveringMap I I π) :
    (let _ : SmoothManifoldWithBoundary n E := s
     IsManifold.maximalAtlas I ∞ E) =
      (let _ : SmoothManifoldWithBoundary n E := s'
       IsManifold.maximalAtlas I ∞ E) := by
  -- Reduce uniqueness to the charted-space owner theorem from Proposition 4.40.
  let cs : ChartedSpace (ℍ^{n}) E := s.toTopologicalManifoldWithBoundary.toChartedSpace
  let cs' : ChartedSpace (ℍ^{n}) E := s'.toTopologicalManifoldWithBoundary.toChartedSpace
  have hsm :
      let _ : ChartedSpace (ℍ^{n}) E := cs
      IsManifold I ∞ E ∧ Manifold.IsSmoothCoveringMap I I π := by
    let _ : SmoothManifoldWithBoundary n E := s
    exact ⟨inferInstance, hπs⟩
  have hsm' :
      let _ : ChartedSpace (ℍ^{n}) E := cs'
      IsManifold I ∞ E ∧ Manifold.IsSmoothCoveringMap I I π := by
    let _ : SmoothManifoldWithBoundary n E := s'
    exact ⟨inferInstance, hπs'⟩
  have hEq :
      (let _ : ChartedSpace (ℍ^{n}) E := cs
       let _ : IsManifold I ∞ E := hsm.1
       IsManifold.maximalAtlas I ∞ E) =
        (let _ : ChartedSpace (ℍ^{n}) E := cs'
         let _ : IsManifold I ∞ E := hsm'.1
         IsManifold.maximalAtlas I ∞ E) :=
    smooth_covering_same_smooth_structure I π hsm hsm'
  simpa [cs, cs'] using hEq

/- A smooth manifold-with-boundary structure on the total space of a cover has the expected
boundary behavior if the covering projection becomes a smooth map for that structure. -/
-- Proof sketch: Use evenly covered neighborhoods in `M` and the preferred boundary charts on `M`
-- to pull back a `leeBoundaryModelWithCorners n`-charted atlas to `E`. The lifted charts are
-- smooth because a covering map is locally a homeomorphism, so the pulled-back atlas gives a
-- smooth manifold-with-boundary structure for which `π` is smooth.
/-- Proposition 4.41 (1): A topological covering of a connected smooth manifold with boundary,
with second-countable total space, admits a smooth manifold-with-boundary structure on the total
space for which the projection is a smooth covering map. -/
theorem exists_smooth_boundary_covering_structure
    [SecondCountableTopology E] (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ s : SmoothManifoldWithBoundary n E,
      let _ : SmoothManifoldWithBoundary n E := s
      Manifold.IsSmoothCoveringMap I I π := by
  -- Specialize Proposition 4.40 to the canonical lifted boundary atlas and package that atlas
  -- into the source-facing `SmoothManifoldWithBoundary` owner.
  have h_infty_lift :
      (let _ : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
       IsManifold I ∞ E) := by
    exact lifted_covering_chartedSpace_isManifold I (H := ℍ^{n}) π hπ
  let cs : ChartedSpace (ℍ^{n}) E := lifted_covering_chartedSpace (H := ℍ^{n}) π hπ
  let _ : ChartedSpace (ℍ^{n}) E := cs
  let _ : IsManifold I ∞ E :=
    by
      simpa [cs] using h_infty_lift
  let hω : IsManifold I ω E := smooth_covering_structure_isManifold_omega (π := π) hπ
  let hT2 : T2Space E := t2Space_of_isCoveringMap (π := π) hπ
  let s : SmoothManifoldWithBoundary n E :=
    { toTopologicalManifoldWithBoundary :=
        { toT2Space := hT2
          toSecondCountableTopology := inferInstance
          toChartedSpace := cs
          toIsManifold := inferInstance }
      smooth := hω }
  refine ⟨s, ?_⟩
  -- The packaged smooth structure uses the same canonical lifted atlas, so the covering-map data
  -- proved above transfers without further changes.
  let _ : SmoothManifoldWithBoundary n E := s
  simpa [cs] using
    (canonical_lifted_covering_structure_isSmoothCoveringMap (π := π) hπ h_surj)

-- Proof sketch: Any two compatible smooth structures on `E` are locally obtained by pulling back
-- the same boundary charts on `M` through the same covering map. This determines the maximal smooth
-- atlas, not the concrete `ChartedSpace` owner data stored in a structure instance.
/-- Proposition 4.41 (3): The smooth manifold-with-boundary structure on the covering space is
unique in the sense of inducing a unique maximal smooth atlas. -/
theorem exists_unique_smooth_boundary_covering_structure
    [SecondCountableTopology E] (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ s : SmoothManifoldWithBoundary n E,
      let _ : SmoothManifoldWithBoundary n E := s
      Manifold.IsSmoothCoveringMap I I π ∧
        ∀ s' : SmoothManifoldWithBoundary n E,
          (let _ : SmoothManifoldWithBoundary n E := s'
           Manifold.IsSmoothCoveringMap I I π) →
            (let _ : SmoothManifoldWithBoundary n E := s
             IsManifold.maximalAtlas I ∞ E) =
            (let _ : SmoothManifoldWithBoundary n E := s'
             IsManifold.maximalAtlas I ∞ E) := by
  -- Combine the existence theorem with the uniqueness adapter for boundary structures.
  have hExists :
      ∃ s : SmoothManifoldWithBoundary n E,
        let _ : SmoothManifoldWithBoundary n E := s
        Manifold.IsSmoothCoveringMap I I π :=
    exists_smooth_boundary_covering_structure (π := π) hπ h_surj
  rcases hExists with ⟨s, hs⟩
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  exact smooth_boundary_covering_same_smooth_structure π s s' hs hs'

end Existence
end
