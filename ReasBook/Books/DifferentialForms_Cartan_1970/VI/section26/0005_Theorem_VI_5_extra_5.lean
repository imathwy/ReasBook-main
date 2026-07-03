import Mathlib
import DifferentialForms_Cartan_1970.VI.section26.«0002_Definition_VI_5_extra_2»

open scoped Manifold

/- Domain sampling: the primary domain here is connected one-dimensional complex manifolds together
with unramified covering surfaces over them. The relevant declarations inspected before this
refinement were:
* the chapter-local primitive owner `UnramifiedSurfaceOver` in
  `DifferentialForms_Cartan_1970/VI/section26/0002_Definition_VI_5_extra_2.lean`, which records the topological
  local-homeomorphism data over a base;
* the source-facing refinement `ConnectedHausdorffUnramifiedSurfaceOver` in the same file, which
  adds the connected Hausdorff hypotheses required by the theorem;
* the bridge `ConnectedHausdorffUnramifiedSurfaceOver.toRiemannSurfaceOver`, showing that
  `RiemannSurfaceOver` is downstream derived API rather than the primitive owner for the universal
  covering theorem itself;
* mathlib's owner theorem `IsCoveringMap.isLocalHomeomorph`, which places the covering property at
  the same topological owner level.
Source/core/bridge triage: this theorem is `source-facing`, so its main existential object should
be the unramified-covering owner `ConnectedHausdorffUnramifiedSurfaceOver Y`. The
`RiemannSurfaceOver` package is a `bridge/view` layer available afterwards when one wants the
induced complex-analytic surface structure. Primitive data is therefore the unramified-surface
owner and the simply connectedness, covering, and surjectivity properties of its projection. -/

-- Declarations for this item will be appended below by the statement pipeline.

universe uY

/-- Theorem VI.5-extra-5: any connected one-dimensional complex manifold `Y` has a simply
connected unramified surface over it whose projection is a surjective covering map. This includes
the special case of a connected open subset of `ℂ`, viewed as a Riemann surface. -/
theorem connected_complex_manifold_has_simplyConnected_covering
    {Y : Type uY} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space Y]
    [ConnectedSpace Y] :
    ∃ X : ConnectedHausdorffUnramifiedSurfaceOver Y,
      SimplyConnectedSpace X ∧ IsCoveringMap X.projection ∧ X.projection.Surjective := sorry
