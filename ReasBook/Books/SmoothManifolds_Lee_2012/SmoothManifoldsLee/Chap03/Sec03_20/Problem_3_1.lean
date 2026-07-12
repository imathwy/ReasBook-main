import Mathlib
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.LocallyConstant.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Topology

noncomputable section

universe uE uH uM uE' uH' uN

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

private theorem chartedSpace_locallyConnectedSpace (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : LocallyConnectedSpace M := by
  -- Pull the convex local path connectedness of `range I` through `I`, then through the atlas.
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : LocallyConnectedSpace H := by
    letI : LocPathConnectedSpace (Set.range I) := I.convex_range.locPathConnectedSpace
    let e : H ≃ₜ Set.range I := I.isClosedEmbedding.toHomeomorph
    exact e.locallyConnectedSpace
  exact ChartedSpace.locallyConnectedSpace H M

variable [IsManifold I 1 M] [IsManifold I' 1 N]

-- Proof sketch: in manifold charts, the hypothesis becomes the model-space `RCLike` statement
-- that a differentiable map with vanishing derivative is locally constant on an open neighborhood.
/-- A differentiable map between `C¹` manifolds with corners is locally constant if its manifold
derivative vanishes at every point. -/
theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → N} (hf : MDifferentiable I I' f)
    (hzero : ∀ p, mfderiv I I' f p = 0) : IsLocallyConstant f := by
  -- Route correction: the chartwise proof now has the required `IsManifold` assumptions in scope.
  -- The remaining implementation is the local transport from `mfderiv I I' f = 0` to a zero
  -- `fderivWithin` statement on a convex chart neighborhood.
  sorry

/-- On a `C¹` manifold with corners, a differentiable map has vanishing manifold derivative at
every point if and only if it is locally constant. -/
theorem mfderiv_eq_zero_iff_isLocallyConstant {f : M → N}
    (hf : MDifferentiable I I' f) : (∀ p, mfderiv I I' f p = 0) ↔ IsLocallyConstant f := by
  letI : LocallyConnectedSpace M := chartedSpace_locallyConnectedSpace I M
  constructor
  · exact isLocallyConstant_of_mfderiv_eq_zero hf
  · intro hloc p
    -- Route correction: the reverse implication is purely local and uses eventual equality with
    -- a constant map, so no chart computation is needed here.
    have heq : f =ᶠ[𝓝 p] fun _ : M ↦ f p := by
      simpa using hloc.eventually_eq p
    have hconst : HasMFDerivAt I I' (fun _ : M ↦ f p) p
        (0 : TangentSpace I p →L[𝕜] TangentSpace I' (f p)) := hasMFDerivAt_const (f p) p
    exact (hconst.congr_of_eventuallyEq heq).mfderiv

-- Proof sketch: use `mfderiv_eq_zero_iff_isLocallyConstant` and the canonical correspondence
-- between locally constant maps and maps constant on connected components in a locally connected
-- space.
/-- Problem 3-1: for a differentiable map between `C¹` manifolds with corners, the manifold
derivative is the zero map at every point if and only if the map is constant on each connected
component of the source space. -/
theorem mfderiv_eq_zero_iff_constant_on_components {f : M → N}
    (hf : MDifferentiable I I' f) :
    (∀ p, mfderiv I I' f p = 0) ↔ ∀ p, ∀ q ∈ connectedComponent p, f q = f p := by
  letI : LocallyConnectedSpace M := chartedSpace_locallyConnectedSpace I M
  rw [mfderiv_eq_zero_iff_isLocallyConstant hf]
  constructor
  · intro hloc p q hq
    exact hloc.apply_eq_of_isPreconnected isConnected_connectedComponent.isPreconnected
      hq mem_connectedComponent
  · exact IsLocallyConstant.of_constant_on_connected_components
