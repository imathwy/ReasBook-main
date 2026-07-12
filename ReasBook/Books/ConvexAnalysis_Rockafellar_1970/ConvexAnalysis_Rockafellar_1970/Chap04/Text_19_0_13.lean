import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Crollary_17_1_7

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.13 is stated at the intrinsic witness owner
  `linearHyperplaneWitnessSet`; this keeps the public theorem independent of any coordinate model
  and independent of any concrete dual-space owner.
- `core/canonical`: the owner abstractions are pairing-parametric `Set.IsPolyhedral`,
  `linearHyperplaneWitnessSet`, the generic closedness obstruction theorem
  `convexHull_linearHyperplaneWitnessSet_not_isClosed`; the polyhedral
  contradiction is packaged as `convexHull_linearHyperplaneWitnessSet_not_isPolyhedral`.
- `bridge/view`: no extra concrete-model bridge is needed in this file; polyhedral-closedness is
  consumed directly from the pairing-continuity owner layer.

Primitive data vs derived API:
- primitive witness data: one linear functional `f : V →ₗ[𝕜] 𝕜` defining a hyperplane,
  one nonzero in-hyperplane direction `u`, and one off-hyperplane point `y`;
- bridge realization: the only bridge step is
  `Set.IsPolyhedral.isClosed_of_forall_continuous`, used at the primitive
  `HasContinuousPairing` owner layer;
- derived API: the source-facing theorem is intrinsic (`linearHyperplaneWitnessSet`) and avoids
  finite-dimensional or concrete-dual specialization.

Layer target: `source-facing`.
-/

/-- Text 19.0.13 (source-facing canonical owner form): if one adjoins an off-hyperplane point to
a hyperplane, the resulting convex hull cannot be polyhedral. -/
theorem convexHull_linearHyperplaneWitnessSet_not_isPolyhedral
    {V : Type*}
    [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    [ContinuousAdd V] [ContinuousSMul 𝕜 V]
    {Y : Type*} [HasPairing V Y 𝕜] [HasContinuousPairing V Y 𝕜]
    {f : V →ₗ[𝕜] 𝕜} {u y : V}
    (hu : u ≠ 0)
    (hu_hyperplane : u ∈ linearHyperplane f (0 : 𝕜))
    (hy_offHyperplane : y ∉ linearHyperplane f (0 : 𝕜)) :
    ¬ (convexHull 𝕜 (linearHyperplaneWitnessSet f y)).IsPolyhedral 𝕜 Y := by
  intro hpoly
  have hclosed : IsClosed (convexHull 𝕜 (linearHyperplaneWitnessSet f y)) :=
    Set.IsPolyhedral.isClosed_of_forall_continuous (𝕜 := 𝕜) (E := V) (Y := Y) hpoly
      (fun y' ↦ HasContinuousPairing.continuous_pairing_left (X := V) (Y := Y) (𝕜 := 𝕜) y')
  exact convexHull_linearHyperplaneWitnessSet_not_isClosed hu
    hu_hyperplane hy_offHyperplane
    hclosed

end
