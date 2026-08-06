import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.FiberBundle.Trivialization

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Bundle

variable {G : Type u} {B : Type v} {Z : Type w}
variable [Group G] [TopologicalSpace G]
variable [TopologicalSpace B] [TopologicalSpace Z]
variable [MulAction G Z] [ContinuousSMul G Z]

-- Mathlib recall: `Bundle.Trivialization` is the canonical owner for local product charts over a
-- projection map, so the principal-bundle condition is expressed by adding fiberwise
-- `G`-equivariance to these local trivializations.

namespace Bundle.Trivialization

/-- The fiberwise inverse map at `b ∈ e.baseSet`, exposed using the canonical singleton-fiber
homeomorphism rather than the underlying `OpenPartialHomeomorph`. -/
abbrev symmAt {F : Type u} {B : Type v} {Z : Type w} [TopologicalSpace F] [TopologicalSpace B]
    [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj) {b : B}
    (hb : b ∈ e.baseSet) : F → Z := fun y ↦ (e.preimageSingletonHomeomorph hb).symm y

end Bundle.Trivialization

/-- Definition 23.8.1: a map `p : Z → B` is a principal `G`-bundle when the `G`-action on `Z`
is free and every `b₀ : B` has a local trivialization over some neighborhood `U = e.baseSet`
whose inverse identifies the action on each fiber over `U` with translation on the `G`-factor. -/
class IsPrincipalBundleMap (G : Type u) [Group G] [TopologicalSpace G]
    [MulAction G Z] [ContinuousSMul G Z] (p : Z → B) : Prop extends IsCancelSMul G Z where
  equivariant_trivializationAt :
    ∀ b₀ : B, ∃ e : Trivialization G p,
      b₀ ∈ e.baseSet ∧
        ∀ (b : B) (hb : b ∈ e.baseSet) (g x : G),
          e.symmAt hb (g • x) = g • e.symmAt hb x

namespace IsPrincipalBundleMap

/-- For a principal bundle map, the projection is constant on `G`-orbits in the total space. -/
theorem proj_smul {p : Z → B} (hp : IsPrincipalBundleMap G p) (g : G) (z : Z) :
    p (g • z) = p z := by
  -- Choose a local trivialization centered at the base point of `z`.
  obtain ⟨e, hb, hEq⟩ := hp.equivariant_trivializationAt (p z)
  have hzs : z ∈ e.source := e.mem_source.mpr hb
  have hsymm : e.symmAt hb ((e z).2) = z := by
    -- The inverse chart sends the fiber coordinate of `z` back to `z`.
    simpa [Bundle.Trivialization.symmAt] using e.symm_apply_mk_proj hzs
  have hproj : ∀ x : G, p (e.symmAt hb x) = p z := by
    intro x
    -- Points produced by `symmAt` lie in the fiber over the chosen base point.
    simpa [Bundle.Trivialization.symmAt, Set.mem_singleton_iff] using
      ((e.preimageSingletonHomeomorph hb).symm x).property
  have htranslate : e.symmAt hb (g • (e z).2) = g • z := by
    -- Fiberwise equivariance identifies translation in the model fiber with translation on `Z`.
    rw [hEq (p z) hb g ((e z).2), hsymm]
  calc
    p (g • z) = p (e.symmAt hb (g • (e z).2)) := by rw [htranslate.symm]
    _ = p z := hproj (g • (e z).2)

end IsPrincipalBundleMap
