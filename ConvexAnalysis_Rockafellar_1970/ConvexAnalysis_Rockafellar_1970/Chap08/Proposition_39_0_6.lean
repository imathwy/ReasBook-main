import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_5

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.6 states three graph-level facts about a convex process:
  closure commutes with inverse, closed fibers are closed, and every nonempty fiber has common
  recession cone `A0`.
- `core/canonical`: the owner abstractions already present are the relation inverse `SetRel.inv`,
  the relation-closure owner `SetRel.closure`, the relation closedness owner `SetRel.IsClosed`,
  the process predicate `SetRel.IsConvexProcess 𝕜`, the relation image owner `A.image s` with
  singleton-fiber notation `A[[u]]`, and the
  recession-cone owner `0⁺[𝕜] C`.
- `bridge/view`: the textbook fiber notation `Au` is rendered canonically as
  `A[[u]]`, while the source zero fiber `A0` is `A[[0]]`.

Domain-style sampling used here:
- `SetRel.inv`, `SetRel.image`, and `SetRel.dom` from `Mathlib.Data.Rel`;
- `_root_.closure` and `_root_.IsClosed` on graph subsets of product spaces;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `SetRel.IsConvexProcess.convex_image_singleton` and
  `SetRel.IsConvexProcess.isConvexCone_image_zero` from `Chap08.Proposition_39_0_2`;
- `Convex.mem_recessionCone_of_nonneg_ray` from `Chap02.Theorem_8_3`.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive graph operations: inverse, relation closure, singleton-fiber image, and zero-fiber
  image;
- derived API: fiber closedness and the common recession-cone formula for closed convex processes.

Layer target:
- clauses (1) and (2) are `bridge/view` facts on the canonical relation owner;
- clause (3) is `source-facing`, stated directly on the existing convex-process owner.

Topology-layer decision:
- this item is about graph closure/closedness of relations, whose canonical owner in this project
  is ambient closedness in `U × X` via `SetRel.closure` / `SetRel.IsClosed`;
- no intrinsic/relative closure owner for relation graphs is introduced here, so ambient topology
  is the primary layer and any relative reformulations are downstream views.
-/

section InverseClosure

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

-- Proof sketch: the inverse relation is the image of the graph under the coordinate-swap
-- homeomorphism `Prod.swap`, and homeomorphisms commute with closure. Rewriting the swapped closed
-- graph back through the canonical surfaces `A⁻¹` and `cl(·)` yields the stated identity.
/-- Proposition 39.0.6 (1): closure commutes with inverse relation. For a convex process this is
the source identity `cl (A⁻¹) = (cl A)⁻¹`. -/
theorem closure_inv (A : SetRel U X) :
    cl(A⁻¹) = (cl(A))⁻¹ := by
  simpa [SetRel.inv] using
    ((Homeomorph.prodComm U X).symm.preimage_closure (A : Set (U × X))).symm

end InverseClosure

section ClosedFibers

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

namespace IsClosed

-- Proof sketch: the fiber `A[[u]]` is the preimage of the graph `A` under the
-- continuous map `x ↦ (u, x)`. A closed relation graph therefore has closed singleton fibers.
/-- Proposition 39.0.6 (2): if a relation is closed, then every singleton fiber
`A[[u]]` is closed. For a closed convex process this is the source assertion that
each set `Au` is closed. -/
theorem image_singleton
    {A : SetRel U X} (hA_closed : A.IsClosed) (u : U) :
    _root_.IsClosed (A[[u]]) := by
  let f : X → U × X := fun x ↦ (u, x)
  have hf : Continuous f := by
    simpa [f] using continuous_const.prodMk continuous_id
  simpa [SetRel.IsClosed, SetRel.image, f] using hA_closed.preimage hf

end IsClosed

end ClosedFibers

section RecessionFibers

variable {𝕜 : Type w} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {U : Type u} [AddCommGroup U] [Module 𝕜 U]
variable {X : Type v} [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace (U × X)] [IsTopologicalAddGroup (U × X)]
variable [ContinuousSMul 𝕜 (U × X)]

namespace IsConvexProcess

-- Proof sketch: one inclusion uses the convex-process graph cone laws together with the zero-fiber
-- cone API from Proposition 39.0.2. For the reverse inclusion, a fiber recession direction gives a
-- nonnegative ray in the graph along direction `(0, y)`; apply
-- `Convex.mem_recessionCone_of_nonneg_ray` to the closed convex graph and evaluate at the origin to
-- recover `(0, y) ∈ A`, i.e. `y ∈ A[[0]]`.
/-- Proposition 39.0.6 (3): for a closed convex process, every nonempty fiber
`A[[u]]` has recession cone `A[[0]]`. Hence all fibers over
points of `A.dom` share the same recession cone `A0`. This owner-level form uses the canonical
relation domain owner `u ∈ A.dom`. -/
theorem recessionCone_image_singleton_eq_image_zero
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜)
    (hA_closed : A.IsClosed)
    (u : U) (hu : u ∈ A.dom) :
    0⁺[𝕜] (A[[u]]) = A[[0]] := by
  rcases hu with ⟨x, hux⟩
  have hx : x ∈ A[[u]] := SetRel.mem_image.mpr ⟨u, by simp, hux⟩
  ext y
  constructor
  · intro hy
    have hRay : ∀ a : 𝕜, 0 ≤ a → (u, x) + a • (0, y) ∈ (A : Set (U × X)) := by
      intro a ha
      have hxay : x + a • y ∈ A[[u]] := (Set.mem_recessionCone_iff.mp hy) x hx a ha
      rcases SetRel.mem_image.mp hxay with ⟨u', hu', hu'xay⟩
      have hu' : u' = u := by simpa using hu'
      subst hu'
      simpa [Prod.mk_add_mk, Prod.smul_mk] using hu'xay
    have hdir : (0, y) ∈ 0⁺[𝕜] (A : Set (U × X)) :=
      hA.convex.mem_recessionCone_of_nonneg_ray (x := (u, x)) hA_closed hRay
    have h0y : (0, y) ∈ (A : Set (U × X)) := by
      have hstep :
          (0 : U × X) + (1 : 𝕜) • (0, y) ∈ (A : Set (U × X)) :=
        (Set.mem_recessionCone_iff.mp hdir) (0, 0) hA.zero_mem 1 (le_of_lt zero_lt_one)
      simpa [Prod.mk_add_mk, Prod.smul_mk] using hstep
    exact SetRel.mem_image.mpr ⟨0, by simp, h0y⟩
  · intro hy0
    rcases SetRel.mem_image.mp hy0 with ⟨u0, hu0, hu0y⟩
    have hu0 : u0 = 0 := by simpa using hu0
    subst hu0
    refine Set.mem_recessionCone_iff.mpr ?_
    intro x hx a ha
    rcases SetRel.mem_image.mp hx with ⟨u', hu', hu'x⟩
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simpa using hx
    · have hsmul : (0 : U) ~[A] a • y := by
        simpa [smul_zero] using hA.smul_mem ha_pos hu0y
      have hsum : u' ~[A] x + a • y := by
        simpa [smul_zero] using hA.add_mem hu'x hsmul
      exact SetRel.mem_image.mpr ⟨u', hu', hsum⟩

/-- Proposition 39.0.6 (3): for a closed convex process, every nonempty fiber
`A[[u]]` has recession cone `A[[0]]`. Hence all fibers over
points of `A.dom` share the same recession cone `A0`. This bridge form uses explicit nonemptiness
of the singleton fiber. -/
theorem recessionCone_image_singleton_eq_image_zero_of_nonempty
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜)
    (hA_closed : A.IsClosed)
    (u : U) (hu : (A[[u]]).Nonempty) :
    0⁺[𝕜] (A[[u]]) = A[[0]] := by
  rcases hu with ⟨x, hx⟩
  rcases SetRel.mem_image.mp hx with ⟨u', hu', hu'x⟩
  have hu' : u' = u := by simpa using hu'
  have hudom : u ∈ A.dom := ⟨x, by simpa [hu'] using hu'x⟩
  exact hA.recessionCone_image_singleton_eq_image_zero hA_closed u hudom

end IsConvexProcess

end RecessionFibers

end SetRel
