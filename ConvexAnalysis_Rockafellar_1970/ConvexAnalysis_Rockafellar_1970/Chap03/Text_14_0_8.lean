import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_7

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [ClosedIicTopology 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M] [TopologicalSpace M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜] [HasContinuousPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.8 states that taking the polar commutes with topological closure.
- `core/canonical`: the owner objects are `PointedCone.dual
  (-(HasLinearPairing.pairingLinear : M →ₗ[𝕜] Module.Dual 𝕜 N)) K` from Text 14.0.1 and the
  standard topological closure operator `closure`.
- `bridge/view`: the result is a direct equality between two source-visible set constructions, so
  no extra cone package or bridge wrapper is needed.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- the standard closure operator `closure`;
- closed half-space preimages via `isClosed_Iic.preimage`.

Primitive data vs derived API:
- primitive input: a set `K : Set M`;
- primitive owner: `PointedCone.dual (-(HasLinearPairing.pairingLinear)) K`;
- derived source-facing content: the equality of the two polar sets obtained before and after
  closure.

Layer target: `bridge/view`.

Topology-layer note:
- the source owner here is `polarCone : Set M → PointedCone 𝕜 N`, with no distinguished ambient
  subset in
  its data;
- consequently, the canonical hull operation on the source side is ambient `closure`;
- intrinsic/relative closure statements require an extra carrier parameter and belong to a
  separate bridge theorem, not to this owner-level closure invariance API.

The source's nonempty and convex-cone hypotheses are redundant for this equality, since closure
invariance already holds for the owner dual cone of an arbitrary set.
-/

/-- Text 14.0.8 at the owner layer: taking the chapter polar commutes with closure. -/
@[simp] theorem polarCone_closure (K : Set M) :
    ((closure K)ᵒ[𝕜] : PointedCone 𝕜 N) = Kᵒ[𝕜] := by
  exact
    polarCone_closure_of_continuous (𝕜 := 𝕜) (M := M) (N := N) (K := K)
      (hcont := fun xStar : N =>
        HasContinuousPairing.continuous_pairing_left
          (X := M) (Y := N) (𝕜 := 𝕜) xStar)

end
