import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.7 states that the polar cone `Kᵒ` from Text 14.0.1 is closed,
  convex, stable under nonnegative scalar multiplication, contains the origin, and hence is a cone
  in the chapter's set-level sense.
- `core/canonical`: the owner abstraction is `PointedCone.dual` at the primitive linear-pairing
  layer, used at the source-negated pairing map `-(HasLinearPairing.pairingLinear)`.
- `bridge/view`: `Kᵒ[𝕜]` is Rockafellar's nonpositive-sign-convention view of that owner. The
  public API should therefore expose only source-facing properties of `Kᵒ[𝕜]`, not a parallel local
  cone package.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `PointedCone.dual`;
- `PointedCone.convex`;
- `ConvexCone.isCone`;
- `PointedCone.smul_mem`.
- `Set.IsCone 𝕜`.

Primitive data vs derived API:
- primitive input: a subset `K : Set M`;
- primitive owner: `PointedCone.dual (-(HasLinearPairing.pairingLinear)) K`;
- derived source-facing API: convexity, membership of `0` in `Kᵒ[𝕜]`, the set-level cone predicate
  `Set.IsCone 𝕜 Kᵒ[𝕜]`, and nonnegative scalar stability of `Kᵒ[𝕜]`.

Layer target: `bridge/view`.
-/

/-- Text 14.0.7 (2): the polar cone of a set `K` is convex. This is a direct owner-side fact for
the dual cone and holds for arbitrary subsets. -/
theorem convex_polarCone (K : Set M) :
    Convex 𝕜 (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  simpa using PointedCone.convex (Kᵒ[𝕜] : PointedCone 𝕜 N)

/-- Text 14.0.7 (4): the polar cone `Kᵒ[𝕜]` contains the origin. -/
theorem zero_mem_polarCone (K : Set M) :
    (0 : N) ∈ Kᵒ[𝕜] := by
  simp

/-- Text 14.0.7, in the chapter's set-level cone vocabulary: the polar cone is a cone. -/
theorem isCone_polarCone (K : Set M) :
    Set.IsCone 𝕜 (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  simpa using ConvexCone.isCone ((Kᵒ[𝕜] : PointedCone 𝕜 N) : ConvexCone 𝕜 N)

/-- Text 14.0.7 (3): the polar cone is stable under nonnegative scalar multiplication. -/
theorem smul_mem_polarCone (K : Set M) {a : 𝕜} (ha : 0 ≤ a) {xStar : N}
    (hxStar : xStar ∈ Kᵒ[𝕜]) :
    a • xStar ∈ Kᵒ[𝕜] := by
  simpa using (Kᵒ[𝕜] : PointedCone 𝕜 N).smul_mem ha hxStar

end

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
  [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M] [TopologicalSpace M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Topology-layer note:
- the source-facing owner `K ↦ Kᵒ[𝕜]` has no extra carrier parameter on the source side, so its
  closure-invariance API is canonically ambient `closure`;
- intrinsic/relative closure formulations require additional carrier data and therefore belong to
  separate bridge theorems, not to this owner-level theorem.
-/

/-- Closure invariance for the chapter polar owner under continuity of left pairing evaluation, at
the canonical `PointedCone` owner layer. -/
@[simp] theorem polarCone_closure_of_continuous (K : Set M)
    (hcont : ∀ xStar : N, Continuous (fun x : M ↦ (⟪x, xStar⟫ₚ : 𝕜))) :
    ((closure K)ᵒ[𝕜] : PointedCone 𝕜 N) = (Kᵒ[𝕜] : PointedCone 𝕜 N) := by
  ext xStar
  constructor
  · intro hx
    refine (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).2 ?_
    intro x hxK
    exact
      (mem_polarCone_iff_pairing (K := closure K) (xStar := xStar)).1 hx x
        (subset_closure hxK)
  · intro hx
    refine (mem_polarCone_iff_pairing (K := closure K) (xStar := xStar)).2 ?_
    have hsubset : K ⊆ {x : M | (⟪x, xStar⟫ₚ : 𝕜) ≤ 0} := by
      intro x hxK
      exact (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).1 hx x hxK
    have hclosed : IsClosed {x : M | (⟪x, xStar⟫ₚ : 𝕜) ≤ 0} := by
      simpa using (isClosed_Iic.preimage (hcont xStar))
    intro x hxClosure
    exact closure_minimal hsubset hclosed hxClosure

/-- Set-level closure invariance corollary for the chapter polar owner under continuity of left
pairing evaluation. -/
@[simp] theorem polarCone_closure_eq_of_continuous (K : Set M)
    (hcont : ∀ xStar : N, Continuous (fun x : M ↦ (⟪x, xStar⟫ₚ : 𝕜))) :
    (↑((closure K)ᵒ[𝕜] : PointedCone 𝕜 N) : Set N) =
      (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  exact congrArg (fun P : PointedCone 𝕜 N ↦ (P : Set N))
    (polarCone_closure_of_continuous (K := K) hcont)

end

section

open scoped Rockafellar PolarCone

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
  [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommMonoid M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N]
variable [HasLinearPairing M N 𝕜]

/-!
Topology-layer note:
- `isClosed_polarCone` is an owner-level closedness theorem for the ambient codomain topology on
  `N`;
- relative/intrinsic closedness statements for `Kᵒ[𝕜]` require an additional ambient subset in `N`,
  so they are downstream bridge results rather than the primitive source-facing API here.
-/

/-- Text 14.0.7 (1): the polar cone `Kᵒ[𝕜]` of a set `K` is closed at the pairing-continuity
layer. -/
theorem isClosed_polarCone (K : Set M)
    (hcont : ∀ x : M, Continuous (fun xStar : N ↦ (⟪x, xStar⟫ₚ : 𝕜))) :
    IsClosed (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) := by
  classical
  have hEq :
      (↑(Kᵒ[𝕜] : PointedCone 𝕜 N) : Set N) =
        ⋂ x : {x : M // x ∈ K}, {xStar : N | (⟪(x : M), xStar⟫ₚ : 𝕜) ≤ 0} := by
    ext xStar
    constructor
    · intro hx
      have hxall : ∀ x : {x : M // x ∈ K}, (⟪(x : M), xStar⟫ₚ : 𝕜) ≤ 0 := by
        intro x
        exact (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).1 hx (x : M) x.2
      simpa [Set.mem_iInter] using hxall
    · intro hx
      have hxall : ∀ x : {x : M // x ∈ K}, (⟪(x : M), xStar⟫ₚ : 𝕜) ≤ 0 := by
        simpa [Set.mem_iInter] using hx
      exact (mem_polarCone_iff_pairing (K := K) (xStar := xStar)).2 <| by
        intro x hxK
        exact hxall ⟨x, hxK⟩
  rw [hEq]
  refine isClosed_iInter ?_
  intro x
  simpa using (isClosed_Iic.preimage (hcont (x : M)))

end
