import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_14
import ConvexAnalysis_Rockafellar_1970.Chap04.Propositon_17_0_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped Rockafellar

/-!
Source/core/bridge triage:
- `source-facing`: Propositon 17.0.15 has two atomic clauses: skew orthants are closed (under the
  source closedness hypothesis), and more generally generalized simplices are closed.
- `core/canonical`: the orthant clause is owned by `Set.IsOrthant`, now at the intrinsic
  nonnegative image layer `f '' Set.Ici (0 : M)` for a source module `M`; the simplex clause is
  already the canonical owner theorem `Affine.Simplex.isClosed`.
- `bridge/view`: the map-level closedness bridge for injective affine maps from finite-dimensional
  sources over a complete nontrivially normed scalar field is an internal helper; the public owner
  surface remains `Set.IsOrthant`.
- Domain-style sampling used here: `Set.IsOrthant`, finite-dimensional closed-map transport for
  affine maps, and `Affine.Simplex.isClosed`.
- Primitive data vs derived API: an orthant witness `hs : s.IsOrthant 𝕜 M` and source orthant
  closedness (`IsClosed (Set.Ici (0 : M))`) are primitive inputs; orthant closedness in the target
  is derived.
- Layer target: split item. Clause (1) stays `source-facing` at the canonical orthant owner layer;
  clause (2) is `core/canonical` via direct reuse.
-/

section Orthant

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]

open Set

-- Internal bridge used only to derive orthant closedness from the owner witness in this file.
private theorem isClosedMap_of_injective_affine {V : Type*}
    [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V]
    [FiniteDimensional 𝕜 V]
    {P : Type*} [TopologicalSpace P] [AddTorsor E P] [IsTopologicalAddTorsor P]
    (f : V →ᵃ[𝕜] P) (hf : Function.Injective f) :
    IsClosedMap f := by
  intro s hs
  have hlin_inj : Function.Injective f.linear := (AffineMap.linear_injective_iff (f := f)).2 hf
  have hclosedEmbedding : Topology.IsClosedEmbedding f.linear :=
    LinearMap.isClosedEmbedding_of_injective (f := f.linear) (LinearMap.ker_eq_bot.2 hlin_inj)
  have hlin_closed : IsClosed (f.linear '' s) :=
    (Topology.IsClosedEmbedding.isClosedMap hclosedEmbedding) _ hs
  have hfx (x : V) : f x = f.linear x +ᵥ f 0 := by
    simpa [vadd_eq_add] using (f.map_vadd (0 : V) x)
  have himage : f '' s = (fun y : E => y +ᵥ f 0) '' (f.linear '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨f.linear x, ⟨x, hx, rfl⟩, ?_⟩
      exact (hfx x).symm
    · rintro ⟨z, hz, hy⟩
      rcases hz with ⟨x, hx, hz'⟩
      refine ⟨x, hx, ?_⟩
      calc
        f x = f.linear x +ᵥ f 0 := hfx x
        _ = z +ᵥ f 0 := by rw [hz']
        _ = y := hy
  rw [himage]
  exact ((Homeomorph.vaddConst (f 0)).isClosed_image).2 hlin_closed

namespace Set.IsOrthant

/-- Propositon 17.0.15 (1): every skew orthant is closed once the source nonnegative orthant is
closed. -/
theorem isClosed {M : Type*}
    [TopologicalSpace M] [AddCommGroup M] [Module 𝕜 M]
    [Preorder M]
    [IsTopologicalAddGroup M] [ContinuousSMul 𝕜 M] [T2Space M]
    [FiniteDimensional 𝕜 M]
    {P : Type*} [TopologicalSpace P] [AddTorsor E P] [IsTopologicalAddTorsor P]
    {s : Set P} (hs : s.IsOrthant 𝕜 M)
    (hMclosed : IsClosed (Set.Ici (0 : M))) :
    IsClosed s := by
  rcases (Set.IsOrthant.exists_image_Ici (𝕜 := 𝕜) (M := M) hs) with ⟨f, hf, rfl⟩
  exact (isClosedMap_of_injective_affine (f := f) hf) _ hMclosed

/-- Closed-Ici bridge form of Proposition 17.0.15 (1): if the source order has intrinsic closed
upper intervals, skew orthants are closed without an explicit `Set.Ici` closedness hypothesis. -/
theorem isClosed_of_closedIciTopology {M : Type*}
    [TopologicalSpace M] [AddCommGroup M] [Module 𝕜 M]
    [Preorder M] [ClosedIciTopology M]
    [IsTopologicalAddGroup M] [ContinuousSMul 𝕜 M] [T2Space M]
    [FiniteDimensional 𝕜 M]
    {P : Type*} [TopologicalSpace P] [AddTorsor E P] [IsTopologicalAddTorsor P]
    {s : Set P} (hs : s.IsOrthant 𝕜 M) :
    IsClosed s :=
  hs.isClosed (isClosed_Ici : IsClosed (Set.Ici (0 : M)))

end Set.IsOrthant

end Orthant

/- Propositon 17.0.15 (2): more generally, every generalized simplex is closed. This clause is
already the canonical simplex-carrier theorem `Affine.Simplex.isClosed`, reused
directly here. -/
recall Affine.Simplex.isClosed
