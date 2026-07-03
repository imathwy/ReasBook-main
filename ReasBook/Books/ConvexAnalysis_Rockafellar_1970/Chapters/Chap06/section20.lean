import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_20 (from Chap02) -/
section IntrinsicInterior

open scoped Pointwise Rockafellar

variable {𝕜 E : Type*}
  [DivisionRing 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [SMulCommClass 𝕜ˣ 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.20 records two closure properties of convex cones in a
  finite-dimensional real normed space, hence in `ℝ^n`: their relative interiors and their
  closures are again convex cones.
- `core/canonical`: for clause (1), the source-facing owner abstractions are `Set.IsCone 𝕜` for
  the conic property, `intrinsicInterior 𝕜` for relative interior, and the intrinsic-dilation
  bridge `Set.intrinsicInterior_smul` from Corollary 6.6.1.
  Clause (2) is owned separately by the canonical closure construction `ConvexCone.closure`, whose
  natural ambient assumptions are strictly weaker still.
- `bridge/view`: clause (1) is exposed directly on the source-facing owner
  `Set.IsConvexCone 𝕜` by combining the cone-side owner theorem below with the upstream convexity
  owner theorem `Convex.intrinsicInterior`.
- Primitive data vs derived API: for clause (1), the primitive source-facing input is the cone
  predicate `Set.IsCone 𝕜 K` on a set `K`. Equality of positive dilates `c • K = K` and the cone
  structure on `intrinsicInterior 𝕜 K` are derived API on that owner surface.
- Layer target: clause (1) is owner-level derived API on `Set.IsCone`; clause (2) is exact owner
  reuse via `ConvexCone.closure` in its own weaker owner section below.
-/

/- Text 6.20 (1), convexity component: the relative interior of a convex set is convex, so for a
convex cone this part is exactly the upstream owner theorem `Convex.intrinsicInterior`. -/

namespace Set.IsCone

/-- Text 6.20 (1), cone component: the relative interior of a convex cone is again a cone in the
source-facing sense `Set.IsCone 𝕜`. Combined with `Convex.intrinsicInterior`, this recovers the
full convex-cone statement under the additional convexity hypothesis. -/
theorem intrinsicInterior {K : Set E} (hK : Set.IsCone 𝕜 K) :
    Set.IsCone 𝕜 (ri[𝕜](K)) := by
  intro y hy
  rcases hy with ⟨c, hc, x, hx, rfl⟩
  have hsmul : c • K = K := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    constructor
    · intro hz
      simpa [smul_smul, hc.ne'] using hK.smul_mem hc hz
    · exact hK.smul_mem (inv_pos.2 hc)
  have hri_smul :
      ri[𝕜](c • K) = c • ri[𝕜](K) := by
    simpa using Set.intrinsicInterior_smul K c
      (Or.inr (isUnit_iff_ne_zero.mpr hc.ne')) ⟨x, hx⟩
  have hcx : c • x ∈ c • ri[𝕜](K) := ⟨x, hx, rfl⟩
  have hcx' : c • x ∈ ri[𝕜](c • K) := by
    simpa [hri_smul] using hcx
  simpa [hsmul] using hcx'

end Set.IsCone

namespace Set.IsConvexCone

variable {𝕜 E : Type*}
  [Field 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [SMulCommClass 𝕜ˣ 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- Text 6.20 (1), source-facing owner form: the relative interior of a convex cone is again a
convex cone. -/
theorem intrinsicInterior {K : Set E} (hK : Set.IsConvexCone 𝕜 K) :
    Set.IsConvexCone 𝕜 (ri[𝕜](K)) := by
  exact ⟨hK.isCone.intrinsicInterior, hK.convex.intrinsicInterior⟩

end Set.IsConvexCone

end IntrinsicInterior

section Closure

open Set
open scoped Pointwise

namespace Set.IsCone

variable {𝕜 : Type*} [LT 𝕜] [Zero 𝕜]
variable {E : Type*} [TopologicalSpace E] [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E]

/-- Text 6.20 (2), unbundled owner form: the closure of a cone is again a cone. -/
theorem closure {K : Set E} (hK : Set.IsCone 𝕜 K) :
    Set.IsCone 𝕜 (_root_.closure K) := by
  intro x hx
  rcases hx with ⟨c, hc, y, hy, rfl⟩
  have hsubset : c • K ⊆ K := hK.smul_set_subset hc
  have hcy : c • y ∈ _root_.closure (c • K) :=
    (smul_closure_subset c K) ⟨y, hy, rfl⟩
  exact (closure_mono hsubset) hcy

end Set.IsCone

namespace Set.IsConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [SMul 𝕜 E]
variable [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

/-- Text 6.20 (2), source-facing owner form: the closure of a convex cone is again a convex
cone. This is the direct unbundled owner theorem behind later graph-closure arguments. -/
theorem closure {K : Set E} (hK : Set.IsConvexCone 𝕜 K) :
    Set.IsConvexCone 𝕜 (_root_.closure K) := by
  refine ⟨hK.isCone.closure, ?_⟩
  intro x hx y hy a b ha hb hab
  exact map_mem_closure₂
    (f := fun x y : E ↦ a • x + b • y)
    ((continuous_fst.const_smul a).add (continuous_snd.const_smul b))
    hx hy
    (fun x hx y hy ↦ hK.convex hx hy ha hb hab)

end Set.IsConvexCone

section ConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/- Text 6.20 (2), bundled companion: the closure of a convex cone is canonically a convex cone,
namely
`ConvexCone.closure`. In the source this is stated for cones in `ℝ^n`; the owner construction
itself lives in the weaker topological additive `𝕜`-module context below. -/
recall ConvexCone.closure

end ConvexCone

end Closure
