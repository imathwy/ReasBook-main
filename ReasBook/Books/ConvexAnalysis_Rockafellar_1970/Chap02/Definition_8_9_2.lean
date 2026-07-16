import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_0

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {𝕜 : Type*} [DivisionRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddGroup α] [ConditionallyCompleteLattice α]

open scoped Rockafellar

namespace Function

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.9.2 introduces the numerical invariants lineality and rank of a
  convex function.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.lineal` from Definition 8.9.0, reused in Definition 8.9.1 as the source's
  affine-direction space, together with the affine-dimension owner `Set.affineDim`.
- `bridge/view`: the numerical invariants are exposed directly from these owners
  rather than through a second wrapper layer.
- Primitive data vs derived API: the primitive data are the affine dimensions of `dom(f)` and of
  `lineal f`; the scalar quantities `lineality[𝕜](f)` and `rank[𝕜](f)` are derived API.

Domain-style sampling used here:
- `Set.affineDim` from Definition 2.4.10;
- `Function.lineal` and `Function.mem_lineal_iff` from Definition 8.9.0;
- `Function.mem_lineal_iff_zero_mem_lin_epi`
  from Definition 8.9.1.

Layer target: `core/canonical` owner layer on `Function`, with theorem surfaces using the
owner-level notation directly.
-/

variable (𝕜)

/-- Definition 8.9.2: the lineality of a convex function is the affine dimension of the owner
`lineal f` used in Definition 8.9.1 for its affine-direction space. -/
abbrev lineality (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] : ℤ :=
  dim[𝕜](lin(f))

scoped[Rockafellar] notation (name := functionLinealityNotation_8_9_2)
    "lineality[" 𝕜 "](" f ")" => Function.lineality 𝕜 f

/-- The lineality of a function is the affine dimension of `lineal f`. -/
theorem lineality_eq (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] :
    lineality[𝕜](f) = dim[𝕜](lin(f)) :=
  rfl

/-- Definition 8.9.2: the rank of a convex function is the affine dimension of its effective
domain minus its lineality. -/
abbrev rank (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction] : ℤ :=
  dim[𝕜](dom(f)) - lineality[𝕜](f)

scoped[Rockafellar] notation (name := functionRankNotation_8_9_2)
    "rank[" 𝕜 "](" f ")" => Function.rank 𝕜 f

/-- The rank of a function is the affine dimension of its effective domain minus its lineality. -/
theorem rank_eq (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction] :
    rank[𝕜](f) = dim[𝕜](dom(f)) - lineality[𝕜](f) :=
  rfl

end Function

end
