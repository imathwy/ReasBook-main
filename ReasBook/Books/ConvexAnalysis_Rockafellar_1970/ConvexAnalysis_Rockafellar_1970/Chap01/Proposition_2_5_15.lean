import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Proposition 2.5.15 asserts that the two orthants introduced just above are
  convex cones in the textbook sense.
- `core/canonical`: the nonnegative orthant clause belongs at the generic ordered-module owner
  layer `orthant[𝕜](M)`; for the positive orthant this file works on the canonical owner surface
  `orthant⁺[𝕜](M)`.
- `bridge/view`: both clauses are set-level `Set.IsConvexCone` statements, proved from the bundled
  owner for `orthant[𝕜](M)` and from Definition 2.5.12 for `orthant⁺[𝕜](M)`.
- Primitive data vs derived API: the orthants themselves are already defined; the convex-cone
  claims are derived from the existing carrier descriptions, cone closure, and convexity theorems.
- Domain-style sampling: `ConvexCone.positive`, `ConvexCone.mem_positive`, `Set.IsCone.hull_eq`,
  `Set.IsConvexCone.hull_eq_iff`, `mem_orthant_iff`, and
  `mem_positiveOrthant_iff_mem_interior_Ici`.
- Layer target: both clauses are now `source-facing` set-level convex-cone statements through the
  short owner `Set.IsConvexCone`; clause (1) is scalar/ambient-generalized, and clause (2) is
  implemented at the same abstract ordered topological module layer as Definition 2.5.12.
-/

section Orthant

variable {𝕜 M : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M]

/- Proposition 2.5.15 (1): the non-negative orthant is a convex cone at the canonical scalar and
ambient owner layer. -/
namespace Set.IsConvexCone

/-- Proposition 2.5.15: the nonnegative orthant is a convex cone. -/
theorem orthant :
    Set.IsConvexCone 𝕜 (orthant[𝕜](M)) := by
  -- Transport the bundled positive cone result directly to the orthant carrier.
  simpa using (ConvexCone.positive 𝕜 M).isConvexCone

end Set.IsConvexCone

/-- Helper for Proposition 2.5.15: expose the nonnegative-orthant clause without reopening the
owner namespace. -/
theorem orthant_isConvexCone :
    Set.IsConvexCone 𝕜 (orthant[𝕜](M)) := by
  -- Reuse the owner theorem verbatim through the source-facing wrapper name.
  simpa using (Set.IsConvexCone.orthant (𝕜 := 𝕜) (M := M))

end Orthant

section PositiveOrthant

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable {M : Type*} [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
variable [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]
variable [ContinuousConstSMul 𝕜 M] [ContinuousConstVAdd M M]

/- Proposition 2.5.15 (2): the positive orthant is a convex cone at the abstract owner layer. -/
namespace Set.IsConvexCone

/-- Proposition 2.5.15: the positive orthant is a convex cone. -/
theorem positiveOrthant :
    Set.IsConvexCone 𝕜 (orthant⁺[𝕜](M)) := by
  -- Combine the previously proved cone and convexity facts at the set owner level.
  exact ⟨isCone_positiveOrthant, convex_positiveOrthant⟩

end Set.IsConvexCone

/-- Helper for Proposition 2.5.15: expose the positive-orthant clause without reopening the
owner namespace. -/
theorem positiveOrthant_isConvexCone :
    Set.IsConvexCone 𝕜 (orthant⁺[𝕜](M)) := by
  -- Reuse the owner theorem verbatim through the source-facing wrapper name.
  simpa using (Set.IsConvexCone.positiveOrthant (𝕜 := 𝕜) (M := M))

end PositiveOrthant
