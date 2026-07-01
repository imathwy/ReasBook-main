import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

namespace Rockafellar

/- Source notation for the canonical positive orthant as the interior of the nonnegative orthant. -/
scoped notation:max "orthant⁺[" 𝕜 "](" M ")" => interior (orthant[𝕜](M))

end Rockafellar

open scoped Rockafellar
/-
Source/core/bridge triage:
- `source-facing`: Definition 2.5.12 names the positive orthant as the interior of the
  nonnegative cone.
- `core/canonical`: the owner surface is the short notation `orthant⁺[𝕜](M)`, definitionally
  equal to `interior (orthant[𝕜](M))` at the abstract ordered topological module layer.
- Primitive data vs derived API: `orthant[𝕜](M)` and topological interior are primitive;
  cone/convex facts below are derived bridge API, with any `ConvexCone.positive` references
  kept inside bridge proofs.
- Domain-style sampling: `orthant[𝕜](M)`, `ConvexCone.smul_mem`, and `interior`.
- Layer target: `core/canonical`; concrete coordinate models and coordinatewise positivity tests
  belong in downstream bridge files.
-/

section PositiveOrthantMembership

variable {𝕜 M : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]

/-- Definition 2.5.12: bridge form of positive-orthant membership through the concrete upper-set model. -/
theorem mem_positiveOrthant_iff_mem_interior_Ici {x : M} :
    x ∈ orthant⁺[𝕜](M) ↔
      x ∈ interior (Set.Ici (0 : M)) := by
  -- Unfold the positive-orthant owner once and rewrite through Definition 2.5.11.
  rw [orthant_eq_Ici]

end PositiveOrthantMembership

section PositiveOrthantCone

variable {𝕜 M : Type*} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]

variable [ContinuousConstSMul 𝕜 M]

/-- Helper for Definition 2.5.12: positive scalar multiplication preserves the nonnegative orthant. -/
private theorem smul_orthant_subset {c : 𝕜} (hc : 0 < c) :
    c • orthant[𝕜](M) ⊆ orthant[𝕜](M) := by
  -- Route correction: keep the interior-of-orthant owner and remove the parser-invalid `omit`
  -- wrapper; the carrier-level cone argument is unchanged.
  -- Reduce membership in the scalar image to a point of the underlying positive cone.
  rintro _ ⟨y, hy, rfl⟩
  exact (ConvexCone.positive 𝕜 M).smul_mem hc hy

/-- Helper for Definition 2.5.12: the interior of the orthant is stable under positive scaling. -/
private theorem smul_mem_positiveOrthant {c : 𝕜} (hc : 0 < c) {x : M}
    (hx : x ∈ orthant⁺[𝕜](M)) :
    c • x ∈ orthant⁺[𝕜](M) := by
  -- First place the scaled point in the scaled interior.
  have hx_smul : c • x ∈ c • orthant⁺[𝕜](M) :=
    Set.smul_mem_smul_set hx
  have hx_interior : c • x ∈ interior (c • orthant[𝕜](M)) := by
    rw [interior_smul₀ (α := M) (G₀ := 𝕜) (c := c) (ne_of_gt hc)]
    exact hx_smul
  -- Then move back to the original orthant using monotonicity of interior.
  exact interior_mono (smul_orthant_subset hc) hx_interior

/-- The positive orthant is a cone at the canonical owner level. -/
theorem isCone_positiveOrthant :
    Set.IsCone 𝕜 (orthant⁺[𝕜](M)) := by
  -- Cone closure reduces to positive-scalar closure on the carrier set.
  refine (Set.isCone_iff_forall_pos_smul_subset (𝕜 := 𝕜) (K := orthant⁺[𝕜](M))).2 ?_
  intro c hc x hx
  -- Rewrite the scaled interior back to an interior of a scaled carrier set.
  have hx_interior : x ∈ interior (c • orthant[𝕜](M)) := by
    rwa [← interior_smul₀ (α := M) (G₀ := 𝕜) (c := c) (ne_of_gt hc)] at hx
  -- Then shrink along the carrier-level orthant inclusion.
  exact interior_mono (smul_orthant_subset hc) hx_interior

end PositiveOrthantCone

section PositiveOrthantConvex

variable {𝕜 M : Type*} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]

variable [ContinuousConstSMul 𝕜 M] [ContinuousConstVAdd M M]

/-- Helper for Definition 2.5.12: the nonnegative orthant is closed under addition. -/
private theorem add_orthant_subset :
    orthant[𝕜](M) + orthant[𝕜](M) ⊆ orthant[𝕜](M) := by
  -- Route correction: keep the additive proof at the carrier level and only transport to
  -- interiors afterward, instead of changing the source-faithful owner.
  -- Expand membership in the Minkowski sum and use addition in the ambient positive cone.
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact (ConvexCone.positive 𝕜 M).add_mem hu hv

/-- Helper for Definition 2.5.12: the interior of the orthant is closed under addition. -/
private theorem add_mem_positiveOrthant {x y : M}
    (hx : x ∈ orthant⁺[𝕜](M))
    (hy : y ∈ orthant⁺[𝕜](M)) :
    x + y ∈ orthant⁺[𝕜](M) := by
  -- Add an interior point to a point of the orthant to reach the interior of the Minkowski sum.
  have hxy : x + y ∈ interior (orthant[𝕜](M) + orthant[𝕜](M)) := by
    exact subset_interior_add_right (Set.add_mem_add (interior_subset hx) hy)
  -- The Minkowski sum sits back inside the orthant because the orthant is additive.
  have hsubset : interior (orthant[𝕜](M) + orthant[𝕜](M)) ⊆ orthant⁺[𝕜](M) :=
    interior_mono add_orthant_subset
  exact hsubset hxy

/-- Helper for Definition 2.5.12: scalar closure of the positive orthant in the exact field shape
required by `ConvexCone`. -/
private theorem positiveOrthant_smul_mem_field :
    ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ orthant⁺[𝕜](M) → c • x ∈ orthant⁺[𝕜](M) := by
  -- Reuse the owner-level scalar-stability bridge from the cone section.
  intro c hc x hx
  exact smul_mem_positiveOrthant hc hx

/-- Helper for Definition 2.5.12: additive closure of the positive orthant in the exact field shape
required by `ConvexCone`. -/
private theorem positiveOrthant_add_mem_field :
    ∀ ⦃x : M⦄, x ∈ orthant⁺[𝕜](M) → ∀ ⦃y : M⦄, y ∈ orthant⁺[𝕜](M) →
      x + y ∈ orthant⁺[𝕜](M) := by
  -- Reuse the owner-level additive-stability bridge for the cone packaging step.
  intro x hx y hy
  exact add_mem_positiveOrthant hx hy

/-- Helper for Definition 2.5.12: the positive orthant carries the canonical convex-cone
structure induced by the established scalar and additive closure lemmas. -/
private def positiveOrthantCone : ConvexCone 𝕜 M :=
  { carrier := orthant⁺[𝕜](M)
    smul_mem' := positiveOrthant_smul_mem_field
    add_mem' := positiveOrthant_add_mem_field }

/-- The positive orthant is convex after forgetting to its carrier set. -/
theorem convex_positiveOrthant :
    Convex 𝕜 (orthant⁺[𝕜](M)) := by
  -- Package the established scalar and additive closure into the canonical local cone owner.
  -- A convex cone has a convex carrier set.
  simpa [positiveOrthantCone] using (ConvexCone.convex (positiveOrthantCone : ConvexCone 𝕜 M))

end PositiveOrthantConvex
