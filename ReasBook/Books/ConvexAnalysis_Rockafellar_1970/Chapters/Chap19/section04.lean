import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_19_4 (from Chap04) -/
noncomputable section

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {α : Type*} [OrderedAddCommGroup α] [Module 𝕜 α]
  [TopologicalSpace α] [IsTopologicalAddGroup α]
  [ContinuousSMul 𝕜 α] [FiniteDimensional 𝕜 α]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 19.4 says that the pointwise sum of two polyhedral convex functions
  taking values in `(-∞, +∞]` is again polyhedral convex.
- `core/canonical`: the owner predicate already present upstream is
  `Function.HasPolyhedralEpigraph` on intrinsic epigraphs `epi f` for functions
  `f : E → WithTopBot α`.
- `bridge/view`: this item keeps only the canonical owner theorem on `WithTopBot α`; any concrete
  scalar-codomain specialization belongs in downstream files.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph`;
- the pointwise function addition `f₁ + f₂`;
- the primitive codomain-side exclusion of `⊥`, written as `∀ x, fᵢ x ≠ ⊥`, with
  `∀ x, ⊥ < fᵢ x` kept as a thin bridge surface.

Primitive data vs derived API:
- primitive inputs: the two functions `f₁` and `f₂`;
- source hypotheses: each function has polyhedral epigraph and takes values in `(-∞, +∞]`,
  written at the primitive owner surface as `∀ x, fᵢ x ≠ ⊥`;
- derived output: the pointwise sum `f₁ + f₂` has polyhedral epigraph.

Layer target: `core/canonical`, stated directly on `Function.HasPolyhedralEpigraph` at the
Chapter 19 finite-dimensional polyhedral-image layer:
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]` and
`[TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
[ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]`, with codomain ambient module
`[OrderedAddCommGroup α] [Module 𝕜 α] [TopologicalSpace α] [IsTopologicalAddGroup α]
[ContinuousSMul 𝕜 α] [FiniteDimensional 𝕜 α]`.
-/

namespace Function.HasPolyhedralEpigraph

-- Proof sketch: combine the two owner hypotheses and the pointwise `⊥`-exclusion hypotheses
-- under pointwise addition, then transport this combined structure to the epigraph owner layer.
/-- Theorem 19.4, primitive codomain owner form: if `f₁` and `f₂` have polyhedral epigraphs and
never take the value `⊥`, then their pointwise sum has polyhedral epigraph. -/
theorem add_of_ne_bot
    {f₁ f₂ : E → WithTopBot α}
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (f₁ + f₂).HasPolyhedralEpigraph := by
  let fstMap : E × α × α →ₗ[𝕜] E :=
    LinearMap.fst 𝕜 E (α × α)
  let μ₁Map : E × α × α →ₗ[𝕜] α :=
    (LinearMap.fst 𝕜 α α).comp (LinearMap.snd 𝕜 E (α × α))
  let μ₂Map : E × α × α →ₗ[𝕜] α :=
    (LinearMap.snd 𝕜 α α).comp (LinearMap.snd 𝕜 E (α × α))
  let toEμ₁ : E × α × α →ₗ[𝕜] E × α := fstMap.prod μ₁Map
  let toEμ₂ : E × α × α →ₗ[𝕜] E × α := fstMap.prod μ₂Map
  let sumMap : E × α × α →ₗ[𝕜] E × α := fstMap.prod (μ₁Map + μ₂Map)
  let constraints : Set (E × α × α) := (toEμ₁ ⁻¹' epi f₁) ∩ (toEμ₂ ⁻¹' epi f₂)
  have hconstraints_poly : constraints.IsPolyhedral 𝕜 := by
    have h₁ : (toEμ₁ ⁻¹' epi f₁).IsPolyhedral 𝕜 :=
      Set.IsPolyhedral.linear_preimage hf₁ toEμ₁
    have h₂ : (toEμ₂ ⁻¹' epi f₂).IsPolyhedral 𝕜 :=
      Set.IsPolyhedral.linear_preimage hf₂ toEμ₂
    exact Set.IsPolyhedral.inter (𝕜 := 𝕜) h₁ h₂
  have himage_poly : (sumMap '' constraints).IsPolyhedral 𝕜 :=
    Set.IsPolyhedral.linear_image hconstraints_poly sumMap
  have hepi_eq_image : epi (f₁ + f₂) = sumMap '' constraints := by
    ext p
    rcases p with ⟨x, μ⟩
    constructor
    · intro hp
      have hle : f₁ x + f₂ x ≤ (μ : WithTopBot α) := by
        simpa [mem_epi_iff] using hp
      have h₁_ne_top : f₁ x ≠ ⊤ := by
        intro h₁_top
        have hsum_top : f₁ x + f₂ x = (⊤ : WithTopBot α) := by
          simpa [h₁_top] using WithBotTop.top_add_of_ne_bot (hf₂_ne_bot x)
        have htop_le : (⊤ : WithTopBot α) ≤ (μ : WithTopBot α) := by
          rw [← hsum_top]
          exact hle
        have hnot : ¬ (⊤ : WithTopBot α) ≤ (μ : WithTopBot α) := by
          simp [top_le_iff]
        exact hnot htop_le
      have h₂_ne_top : f₂ x ≠ ⊤ := by
        intro h₂_top
        have hsum_top : f₁ x + f₂ x = (⊤ : WithTopBot α) := by
          simpa [h₂_top] using WithBotTop.add_top_of_ne_bot (hf₁_ne_bot x)
        have htop_le : (⊤ : WithTopBot α) ≤ (μ : WithTopBot α) := by
          rw [← hsum_top]
          exact hle
        have hnot : ¬ (⊤ : WithTopBot α) ≤ (μ : WithTopBot α) := by
          simp [top_le_iff]
        exact hnot htop_le
      rcases (WithBotTop.canLift_iff_ne_top_ne_bot).2 ⟨h₁_ne_top, hf₁_ne_bot x⟩ with ⟨a, ha⟩
      rcases (WithBotTop.canLift_iff_ne_top_ne_bot).2 ⟨h₂_ne_top, hf₂_ne_bot x⟩ with ⟨b, hb⟩
      have hab_le : a + b ≤ μ := by
        exact WithBotTop.coe_le_coe.mp (by simpa [ha, hb] using hle)
      refine ⟨(x, a, μ - a), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · change toEμ₁ (x, a, μ - a) ∈ epi f₁
          exact mem_epi_iff.mpr (by
            simp [fstMap, μ₁Map,
              LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, ha])
        · change toEμ₂ (x, a, μ - a) ∈ epi f₂
          have hb_le : b ≤ μ - a := by
            exact (le_sub_iff_add_le).2 (by
              simpa [add_comm, add_left_comm, add_assoc] using hab_le)
          have h₂_le : f₂ x ≤ ((μ - a : α) : WithTopBot α) := by
            simpa [hb] using (WithBotTop.coe_le_coe.mpr hb_le)
          exact mem_epi_iff.mpr (by
            simpa [toEμ₂, fstMap, μ₂Map, LinearMap.prod_apply,
              LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply] using h₂_le)
      · ext
        · simp [sumMap, fstMap, μ₁Map, μ₂Map, LinearMap.prod_apply,
            LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply]
        · simp [sumMap, fstMap, μ₁Map, μ₂Map, LinearMap.prod_apply,
            LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply]
    · rintro ⟨q, hq, hqsum⟩
      rcases hq with ⟨hq₁, hq₂⟩
      have h₁_le : f₁ q.1 ≤ (q.2.1 : WithTopBot α) := by
        exact mem_epi_iff.mp (by
          simpa [toEμ₁, fstMap, μ₁Map, LinearMap.prod_apply,
            LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply] using hq₁)
      have h₂_le : f₂ q.1 ≤ (q.2.2 : WithTopBot α) := by
        exact mem_epi_iff.mp (by
          simpa [toEμ₂, fstMap, μ₂Map, LinearMap.prod_apply,
            LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply] using hq₂)
      have hsum_le : f₁ q.1 + f₂ q.1 ≤ ((q.2.1 + q.2.2 : α) : WithTopBot α) :=
        add_le_add h₁_le h₂_le
      have hmem_q : sumMap q ∈ epi (f₁ + f₂) :=
        mem_epi_iff.mpr (by
          simpa [sumMap, fstMap, μ₁Map, μ₂Map, LinearMap.prod_apply,
            LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply] using hsum_le)
      exact hqsum ▸ hmem_q
  change Set.IsPolyhedral 𝕜 (epi (f₁ + f₂))
  rw [hepi_eq_image]
  exact himage_poly

/-- Theorem 19.4, bridge form with explicit `(-∞, +∞]` surface phrasing. -/
theorem add
    {f₁ f₂ : E → WithTopBot α}
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₁_bot_lt : ∀ x : E, ⊥ < f₁ x)
    (hf₂_bot_lt : ∀ x : E, ⊥ < f₂ x) :
    (f₁ + f₂).HasPolyhedralEpigraph :=
  add_of_ne_bot hf₁ hf₂ (fun x ↦ ne_of_gt (hf₁_bot_lt x)) (fun x ↦ ne_of_gt (hf₂_bot_lt x))

end Function.HasPolyhedralEpigraph

end
