import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise

universe u v w

section

namespace Function

variable {𝕜 : Type v} {α : Type w}

/-- Helper for Theorem 4.7: the canonical scalar action on `WithTopBot α` acts on finite values
and fixes the two boundary points. -/
local instance instSMulWithTopBot [SMul 𝕜 α] : SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

/-- Helper for Theorem 4.7: the chapter owner `Function.IsConvex` is convexity of the finite-height
epigraph. This local file keeps the owner surface available without routing through the broken
`Theorem_4_2` module. -/
abbrev IsConvex (𝕜 : Type v) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type w} [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Helper for Theorem 4.7: a `WithTopBot α` value that is neither `⊤` nor `⊥` is represented by
some finite height `a : α`. -/
private theorem exists_coe_of_ne_top_ne_bot
    {α : Type w} {z : WithTopBot α} (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : α, (a : WithTopBot α) = z := by
  cases hz : z using WithTop.recTopCoe with
  | top =>
      exact False.elim (hz_top hz)
  | coe z' =>
      cases hz' : z' using WithBot.recBotCoe with
      | bot =>
          exact False.elim (hz_bot (by simp [hz, hz']))
      | coe a =>
          exact ⟨a, rfl⟩

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 4.7 says that for a positively homogeneous function
  `f : E → [-∞, +∞]`, convexity is equivalent to subadditivity.
- `core/canonical`: the governing object is the finite-height epigraph `epi f`; the owner
  predicate `Function.IsConvex` is just `Convex 𝕜 (epi f)`.
- `bridge/view`: positive homogeneity makes `epi f` a cone, and subadditivity is equivalent to
  closure of `epi f` under addition. Theorem 2.6 then identifies convexity of that cone with
  additive closure.
- Primitive data vs derived API: the primitive datum is the function `f`; positive homogeneity and
  the non-`⊥` side condition are source-facing hypotheses, while convexity and subadditivity are
  derived viewpoints on the same epigraph geometry.
-/

section Cone

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type w} [PartialOrder α] [SMul 𝕜 α]
variable [PosSMulMono 𝕜 α]

/-- Helper for Theorem 4.7: the finite-height epigraph of a positively homogeneous function is a
cone. -/
theorem isCone_epi_of_positivelyHomogeneous
    {f : E → WithTopBot α} (hf_hom : f.PositivelyHomogeneous 𝕜) :
    Set.IsCone 𝕜 (epi f) := by
  intro c hc p hp
  rcases p with ⟨x, μ⟩
  rw [mem_epi_iff] at hp ⊢
  -- Positive homogeneity rewrites the function value, then scalar monotonicity lifts the height
  -- inequality to the scaled point.
  calc
    f (c • x) = c • f x := by simpa using hf_hom.map_smul hc x
    _ ≤ c • μ := by
      match hfx : f x with
      | ⊥ =>
          have hfx_bot : f x = ⊥ := by
            simpa using hfx
          change (⊥ : WithTopBot α) ≤ ((c • μ : α) : WithTopBot α)
          exact bot_le
      | (a : α) =>
          have hfx_coe : f x = (a : WithTopBot α) := by
            simpa using hfx
          have hle' : (a : WithTopBot α) ≤ (μ : WithTopBot α) := by
            simpa [hfx_coe] using hp
          have hle : a ≤ μ := by
            exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hle')
          have hsmul : c • ((a : α) : WithTopBot α) ≤ c • ((μ : α) : WithTopBot α) := by
            change ((c • a : α) : WithTopBot α) ≤ ((c • μ : α) : WithTopBot α)
            exact WithTop.coe_le_coe.mpr
              (WithBot.coe_le_coe.mpr (smul_le_smul_of_nonneg_left hle hc.le))
          simpa [hfx_coe] using hsmul
      | ⊤ =>
          have hfx_top : f x = ⊤ := by
            simpa using hfx
          rw [hfx_top] at hp
          have hnot : ¬ ((⊤ : WithTopBot α) ≤ (μ : WithTopBot α)) := by
            simp
          exact False.elim (hnot hp)

end Cone

section Subadditivity

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type w} [AddCommMonoid α] [PartialOrder α] [Module 𝕜 α]
variable [AddLeftMono α] [PosSMulMono 𝕜 α]

/-- Helper for Theorem 4.7: a pointwise subadditivity inequality makes the finite-height epigraph
closed under set addition. -/
theorem epi_add_subset_of_subadditive
    {f : E → WithTopBot α}
    (hsub : ∀ x y : E, f (x + y) ≤ f x + f y) :
    epi f + epi f ⊆ epi f := by
  rintro _ ⟨⟨x, μ⟩, hx_epi, ⟨y, ν⟩, hy_epi, rfl⟩
  rw [mem_epi_iff] at hx_epi hy_epi ⊢
  -- The source inequality closes the function value, and the epigraph bounds close the height.
  exact (hsub x y).trans <| add_le_add hx_epi hy_epi

section

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type w} [AddCommMonoid α] [PartialOrder α] [Module 𝕜 α]
variable [PosSMulMono 𝕜 α]

/-- Helper for Theorem 4.7: additive closure of the finite-height epigraph recovers the pointwise
subadditivity inequality, provided `f` never takes the value `⊥`. -/
theorem subadditive_of_epi_add_subset
    {f : E → WithTopBot α} (hf_ne_bot : ∀ x : E, f x ≠ ⊥)
    (hadd : epi f + epi f ⊆ epi f) :
    ∀ x y : E, f (x + y) ≤ f x + f y := by
  intro x y
  by_cases hxtop : f x = ⊤
  · -- If `f x = ⊤`, then the right-hand side is already `⊤`.
    rw [hxtop]
    exact le_top
  by_cases hytop : f y = ⊤
  · -- The symmetric `⊤` branch is again immediate.
    rcases exists_coe_of_ne_top_ne_bot hxtop (hf_ne_bot x) with ⟨μ, hμ⟩
    have hsum_top : f x + f y = (⊤ : WithTopBot α) := by
      rw [hytop]
      simp
    rw [hsum_top]
    exact le_top
  have hxbot : f x ≠ ⊥ := hf_ne_bot x
  have hybot : f y ≠ ⊥ := hf_ne_bot y
  rcases exists_coe_of_ne_top_ne_bot hxtop hxbot with ⟨μ, hμ⟩
  rcases exists_coe_of_ne_top_ne_bot hytop hybot with ⟨ν, hν⟩
  have hx_epi : (x, μ) ∈ epi f := by
    rw [mem_epi_iff]
    simp [hμ]
  have hy_epi : (y, ν) ∈ epi f := by
    rw [mem_epi_iff]
    simp [hν]
  have hxy_epi : (x + y, μ + ν) ∈ epi f := by
    -- Closure of `epi f` under addition turns the canonical points above `x` and `y`
    -- into the canonical point above `x + y`.
    exact hadd ⟨(x, μ), hx_epi, (y, ν), hy_epi, rfl⟩
  have hxy_le : f (x + y) ≤ μ + ν := by
    exact mem_epi_iff.mp hxy_epi
  simpa [hμ, hν] using hxy_le

end

-- Route correction: the file originally routed through a mixed `ConvexOn`/finite-height epigraph
-- argument. The source proof works directly on the finite-height epigraph `epi f`, so the final
-- theorem now stays entirely on that owner and applies Theorem 2.6 exactly as in Rockafellar.
/-- Theorem 4.7: a positively homogeneous function `f : E → (-∞, +∞]` is convex if and only if
it is subadditive, i.e. `f (x + y) ≤ f x + f y` for all `x, y ∈ E`. -/
theorem isConvex_iff_subadditive_of_positivelyHomogeneous
    [PosMulReflectLT 𝕜]
    {f : E → WithTopBot α} (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_ne_bot : ∀ x : E, f x ≠ ⊥) :
    f.IsConvex 𝕜 ↔ ∀ x y : E, f (x + y) ≤ f x + f y := by
  -- Theorem 2.6 applies to the cone `epi f`; the remaining bridge is exactly the source
  -- equivalence between additive closure of the epigraph and subadditivity of `f`.
  refine (isCone_epi_of_positivelyHomogeneous hf_hom).convex_iff_add_subset.trans ?_
  constructor
  · exact subadditive_of_epi_add_subset hf_ne_bot
  · exact epi_add_subset_of_subadditive

end Subadditivity

end Function
end
