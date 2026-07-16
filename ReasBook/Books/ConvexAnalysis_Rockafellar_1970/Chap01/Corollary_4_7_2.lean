import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

namespace Function

local instance instSmulWithTopBot472 {𝕜 : Type v} {α : Type u} [SMul 𝕜 α] :
    SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

private def withTopBotNeg {α : Type u} [Neg α] : WithTopBot α → WithTopBot α
  | ⊥ => ⊤
  | (a : α) => (-a : α)
  | ⊤ => ⊥

local instance instNegWithTopBot472 {α : Type u} [Neg α] : Neg (WithTopBot α) :=
  ⟨withTopBotNeg⟩

@[simp] private theorem withTopBot_neg_coe {α : Type u} [Neg α] (a : α) :
    -((a : WithTopBot α)) = ((-a : α) : WithTopBot α) :=
  rfl

@[simp] private theorem withTopBot_neg_top {α : Type u} [Neg α] :
    -((⊤ : WithTopBot α)) = (⊥ : WithTopBot α) :=
  rfl

@[simp] private theorem withTopBot_neg_bot {α : Type u} [Neg α] :
    -((⊥ : WithTopBot α)) = (⊤ : WithTopBot α) :=
  rfl

private theorem withTopBot_exists_coe_of_ne_top_ne_bot {α : Type u} {z : WithTopBot α}
    (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : α, (a : WithTopBot α) = z := by
  cases hz : z using WithTop.recTopCoe with
  | top => exact False.elim (hz_top hz)
  | coe z' =>
      cases hz' : z' using WithBot.recBotCoe with
      | bot => exact False.elim (hz_bot (by simp [hz, hz']))
      | coe a => exact ⟨a, rfl⟩

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 4.7.2 states that a positively homogeneous proper convex function
  satisfies `f (-x) ≥ -f x`.
- `core/canonical`: the function uses the project-wide `WithTopBot` codomain and
  `Function.IsConvex` owner from Theorem 4.2.
- `bridge/view`: Theorem 4.7 supplies subadditivity directly on that owner; no raw coercion between
  the incompatible `WithBotTop` and `WithTopBot` boundary conventions is used.
- Primitive data vs derived API: positive homogeneity, convexity, and exclusion of `⊥` are the
  primitive assumptions; the symmetry inequality is derived from subadditivity at `x + (-x)`.
- Layer target: source-facing theorem over the canonical extended-value owner.
-/

section ZeroValue

variable {𝕜 : Type v} [DivisionRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-- A positively homogeneous extended-valued function that never equals `⊥` is nonnegative
at the origin. -/
theorem zero_le_apply_zero_of_positivelyHomogeneous {f : E → WithTopBot 𝕜}
    (hf_hom : f.PositivelyHomogeneous 𝕜) (hf_ne_bot : ∀ y : E, f y ≠ ⊥) :
    (0 : WithTopBot 𝕜) ≤ f 0 := by
  by_cases hzero_top : f 0 = ⊤
  · simp [hzero_top]
  · have hzero_ne_bot : f 0 ≠ ⊥ := hf_ne_bot 0
    rcases withTopBot_exists_coe_of_ne_top_ne_bot hzero_top hzero_ne_bot with ⟨a, ha⟩
    have hhom_zero : (a : WithTopBot 𝕜) = (2 : 𝕜) • (a : WithTopBot 𝕜) := by
      simpa [ha] using hf_hom.map_smul (zero_lt_two : (0 : 𝕜) < 2) (0 : E)
    have htwo : a = 2 * a := by
      exact WithBot.coe_injective (WithTop.coe_injective hhom_zero)
    have hzero_eq : a = 0 := by
      have hadd : a + a = a := by
        simpa [two_mul] using htwo.symm
      apply add_left_cancel (a := a)
      simpa [add_zero] using hadd
    rw [← ha, hzero_eq]
    exact le_rfl

end ZeroValue

section Symmetry

variable {𝕜 : Type v} [DivisionRing 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [PosMulReflectLT 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-- Corollary 4.7.2, owner-minimal form. -/
theorem apply_neg_ge_neg_apply {f : E → WithTopBot 𝕜}
    (hf_hom : f.PositivelyHomogeneous 𝕜) (hf_ne_bot : ∀ y : E, f y ≠ ⊥)
    (hf_convex : f.IsConvex 𝕜) (x : E) :
    f (-x) ≥ -f x := by
  have hsubadd :=
    (isConvex_iff_subadditive_of_positivelyHomogeneous hf_hom hf_ne_bot).mp hf_convex
  have hzero_nonneg : (0 : WithTopBot 𝕜) ≤ f 0 :=
    zero_le_apply_zero_of_positivelyHomogeneous hf_hom hf_ne_bot
  have hsum_nonneg : (0 : WithTopBot 𝕜) ≤ f x + f (-x) := by
    exact hzero_nonneg.trans (by simpa using hsubadd x (-x))
  by_cases hfx_top : f x = ⊤
  · simp [hfx_top]
  · by_cases hnegx_top : f (-x) = ⊤
    · simp [hnegx_top]
    · have hx_ne_bot : f x ≠ ⊥ := hf_ne_bot x
      have hnegx_ne_bot : f (-x) ≠ ⊥ := hf_ne_bot (-x)
      rcases withTopBot_exists_coe_of_ne_top_ne_bot hfx_top hx_ne_bot with ⟨a, ha⟩
      rcases withTopBot_exists_coe_of_ne_top_ne_bot hnegx_top hnegx_ne_bot with ⟨b, hb⟩
      have hsum_nonneg' : (0 : 𝕜) ≤ a + b := by
        have hsum_nonneg'' :
            ((0 : 𝕜) : WithTopBot 𝕜) ≤ ((a + b : 𝕜) : WithTopBot 𝕜) := by
          simpa [ha, hb] using hsum_nonneg
        exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hsum_nonneg'')
      have hneg_ab : -a ≤ b :=
        (neg_le_iff_add_nonneg).2 (by simpa [add_comm] using hsum_nonneg')
      rw [← ha, ← hb]
      exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr hneg_ab)

/-- Corollary 4.7.2 in the textbook properness form. -/
theorem apply_neg_ge_neg_apply_of_proper {f : E → WithTopBot 𝕜}
    (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) (x : E) :
    f (-x) ≥ -f x :=
  apply_neg_ge_neg_apply hf_hom hf_proper.ne_bot hf_convex x

end Symmetry

end Function

end
