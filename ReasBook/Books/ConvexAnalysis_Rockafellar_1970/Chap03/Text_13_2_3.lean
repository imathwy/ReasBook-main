import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.ERealSMul
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] instSMulRealEReal

section SupportFunctionSublinear

open scoped Rockafellar

universe u v

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Text 13.2.3 (2): the support function satisfies the subadditivity inequality
`δ*(x₁⋆ + x₂⋆ | C) ≤ δ*(x₁⋆ | C) + δ*(x₂⋆ | C)`. This canonical inequality already holds for an
arbitrary subset at the pairing-owner level. -/
theorem supportFunction_add_le (C : Set Y) (x₁ x₂ : X) :
    (δᵛ(x₁ + x₂ | C) : WithTopBot 𝕜) ≤ δᵛ(x₁ | C) + δᵛ(x₂ | C) := by
  rw [supportFunction_def, supportFunction_def, supportFunction_def]
  refine iSup_le ?_
  intro y
  calc
    (⟪x₁ + x₂, (y : Y)⟫ₚ : WithTopBot 𝕜) =
        (⟪x₁, (y : Y)⟫ₚ : WithTopBot 𝕜) + (⟪x₂, (y : Y)⟫ₚ : WithTopBot 𝕜) := by
          change (((HasLinearPairing.pairingLinear.flip (y : Y)) (x₁ + x₂) : 𝕜) :
              WithTopBot 𝕜) =
            (((HasLinearPairing.pairingLinear.flip (y : Y)) x₁ : 𝕜) : WithTopBot 𝕜) +
              (((HasLinearPairing.pairingLinear.flip (y : Y)) x₂ : 𝕜) : WithTopBot 𝕜)
          simp
    _ ≤ (⨆ z : C, (⟪x₁, (z : Y)⟫ₚ : WithTopBot 𝕜)) +
          (⨆ z : C, (⟪x₂, (z : Y)⟫ₚ : WithTopBot 𝕜)) := by
            exact add_le_add
              (le_iSup (fun z : C ↦ (⟪x₁, (z : Y)⟫ₚ : WithTopBot 𝕜)) y)
              (le_iSup (fun z : C ↦ (⟪x₂, (z : Y)⟫ₚ : WithTopBot 𝕜)) y)

end SupportFunctionSublinear

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 13.2.3 states that the support function `δᵛ(· | C)` is lower
  semicontinuous and subadditive.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`,
  the notation `δᵛ(· | C)`, its owner formula `supportFunction_def`, mathlib's
  `LowerSemicontinuous`, the chapter conjugacy bridge
  `convexConjugate_indicatorFunction_eq_supportFunction`, and the earlier owner theorem
  `Function.isConvex_supportFunction`.
- `bridge/view`: the source's `R^n` model is a concrete realization of the same owner statements
  on a real inner-product space, so this file should live at the inner-product-space owner level
  rather than at a local Euclidean-coordinate wrapper.
- Primitive data vs derived API: the subset `C : Set E` and its support function are primitive;
  lower semicontinuity, convexity, and subadditivity are derived properties.

Domain-style sampling used here:
- `supportFunction` and the notation `δᵛ(· | C)`;
- `supportFunction_def`;
- `Function.isConvex_supportFunction`;
- `lowerSemicontinuous_convexConjugate`;
- `convexConjugate_indicatorFunction_eq_supportFunction`.

Layer target: `source-facing`; this file keeps Rockafellar's two consequences as thin theorems
about the existing owner `supportFunction`, without introducing a parallel wrapper for support
functions or a second subadditivity abstraction.

Semantic note:
- both conclusions hold for arbitrary subsets `C ⊆ R^n`, so the textbook's nonemptiness and
  convexity assumptions are redundant and are omitted from the Lean statements.
-/

-- Proof sketch: rewrite `supportFunction C` as the Fenchel conjugate of `indicatorFunction C`
-- using `convexConjugate_indicatorFunction_eq_supportFunction`, then apply
-- `lowerSemicontinuous_convexConjugate`.
/-- Text 13.2.3 (1): the support function `δ*(· | C)` is lower semicontinuous on `R^n`. This
holds for every subset `C`, so in particular for the nonempty convex sets of the textbook
statement. -/
theorem lowerSemicontinuous_supportFunction (C : Set E) :
    LowerSemicontinuous (δᵛ(· | C) : E → WithTopBot ℝ) := by
  sorry

end
