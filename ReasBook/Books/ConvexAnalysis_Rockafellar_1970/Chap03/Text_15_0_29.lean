import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Function
  (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem
    le_verticalInfimum_of_subset_epi)
open scoped Rockafellar

universe u v w

section

-- Assumption layer minimized to the primitive data used by the statement:
-- ordered codomain operations for `WithBotTop 𝕜` and a pairing, with no field or linear structure.
variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [One 𝕜] [Add 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.29 extends the polar-gauge construction from gauges to convex
  functions by replacing the gauge inequality `⟪x, x⋆⟫ ≤ μ⋆ f x` with
  `⟪x, x⋆⟫ ≤ 1 + μ⋆ f x`.
- `core/canonical`: as in the earlier owner `gauge_polar`, the implementation should reuse the
  Chapter 1 fiber-infimum owner `Function.verticalInfimum` instead of duplicating a raw `sInf`
  definition. The same-kind neighboring owners are `gauge_polar`, `indicatorFunction`, and
  `Set.polar`.
- `bridge/view`: the companion theorems below identify this function polar with `gauge_polar`
  under positive homogeneity and with the set-polar bridge on indicator inputs,
  while the final inequality is stated directly on finite-value points of `f` and its polar.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `gauge_polar` from `Text_15_0_5`;
- `Function.verticalInfimum` and `Function.verticalInfimum_eq_sInf` from `Theorem_5_3`;
- `indicatorFunction` from `Defintion_4_8_1`;
- `Set.polar` from `Text_14_0_5`.

Primitive data vs derived API:
- primitive inputs: a function `f : X → WithBotTop 𝕜` and a dual point `xStar : Y`;
- primitive source-facing owner: `convex_function_polar`;
- primitive implementation data: the admissible-majorant subset of `Y × 𝕜` fed to
  `Function.verticalInfimum`;
- derived API: the owner-facing majorant bound, nonnegativity, the positive-homogeneous
  specialization to `gauge_polar`, the companion `sInf` formula over nonnegative scalars, the
  indicator
  specialization, and the source inequality on finite-value points.

Layer target: `source-facing`. There is no existing project owner for this exact affine-majorant
polar construction, so the public owner remains local, but its implementation should still reuse
the chapter's canonical infimum abstraction. The construction only needs dual evaluation, so it
is stated at the pairing layer `HasPairing X Y 𝕜` rather than a concrete inner-product model.
-/

def convexFunctionPolarMajorantsAt (f : X → WithBotTop 𝕜) (xStar : Y) : Set 𝕜 :=
  {μ : 𝕜 |
    0 ≤ μ ∧
      ∀ x : X, ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ (1 : WithBotTop 𝕜) + (μ : WithBotTop 𝕜) * f x}

/-- The admissible affine-majorant heights for `fᵒ xStar`, viewed in `WithBotTop 𝕜`. -/
def convexFunctionPolarMajorantHeights (f : X → WithBotTop 𝕜) (xStar : Y) : Set (WithBotTop 𝕜) :=
  ((↑) : 𝕜 → WithBotTop 𝕜) '' convexFunctionPolarMajorantsAt f xStar

private def convexFunctionPolarMajorants (f : X → WithBotTop 𝕜) : Set (Y × 𝕜) :=
  {p : Y × 𝕜 |
    p.2 ∈ convexFunctionPolarMajorantsAt f p.1}

/-- Text 15.0.29: the polar `fᵒ` of a convex function `f` is the Chapter 1 vertical infimum of
the admissible affine-majorant set. It is written `fᵒ` after
`open scoped ConvexFunctionPolar`. -/
def convex_function_polar (f : X → WithBotTop 𝕜) : Y → WithBotTop 𝕜 :=
  verticalInfimum (convexFunctionPolarMajorants f)

namespace ConvexFunctionPolar

scoped postfix:max "ᵒ" => convex_function_polar

end ConvexFunctionPolar

open scoped ConvexFunctionPolar

/-- The value of `fᵒ` at `xStar` is the infimum of the admissible
nonnegative affine majorants from the source formula. -/
theorem convex_function_polar_eq_sInf_nonneg_affine_majorants
    (f : X → WithBotTop 𝕜) (xStar : Y) :
    fᵒ xStar = sInf (convexFunctionPolarMajorantHeights f xStar) := by
  simpa
      [convex_function_polar, convexFunctionPolarMajorantHeights, convexFunctionPolarMajorants,
        convexFunctionPolarMajorantsAt] using
    (verticalInfimum_eq_sInf (convexFunctionPolarMajorants f) xStar)

-- Proof sketch: `convex_function_polar f xStar` is the infimum of the `WithBotTop 𝕜` image of
-- the admissible affine majorants, so every particular nonnegative majorant contributes one upper
-- bound for that infimum after coercion to `WithBotTop 𝕜`.
/-- Any admissible affine majorant bounds the polar function from above. -/
theorem convex_function_polar_le_of_majorant
    {f : X → WithBotTop 𝕜} {xStar : Y} {μStar : 𝕜}
    (hμ : μStar ∈ convexFunctionPolarMajorantsAt f xStar) :
    fᵒ xStar ≤ (μStar : WithBotTop 𝕜) := by
  have hmajorant : (xStar, μStar) ∈ convexFunctionPolarMajorants f := hμ
  simpa [convex_function_polar] using
    (verticalInfimum_le_of_mem hmajorant :
      verticalInfimum (convexFunctionPolarMajorants f) xStar ≤ μStar)

-- Proof sketch: every element of the image in the defining `sInf` is nonnegative because the
-- defining scalar satisfies `0 ≤ μStar`. The infimum of a set of nonnegative `WithBotTop 𝕜`
-- values is therefore nonnegative; if the set is empty, the infimum is `⊤`, which is still
-- nonnegative.
/-- The polar of a convex function takes nonnegative values in `WithBotTop 𝕜`. -/
theorem convex_function_polar_nonneg (f : X → WithBotTop 𝕜) (xStar : Y) :
    0 ≤ fᵒ xStar := by
  have hmajorants :
      convexFunctionPolarMajorants f ⊆ epi (fun _ : Y ↦ (0 : WithBotTop 𝕜)) := by
    rintro ⟨x, μ⟩ hμ
    refine mem_epi_restrict_iff.mpr ⟨by simp, ?_⟩
    change ((0 : 𝕜) : WithBotTop 𝕜) ≤ (μ : WithBotTop 𝕜)
    exact WithBotTop.coe_le_coe.mpr hμ.1
  have hnonneg := le_verticalInfimum_of_subset_epi hmajorants
  simpa [convex_function_polar] using hnonneg xStar

end

open scoped ConvexFunctionPolar

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

-- Proof sketch: positive homogeneity lets one scale the defining inequality
-- `⟪x, x⋆⟫ ≤ 1 + μ⋆ k x` along rays and send the scale to `+∞`, eliminating the constant term `1`
-- and recovering exactly the majorant condition from `gauge_polar`. The converse implication is
-- immediate because `⟪x, x⋆⟫ ≤ μ⋆ k x` implies `⟪x, x⋆⟫ ≤ 1 + μ⋆ k x`.
/-- For a positively homogeneous function, hence in particular for a gauge, the present polar
agrees with the earlier polar gauge `gauge_polar`. -/
theorem convex_function_polar_eq_gauge_polar
    {k : X → WithBotTop 𝕜} (hk_hom : k.PositivelyHomogeneous 𝕜) (xStar : Y) :
    kᵒ xStar = gauge_polar k xStar := sorry

end

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜]
variable [Zero 𝕜] [One 𝕜] [Add 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]

-- Proof sketch: for `indicatorFunction C`, the defining inequality is automatic outside `C`
-- because the right-hand side is `⊤`, while on `C` it becomes `⟪x, x⋆⟫ ≤ 1`. Hence admissibility
-- no longer depends on `μ⋆`: either `xStar ∈ Set.polar C`, in which case `μ⋆ = 0` is admissible
-- and the infimum is `0`, or else no admissible majorant exists and the infimum is `⊤`.
/-- The polar of a set indicator is the indicator of the polar set. -/
theorem convex_function_polar_indicatorFunction_eq_indicatorFunction_polar
    (C : Set X) :
    (δ[𝕜](· | C))ᵒ = (fun y : Y ↦ δ[𝕜](y | (Cᵒ[𝕜]))) := sorry

end

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [One 𝕜] [Add 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

-- Proof sketch: fix `x` and use the defining infimum for `convex_function_polar f xStar`. For any
-- admissible `μ⋆`, the displayed inequality gives `⟪x, x⋆⟫ ≤ 1 + μ⋆ f x`. Since `f x` is assumed
-- finite and nonnegative, one can pass from all admissible `μ⋆` to their infimum, obtaining the
-- same inequality with `μ⋆ = convex_function_polar f xStar`.
/-- If `x` is a finite-value point of a nonnegative `WithBotTop 𝕜`-valued function `f` and
`xStar` is a finite-value point of its polar `fᵒ`, then
`⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`. -/
theorem inner_le_one_add_mul_convex_function_polar
    {f : X → WithBotTop 𝕜} {x : X} {xStar : Y} (hx_nonneg : 0 ≤ f x)
    (hx_dom : f x < ⊤) (hxStar_dom : fᵒ xStar < ⊤) :
    (((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤
      (1 : WithBotTop 𝕜) + f x * fᵒ xStar) := sorry

end
