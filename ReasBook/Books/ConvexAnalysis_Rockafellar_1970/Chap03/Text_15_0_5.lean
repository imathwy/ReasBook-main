import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Function
  (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem
    le_verticalInfimum_of_subset_epi)
open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.5 defines the polar of a gauge by taking the infimum of the
  nonnegative scalars `μ⋆` such that `⟪x, x⋆⟫ₚ ≤ μ⋆ k x` for every `x`.
- `core/canonical`: the public owner remains the source-facing function `gauge_polar`, but its
  implementation should reuse the Chapter 1 infimum owner `Function.verticalInfimum` applied to the
  admissible-majorant set rather than duplicating that fiber-infimum construction locally.
- `bridge/view`: the textbook `sInf` formula over nonnegative scalars is kept as a companion
  specification theorem, not as a second public owner.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`, identifying the owner class of functions to which the source gives
  this construction;
- `Function.verticalInfimum` from `Theorem_5_3`, for the project pattern of scalar-parameter
  infima cast into `WithBotTop 𝕜`;
- `Function.verticalInfimum_eq_sInf`, showing the exact owner-side fiber-infimum formula;
- `egauge ℝ≥0` from `Text_5_4_10`, as a nearby canonical infimum-style gauge construction.

Primitive data vs derived API:
- primitive inputs: a function `k : X → WithBotTop 𝕜` and a dual point `xStar : Y`;
- primitive source-facing owner: the function `gauge_polar`;
- primitive implementation data: the admissible-majorant subset of `Y × 𝕜` fed to
  `Function.verticalInfimum`;
- derived API: basic order facts such as admissible majorants bounding the infimum and
  nonnegativity of the resulting value, together with the intrinsic majorant-height `sInf`
  specification theorem.

Layer target: `source-facing`. The construction only needs dual evaluation, so it is owned at the
pairing layer `HasPairing X Y 𝕜` rather than the concrete inner-product self-dual model. The gauge
assumption from the prose is not needed for the bare infimum formula itself, so it is omitted from
the definition header exactly as in the project's other raw infimum-based owners.
-/

def gaugePolarMajorantsAt (k : X → WithBotTop 𝕜) (xStar : Y) : Set 𝕜 :=
  {μ : 𝕜 |
    0 ≤ μ ∧
      ∀ x : X, ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ (μ : WithBotTop 𝕜) * k x}

/-- The admissible majorant heights for `kᵒ xStar`, viewed in `WithBotTop 𝕜`. -/
def gaugePolarMajorantHeights (k : X → WithBotTop 𝕜) (xStar : Y) : Set (WithBotTop 𝕜) :=
  ((↑) : 𝕜 → WithBotTop 𝕜) '' gaugePolarMajorantsAt k xStar

private def gaugePolarMajorants (k : X → WithBotTop 𝕜) : Set (Y × 𝕜) :=
  {p : Y × 𝕜 |
    p.2 ∈ gaugePolarMajorantsAt k p.1}

/-- Text 15.0.5: the polar gauge `kᵒ`, written `kᵒ` after `open scoped GaugePolar`, is the
Chapter 1 vertical infimum of the admissible-majorant set. This keeps the source-facing owner
while reusing the project's canonical infimum construction. -/
def gauge_polar (k : X → WithBotTop 𝕜) : Y → WithBotTop 𝕜 :=
  verticalInfimum (gaugePolarMajorants k)

end

namespace GaugePolar

scoped postfix:max "ᵒ" => gauge_polar

end GaugePolar

section

open scoped GaugePolar

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

/-- The value of `kᵒ` at `xStar` is the infimum of the admissible nonnegative scalar majorants
from the source formula. -/
theorem gauge_polar_eq_sInf_nonneg_majorants
    (k : X → WithBotTop 𝕜) (xStar : Y) :
    kᵒ xStar =
      sInf (gaugePolarMajorantHeights k xStar) := by
  simpa [gauge_polar, gaugePolarMajorantHeights, gaugePolarMajorants, gaugePolarMajorantsAt] using
    (verticalInfimum_eq_sInf (gaugePolarMajorants k) xStar)

-- Proof sketch: `gauge_polar k xStar` is the infimum of the `WithBotTop 𝕜` image of the admissible
-- nonnegative scalar majorants, so any particular admissible nonnegative `μStar` contributes one
-- upper bound for that infimum after coercion to `WithBotTop 𝕜`.
/-- Any admissible majorant for the defining inequality bounds the polar gauge from above. -/
theorem gauge_polar_le_of_majorant
    {k : X → WithBotTop 𝕜} {xStar : Y} (μStar : 𝕜)
    (hμ : μStar ∈ gaugePolarMajorantsAt k xStar) :
    kᵒ xStar ≤ (μStar : WithBotTop 𝕜) := by
  have hmajorant : (xStar, μStar) ∈ gaugePolarMajorants k := hμ
  simpa [gauge_polar] using
    (verticalInfimum_le_of_mem hmajorant :
      verticalInfimum (gaugePolarMajorants k) xStar ≤ μStar)

-- Proof sketch: every element of the image in the defining `sInf` is nonnegative because each
-- defining scalar satisfies the explicit constraint `0 ≤ μ`. The infimum of a set of
-- nonnegative `WithBotTop 𝕜` values is therefore nonnegative; if the set is empty, the
-- infimum is `⊤`,
-- which is still nonnegative.
/-- The polar gauge takes nonnegative values in `WithBotTop 𝕜`. -/
theorem gauge_polar_nonneg (k : X → WithBotTop 𝕜) (xStar : Y) :
    0 ≤ kᵒ xStar := by
  have hmajorants :
      gaugePolarMajorants k ⊆ epi (fun _ : Y ↦ (0 : WithBotTop 𝕜)) := by
    rintro ⟨x, μ⟩ hμ
    refine mem_epi_restrict_iff.mpr ⟨by simp, ?_⟩
    change ((0 : 𝕜) : WithBotTop 𝕜) ≤ (μ : WithBotTop 𝕜)
    exact WithBotTop.coe_le_coe.mpr hμ.1
  have hnonneg := le_verticalInfimum_of_subset_epi hmajorants
  simpa [gauge_polar] using hnonneg xStar

end
