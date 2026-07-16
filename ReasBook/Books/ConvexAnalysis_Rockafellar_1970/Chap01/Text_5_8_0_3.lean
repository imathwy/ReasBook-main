import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*} {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

variable (f₁ f₂ : E → WithTopBot 𝕜)

variable [IsStrictOrderedRing 𝕜]

namespace Function

/-- Helper for Text 5.8.0.3: the vertical infimum of a set of finite-height epigraph points is the
pointwise infimum of the corresponding scalar fibers. -/
noncomputable def verticalInfimumOfEpigraphSet (F : Set (E × 𝕜)) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F})

/-- Helper for Text 5.8.0.3: Rockafellar's convex hull of a function is the vertical infimum of
the convex hull of its epigraph. -/
noncomputable def convexHullOfEpigraph (g : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  verticalInfimumOfEpigraphSet (_root_.convexHull 𝕜 (epi g))

local notation "verticalInfimum" => Function.verticalInfimumOfEpigraphSet
local notation:max "conv(" g ")" => Function.convexHullOfEpigraph g

/-- Helper for Text 5.8.0.3: the epigraph of the pointwise infimum of two functions is exactly
the union of their epigraphs. -/
private theorem epi_inf_eq_union_epi
    {E : Type*} {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜]
    (f₁ f₂ : E → WithTopBot 𝕜) :
    epi (f₁ ⊓ f₂) = epi f₁ ∪ epi f₂ := by
  -- Membership in the epigraph of a pointwise infimum is a disjunction in a linear order.
  ext p
  simp

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.8.0.3 identifies `conv(f₁ ⊓ f₂)` with the vertical infimum attached to
  `convexHull 𝕜 (epi f₁ ∪ epi f₂)`.
- `core/canonical`: the only owners needed here are the vertical fiber infimum and the convex hull
  of an epigraph.
- `bridge/view`: the proof is the direct rewrite `epi (f₁ ⊓ f₂) = epi f₁ ∪ epi f₂`.
- Primitive data vs derived API: the pair `(f₁, f₂)` is primitive; the function equality is the
  source-facing derived statement.

Domain-style sampling used here:
- `verticalInfimum`;
- `_root_.convexHull`;
- `epi`.
-/

/-- Helper for Text 5.8.0.3: unfolding Rockafellar's function convex hull and rewriting the
epigraph of the pointwise infimum gives the canonical two-function identity. -/
theorem conv_inf_eq_verticalInfimum_convexHull_union_epi
    : conv(f₁ ⊓ f₂) =
        verticalInfimum (_root_.convexHull 𝕜 (epi f₁ ∪ epi f₂)) := by
  -- Unfold Rockafellar's `conv` owner and rewrite the infimum epigraph as a union.
  let _ : IsStrictOrderedRing 𝕜 := inferInstance
  simp [Function.convexHullOfEpigraph, epi_inf_eq_union_epi]

/-- Text 5.8.0.3 in source-facing form: the vertical infimum attached to the convex hull of the
union of the two scalar epigraphs is `conv(f₁ ⊓ f₂)`. -/
theorem verticalInfimum_convexHull_union_epi_eq_conv_inf
    : verticalInfimum (_root_.convexHull 𝕜 (epi f₁ ∪ epi f₂)) =
        conv(f₁ ⊓ f₂) := by
  -- The labeled theorem is the symmetric restatement of the canonical orientation above.
  simpa using (conv_inf_eq_verticalInfimum_convexHull_union_epi
    (f₁ := f₁) (f₂ := f₂)).symm

end Function

end
