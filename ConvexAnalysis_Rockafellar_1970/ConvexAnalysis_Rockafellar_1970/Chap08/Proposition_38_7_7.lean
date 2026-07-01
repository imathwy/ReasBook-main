import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_3_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_7_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_7

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable {F : U → X → WithBotTop ℝ} {f : U → WithBotTop ℝ} {gStar : X → WithBotTop ℝ}

local notation "IsCofinite[ℝ]" => Function.IsCofinite (𝕜 := ℝ)
local notation "F⋆" => (adjoint X U F : X → U → WithBotTop ℝ)
local notation "adjointUpperImage" =>
  upperPerturbationFunction (fun u x ↦ gStar x - F⋆ x u)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.7 states the inner-product identity
  `⟨Ff, g⋆⟩ = ⟨f, F⋆ g⋆⟩` for a co-finite closed-convex bifunction `F`, a co-finite convex
  function `f`, and a co-finite concave function `gStar`.
- `core/canonical`: the stable owners already present in the project are `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.upperPerturbationFunction`, `Function.innerProduct`,
  `Function.IsCofinite`, `Bifunction.IsClosedConvex`, and `Bifunction.IsCofinite X U`.
- `bridge/view`: no new owner is introduced here; the source term `F⋆ g⋆` is written directly
  with the canonical owner `upperPerturbationFunction`.

Domain-style sampling used here:
- `Bifunction.image` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Definition_6_30_14`, reused through
  `Proposition_38_7_2`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Function.innerProduct` from `Definition_38_5_2`;
- `Function.IsCofinite` from `Text_13_3_1`;
- `Bifunction.IsClosedConvex` and `Bifunction.IsCofinite X U` from `Proposition_38_7_2`.

Primitive data vs derived API:
- primitive source inputs: a bifunction `F : U → X → WithBotTop ℝ`, a convex-side function
  `f : U → WithBotTop ℝ`, and a concave-side function `gStar : X → WithBotTop ℝ`;
- primitive source-facing owners reused upstream: `image F f`, `adjoint X U F`,
  `upperPerturbationFunction`, `innerProduct`, `IsClosedConvex`, and `IsCofinite X U`;
- derived API here: the co-finite inner-product identity written directly with that owner.

Layer target: `source-facing`.
-/

-- Proof sketch: expand the left inner product using Definition 38.5.2, express the adjoint-side
-- action `F⋆ g⋆` with `upperPerturbationFunction`, and apply the Chapter 38.7 duality identity
-- slice by slice. The co-finiteness hypotheses on `F`, `f`, and `gStar` let one exchange the two
-- suprema/infima without a duality gap.
/-- Proposition 38.7.7: for a co-finite closed-convex bifunction `F`, a co-finite convex
function `f`, and a co-finite concave function `gStar`, the Chapter 38 inner product of
`image F f` with `gStar` equals the inner product of `f` with the adjoint-side concave image
`adjointUpperImage`, which is the source term `F⋆ g⋆` rendered in the existing owner language. -/
theorem innerProduct_image_eq_innerProduct_adjointUpperImage
    (hF_closedConvex : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hf_cofinite : IsCofinite[ℝ] f) (hgStar_cofinite : IsCofinite[ℝ] (-gStar)) :
    Function.innerProduct (image F f) gStar =
      Function.innerProduct f adjointUpperImage := by
  sorry

end

end Bifunction
