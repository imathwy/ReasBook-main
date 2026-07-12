import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_7_4

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {𝕜 : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: the opening definition of §38 introduces the addition-like operation
  `F₁ D F₂` on bifunctions, obtained by taking infimal convolution in the second variable while
  the first variable is held fixed.
- `core/canonical`: the chapter owner is `infimal_convolution` / `□` on one-variable functions;
  the bifunction operation is the direct slice expression `fun u ↦ F₁ u □ F₂ u`.
- `bridge/view`: Section 38 keeps a source-facing notation `D`, but its implementation layer is
  exactly this slice-level canonical owner expression.

Domain-style sampling used here:
- `infimal_convolution` / `□` from `Chap01.Text_5_4_0`;
- `infimal_convolution_apply` from the same owner layer;
- `Bifunction.perturbationFunction` from `Chap06.Definition_6_29_1` as the existing project
  pattern for a source-facing bifunction owner built directly from an indexed-infimum function
  construction.

Primitive data vs derived API:
- primitive source data: the bifunctions `F₁` and `F₂`;
- primitive source-facing owner: `infimalConvolution`, written `F₁ D F₂`;
- derived API: the pointwise evaluation formula and the uncurried identity companion.

Layer target: `source-facing`.
-/

section Owner

variable [ConditionallyCompleteLinearOrder 𝕜] [Add 𝕜]
variable [Add X]

/-- Definition 38.0.1: the infimal convolution of two bifunctions is obtained by taking, for each
`u`, the infimal convolution of the functions `F₁ u` and `F₂ u` in the second variable. The
textbook proper-convex hypotheses belong to later theorems, not to the primitive definition of
this source-facing owner. -/
abbrev infimalConvolution (F₁ F₂ : U → X → WithBotTop 𝕜) : U → X → WithBotTop 𝕜 :=
  fun u ↦ F₁ u □ F₂ u

scoped[Rockafellar] infixl:70 " D " => Bifunction.infimalConvolution

/-- The Section 38 bifunction operation is exactly the uncurried graph function built from the
slice-level owner expression `fun u ↦ F₁ u □ F₂ u`. -/
@[simp] theorem uncurry_infimalConvolution
    (F₁ F₂ : U → X → WithBotTop 𝕜) :
    Function.uncurry (F₁ D F₂) =
      Function.uncurry (fun u ↦ F₁ u □ F₂ u) := by
  rfl

end Owner

section SubtractionFormula

variable [ConditionallyCompleteLinearOrder 𝕜] [Add 𝕜]
variable [AddCommGroup X]

/-- Evaluating `F₁ D F₂` at `(u, x)` gives the infimum of `F₁ u y + F₂ u (x - y)` over all
`y`. -/
@[simp] theorem infimalConvolution_apply
    (F₁ F₂ : U → X → WithBotTop 𝕜) (u : U) (x : X) :
    (F₁ D F₂) u x = ⨅ y : X, F₁ u y + F₂ u (x - y) := by
  change ((F₁ u) □ (F₂ u)) x = ⨅ y : X, F₁ u y + F₂ u (x - y)
  exact infimal_convolution_apply (F₁ u) (F₂ u) x

end SubtractionFormula

end

end Bifunction
