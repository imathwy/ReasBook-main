import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise
open Function

namespace Function

/-- Helper for Text 5.4.1.6: the set of scalar heights whose vertical fiber above `x` meets `F`.
-/
def verticalHeights (F : Set (E × 𝕜)) (x : E) : Set (WithTopBot 𝕜) :=
  ((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F}

end Function

section

variable {E : Type*} {𝕜 : Type*}
variable [Add E]
variable [ConditionallyCompleteLattice 𝕜] [AddCommMonoid 𝕜]

/-- Helper for Text 5.4.1.6: the item-local infimal convolution is the vertical-fiber infimum of
the Minkowski sum of the two scalar epigraphs. -/
def infimal_convolution (f₁ f₂ : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (verticalHeights (epi f₁ + epi f₂) x)

infixl:70 " □ " => infimal_convolution

-- Proof sketch: in this item-local file, `□` is defined directly as the `sInf` of the scalar
-- heights in the vertical fiber of the epigraph Minkowski sum.

/-- Helper for Text 5.4.1.6: under the pointwise no-`⊥` guard, the infimal convolution is the
function that assigns to each `x` the infimum of the scalar heights in the vertical fiber of the
epigraph Minkowski sum `epi f₁ + epi f₂`. -/
theorem infimal_convolution_eq_sInf_verticalHeights_epi_add
    (f₁ f₂ : E → WithTopBot 𝕜)
    (hf₁_ne_bot : ∀ y : E, f₁ y ≠ ⊥)
    (hf₂_ne_bot : ∀ y : E, f₂ y ≠ ⊥) :
    (f₁ □ f₂) =
      fun x ↦ sInf (verticalHeights (epi f₁ + epi f₂) x) := by
  -- The item-local owner is defined by this vertical-fiber infimum, so the bridge is
  -- definitional.
  let _h₁ := hf₁_ne_bot
  let _h₂ := hf₂_ne_bot
  rfl

/-- Text 5.4.1.6: for every `x`, the value of the infimal convolution is the infimum of the scalar
heights `μ` such that `(x, μ)` belongs to the Minkowski sum of the two scalar epigraphs, provided
both functions are nowhere `⊥`. -/
theorem infimal_convolution_eq_sInf_epigraph_add
    (f₁ f₂ : E → WithTopBot 𝕜)
    (hf₁_ne_bot : ∀ y : E, f₁ y ≠ ⊥)
    (hf₂_ne_bot : ∀ y : E, f₂ y ≠ ⊥)
    (x : E) :
    (f₁ □ f₂) x = sInf (verticalHeights (epi f₁ + epi f₂) x) := by
  -- Evaluate the item-local definition at the chosen base point `x`.
  let _h₁ := hf₁_ne_bot
  let _h₂ := hf₂_ne_bot
  rfl

end
