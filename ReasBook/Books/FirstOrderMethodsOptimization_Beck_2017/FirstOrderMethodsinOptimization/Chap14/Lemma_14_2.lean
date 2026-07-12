import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_3
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Definition_14_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

/- `Lemma 14.2` is a `bridge/view` item. The source-facing coordinatewise minimum owner is
`is_coordinatewise_minimum`, the canonical Chapter 14 regularity owner is
`IsAlternatingMinimizationCompositeModel`, and the downstream Chapter 3 owner is
`is_stationary_point`. The theorem should therefore expose the model assumptions through the
existing owner class instead of restating its fields as a second public hypothesis bundle. -/

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}

/-- The Chapter 3 stationary-point owner uses the product-space module induced by the chosen
inner product on `Π i, E_i`. -/
local instance : Module ℝ ((i : Fin p) → Ei i) :=
  (inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule

local notation "F" => composite_model_objective f (separableSum g)

-- Proof sketch: fix a block `i`. The coordinate-wise minimum inequalities for `F` imply that
-- `xStar i` globally minimizes the one-block slice `y ↦ f (Function.update xStar i y) + g i y`.
-- The standing Assumption 14.6 owner `IsAlternatingMinimizationCompositeModel f g` supplies the
-- regularity hypotheses needed for the one-block first-order optimality theorem, giving
-- `-∇ᵢ f(xStar) ∈ ∂ g_i(xStar_i)` for every block. The block-separable regularizer then
-- identifies these coordinatewise subgradient conditions with the Chapter 3 stationary-point
-- predicate for `f + separableSum g`.
/-- Lemma 14.2: under the standing composite-model assumptions from Assumption 14.6, every
coordinate-wise minimum of the composite objective `F(x) = f(x) + ∑ i, g_i(x_i)` is a stationary
point of the composite problem `(14.9)`. The coordinate-wise minimum hypothesis uses the
source-facing owner predicate from Definition 14.2 directly on the block product, while the
regularity assumptions are supplied canonically by
`IsAlternatingMinimizationCompositeModel f g`. -/
theorem is_stationary_point_of_coordinatewise_minimum
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hcoord : is_coordinatewise_minimum F xStar) :
    is_stationary_point f (separableSum g) xStar := sorry

end
