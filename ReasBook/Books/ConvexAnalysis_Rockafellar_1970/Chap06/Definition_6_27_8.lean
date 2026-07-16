import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section OrderedNormed

universe u

open scoped Rockafellar

variable {𝕜 : Type u} [Preorder 𝕜] [Pow 𝕜 ℕ] [SeminormedAddCommGroup 𝕜]

local notation "R2" => (𝕜 × 𝕜)
local notation "P" => (paraboloidEpigraph : Set R2)
local notation "f₀" => parabolicF0
local notation "q₂" => ((Function.toWithTopBot (fun ξ : R2 ↦ ‖ξ‖ ^ 2)) : R2 → WithTopBot ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.8 presents the squared-distance branch `f₀` as the infimal
  convolution of the quadratic branch with the indicator of `P`, and then defines the real-valued
  example `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁`.
- `core/canonical`: the owner abstractions already present are the source-facing squared-distance
  owner `parabolicF0`, the Chapter 1 infimal convolution owner `infimal_convolution` (notation
  `□`), the lifted quadratic branch
  `((fun x : R2 ↦ ‖x‖ ^ 2).toWithTopBot : R2 → WithTopBot ℝ)`, and the indicator owner
  `δ(· | P)`.
- `bridge/view`: this file keeps `parabolicF0` as the source-facing owner from
  Definition 6.27.7 and adds the canonical bridge theorem identifying its `WithTopBot` lift with
  the infimal convolution presentation. The affine perturbation `parabolicObjective` remains the
  genuinely new source-facing definition in this item.
- Primitive data vs derived API: the only new public data are the real-valued objective
  `parabolicObjective`; the infimal-convolution formula for `f₀` is exposed as derived bridge API
  on the existing owner `parabolicF0`.

Domain-style sampling used here:
- `parabolicF0`;
- `Function.toWithTopBot`;
- `indicator` / `δ(· | C)`;
- the binary infimal-convolution owner `infimal_convolution`.

Layer target: `bridge/view` for the infimal-convolution presentation of `f₀`, and
`source-facing` for the new objective.
-/

-- Proof sketch: by definition, `f₀ x` is the infimum over
-- `p ∈ P` of the squared Euclidean distance `‖x - p‖ ^ 2`. Unfolding the Chapter 1 owner
-- `infimal_convolution` with the indicator of `P` gives the same infimum over decompositions
-- `x = y + p`, i.e. over `p ∈ P` with quadratic cost `‖y‖ ^ 2 = ‖x - p‖ ^ 2`.
/-- Definition 6.27.8 (1): owner-level bridge form. The source-facing squared-distance branch
`f₀` is exactly the infimal convolution of the squared Euclidean norm with the indicator of the
parabolic set `P`. -/
theorem parabolicF0_eq_infimalConvolution :
    parabolicF0.toWithTopBot = infimal_convolution q₂ (δ[ℝ](· | P)) := sorry

/-- Pointwise form of `parabolicF0_eq_infimalConvolution`. -/
@[simp] theorem parabolicF0_eq_infimalConvolution_apply (ξ : R2) :
    parabolicF0.toWithTopBot ξ = (infimal_convolution q₂ (δ[ℝ](· | P))) ξ := sorry

end OrderedNormed

section RealObjective

local notation "R2" => (ℝ × ℝ)
local notation "f₀" => parabolicF0

/-- Definition 6.27.8 (2): the example objective `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁`. -/
def parabolicObjective : R2 → ℝ :=
  fun ξ ↦ f₀ ξ - ξ.1

@[simp] theorem parabolicObjective_apply (ξ : R2) :
    parabolicObjective ξ = f₀ ξ - ξ.1 :=
  rfl

end RealObjective
