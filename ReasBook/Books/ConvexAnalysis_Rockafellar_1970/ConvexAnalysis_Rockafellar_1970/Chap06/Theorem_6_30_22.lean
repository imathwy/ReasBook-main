import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped BigOperators NNReal Rockafellar

universe u v w

attribute [local instance] Classical.propDecidable

namespace Bifunction

section

variable {E : Type u} {𝕜 : Type w} {ι : Type v}
variable [AddCommGroup E]
variable [Preorder 𝕜]

local notation "U" => (ι → 𝕜) × (E × (ι → E))

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.22 studies the specific enlarged-perturbation bifunction
  `G_w (x) = f₀ (x - x₀) + δ(x | f_i (x - x_i) ≤ v_i)`.
- `core/canonical`: the chapter owners on the dual side are already
  `Bifunction.adjoint` from Definition 6.30.14 and the right scalar multiple `•ʳ` from
  Text 5.4.2, so the main theorem should be a direct formula on those owners rather than on a
  parallel local scaled-conjugate wrapper.
- `bridge/view`: the theorem also has a zero-slice dual-objective specialization, recorded here as
  a companion theorem through the existing zero-slice owner `Bifunction.objective`.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.objective` from `Definition_6_29_12`;
- `Function.rightScalarMul` / `•ʳ` from `Chap01.Text_5_4_2`;
- `convexConjugate` / `(·)⋆` and the Chapter 1 indicator owner `δ(· | ·)`;
- product and inner-product pairing owners from `Chap01.HasPairing`, reused implicitly through the
  existing chapter notation `⟪·, ·⟫ₚ`.

Primitive data vs derived API:
- primitive function data: the objective branch `f₀` and the finite family of constraints `f`;
- primitive source-facing objects introduced here: the feasible slice
  `enlargedPerturbationFeasibleSet` and the bifunction `enlargedPerturbationProgram`;
- derived API: the adjoint formula and its zero-slice dual-objective specialization.
-/

/-- The feasible slice cut out by the enlarged-perturbation thresholds `u` and shifts `xs`: it is
the set of all `x` satisfying `f i (x - xs i) ≤ u i` for every constraint index `i`. -/
def enlargedPerturbationFeasibleSet
    (f : ι → E → WithBotTop 𝕜) (u : ι → 𝕜) (xs : ι → E) : Set E :=
  {x | ∀ i : ι, f i (x - xs i) ≤ (u i : WithBotTop 𝕜)}

-- Proof sketch: unfold `enlargedPerturbationFeasibleSet`; membership in the defining set-builder
-- is exactly the displayed family of shifted inequality constraints.
/-- Membership in the enlarged-perturbation feasible slice is the coordinatewise family of
inequalities `f i (x - xs i) ≤ u i`. -/
@[simp] theorem mem_enlargedPerturbationFeasibleSet
    (f : ι → E → WithBotTop 𝕜) (u : ι → 𝕜) (xs : ι → E) (x : E) :
    x ∈ enlargedPerturbationFeasibleSet f u xs ↔
      ∀ i : ι, f i (x - xs i) ≤ (u i : WithBotTop 𝕜) :=
  Iff.rfl

/-- The enlarged-perturbation bifunction of Theorem 6.30.22, with perturbation variable
`w = (u, x₀, (xᵢ)ᵢ)` represented as `(u, (x₀, xs))`. -/
def enlargedPerturbationProgram
    [Add 𝕜] [Zero 𝕜]
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜) :
    U → E → WithBotTop 𝕜 :=
  fun w x ↦
    f0 (x - w.2.1) + δ[𝕜](x | enlargedPerturbationFeasibleSet f w.1 w.2.2)

-- Proof sketch: unfold `enlargedPerturbationProgram`; evaluation at `(u, xs, x)` is exactly the
-- displayed objective-shift plus indicator-of-feasible-slice formula.
/-- Evaluating the enlarged-perturbation bifunction gives the shifted objective
`f₀ (x - x₀)` plus the indicator of the slice cut out by the shifted constraints. -/
@[simp] theorem enlargedPerturbationProgram_apply
    [Add 𝕜] [Zero 𝕜]
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜)
    (u : ι → 𝕜) (x0 : E) (xs : ι → E) (x : E) :
    enlargedPerturbationProgram f0 f (u, (x0, xs)) x =
      f0 (x - x0) + δ[𝕜](x | enlargedPerturbationFeasibleSet f u xs) :=
  rfl

end

section

variable {E : Type u} {EStar : Type v} {𝕜 : Type w} {ι : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Fintype ι]
variable [AddCommGroup E] [SMul 𝕜 E]
variable [AddCommMonoid EStar] [Neg EStar] [SMul 𝕜 EStar] [HasPairing E EStar 𝕜]

local notation "U" => (ι → 𝕜) × (E × (ι → E))
local notation "UStar" => (ι → 𝕜) × (EStar × (ι → EStar))
local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- The multiplier block `𝕜^ι` carries the canonical coordinate pairing used by the perturbation
adjoint owner. -/
local instance : HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 := instHasPairingOfHasLinearPairing

/-- The perturbation-shift block `(x₀, (xᵢ)ᵢ)` pairs with its dual block
`(x⋆₀, (x⋆ᵢ)ᵢ)` by the distinguished ambient pairing plus the coordinatewise sum. -/
local instance :
    HasPairing (E × (ι → E)) (EStar × (ι → EStar)) 𝕜 where
  pairing xs xsStar := ⟪xs.1, xsStar.1⟫ₚ + ∑ i, ⟪xs.2 i, xsStar.2 i⟫ₚ

-- Proof sketch: expand `adjoint` for the owner
-- `enlargedPerturbationProgram f0 f`, rewrite the product pairing on
-- `((ι → 𝕜) × (E × (ι → E))) × E`, and then perform the source changes of variables
-- `y₀ = x - x₀` and `yᵢ = x - xᵢ`. Taking the infimum over the free `x` variable gives `⊥`
-- unless `x0Star + ∑ i, xsStar i = xStar` in the explicit dual ambient type `EStar`.
-- The remaining terms
-- split into the Fenchel conjugate of `f₀`
-- and the one-constraint scalar cases recorded by the existing right scalar multiple owner `•ʳ`;
-- negative multipliers
-- force the value `⊥`.
/-- Theorem 6.30.22: the adjoint of the enlarged-perturbation program equals the negative sum of
the objective conjugate and the scaled constraint conjugates when the multiplier vector satisfies
the canonical order condition `0 ≤ uStar` and the distinguished-plus-family dual shift block
sums to `x⋆`;
otherwise the adjoint value is `-∞`. -/
theorem adjointFunction_enlargedPerturbationProgram_apply
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜)
    (hf0_proper : f0.IsProper) (hf0_convex : f0.IsConvex 𝕜)
    (hf_proper : ∀ i : ι, (f i).IsProper)
    (hf_convex : ∀ i : ι, (f i).IsConvex 𝕜)
    (hf_dom : ∀ i : ι, dom(f i) = Set.univ)
    (xStar : EStar) (uStar : ι → 𝕜) (x0Star : EStar) (xsStar : ι → EStar) :
    (enlargedPerturbationProgram f0 f)⋆ xStar (uStar, (x0Star, xsStar)) =
      if hu : 0 ≤ uStar then
        if hsum : x0Star + ∑ i, xsStar i = xStar then
          - (((f0⋆ : EStar → WithBotTop 𝕜) x0Star) +
              ∑ i : ι, ((⟨uStar i, hu i⟩ : 𝕜≥0) •ʳ (f i)⋆) (xsStar i))
        else
          ⊥
      else
        ⊥ := sorry

-- Proof sketch: specialize `adjointFunction_enlargedPerturbationProgram_apply` to `xStar = 0`
-- and rewrite the zero slice through the owner notation `((F⋆)₀) u = F⋆ 0 u`.
/-- The zero-slice dual objective of the enlarged-perturbation program is the source maximization
problem with nonnegative multipliers and vanishing distinguished-plus-family dual shift sum. -/
theorem objective_adjointFunction_enlargedPerturbationProgram_apply
    (f0 : E → WithBotTop 𝕜) (f : ι → E → WithBotTop 𝕜)
    (hf0_proper : f0.IsProper) (hf0_convex : f0.IsConvex 𝕜)
    (hf_proper : ∀ i : ι, (f i).IsProper)
    (hf_convex : ∀ i : ι, (f i).IsConvex 𝕜)
    (hf_dom : ∀ i : ι, dom(f i) = Set.univ)
    (uStar : ι → 𝕜) (x0Star : EStar) (xsStar : ι → EStar) :
    (((enlargedPerturbationProgram f0 f)⋆ : EStar → UStar → WithBotTop 𝕜)₀)
      (uStar, (x0Star, xsStar)) =
      if hu : 0 ≤ uStar then
        if hsum : x0Star + ∑ i, xsStar i = (0 : EStar) then
          - (((f0⋆ : EStar → WithBotTop 𝕜) x0Star) +
              ∑ i : ι, ((⟨uStar i, hu i⟩ : 𝕜≥0) •ʳ (f i)⋆) (xsStar i))
        else
          ⊥
      else
        ⊥ := sorry

end

end Bifunction
