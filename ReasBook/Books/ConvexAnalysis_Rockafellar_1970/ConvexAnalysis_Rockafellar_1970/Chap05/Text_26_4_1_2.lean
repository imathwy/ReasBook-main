import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_25_5_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function.IsClosedProperConvex

variable {f : E → EReal}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.4.1.2 says that for an essentially smooth closed proper convex
  function, the gradient map on `C = interior (dom(f))` continuously parameterizes the Legendre
  side `D`, and under this parameterization the conjugate value is the affine defect
  `⟪x, ∇ f(x)⟫ - f(x)`.
- `core/canonical`: the chapter owners already present are `LowerSemicontinuous`,
  `Function.IsEssentiallySmooth`, `interior (dom(f))`, `dom∂(·)`, `f.realBranch`, the conjugate
  `f⋆`, its canonical finite branch `(fStar).realBranch`, and the set-mapping owners
  `Set.MapsTo` / `Set.SurjOn`
  already used elsewhere in the chapter for raw owner maps between canonical domains.
- `bridge/view`: the declarations below keep the source parameterization on the raw gradient map
  `x ↦ ∇ f.realBranch x`, recording that it maps `C` onto the canonical Legendre-side domain
  `D = dom∂((f⋆ : E → EReal))`, is continuous on the intrinsic subtype `C`, and satisfies the
  conjugate-value formula pointwise through the conjugate's canonical finite branch
  `(fStar).realBranch` along that owner map.

Domain-style sampling used here:
- `Function.subdifferentialAt_eq_singleton_gradient_of_mem_interior_dom` from `Theorem_26_1`;
- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` from
  `Corollary_23_5_1`;
- `Function.continuous_gradient_realBranch_on_open_convex` from `Corollary_25_5_1`;
- the Corollary 26.4.1 conjugate strict-convexity/domain theorem
  `convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between`.

Primitive data vs derived API:
- primitive inputs: the genuinely extra lower-semicontinuity hypothesis
  `hclosed : LowerSemicontinuous f` together with the source hypothesis
  `hess : f.IsEssentiallySmooth`, whose owner already carries convexity and properness;
- primitive source-facing object: the raw gradient branch `x ↦ ∇ f.realBranch x` on
  `C = interior (dom(f))`;
- derived API: the `Set.MapsTo` / `Set.SurjOn` description of its Legendre-side image
  `D = dom∂((f⋆ : E → EReal))`, continuity of the restricted gradient branch on the subtype `C`,
  and the conjugate-value identity stated on the canonical branch `(fStar).realBranch`.

Layer target: `bridge/view`, organized under the canonical closed-proper-convex owner namespace
already used by the neighboring Chapter 26 Legendre results.
-/

local notation "C" => interior (dom(f))
local notation "fStar" => ((f⋆ : E → EReal))
local notation "D" => dom∂(fStar)

-- Proof sketch: for `x ∈ C`, Theorem 26.1 identifies `∂f(x)` with the singleton
-- `{∇ f.realBranch x}`. Corollary 23.5.1 then transfers this membership across Fenchel conjugacy
-- to `x ∈ ∂f⋆(∇ f.realBranch x)`, which is exactly the statement that the gradient value belongs
-- to the canonical Legendre-side domain `D`.
/-- The raw gradient branch `x ↦ ∇ f.realBranch x` maps the primal interior domain
`C = interior (dom(f))` into the canonical Legendre-side domain
`D = dom∂((f⋆ : E → EReal))`. -/
theorem mapsTo_gradient_realBranch_interior_dom_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) :
    Set.MapsTo (fun x ↦ ∇ f.realBranch x) C D := sorry

-- Proof sketch: take any `xStar` in the canonical Legendre-side domain
-- `D`, so some `x` satisfies `x ∈ ∂f⋆(xStar)`. By
-- Corollary 23.5.1 this means `xStar ∈ ∂f(x)`. Essential smoothness and Theorem 26.1 force
-- `x ∈ C` and identify that subgradient fiber with the singleton `{∇ f.realBranch x}`, so
-- `xStar` is exactly the value of the raw gradient branch at some point of `C`.
/-- The raw gradient branch `x ↦ ∇ f.realBranch x` maps `C = interior (dom(f))` onto the
canonical Legendre-side domain `D = dom∂((f⋆ : E → EReal))`. -/
theorem surjOn_gradient_realBranch_interior_dom_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) :
    Set.SurjOn (fun x ↦ ∇ f.realBranch x) C D := sorry

section FiniteDimensional

variable [FiniteDimensional ℝ E]

-- Proof sketch: this is the exact Chapter 25 owner theorem
-- `Function.continuous_gradient_realBranch_on_open_convex` specialized to
-- `C = interior (dom(f))`. Essential smoothness already supplies convexity of `f`, finiteness of
-- `f` on `C`, and differentiability of `f.realBranch` on `C`.
/-- The raw gradient branch `x ↦ ∇ f.realBranch x` is continuous on the intrinsic subtype
`C = interior (dom(f))`. Combined with the maps-to theorem above, this is the source-facing
continuous parameterization of the canonical Legendre-side domain `D`. -/
theorem continuous_gradient_realBranch_on_interior_dom_of_isEssentiallySmooth
    (hess : f.IsEssentiallySmooth) :
    Continuous (fun x : C ↦ ∇ f.realBranch (x : E)) := by
  have hdom_convex : Convex ℝ dom(f) := hess.convex.convex_dom
  have hC_convex : Convex ℝ C := hdom_convex.interior
  refine Function.continuous_gradient_realBranch_on_open_convex
    isOpen_interior hC_convex hess.convex ?_ hess.differentiableOn_realBranch
  intro x hx
  exact ⟨interior_subset hx, hess.proper.ne_bot x⟩

end FiniteDimensional

-- Proof sketch: for `x ∈ interior (dom(f))`, Theorem 26.1 gives
-- `∇ f.realBranch x ∈ ∂f(x)`. Corollary 23.5.1 moves this to the conjugate side, so Fenchel-Young
-- equality from Theorem 23.5 applies at `(x, ∇ f.realBranch x)`, yielding the stated affine
-- defect formula directly on the owner gradient branch.
/-- Text 26.4.1.2: for `x ∈ C = interior (dom(f))`, the canonical Legendre-side branch value of
the Fenchel conjugate at the gradient point `xStar = ∇ f.realBranch x ∈ D = dom∂((f⋆ : E →
EReal))` is the affine defect `⟪x, xStar⟫ - f(x)`. Equivalently, the Legendre conjugate may be
viewed as a generally nonconvex function on `C` itself through the raw gradient branch. -/
theorem convexConjugate_realBranch_gradient_eq_inner_sub_of_mem_interior_dom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ C) :
    (fStar).realBranch (∇ f.realBranch x) =
      ⟪x, ∇ f.realBranch x⟫ - f.realBranch x := sorry

end Function.IsClosedProperConvex

end
