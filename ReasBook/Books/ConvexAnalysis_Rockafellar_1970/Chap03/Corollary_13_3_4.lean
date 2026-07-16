import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_7_0
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.4 studies the translated function
  `g(x) = f x - ⟪x, x⋆⟫` for a closed proper convex function `f` and characterizes the position of
  `x⋆` relative to `dom f⋆` in terms of the recession function `g₀⁺`.
- `core/canonical`: the owner abstractions already present in the project are
  `isClosedProperConvexFunction`, `convexConjugate`, `ConvexERealFunction.recessionFunction`,
  `Function.constancySpace`, `closure`, `intrinsicInterior ℝ`, `interior`, and
  `affineSpan`.
- `bridge/view`: Rockafellar's `dom f⋆` is rendered by the chapter's canonical effective-domain
  owner `dom(f⋆)`, while the translated function `g` is written directly as the affine
  perturbation `fun x ↦ f x - (⟪x, xStar⟫ : EReal)`.

Domain-style sampling used here:
- `mem_closure_iff_dual_le_supportFunction` and
  `mem_intrinsicInterior_iff_mem_closure_and_lt_of_support_asymmetry` from `Theorem_13_1.lean`;
- `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from
  `Theorem_13_3.lean`;
- `convexConjugate_affineChange` from `Theorem_12_3.lean`;
- `Function.constancySpace` and `Function.mem_constancySpace_iff` from
  `Definiton_8_7_0.lean`;
- the topological owners `closure`, `intrinsicInterior ℝ`, `interior`, and `affineSpan`.

Primitive data vs derived API:
- primitive inputs: the function `f` and the fixed vector `xStar`;
- derived owner hypothesis: `isClosedProperConvexFunction f`;
- source-facing core object: the translated function `g(x) = f x - ⟪x, x⋆⟫`;
- derived API: the four domain-position criteria for `xStar`.

Layer target: `source-facing`, stated directly in the canonical project language without replacing
the translated function by an existential or surrogate package.
-/

variable (f : E → EReal) (xStar : E)
variable (hf : f.IsClosedProperConvex)

local notation "g" => fun x ↦ f x - (⟪x, xStar⟫ : EReal)
local notation "g0⁺" => ((g)₀⁺)

-- Proof sketch: let `g := fun x ↦ f x - (⟪x, xStar⟫ : EReal)`. The canonical affine-conjugation
-- owner `convexConjugate_affineChange` identifies the conjugate
-- domain of `g` as the translate `dom(f⋆) - xStar`. Theorem 13.3 identifies the
-- support function of that translated domain with `g0⁺`, and Theorem 13.1's
-- closure criterion at the origin rewrites `0 ∈ closure (dom g⋆)` as pointwise nonnegativity of
-- `g₀⁺`.
/-- Corollary 13.3.4 (1): clause (a). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `cl (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` is nonnegative in every direction. -/
theorem mem_closure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction_inner_sub
    :
    xStar ∈ closure (dom((f⋆ : E → EReal))) ↔
      ∀ y : E, (0 : EReal) ≤ g0⁺ y := sorry

-- Proof sketch: keep `g := fun x ↦ f x - (⟪x, xStar⟫ : EReal)` and translate `dom g⋆` back
-- to `dom f⋆` as in part (a). The support-function formula from Theorem 13.3 gives
-- `supportFunction (dom g⋆) = g₀⁺`, while the relative-interior criterion from Theorem 13.1 at
-- the origin says exactly that every direction is either a zero direction in the owner constancy
-- space `Function.constancySpace g0⁺` or has strictly positive value.
/-- Corollary 13.3.4 (2): clause (b). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `ri (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` is strictly positive in every direction except the zero directions in
`Function.constancySpace g₀⁺`. -/
theorem
    mem_intrinsicInterior_effectiveDomain_convexConjugate_iff_pos_or_zero_on_constancySpace_recessionFunction_inner_sub
    :
    xStar ∈ intrinsicInterior ℝ (dom((f⋆ : E → EReal))) ↔
      ∀ y : E,
        (0 : EReal) < g0⁺ y ∨
          (y ∈ Function.constancySpace g0⁺ ∧ g0⁺ y = (0 : EReal)) := sorry

-- Proof sketch: again translate to the origin for `dom g⋆`. Theorem 13.1 identifies interior
-- membership of a convex set with strict support-function positivity on every nonzero direction;
-- using Theorem 13.3 to replace that support function by `g₀⁺` yields the displayed criterion.
/-- Corollary 13.3.4 (3): clause (c). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `int (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` is strictly positive in every nonzero direction. -/
theorem mem_interior_effectiveDomain_convexConjugate_iff_pos_recessionFunction_inner_sub_of_ne_zero
    :
    xStar ∈ interior (dom((f⋆ : E → EReal))) ↔
      ∀ y : E, y ≠ 0 →
        (0 : EReal) < g0⁺ y := sorry

-- Proof sketch: let `g := fun x ↦ f x - (⟪x, xStar⟫ : EReal)` as above. The affine-span
-- criterion for the origin in a convex set says `0 ∈ aff (dom g⋆)` exactly when the support
-- interval of `dom g⋆` collapses only at `0`: whenever the lower and upper support values agree,
-- that common value must be `0`. Theorem 13.3 replaces the support function of `dom g⋆` by `g₀⁺`,
-- yielding the displayed support-symmetry criterion for the translated recession function.
/-- Corollary 13.3.4 (4): clause (d). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `aff (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` has the property that every direction where the support symmetry relation
`-g₀⁺(-y) = g₀⁺ y` holds actually has common value `0`. -/
theorem mem_affineSpan_effectiveDomain_convexConjugate_iff_zero_of_support_symmetry_recessionFunction_inner_sub
    :
    xStar ∈ affineSpan ℝ (dom((f⋆ : E → EReal))) ↔
      ∀ y : E,
        -(g0⁺ (-y)) = g0⁺ y → g0⁺ y = (0 : EReal) := sorry

end
