import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_26_2_1 (from Chap05) -/
universe u

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 26.2.1 introduces strict convexity on a convex set and the Chapter
  26 notion of essential strict convexity for a proper convex function, phrased through convex
  subsets of the subdifferential domain.
- `core/canonical`: the owner abstractions are mathlib's
  `StrictConvexOn 𝕜 C g`, `Function.IsConvex`, `Function.IsProper`, and the canonical
  relation-domain owner `dom∂[Y](f)` at explicit pairing codomain `Y`.
- `bridge/view`: the textbook set `{x | ∂f(x) ≠ ∅}` is the companion reformulation of the
  canonical owner domain `dom∂[Y](f)` via
  `mem_subdifferentialGraph_dom`.

Domain-style sampling used here:
- `StrictConvexOn` from mathlib's convex-function owner layer;
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `SetRel.dom` specialized to the subdifferential graph in `Chap05.Definition_5_24_1`.

Primitive data vs derived API:
- primitive source data: a proper convex function `f : E → WithTopBot 𝕜` and pairing codomain `Y`;
- primitive owner: `Function.IsEssentiallyStrictlyConvex f Y`, storing convexity, properness,
  and strict convexity of `f` on each convex subset of `dom∂[Y](f)`;
- derived API: the textbook reformulation using pointwise nonemptiness `∂[Y]f(x) ≠ ∅`.

Layer target:
- `StrictConvexOn`: `core/canonical` recall, since the source strict-convexity clause already has
  the canonical mathlib owner;
- `Function.IsEssentiallyStrictlyConvex`: `source-facing`, because this numbered item is the
  source definition site of the Chapter 26 notion;
- `strictConvexOn_of_forall_subdifferentialAt_nonempty`: `bridge/view` at the canonical
  nonemptiness layer;
- `strictConvexOn_of_forall_subdifferentialAt_ne_empty`: `bridge/view` in textbook `≠ ∅` form.
-/

/- Definition 26.2.1 (strict-convexity clause): the source notion of a function being strictly
convex on a convex set is the canonical mathlib owner `StrictConvexOn`. -/
recall StrictConvexOn

namespace Function

section

variable {𝕜 : Type _} [Semiring 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-- Definition 26.2.1: a proper `WithTopBot 𝕜`-valued function is essentially strictly convex
when it is strictly convex on every convex subset of the canonical subgradient-domain owner
`dom∂[Y](f)`. -/
@[mk_iff]
class IsEssentiallyStrictlyConvex (f : E → WithTopBot 𝕜)
    (Y : Type _ := StrongDual 𝕜 E) [HasPairing E Y 𝕜] : Prop where
  convex : f.IsConvex 𝕜
  proper : f.IsProper
  strictConvexOn {C : Set E} (hC_convex : Convex 𝕜 C) (hC_dom : C ⊆ dom∂[Y](f)) :
      StrictConvexOn 𝕜 C f

namespace IsEssentiallyStrictlyConvex

/-- Canonical nonemptiness bridge for Definition 26.2.1: on any convex set contained in the points
where `∂[Y]f(x)` is nonempty, `f` is strictly convex. -/
theorem strictConvexOn_of_forall_subdifferentialAt_nonempty
    {f : E → WithTopBot 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : IsEssentiallyStrictlyConvex (Y := Y) f)
    {C : Set E} (hC_convex : Convex 𝕜 C)
    (hC_subdiff_nonempty : ∀ ⦃x : E⦄, x ∈ C → (∂[Y]f(x)).Nonempty) :
    StrictConvexOn 𝕜 C f := by
  have hC_dom : C ⊆ dom∂[Y](f) := by
    intro x hx
    exact (_root_.mem_domSubdifferential_iff_nonempty (f := f) (Y := Y)).2
      (hC_subdiff_nonempty hx)
  exact hf.strictConvexOn hC_convex hC_dom

/-- Textbook reformulation of Definition 26.2.1 in `≠ ∅` form. -/
theorem strictConvexOn_of_forall_subdifferentialAt_ne_empty
    {f : E → WithTopBot 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : IsEssentiallyStrictlyConvex (Y := Y) f)
    {C : Set E} (hC_convex : Convex 𝕜 C)
    (hC_subdiff_nonempty : ∀ ⦃x : E⦄, x ∈ C → ∂[Y]f(x) ≠ ∅) :
    StrictConvexOn 𝕜 C f := by
  refine strictConvexOn_of_forall_subdifferentialAt_nonempty (Y := Y) hf hC_convex ?_
  intro x hx
  exact Set.nonempty_iff_ne_empty.2 (hC_subdiff_nonempty hx)

end IsEssentiallyStrictlyConvex

end

end Function

/-! ### Example_26_2_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar

local notation "R2" => ℝ × ℝ
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

local instance instHasPairingPrimalStrongDual : HasPairing R2 (StrongDual ℝ R2) ℝ where
  pairing x xStar := xStar x

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 26.2.1 is a concrete planar `WithBotTop ℝ`-valued function with three
  source-facing claims: `dom ∂f` is the open positive quadrant, the function is strictly convex
  there but not on all of `dom(f)`, and nevertheless it is essentially strictly convex and
  essentially smooth.
- `core/canonical`: the owner abstractions already present in the chapter are
  `dom∂(f)`, `StrictConvexOn ℝ C g`,
  `Function.IsClosedProperConvex`, `Function.IsEssentiallyStrictlyConvex`, and
  `Function.IsEssentiallySmooth`, together with the upstream concrete owner
  `quadraticOverLinearFunction`.
- `bridge/view`: this item introduces no new owner. It is an explicit example function together
  with companion theorems stated directly on those existing owners, reusing the Chapter 10
  quadratic-over-linear owner rather than reimplementing its branch structure.

Domain-style sampling used here:
- `quadraticOverLinearFunction` from `Chap02.Theorem_10_1_4`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsEssentiallySmooth` from `Chap05.Definition_26_1_1`;
- `Function.IsEssentiallyStrictlyConvex` from `Chap05.Definition_26_2_1`;
- `dom∂(f)` from `Chap05.Definition_5_24_1`;
- pair-coordinate set surfaces `{ξ : R2 | 0 < ξ.1 ∧ 0 < ξ.2}` and
  `{ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0}`;
- `StrictConvexOn` from mathlib's convex-function owner layer.

Primitive data vs derived API:
- primitive source-facing data: the explicit function on `R²`, the open positive-quadrant set
  owner, and the nonnegative `ξ₁`-axis set;
- derived API: closed-proper-convexity of the example, the subdifferential-domain identification,
  strict convexity on the open quadrant, constancy on the axis, failure of strict convexity on the
  whole effective domain, and the final Chapter 26 essential-regularity conclusions.

Layer target: `source-facing`.
-/

/-- The open positive quadrant `{(ξ₁, ξ₂) | ξ₁ > 0, ξ₂ > 0}` in `R²`. -/
def quadraticSqrtExamplePositiveQuadrant : Set R2 :=
  {ξ : R2 | 0 < ξ.1 ∧ 0 < ξ.2}

/-- The nonnegative `ξ₁`-axis `{(ξ₁, 0) | ξ₁ ≥ 0}` in `R²`. -/
def quadraticSqrtExampleNonnegativeXAxis : Set R2 :=
  {ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0}

/-- The quadratic-over-linear minus square-root function:
`f(ξ₁, ξ₂) = ξ₂² / (2 ξ₁) - 2 √ξ₂` for `ξ₁ > 0` and `ξ₂ ≥ 0`,
`f(0, 0) = 0`, and `f = +∞` otherwise. -/
def quadraticSqrtExampleFunction : R2 → WithBotTop ℝ :=
  quadraticOverLinearFunction +
    (fun ξ : R2 ↦ ((-(2 : ℝ) * Real.sqrt ξ.2 : ℝ) : WithBotTop ℝ)) +
    (δ(· | {ξ : R2 | 0 ≤ ξ.2}) : R2 → WithBotTop ℝ)

-- Proof sketch: rewrite the example as the sum of the quadratic-over-linear branch
-- `(ξ₁, ξ₂) ↦ ξ₂² / (2 ξ₁)` on `ξ₁ > 0, ξ₂ ≥ 0`, the convex branch `ξ₂ ↦ -2 √ξ₂`, and the
-- `+∞`-extension outside the half-strip together with the finite value at the origin. Convexity
-- comes from the perspective construction and convexity of `-sqrt`, properness from the explicit
-- finite value at `0`, and lower semicontinuity from the boundary behavior of the branch formula.
/-- The quadratic-over-linear minus square-root example function is closed, proper, and convex. -/
theorem quadraticSqrtExampleFunction_isClosedProperConvex :
    IsClosedProperConvex[ℝ] quadraticSqrtExampleFunction := sorry

-- Proof sketch: identify `interior (dom(f))` with the open positive quadrant. Then use the
-- Example 26.2.1 essential-smoothness theorem together with Theorem 26.1: for a closed proper
-- convex function, the subdifferential is nonempty exactly on `interior (dom(f))`.
/-- The subdifferential domain of the quadratic-over-linear minus square-root example function is
the open positive quadrant. -/
theorem quadraticSqrtExample_domSubdifferential_eq_positiveQuadrant :
    dom∂(quadraticSqrtExampleFunction) = quadraticSqrtExamplePositiveQuadrant := sorry

-- Proof sketch: on the open quadrant the finite real branch is smooth. Compute the Hessian of
-- `ξ₂² / (2 ξ₁) - 2 √ξ₂` and show it is positive definite there, yielding strict convexity of the
-- real branch on that open convex set.
/-- On the open positive quadrant, the finite real branch of the quadratic-over-linear minus
square-root example function is strictly convex. -/
theorem quadraticSqrtExample_strictConvexOn_positiveQuadrant :
    StrictConvexOn ℝ quadraticSqrtExamplePositiveQuadrant
      quadraticSqrtExampleFunction.realBranch := sorry

-- Proof sketch: if `ξ₂ = 0` and `ξ₁ ≥ 0`, then either `ξ = 0` or `ξ₁ > 0` with `ξ₂ = 0`. In
-- both cases the defining formula gives the finite value `0`, so every point of the nonnegative
-- `ξ₁`-axis lies in the effective domain.
/-- The nonnegative `ξ₁`-axis lies in the effective domain of the example function. -/
theorem quadraticSqrtExampleNonnegativeXAxis_subset_dom :
    quadraticSqrtExampleNonnegativeXAxis ⊆ dom(quadraticSqrtExampleFunction) := sorry

-- Proof sketch: evaluate the branch formula at `ξ₂ = 0`. The quadratic-over-linear term and the
-- square-root term both vanish, and the origin clause also gives `0`.
/-- Along the nonnegative `ξ₁`-axis, the quadratic-over-linear minus square-root example function
is identically zero. -/
theorem quadraticSqrtExample_eq_zero_on_nonnegativeXAxis :
    Set.EqOn quadraticSqrtExampleFunction 0
      quadraticSqrtExampleNonnegativeXAxis := sorry

-- Proof sketch: the nonnegative `ξ₁`-axis is contained in `dom(f)` by the previous theorem, and
-- the function is constant there. Taking two distinct axis points and their midpoint shows that
-- the strict-convexity inequality fails on `dom(f)`.
/-- The quadratic-over-linear minus square-root example function is not strictly convex on its
whole effective domain. -/
theorem quadraticSqrtExample_not_strictConvexOn_dom :
    ¬ StrictConvexOn ℝ (dom(quadraticSqrtExampleFunction))
      quadraticSqrtExampleFunction.realBranch := sorry

-- Proof sketch: on the open positive quadrant, Theorem 25.1 identifies the subdifferential with
-- the gradient of the finite branch, and the Hessian computation gives strict convexity there.
-- As `ξ₁ ↓ 0` or `ξ₂ ↓ 0` along the interior, the gradient norm tends to `∞`, giving essential
-- smoothness via Definition 26.1.1.
/-- Example 26.2.1: the quadratic-over-linear minus square-root example function is essentially
smooth. -/
theorem quadraticSqrtExampleFunction_isEssentiallySmooth :
    quadraticSqrtExampleFunction.IsEssentiallySmooth := sorry

-- Proof sketch: combine the closed/proper/convex owner, the identification
-- `dom∂(quadraticSqrtExampleFunction) = quadraticSqrtExamplePositiveQuadrant`, and strict
-- convexity of the real branch on that open quadrant. Any convex subset of `dom∂(f)` is then a
-- convex subset of the positive quadrant, so strict convexity restricts to it.
/-- Example 26.2.1: the quadratic-over-linear minus square-root example function is essentially
strictly convex. -/
theorem quadraticSqrtExampleFunction_isEssentiallyStrictlyConvex :
    Function.IsEssentiallyStrictlyConvex quadraticSqrtExampleFunction := sorry

/-! ### Text_26_2_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.2.1 draws two consequences from the definition of essential strict
  convexity and the Chapter 23 subdifferential-domain sandwich: strict convexity on `ri(dom f)`,
  and the caution that `dom ∂f` need not be convex.
- `core/canonical`: the owner abstractions are `Function.IsEssentiallyStrictlyConvex`,
  `StrictConvexOn 𝕜 C f`, `riDom[𝕜](f)`, and the canonical subdifferential-domain owner
  `dom∂[Y](f)`.
- `bridge/view`: the text's `dom ∂f` is expressed directly by the established notation
  `dom∂[Y](f)`;
  no parallel wrapper for the subdifferential domain is introduced.

Domain-style sampling used here:
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `StrictConvexOn` from mathlib's convex-function owner layer;
- `Function.realBranch` from `Chap02.Theorem_10_4`;
- `riDom(·)` from `Chap01.Definition_4_4`;
- `dom∂[·](·)` and `mem_subdifferentialGraph_dom` from `Chap05.Definition_5_24_1`.

Primitive data vs derived API:
- primitive owner data: an essentially strictly convex function `f`;
- derived API: strict convexity of the real branch on `riDom(f)`, and the existential caution that
  `dom∂[Y](f)` need not itself be convex even inside the closed/proper/convex owner layer.

Layer target:
- `Function.IsEssentiallyStrictlyConvex.strictConvexOn_riDom`: `bridge/view`, derived from the
  owner field over the Chapter 23 inclusion `riDom[𝕜](f) ⊆ dom∂[Y](f)`;
- `Function.IsEssentiallyStrictlyConvex.strictConvexOn_realBranch_riDom`: `bridge/view`,
  expressing the finite real branch as a companion view;
- `subdifferentiabilityCounterexample_not_convex_domSubdifferential`: `bridge/view`, translating
  Example 23.4.2 from the graph-domain owner to `dom∂(·)`;
- `exists_nonconvex_domSubdifferential`: a companion existence statement inside
  `Function.IsClosedProperConvex`, not a second owner.
-/

namespace Function

section

variable {𝕜 : Type _}
variable [Field 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [DecidableLT 𝕜]
variable {E : Type u}
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]

namespace IsEssentiallyStrictlyConvex

-- Proof sketch: `riDom(f)` is convex by Theorem 6.2. Apply the defining strict-convexity field
-- of `hf` to the convex set `riDom[𝕜](f)` once the owner-level bridge
-- `riDom[𝕜](f) ⊆ dom∂[Y](f)` is
-- provided.
/-- Primitive owner-level bridge for Text 26.2.1: an essentially strictly convex function is
strictly convex on `ri(dom f)` as soon as `riDom[𝕜](f) ⊆ dom∂[Y](f)` is available. -/
theorem strictConvexOn_riDom_of_subset
    {f : E → WithBotTop 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f)
    (hri : riDom[𝕜](f) ⊆ dom∂[Y](f)) :
    StrictConvexOn 𝕜 riDom[𝕜](f) f := by
  rcases hf with ⟨hconvex, _hproper, hstrictOn⟩
  exact hstrictOn (Convex.intrinsicInterior hconvex.convex_dom) hri

end IsEssentiallyStrictlyConvex

end

section

variable {𝕜 : Type _}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace IsEssentiallyStrictlyConvex

-- Proof sketch: apply the primitive owner-level bridge above with the canonical inclusion
-- `riDom[𝕜](f) ⊆ dom∂[Y](f)` from Remark 5.24.1 for proper convex functions.
/-- Text 26.2.1: whenever the Chapter 23/Remark 5.24.1 inclusion
`riDom[𝕜](f) ⊆ dom∂[Y](f)` is available for proper convex functions, an essentially strictly convex
function is strictly convex on `ri(dom f)`. -/
theorem strictConvexOn_riDom
    {f : E → WithBotTop 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f) :
    StrictConvexOn 𝕜 riDom[𝕜](f) f := by
  rcases hf with ⟨hconvex, hproper, hstrictOn⟩
  exact strictConvexOn_riDom_of_subset (hf := ⟨hconvex, hproper, hstrictOn⟩)
    (_root_.riDom_subset_domSubdifferential_of_convex_proper
      (Y := Y) hconvex hproper)

end IsEssentiallyStrictlyConvex

end

section

variable {E : Type u}
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousConstSMul ℝ E]

namespace IsEssentiallyStrictlyConvex

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in
private theorem strictConvexOn_real_of_coe
    {C : Set E} {g : E → ℝ}
    (h : StrictConvexOn ℝ C (fun x ↦ ((g x : ℝ) : WithBotTop ℝ))) :
    StrictConvexOn ℝ C g := by
  rcases h with ⟨hC_convex, hineq⟩
  refine ⟨hC_convex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hltE :
      (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
        a • (((g x : ℝ) : WithBotTop ℝ)) + b • (((g y : ℝ) : WithBotTop ℝ)) :=
    hineq hx hy hxy ha hb hab
  have hltCoe :
      (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
        (((a * g x + b * g y : ℝ) : WithBotTop ℝ)) := by
    change (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
      (((a : ℝ) : WithBotTop ℝ) * (((g x : ℝ) : WithBotTop ℝ)) +
        ((b : ℝ) : WithBotTop ℝ) * (((g y : ℝ) : WithBotTop ℝ)))
    simpa [smul_eq_mul] using hltE
  exact (WithBotTop.coe_lt_coe).1 hltCoe

-- Proof sketch: first use the canonical owner-level theorem
-- `strictConvexOn_riDom_of_subset` on `f : E → WithBotTop ℝ`; then identify `f` with its finite
-- real branch on `riDom(f)` using `dom∂[Y](f) ⊆ dom(f)`.
/-- Real-branch bridge for Text 26.2.1: once `riDom(f) ⊆ dom∂[Y](f)` is known, strict convexity
of the extended-value owner `f` on `riDom(f)` transfers to strict convexity of `f.realBranch`. -/
theorem strictConvexOn_realBranch_riDom_of_subset
    {f : E → WithBotTop ℝ} {Y : Type _} [HasPairing E Y ℝ]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f)
    (hri : riDom(f) ⊆ dom∂[Y](f)) :
    StrictConvexOn ℝ riDom(f) f.realBranch := by
  rcases hf with ⟨hconvex, hproper, hstrictOn⟩
  have hf' : Function.IsEssentiallyStrictlyConvex (Y := Y) f := ⟨hconvex, hproper, hstrictOn⟩
  have hstrict : StrictConvexOn ℝ riDom(f) f := by
    simpa using
      (strictConvexOn_riDom_of_subset (𝕜 := ℝ) (Y := Y) (f := f) hf' hri)
  have hdomSub : dom∂[Y](f) ⊆ dom(f) :=
    _root_.domSubdifferential_subset_dom (Y := Y) hproper.nonempty_dom
  have hEq : Set.EqOn f (fun x ↦ ((f.realBranch x : ℝ) : WithBotTop ℝ)) riDom(f) := by
    intro x hx
    have hxdomSub : x ∈ dom∂[Y](f) := hri hx
    have hxdom : x ∈ dom(f) := hdomSub hxdomSub
    have hneTop : f x ≠ ⊤ := ne_of_lt (mem_effectiveDomain.mp hxdom)
    have hneBot : f x ≠ ⊥ := hproper.ne_bot x
    simpa [Function.realBranch] using (EReal.coe_toReal hneTop hneBot).symm
  exact strictConvexOn_real_of_coe (hstrict.congr hEq)

end IsEssentiallyStrictlyConvex

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsEssentiallyStrictlyConvex

-- Proof sketch: combine `strictConvexOn_realBranch_riDom_of_subset` with the canonical Chapter 23
-- inclusion from Remark 5.24.1.
/-- Text 26.2.1 (real-branch view): an essentially strictly convex function is strictly convex on
`ri(dom f)` after passing to the finite branch `f.realBranch`. -/
theorem strictConvexOn_realBranch_riDom
    {f : E → WithBotTop ℝ} {Y : Type _} [HasPairing E Y ℝ]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f) :
    StrictConvexOn ℝ riDom(f) f.realBranch := by
  rcases hf with ⟨hconvex, hproper, hstrictOn⟩
  have hf' : Function.IsEssentiallyStrictlyConvex (Y := Y) f := ⟨hconvex, hproper, hstrictOn⟩
  refine strictConvexOn_realBranch_riDom_of_subset (Y := Y) hf' ?_
  simpa using _root_.riDom_subset_domSubdifferential_of_convex_proper
    (Y := Y) hconvex hproper

end IsEssentiallyStrictlyConvex

end

end Function

-- Proof sketch: Example 23.4.2 gives an explicit function on `R²` whose subdifferentiability
-- locus is not convex. Via Definition 5.24.1, that locus is exactly the canonical owner
-- `dom∂(f)`.
/-- Example 23.4.2: the canonical subdifferential-domain owner `dom∂(f)` is not convex for the
closed proper convex counterexample function. -/
theorem subdifferentiabilityCounterexample_not_convex_domSubdifferential :
    ¬ Convex ℝ dom∂(subdifferentiabilityCounterexample) := by
  intro hconv
  have hconv' :
      Convex ℝ (_root_.subdifferentialGraph subdifferentiabilityCounterexample).dom := hconv
  rw [← Function.subdifferentialGraph_dom_eq_intrinsic (f := subdifferentiabilityCounterexample)]
    at hconv'
  exact not_convex_subdifferentialGraph_dom hconv'

/-- The subdifferential domain `dom∂(f)` need not be convex even for a closed proper convex
function. -/
theorem exists_nonconvex_domSubdifferential :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
      (f : E → WithBotTop ℝ),
      Function.IsClosedProperConvex (𝕜 := ℝ) f ∧ ¬ Convex ℝ dom∂(f) := by
  refine ⟨EuclideanSpace ℝ (Fin 2), inferInstance, inferInstance,
    subdifferentiabilityCounterexample, ?_⟩
  constructor
  · simpa using subdifferentiabilityCounterexample_isClosedProperConvex
  · exact subdifferentiabilityCounterexample_not_convex_domSubdifferential

/-! ### Example_26_2_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜]

local notation "R2" => 𝕜 × 𝕜
/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 26.2.2 is a planar `WithBotTop 𝕜`-valued function obtained by adding
  the Chapter 10 quadratic-over-linear owner, the square of the second coordinate, and the
  indicator of the upper half-plane `ξ₂ ≥ 0`. The source-facing conclusions are its explicit
  finite branch formula, owner-level closed/proper/convexity, the relative-interior domain
  identification, strict convexity on that relative interior, the explicit constancy on the
  nonnegative `ξ₁`-axis, the extra subdifferentiability there, and the failure of essential strict
  convexity.
- `core/canonical`: the owner abstractions already present upstream are
  `quadraticOverLinearFunction`, `Function.IsClosedProperConvex`,
  `Function.IsEssentiallyStrictlyConvex`, `riDom[𝕜](·)`, and `dom∂(·)`.
- `bridge/view`: this file keeps the source-facing branch and axis sets directly as canonical
  pair-coordinate `Set` surfaces without adding extra set owners.

Domain-style sampling used here:
- `quadraticOverLinearFunction` from `Chap02.Theorem_10_1_4`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsEssentiallyStrictlyConvex` from `Chap05.Definition_26_2_1`;
- `dom∂(·)` and `mem_subdifferentialGraph_dom` from `Chap05.Definition_5_24_1`.

Primitive data vs derived API:
- primitive source-facing data: the explicit example function, together with the source
  pair-coordinate positive-quadrant/nonnegative-axis/upper-half-plane set surfaces;
- derived API: the branch formula on the positive quadrant, owner-level
  `IsClosedProperConvex`, the `riDom[𝕜]` description, strict convexity on `riDom[𝕜]`, the
  pointwise constancy on the nonnegative `ξ₁`-axis, the `dom∂(·)` inclusion there, and the
  final non-essential-strict-convexity conclusion.

Layer target: `source-facing`.

Scalar/ambient minimality note:
- this item is stated on the pair ambient `R2 = 𝕜 × 𝕜`, matching the Chapter 10 owner
  `quadraticOverLinearFunction` directly and avoiding finite-index Euclidean coordinate wrappers;
- the codomain is the chapter-canonical `WithBotTop 𝕜`;
- the public surfaces use the generic chapter owners `riDom[𝕜](·)`, `dom∂(·)`, and
  `Function.IsEssentiallyStrictlyConvex` directly.
-/

/-- The Example 26.2.2 function on `R²`, obtained by adding the squared second coordinate and
the indicator of `ξ₂ ≥ 0` to the Chapter 10 quadratic-over-linear owner. -/
def positiveQuadrantPerspectiveSquare (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] :
    (𝕜 × 𝕜) → WithBotTop 𝕜 :=
  quadraticOverLinearFunction +
    (fun ξ : 𝕜 × 𝕜 ↦ (((ξ.2) ^ 2 : 𝕜) : WithBotTop 𝕜)) +
    (δ[𝕜](· | {ξ : 𝕜 × 𝕜 | 0 ≤ ξ.2}) : (𝕜 × 𝕜) → WithBotTop 𝕜)

-- Proof sketch: on the branch `ξ₁ > 0`, `ξ₂ ≥ 0`, the Chapter 10 owner
-- `quadraticOverLinearFunction` contributes `ξ₂² / (2 ξ₁)`, the added quadratic term contributes
-- `ξ₂²`, and the indicator term vanishes.
/-- On the source branch `ξ₁ > 0`, `ξ₂ ≥ 0`, Example 26.2.2 has the explicit finite-value formula
`ξ₂² / (2 ξ₁) + ξ₂²`. -/
theorem positiveQuadrantPerspectiveSquare_eq_of_pos_first_of_nonneg_second
    {ξ : R2} (hξ₁ : 0 < ξ.1) (hξ₂ : 0 ≤ ξ.2) :
    (positiveQuadrantPerspectiveSquare 𝕜) ξ =
      (((ξ.2) ^ 2 / (2 * ξ.1) + (ξ.2) ^ 2 : 𝕜) : WithBotTop 𝕜) := sorry

end

section

variable {𝕜 : Type u}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

local notation "R2" => 𝕜 × 𝕜
local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

local instance instHasPairingPrimalStrongDual : HasPairing R2 (StrongDual 𝕜 R2) 𝕜 where
  pairing x xStar := xStar x

-- Proof sketch: the Chapter 10 quadratic-over-linear owner is convex and lower semicontinuous,
-- the added square term is everywhere finite and convex, and the indicator of the closed convex
-- half-plane `ξ₂ ≥ 0` is closed proper convex. The origin remains finite, so the sum is proper.
/-- The Example 26.2.2 function is closed, proper, and convex. -/
theorem positiveQuadrantPerspectiveSquare_isClosedProperConvex :
    IsClosedProperConvex[𝕜] (positiveQuadrantPerspectiveSquare 𝕜) := sorry

-- Proof sketch: the effective domain is `{ξ | 0 < ξ 0 ∧ 0 ≤ ξ 1} ∪ {0}` because the
-- quadratic-over-linear owner is finite exactly on `{ξ | 0 < ξ 0} ∪ {0}`, while the indicator
-- cuts away the half-plane `ξ₂ < 0`. The relative interior of that domain is therefore the open
-- positive quadrant.
/-- The relative interior of the effective domain of the Example 26.2.2 function is the open
positive quadrant. -/
theorem riDom_positiveQuadrantPerspectiveSquare_eq_positiveQuadrant :
    riDom[𝕜](positiveQuadrantPerspectiveSquare 𝕜) =
      {ξ : R2 | 0 < ξ.1 ∧ 0 < ξ.2} := sorry

-- Proof sketch: on `ri(dom f)`, namely the open positive quadrant from the previous theorem, the
-- formula is the sum of the strictly convex perspective term `ξ₂² / (2 ξ₁)` and the strictly
-- convex quadratic term `ξ₂²`, so `f` is strictly convex there.
/-- Example 26.2.2 is strictly convex on `ri(dom f)`. -/
theorem strictConvexOn_riDom_positiveQuadrantPerspectiveSquare :
    StrictConvexOn 𝕜 (riDom[𝕜](positiveQuadrantPerspectiveSquare 𝕜))
      (positiveQuadrantPerspectiveSquare 𝕜) := sorry

-- Proof sketch: if `ξ₂ = 0` and `ξ₁ ≥ 0`, then either `ξ = 0` or `ξ₁ > 0` with `ξ₂ = 0`. In
-- both cases the defining formula gives the finite value `0`.
/-- Along the nonnegative `ξ₁`-axis, Example 26.2.2 is identically zero. -/
theorem positiveQuadrantPerspectiveSquare_eq_zero_on_nonnegativeXAxis :
    Set.EqOn (positiveQuadrantPerspectiveSquare 𝕜) 0
      {ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0} := sorry

-- Proof sketch: at every point of the nonnegative `ξ₁`-axis the function value is `0`, and
-- the affine support with slope `0` is valid there for the canonical primal/dual pairing
-- `HasPairing R2 (StrongDual 𝕜 R2) 𝕜`. Equivalently, one shows
-- `Function.subdifferentialAt positiveQuadrantPerspectiveSquare ξ (StrongDual 𝕜 R2) ≠ ∅`
-- for each such `ξ`, then rewrites this as membership in
-- `dom∂(positiveQuadrantPerspectiveSquare)`.
/-- The canonical subdifferential-domain owner `dom∂(f)` of the Example 26.2.2 function contains
the nonnegative `ξ₁`-axis. -/
theorem positiveQuadrantPerspectiveSquareNonnegativeXAxis_subset_domSubdifferential
    :
    {ξ : R2 | 0 ≤ ξ.1 ∧ ξ.2 = 0} ⊆
      dom∂(positiveQuadrantPerspectiveSquare 𝕜) := sorry

-- Proof sketch: the previous two theorems place the nonnegative `ξ₁`-axis inside `dom ∂f` and
-- show that the function is identically `0` there. Since that axis is convex, the defining
-- strict-convexity condition of `Function.IsEssentiallyStrictlyConvex` fails on a convex subset
-- of the subdifferential domain.
/-- Example 26.2.2: the function
`f(ξ₁, ξ₂) = ξ₂² / (2 ξ₁) + ξ₂²` on `ξ₁ > 0`, `ξ₂ ≥ 0`, with `f(0, 0) = 0` and `f = +∞`
otherwise, is closed proper convex and strictly convex on `ri(dom f)` but is not essentially
strictly convex because `dom ∂f` contains the nonnegative `ξ₁`-axis, where the function is
constant. -/
theorem positiveQuadrantPerspectiveSquare_not_isEssentiallyStrictlyConvex
    :
    ¬ Function.IsEssentiallyStrictlyConvex (f := positiveQuadrantPerspectiveSquare 𝕜) :=
  sorry

end

/-! ### Lemma_26_2 (from Chap05) -/
noncomputable section

open Filter
open scoped Rockafellar Topology

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 26.2 refines the Chapter 26 owner `Function.IsEssentiallySmooth` by
  replacing clause `(c)` in Definition 26.1.1 with the equivalent raywise boundary condition
  `(c')` stated on Rockafellar's directional derivative `f'(x; d)`, whose chapter owner is
  `Function.directionalDerivativeAt`. The textbook proof normalizes to the closed case
  internally, but that closedness is not part of the source-facing public statement.
- `core/canonical`: the owner abstractions already present in the chapter are `dom(·)`,
  `Function.realBranch`, `Function.directionalDerivativeAt`, `Function.IsEssentiallySmooth`,
  `Function.IsConvex`, `Function.IsProper`, `DifferentiableOn`, `fderivWithin`, and `lineDeriv`.
- `bridge/view`: the differentiability clause `(b)` lets one replace the directional-derivative
  ray condition by the real-valued `lineDeriv` ray condition once the genuine finite branch is
  fixed on `riDom(f)` (equivalently `interior (dom(f))` under the source hypotheses). That
  `lineDeriv` formulation is kept only as a companion bridge, not as the main owner-level
  statement.

Domain-style sampling used here:
- `Function.IsEssentiallySmoothOn` / `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.directionalDerivativeAt` from `Lemma_23_0_1`;
- `Function.realBranch` from `Chap02/Theorem_10_4`;
- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper` from
  `Chap02/Theorem_7_4`, which supplies the proof-internal closed-case reduction mentioned in the
  source text;
- `lineDeriv` from mathlib's one-dimensional directional-derivative API;
- `Function.isClosed_subdifferentialGraph` from `Theorem_5_24_7`, which matches the closed-graph
  step in the textbook proof.

Primitive data vs derived API:
- source-facing primitive data: a proper convex function `f` together with the Chapter 26 owner
  data `IsEssentiallySmoothOn (riDom(f)) f.realBranch`;
- core owner-side primitive data for the ray theorem: convexity of `f`, one interior point, and
  the explicit lower-finiteness guard `∀ y ∈ riDom(f), f y ≠ ⊥`;
- primitive owner reused from upstream: `Function.directionalDerivativeAt f x d`;
- derived API: intrinsic transport constructors and source-facing wrappers that keep the
  `riDom(f)`-ray clause and boundary derivative clause explicit on theorem surfaces, together with
  a companion `lineDeriv` bridge transport theorem.

Layer target:
- `IsEssentiallySmoothOn.directionalDerivativeAt_ray_tendsto_atBot`: `core/canonical`;
- `IsEssentiallySmooth.directionalDerivativeAt_ray_tendsto_atBot`: `source-facing` forward
  consequence;
- `IsEssentiallySmoothOn.of_boundaryFDerivWithinNorm_tendstoTop`: `core/canonical`
  constructor;
- `isEssentiallySmooth_of_isEssentiallySmoothOn_riDom`: `source-facing`
  constructor;
- `directionalDerivativeAt_ray_tendsto_atBot_iff_lineDeriv_ray_tendsto_atBot`: `bridge/view`,
  with explicit lower finiteness on `riDom(f)`.

Ambient refinement:
- owner-level ray and line-derivative consequences are exposed from
  `IsEssentiallySmoothOn (riDom(f)) f.realBranch`, while source-facing versions consume
  `hf : f.IsEssentiallySmooth` via `hf.toIsEssentiallySmoothOn`;
- the canonical constructor surface for `Function.IsEssentiallySmooth` is intrinsic
  `IsEssentiallySmoothOn (riDom(f)) f.realBranch` plus
  `(interior (dom(f))).Nonempty`; no parallel public constructor is kept on
  `IsEssentiallySmoothOn (interior (dom(f))) f.realBranch` to avoid exposing derived
  ambient-equality transport data as input.
- the `lineDeriv` bridge remains explicit: this file transports a provided
  boundary-derivative-to-ray equivalence, rather than asserting a new unproved implication.
- scalar canonicalization: this file stays at scalar `ℝ` because both reused Chapter 23/26 owners
  are intrinsically real (`Function.directionalDerivativeAt` uses right-ray filters
  `𝓝[>] (0 : ℝ)`, and `Function.IsEssentiallySmooth` is defined over
  `WithBotTop ℝ` / `DifferentiableOn ℝ`).
-/

namespace IsEssentiallySmoothOn

/-- Owner-level ray consequence from essential smoothness on `riDom(f)`:
if one has a bridge turning boundary Fréchet-derivative blow-up into the ray directional-derivative
condition, then the bridge applies directly to the owner data carried by
`IsEssentiallySmoothOn (riDom(f)) f.realBranch`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot
    {f : E → WithBotTop ℝ}
    (hf : IsEssentiallySmoothOn (riDom(f)) f.realBranch)
    (hboundary_to_ray :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      Tendsto
        (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot)
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_ray ha hx (hf.boundaryFDerivWithinNorm_tendstoTop hx)

-- Proof sketch: package the explicit intrinsic hypotheses directly into the owner fields.
/-- Intrinsic-owner constructor at the canonical owner layer:
if nonemptiness, differentiability, and boundary Fréchet-derivative blow-up are provided on
`riDom(f)`, then one recovers `IsEssentiallySmoothOn (riDom(f)) f.realBranch`. -/
theorem of_boundaryFDerivWithinNorm_tendstoTop
    {f : E → WithBotTop ℝ} (hri : (riDom(f)).Nonempty)
    (hdiff : DifferentiableOn ℝ f.realBranch (riDom(f)))
    (hboundary : ∀ {x : E}, x ∈ frontier (riDom(f)) →
      Tendsto
        (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
        (nhdsWithin x (riDom(f))) atTop) :
    IsEssentiallySmoothOn (riDom(f)) f.realBranch := by
  refine
    { nonempty := hri
      differentiableOn := hdiff
      boundaryFDerivWithinNorm_tendstoTop := ?_ }
  intro x hx
  exact hboundary hx

end IsEssentiallySmoothOn

namespace IsEssentiallySmooth

/-- Source-facing ray consequence from `hf : f.IsEssentiallySmooth`, routed through the canonical
owner set `riDom(f)`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot
    {f : E → WithBotTop ℝ}
    (hf : f.IsEssentiallySmooth)
    (hboundary_to_ray :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      Tendsto
        (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot)
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_ray ha hx (hf.toIsEssentiallySmoothOn.boundaryFDerivWithinNorm_tendstoTop hx)

end IsEssentiallySmooth

/-- Bridge constructor from the intrinsic `riDom(f)` owner layer:
if `f.realBranch` is essentially smooth on `riDom(f)` and `interior (dom(f))` is nonempty, then
the canonical source-facing constructor applies. -/
theorem isEssentiallySmooth_of_isEssentiallySmoothOn_riDom
    {f : E → WithBotTop ℝ} (hconv : f.IsConvex ℝ) (hproper : f.IsProper)
    (hessOn : IsEssentiallySmoothOn (riDom(f)) f.realBranch)
    (hinterior : (interior (dom(f))).Nonempty) :
    f.IsEssentiallySmooth := by
  exact (Function.isEssentiallySmooth_iff f).2 ⟨hessOn, hinterior, hconv, hproper⟩

/-- Companion bridge theorem between Chapter 23 directional-derivative and one-dimensional
`lineDeriv` ray clauses:
if boundary Fréchet-derivative blow-up implies this equivalence on the `riDom(f)` owner layer, then
the equivalence follows for points `a ∈ riDom(f)` and `x ∈ frontier (riDom(f))` from
`IsEssentiallySmoothOn (riDom(f)) f.realBranch`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot_iff_lineDeriv_ray_tendsto_atBot
    {f : E → WithBotTop ℝ}
    (hf : IsEssentiallySmoothOn (riDom(f)) f.realBranch)
    (hboundary_to_iff :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      (
        Tendsto
          (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot ↔
        Tendsto
          (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot
      ))
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot ↔
      Tendsto
        (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_iff ha hx (hf.boundaryFDerivWithinNorm_tendstoTop hx)

namespace IsEssentiallySmooth

/-- Source-facing companion bridge on the canonical owner set `riDom(f)`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot_iff_lineDeriv_ray_tendsto_atBot
    {f : E → WithBotTop ℝ} (hf : f.IsEssentiallySmooth)
    (hboundary_to_iff :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      (
        Tendsto
          (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot ↔
        Tendsto
          (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot
      ))
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot ↔
      Tendsto
        (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_iff ha hx (hf.toIsEssentiallySmoothOn.boundaryFDerivWithinNorm_tendstoTop hx)

end IsEssentiallySmooth

end Function

end
