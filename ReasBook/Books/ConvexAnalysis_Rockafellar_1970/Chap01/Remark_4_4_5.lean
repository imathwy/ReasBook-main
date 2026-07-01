import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Rockafellar
open scoped Pointwise
open Function

universe u v w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 4.4.5 identifies a convex function on a set `C` with the globally
  defined `WithTopBot α`-valued function obtained by adjoining `+∞` outside `C`.
- `core/canonical`: the owner abstractions are the chapter predicate `Function.IsConvex` for the
  ambient `WithTopBot α`-valued function, mathlib's `ConvexOn` for the finite branch on `C`, and
  `Set.piecewise` as the intrinsic two-branch extension owner.
- `bridge/view`: the source-facing bridge is `f.toWithTopBot + δ(· | C)`, and the chapter helper
  owner `Function.toWithTopBotOn f C` is a thin alias to the canonical
  `C.piecewise f.toWithTopBot ⊤` surface.

Domain-style sampling used here:
- `Function.IsConvex` and `Function.isConvex_iff_convex_epigraph` from `Theorem_4_2`;
- `Function.toWithTopBot` from `Chap01.EOrder.Basic`;
- `indicator` and the notation `δ(· | C)` from `Defintion_4_8_1`;
- `Set.piecewise` as the canonical owner for total two-branch functions;
- mathlib's `ConvexOn` and `convexOn_iff_convex_epigraph`.

Primitive data vs derived API:
- primitive data: a set `C : Set E` and an `α`-valued function `f : E → α`;
- derived API: the source-facing bridge `f.toWithTopBot + δ(· | C)`, the helper owner
  `Function.toWithTopBotOn f C`, and the equivalence between global-owner convexity and convexity
  of `f` on `C`.

Layer target: `core/canonical` with `source-facing` bridge; the primary theorem below uses the
canonical `Set.piecewise` owner, while `Function.toWithTopBotOn` and the source formula
`f.toWithTopBot + δ(· | C)` are kept as thin bridges.
-/

section

variable {E : Type u}
variable {α : Type v}

namespace Function

/-- Helper for Remark 4.4.5: the canonical codomain lift views a finite-valued map as
`WithTopBot`-valued. -/
abbrev toWithTopBot (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

/-- Canonical owner for extension by `+∞` outside `C`. -/
def toWithTopBotOn (f : E → α) (C : Set E) : E → WithTopBot α :=
  C.piecewise f.toWithTopBot ⊤

/-- Backward-compatible alias for `Function.toWithTopBotOn`. -/
abbrev toWithBotTopOn (f : E → α) (C : Set E) : E → WithTopBot α :=
  f.toWithTopBotOn C

@[simp] theorem toWithTopBotOn_of_mem (f : E → α) (C : Set E) {x : E} (hx : x ∈ C) :
    f.toWithTopBotOn C x = f x := by
  simp [toWithTopBotOn, hx, Function.toWithTopBot]

@[simp] theorem toWithTopBotOn_of_notMem (f : E → α) (C : Set E) {x : E} (hx : x ∉ C) :
    f.toWithTopBotOn C x = (⊤ : WithTopBot α) := by
  simp [toWithTopBotOn, hx]

/-- Backward-compatible `WithBotTop`-spelled bridge for `toWithTopBotOn_of_mem`. -/
@[simp] theorem toWithBotTopOn_of_mem (f : E → α) (C : Set E) {x : E} (hx : x ∈ C) :
    f.toWithBotTopOn C x = f x := by
  simpa using (toWithTopBotOn_of_mem (f := f) (C := C) hx)

/-- Backward-compatible `WithBotTop`-spelled bridge for `toWithTopBotOn_of_notMem`. -/
@[simp] theorem toWithBotTopOn_of_notMem (f : E → α) (C : Set E) {x : E} (hx : x ∉ C) :
    f.toWithBotTopOn C x = (⊤ : WithTopBot α) := by
  simpa using (toWithTopBotOn_of_notMem (f := f) (C := C) hx)

end Function

section

variable [AddZeroClass α]

namespace Function

-- Proof sketch: unfold `δ(x | C)` and `C.piecewise`, then split on `x ∈ C`. On `C`, the
-- indicator contributes `0`, so the sum reduces to the finite branch `f x`; outside `C`, the
-- indicator contributes `⊤`, so the whole function is `⊤`.
/-- Adding the indicator of `C` to an `α`-valued branch `f` gives the canonical two-branch
function that agrees with `f` on `C` and is `+∞` outside `C`. -/
theorem toWithTopBot_add_indicator_eq_piecewise (f : E → α) (C : Set E) :
    f.toWithTopBot + (δ[α](· | C)) = C.piecewise f.toWithTopBot ⊤ := by
  -- Split on membership in `C`; on-set the indicator is `0`, off-set it is `⊤`.
  funext x
  by_cases hx : x ∈ C <;> simp [hx, Function.toWithTopBot]

/-- Backward-compatible `WithBotTop`-spelled bridge for
`toWithTopBot_add_indicator_eq_piecewise`. -/
theorem toWithBotTop_add_indicator_eq_piecewise (f : E → α) (C : Set E) :
    f.toWithTopBot + (δ[α](· | C)) = C.piecewise f.toWithTopBot ⊤ := by
  simpa using (toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C))

end Function

end

section

variable [AddZeroClass α]

/-- The source-facing `f + δ(· | C)` expression is the canonical extension by `+∞` outside
`C`. -/
theorem Function.toWithTopBotOn_eq_add_indicator (f : E → α) (C : Set E) :
    f.toWithTopBotOn C = f.toWithTopBot + (δ[α](· | C)) := by
  simpa [Function.toWithTopBotOn] using
    (Function.toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C)).symm

/-- Backward-compatible `WithBotTop`-spelled bridge for
`Function.toWithTopBotOn_eq_add_indicator`. -/
theorem Function.toWithBotTopOn_eq_add_indicator (f : E → α) (C : Set E) :
    f.toWithBotTopOn C = f.toWithTopBot + (δ[α](· | C)) := by
  simpa using (Function.toWithTopBotOn_eq_add_indicator (f := f) (C := C))

end

section

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type v} [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [SMul 𝕜 α] [PosSMulMono 𝕜 α]

/-- Helper for Remark 4.4.5: the finite-height epigraph of the canonical extension by `+∞`
outside `C` is exactly the ordinary epigraph of `f` restricted to `C`. -/
theorem piecewise_toWithTopBot_epigraph_eq {C : Set E} {f : E → α} :
    {p : E × α | (C.piecewise f.toWithTopBot ⊤) p.1 ≤ (p.2 : WithTopBot α)} =
      {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
  -- Split on whether the base point lies in `C`; off-set the left inequality is impossible.
  ext p
  by_cases hp : p.1 ∈ C <;> simp [hp, Function.toWithTopBot]

/-- Helper for Remark 4.4.5: under the ordered scalar-action hypotheses used here, a convex
finite-height epigraph yields `ConvexOn` for the underlying finite-valued function. -/
theorem convexOn_of_convex_epigraph_of_pos_smul {C : Set E} {f : E → α}
    (h : Convex 𝕜 {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2}) :
    ConvexOn 𝕜 C f := by
  -- Read convexity of the epigraph on the two canonical points `(x, f x)` and `(y, f y)`.
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1
  · intro x hx y hy a b ha hb hab
    exact (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2

/-- Helper for Remark 4.4.5: under the ordered scalar-action hypotheses used here, `ConvexOn`
forces convexity of the finite-height epigraph. -/
theorem ConvexOn.convex_epigraph_of_pos_smul {C : Set E} {f : E → α}
    (hf : ConvexOn 𝕜 C f) :
    Convex 𝕜 {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
  -- Convex combinations in the epigraph stay above the convex combination of the function values.
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by
      gcongr

-- Proof sketch: rewrite both convexity statements to convexity of the same epigraph set via the
-- canonical piecewise owner.
/-- Canonical `Set.piecewise` extension bridge: convexity of the global extension by `+∞` outside
`C` is exactly convexity of the finite branch on `C`. -/
theorem isConvex_piecewise_toWithTopBot_iff {C : Set E} {f : E → α} :
    (C.piecewise f.toWithTopBot ⊤).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  -- Route correction: pass each direction through the common finite-height epigraph set instead
  -- of trying to rewrite both sides of the equivalence at once.
  constructor
  · intro hpiecewise
    -- Convert global-owner convexity of the extension into convexity of its epigraph.
    have hepigraph :
        Convex 𝕜 {p : E × α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
      simpa [piecewise_toWithTopBot_epigraph_eq (C := C) (f := f)] using
        (Function.isConvex_iff_convex_epigraph
          (𝕜 := 𝕜) (f := C.piecewise f.toWithTopBot ⊤)).1 hpiecewise
    -- Repackage that same epigraph set as the standard `ConvexOn` owner on `C`.
    exact convexOn_of_convex_epigraph_of_pos_smul (𝕜 := 𝕜) (C := C) (f := f) hepigraph
  · intro hf
    -- Start from the ordinary epigraph of `f` on `C`.
    have hepigraph :
        Convex 𝕜 {p : E × α | (C.piecewise f.toWithTopBot ⊤) p.1 ≤ (p.2 : WithTopBot α)} := by
      simpa [piecewise_toWithTopBot_epigraph_eq (C := C) (f := f)] using
        (ConvexOn.convex_epigraph_of_pos_smul (𝕜 := 𝕜) (C := C) (f := f) hf)
    -- Package the rewritten epigraph back into the global-owner convexity statement.
    exact (Function.isConvex_iff_convex_epigraph
      (𝕜 := 𝕜) (f := C.piecewise f.toWithTopBot ⊤)).2 hepigraph

/-- Backward-compatible `WithBotTop`-spelled bridge for
`isConvex_piecewise_toWithTopBot_iff`. -/
theorem isConvex_piecewise_toWithBotTop_iff {C : Set E} {f : E → α} :
    (C.piecewise f.toWithTopBot ⊤).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa using (isConvex_piecewise_toWithTopBot_iff (𝕜 := 𝕜) (C := C) (f := f))

/-- Bridge form using the canonical owner `Function.toWithTopBotOn`. -/
theorem isConvex_toWithTopBotOn_iff {C : Set E} {f : E → α} :
    (f.toWithTopBotOn C).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa [Function.toWithTopBotOn] using
    (isConvex_piecewise_toWithTopBot_iff (C := C) (f := f))

/-- Backward-compatible `WithBotTop`-spelled bridge for
`isConvex_toWithTopBotOn_iff`. -/
theorem isConvex_toWithBotTopOn_iff {C : Set E} {f : E → α} :
    (f.toWithBotTopOn C).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa using (isConvex_toWithTopBotOn_iff (𝕜 := 𝕜) (C := C) (f := f))

/-- Remark 4.4.5: viewing an `α`-valued function on `C` as the globally defined
`WithTopBot α`-valued function `f.toWithTopBot + δ(· | C)` preserves convexity exactly. This is
the owner-level identification between convexity on a fixed set and convexity of the canonical
extension by `+∞` outside that set. -/
theorem isConvex_toWithTopBot_add_indicator_iff {C : Set E} {f : E → α} :
    (f.toWithTopBot + (δ[α](· | C))).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  -- Rewrite the source-facing formula to the canonical piecewise owner.
  rw [Function.toWithTopBot_add_indicator_eq_piecewise (f := f) (C := C)]
  exact isConvex_piecewise_toWithTopBot_iff (𝕜 := 𝕜) (C := C) (f := f)

/-- Backward-compatible `WithBotTop`-spelled bridge for
`isConvex_toWithTopBot_add_indicator_iff`. -/
theorem isConvex_toWithBotTop_add_indicator_iff {C : Set E} {f : E → α} :
    (f.toWithTopBot + (δ[α](· | C))).IsConvex 𝕜 ↔ ConvexOn 𝕜 C f := by
  simpa using (isConvex_toWithTopBot_add_indicator_iff (𝕜 := 𝕜) (C := C) (f := f))

end
