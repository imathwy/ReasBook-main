import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.ERealSMul
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped RealInnerProductSpace Rockafellar

section

variable {𝕜 : Type*} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid α] [SMul 𝕜 α] [Preorder α]

/-!
Core owner triage for the closed/proper/convex predicate used throughout Chapter 12.

- `core/canonical`: the owner abstraction is the class `f.IsClosedProperConvex`, bundling the
  chapter predicates `f.IsConvex` and `f.IsProper` with mathlib's `LowerSemicontinuous`, on a
  topological `𝕜`-module and the canonical extended codomain layer `WithTopBot α`.
- primitive data: the function `f : E → WithTopBot α`;
- derived API: the projection lemmas extracting convexity, properness, and lower semicontinuity.

Domain-style sampling used here:
- the chapter owner `Function.IsConvex` from `Chap01/Theorem_4_2`, which already lives on the
  additive-module layer;
- the chapter owner `Function.IsProper` from `Chap01/Definition_4_6`, which adds no ambient
  structure;
- mathlib's `LowerSemicontinuous` from `Topology/Semicontinuity/Defs`, which only needs a
  topological domain.

Layer target: `core/canonical`; this owner is chapter-wide and is not part of the later
orthant-specific `R^n` bridge layer.
-/

namespace Function

variable (𝕜)
/-- A `WithTopBot α`-valued function on a topological `𝕜`-module is closed proper convex when it is
convex, proper, and lower semicontinuous. -/
class IsClosedProperConvex [TopologicalSpace (WithTopBot α)] (f : E → WithTopBot α) : Prop where
  convex : f.IsConvex 𝕜
  proper : f.IsProper
  closed : LowerSemicontinuous f

variable [TopologicalSpace (WithTopBot α)]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- The closed-proper-convex owner expands to convexity, properness, and lower semicontinuity. -/
theorem isClosedProperConvex_iff (f : E → WithTopBot α) :
    IsClosedProperConvex[𝕜] f ↔
      f.IsConvex 𝕜 ∧ f.IsProper ∧ LowerSemicontinuous f := by
  constructor
  · intro hf
    exact ⟨hf.convex, hf.proper, hf.closed⟩
  · rintro ⟨hconvex, hproper, hlowerSemicontinuous⟩
    exact ⟨hconvex, hproper, hlowerSemicontinuous⟩

namespace IsClosedProperConvex

/-- Lower semicontinuity extracted from the closed-proper-convex owner. -/
theorem lowerSemicontinuous {f : E → WithTopBot α}
    (hf : IsClosedProperConvex[𝕜] f) :
    LowerSemicontinuous f :=
  hf.closed

end IsClosedProperConvex

end Function

end

section

variable {𝕜 : Type*} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [Preorder α]
variable [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- The indicator of a nonempty closed convex set is a closed proper convex function. -/
theorem indicatorFunction_isClosedProperConvex_of_nonempty
    {C : Set E} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    IsClosedProperConvex[𝕜] (δ[α](· | C)) := by
  rw [Function.isClosedProperConvex_iff (𝕜 := 𝕜)]
  refine ⟨(indicator_isConvex_iff (𝕜 := 𝕜) (α := α) C).2 hC_convex, ?_, ?_⟩
  · rw [Function.isProper_iff]
    refine ⟨?_, ?_⟩
    · rcases hC_nonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [hx] using (show (0 : WithTopBot α) < ⊤ by simp)
    · intro x
      by_cases hx : x ∈ C <;> simp [hx]
  · have hC_open_compl : IsOpen Cᶜ := hC_closed.isOpen_compl
    simpa [indicator_eq_setIndicator_compl_top] using
      hC_open_compl.lowerSemicontinuous_indicator
        (show (0 : WithTopBot α) ≤ ⊤ by simp)

end

section

variable {ι : Type u} {𝕜 : Type*}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "E" => ι → 𝕜
local notation "Quadrant" => orthant[𝕜](E)

/-- The distinguished origin point in the nonnegative orthant subtype. -/
def orthantOrigin : Quadrant :=
  ⟨0, by
    change (0 : E) ≤ 0
    exact le_rfl⟩

@[simp] theorem orthantOrigin_fst : (orthantOrigin : Quadrant).1 = 0 := rfl

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item studies functions on `ℝ^n` of the form `f(x) = g(|x|)`, where `|x|`
  means coordinatewise absolute value and `g` is defined on the nonnegative orthant.
- `core/canonical`: the owner abstractions already present in the project are
  `Quadrant`, surfaced as `orthant[𝕜](E)`,
  `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`, `ConvexOn`, and
  `convexConjugate`.
- `bridge/view`: the source orthant profile is best treated as a function
  `Quadrant → WithTopBot α`; clause (2) uses the same codomain layer for conjugation.
  The upstream bridge `Function.extendByTop` from Definition 12.4
  extends an orthant function by `⊤` off the orthant, while `orthantAbsExtension` composes it
  with `coordinatewiseAbsQuadrant`.

Primitive data vs derived API:
- primitive source-facing data: `coordinatewiseAbsQuadrant`, `orthantAbsExtension`, and the
  orthant-native owner `IsMonotoneClosedConvexOnQuadrant g`, whose primitive fields are lower
  semicontinuity of `g`, intrinsic convexity of `g` on the orthant subtype, finiteness of `g` at
  `0`, and the genuinely extra orthant-order monotonicity condition;
- derived bridge API: the orthant evaluation lemmas for `Function.extendByTop`, the
  bridge from intrinsic orthant convexity of `g` to convexity of `Function.extendByTop g` on the
  orthant set,
  ambient closed/proper/convex bridge
  `IsMonotoneClosedConvexOnQuadrant.extendByTop_isClosedProperConvex`, the source-facing
  closed-proper-convex equivalence, and the conjugate formula through the inherited orthant-side
  Fenchel owner `convexConjugate g`.

Layer target: this item stays `source-facing`. The main declarations remain the equivalence for
`f(x) = g(|x|)` and the conjugate formula, while reusing the canonical project owners for convexity,
closedness, properness, the orthant order, and Fenchel conjugation.
-/

/-- The point `|x|`, regarded as a point of the canonical nonnegative orthant subtype. -/
def coordinatewiseAbsQuadrant (x : E) : Quadrant :=
  ⟨fun i ↦ |x i|, fun i ↦ abs_nonneg (x i)⟩

/-- The canonical orthant absolute-value map is coordinatewise absolute value. -/
@[simp] theorem coordinatewiseAbsQuadrant_apply (x : E) (i : ι) :
    (coordinatewiseAbsQuadrant x).1 i = |x i| :=
  rfl

@[simp] theorem coordinatewiseAbsQuadrant_zero :
    coordinatewiseAbsQuadrant (0 : E) = orthantOrigin := by
  ext i
  simp [coordinatewiseAbsQuadrant]

/-- The extension of a function on the nonnegative orthant to all of `R^n` by composition with the
coordinatewise absolute value map. -/
def orthantAbsExtension {β : Type*} (g : Quadrant → β) : E → β :=
  g ∘ coordinatewiseAbsQuadrant

section ClosedProperConvex

variable {α : Type v}
variable [TopologicalSpace (ι → 𝕜)]
variable [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul 𝕜 α]
variable [PartialOrder α]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
namespace Function

/-- A function on the nonnegative orthant has the Chapter 12 orthant profile when its canonical
ambient `⊤`-extension is used only as derived bridge API. Primitive owner data are lower
semicontinuity and intrinsic convexity of the orthant function itself, origin finiteness, and
orthant-order monotonicity. -/
class IsMonotoneClosedConvexOnQuadrant (g : Quadrant → WithTopBot α) : Prop where
  lowerSemicontinuous : LowerSemicontinuous g
  convex : g.IsConvex 𝕜
  finite_origin : ⊥ < g orthantOrigin ∧ g orthantOrigin < ⊤
  monotone : Monotone g

namespace IsMonotoneClosedConvexOnQuadrant

variable [SMul 𝕜 (WithTopBot α)]
variable [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α]

/-- Bridge API: intrinsic convexity of an orthant function yields convexity of its canonical
ambient `⊤`-extension on the orthant set. -/
theorem convexOn_extendByTop {g : Quadrant → WithTopBot α}
    (hg : g.IsMonotoneClosedConvexOnQuadrant) :
    ConvexOn 𝕜 Quadrant (Function.extendByTop g) := by
  sorry

/-- The orthant owner canonically upgrades to the ambient closed-proper-convex owner on the
`⊤`-extension `Function.extendByTop g`. -/
theorem extendByTop_isClosedProperConvex {g : Quadrant → WithTopBot α}
    (hg : g.IsMonotoneClosedConvexOnQuadrant) :
    IsClosedProperConvex[𝕜] (Function.extendByTop g) := by
  sorry

end IsMonotoneClosedConvexOnQuadrant

end Function

variable [SMul 𝕜 (WithTopBot α)]
variable [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α]

-- Proof sketch: for the forward implication, restrict `f(x) = g(|x|)` to the nonnegative
-- orthant to recover `g`, then use symmetry under sign changes and convexity to obtain orthant
-- monotonicity and finiteness at `0`. For the reverse implication, compose `g` with the
-- coordinatewise absolute value map, using convexity and lower semicontinuity of `g` on the
-- orthant together with orthant monotonicity to transfer those properties to all of `R^n`, and use
-- finiteness at `0` to obtain properness.
/-- Text 12.3.6 (1): for `f(x) = g(|x|)`, the function `f` is closed proper convex on `R^n` if and
only if `g` is lower semicontinuous and convex on the nonnegative orthant, is finite at `0`, and
is nondecreasing for the orthant order there. -/
theorem orthantAbsExtension_isClosedProperConvex_iff
    (g : Quadrant → WithTopBot α) :
    IsClosedProperConvex[𝕜] (orthantAbsExtension g) ↔
      g.IsMonotoneClosedConvexOnQuadrant := sorry

end ClosedProperConvex

-- Proof sketch: write the Fenchel conjugate of `orthantAbsExtension g` as the supremum of
-- `⟪x⋆, x⟫ - g(|x|)` over all `x`. For fixed `x⋆`, choose the sign of each coordinate of `x` to
-- match the sign of `x⋆`, so the pairing becomes `⟪|x⋆|, |x|⟫`; then rename `|x|` as a vector in
-- the nonnegative orthant. The resulting supremum is exactly the orthant Fenchel conjugate
-- `convexConjugate g` of the restricted orthant function, evaluated at `|x⋆|` as an orthant
-- point; no extra closedness,
-- convexity, or monotonicity hypothesis on `g` enters this algebraic identity.
/-- Text 12.3.6 (2): the conjugate of `x ↦ g(|x|)` is the orthant Fenchel conjugate
`convexConjugate g`
restricted to the nonnegative orthant, evaluated at the coordinatewise absolute value of the dual
variable. In particular, this identity applies under the orthant-side hypotheses of clause (1). -/
theorem convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant
    {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
    [HasPairing E E (WithTopBot α)]
    [HasPairing Quadrant Quadrant (WithTopBot α)]
    (g : Quadrant → WithTopBot α) :
    (orthantAbsExtension g)⋆ = (g⋆) ∘ coordinatewiseAbsQuadrant := sorry

end
