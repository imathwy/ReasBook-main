import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open scoped Rockafellar

variable {𝕜 : Type u} {E : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [SMul 𝕜 α]
variable [TopologicalSpace (WithTopBot α)]

namespace Function

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.3.1 introduces the property that a convex function is co-finite.
- `core/canonical`: the relevant owner predicates already present in the project are
  `Function.IsClosedProperConvex` for the closed proper convex part and
  `Function.recessionFunction` for Rockafellar's recession function `f₀⁺`.
- `bridge/view`: the textbook phrase "epi f contains no non-vertical half-lines" is rendered by
  the recession condition `(f₀⁺) y = ⊤` for every nonzero direction `y`.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`;
- `Function.isClosedProperConvex_iff`;
- `Function.IsProper`;
- `Function.recessionFunction`;
- `Function.recessionFunction_apply`.

Primitive data vs derived API:
- primitive source-facing data: the intrinsic recession-domain condition
  `dom(f₀⁺) ⊆ {0}`, equivalent to ruling out non-vertical recession directions;
- derived API: the closed/proper/convex package, already owned upstream by
  `Function.IsClosedProperConvex`, and the pointwise nonzero-direction formula
  `f₀⁺ y = ⊤`.

Layer target: this item stays `source-facing`, but it should be expressed as the Chapter 3 owner
predicate for closed proper convexity together with the additional recession clause, not as an
coordinate-model-specific parallel bundle of the same fields. The ambient owner layer is the same
topological `𝕜`-module layer already used by `Function.IsClosedProperConvex` and
`recessionFunction`; textbook coordinate readings remain downstream specializations.
-/

/-- Text 13.3.1: a `WithTopBot α`-valued function on a topological `𝕜`-module is co-finite
when it is closed proper convex and its recession function satisfies `f₀⁺(y) = +∞` for every
nonzero direction `y`, equivalently when `epi f` contains no non-vertical half-lines. -/
@[mk_iff isCofinite_iff]
class IsCofinite (f : E → WithTopBot α) : Prop extends IsClosedProperConvex[𝕜] f where
  dom_recessionFunction_subset_zero : dom ((f)₀⁺) ⊆ ({0} : Set E)

local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

namespace IsCofinite

/-- Co-finiteness implies the nonzero-direction recession formula `f₀⁺ y = ⊤`. -/
theorem recession_eq_top {f : E → WithTopBot α} (hf : IsCofinite[𝕜] f)
    (y : E) (hy : y ≠ 0) :
    ((f)₀⁺) y = ⊤ := by
  have hy_not_mem : y ∉ dom(((f)₀⁺)) := by
    intro hy_mem
    have hy_zero : y = 0 := by
      simpa using hf.dom_recessionFunction_subset_zero hy_mem
    exact hy hy_zero
  have hy_not_lt : ¬ ((f)₀⁺) y < ⊤ := by
    intro hy_lt
    exact hy_not_mem (mem_effectiveDomain.mpr hy_lt)
  exact le_antisymm le_top (le_of_not_gt hy_not_lt)

end IsCofinite

namespace IsClosedProperConvex

/-- For a closed proper convex function, co-finiteness is exactly the added recession clause
`f₀⁺ y = ⊤` on every nonzero direction. -/
theorem isCofinite_iff_forall_ne_zero_recession_eq_top
    {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsCofinite[𝕜] f ↔ ∀ y : E, y ≠ 0 → ((f)₀⁺) y = ⊤ := by
  constructor
  · intro h y hy
    exact h.recession_eq_top y hy
  · intro h
    exact
      { toIsClosedProperConvex := hf
        dom_recessionFunction_subset_zero := by
          intro y hy_dom
          have hy0 : y = 0 := by
            by_contra hy0
            have hy_top : ((f)₀⁺) y = ⊤ := h y hy0
            have hy_not_mem : y ∉ dom(((f)₀⁺)) := by
              simpa [mem_effectiveDomain, hy_top]
            exact hy_not_mem hy_dom
          simp [hy0] }

/-- Backward-compatible short name for
`isCofinite_iff_forall_ne_zero_recession_eq_top`. -/
theorem isCofinite_iff {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsCofinite[𝕜] f ↔ ∀ y : E, y ≠ 0 → ((f)₀⁺) y = ⊤ :=
  isCofinite_iff_forall_ne_zero_recession_eq_top (𝕜 := 𝕜) (f := f) hf

/-- For a closed proper convex function, co-finiteness is equivalent to saying the effective
domain of the recession function is contained in `{0}`. This is the intrinsic owner-level form of
the nonzero-direction recession clause. -/
theorem isCofinite_iff_dom_recessionFunction_subset_zero
    {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsCofinite[𝕜] f ↔ dom(((f)₀⁺)) ⊆ ({0} : Set E) := by
  constructor
  · intro h
    exact h.dom_recessionFunction_subset_zero
  · intro h
    exact
      { toIsClosedProperConvex := hf
        dom_recessionFunction_subset_zero := h }

end IsClosedProperConvex

/-- Co-finiteness unfolds to closed proper convexity plus the nonzero-direction recession
formula. -/
theorem isCofinite_iff_isClosedProperConvex_and_forall_ne_zero_recession_eq_top
    {f : E → WithTopBot α} :
    IsCofinite[𝕜] f ↔
      IsClosedProperConvex[𝕜] f ∧ ∀ y : E, y ≠ 0 → ((f)₀⁺) y = ⊤ := by
  constructor
  · intro hf
    exact ⟨hf.toIsClosedProperConvex, fun y hy => hf.recession_eq_top y hy⟩
  · rintro ⟨hf_closed, hrec⟩
    exact
      (IsClosedProperConvex.isCofinite_iff_forall_ne_zero_recession_eq_top
        (𝕜 := 𝕜) (f := f) hf_closed).2 hrec

end Function

end
