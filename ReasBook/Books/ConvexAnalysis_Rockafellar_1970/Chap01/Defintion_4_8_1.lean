import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 4.8.1 introduces the `0/+∞` indicator attached to a set `C`.
- `core/canonical`: this indicator is the intrinsic two-branch owner
  `C.piecewise (0 : E → WithTopBot α) ⊤`, keeping the owner on the primitive `WithTopBot α`
  codomain layer instead of over-specializing to `EReal`.
- `bridge/view`: the source notations `δ[α](x | C)` and `δ(x | C)` are thin views of this
  canonical owner; the equivalent `Set.indicator`-on-complement formula and
  `effectiveDomain` recovery are derived bridges.
- `primitive data`: only the set `C : Set E`.
- `derived API`: the equivalent `Set.piecewise` owner view, the pointwise `if`-formula, the
  branch evaluation lemmas on and off `C`, the finiteness and zero-value membership
  characterizations, and the recovery of `C` as the effective domain.

Domain-style sampling used here:
- `Set.piecewise` as the generic two-branch owner for total functions;
- `Set.indicator` as the equivalent complement-owner bridge;
- `effectiveDomain` and `mem_effectiveDomain` from `Definition_4_4`;
- `WithTopBot α` as the primitive extended-order codomain layer.
-/

section

variable {E : Type u}
variable {α : Type v} [Zero α]

/-- Defintion 4.8.1: the canonical `0/+∞` indicator attached to a set. -/
def indicator (β : Type v) [Zero β] (C : Set E) : E → WithTopBot β :=
  C.piecewise (0 : E → WithTopBot β) ⊤

/-- Helper for Defintion 4.8.1: a long-name bridge alias for downstream files still using
`indicatorFunction`. -/
abbrev indicatorFunction (C : Set E) : E → WithTopBot α :=
  indicator α C

/-- Rockafellar's source notation for the indicator of a set, with codomain inferred from
context. -/
scoped[Rockafellar] notation:70 "δ(" x " | " C ")" =>
  indicator _ C x

/-- Rockafellar's source notation for the indicator of a set. -/
scoped[Rockafellar] notation:70 "δ[" β "](" x " | " C ")" =>
  indicator β C x

open scoped Rockafellar

/-- Helper for Defintion 4.8.1: Rockafellar's indicator notation is exactly `Set.indicator` on
the complement with constant value `⊤`. -/
@[simp] theorem indicator_eq_setIndicator_compl_top (C : Set E) :
    indicator α C = Set.indicator (Cᶜ) (fun _ ↦ (⊤ : WithTopBot α)) := by
  funext x
  by_cases hx : x ∈ C <;> simp [indicator, hx]

/-- Helper for Defintion 4.8.1: bridge to the two-branch `Set.piecewise` owner view. -/
@[simp] theorem indicator_eq_piecewise (C : Set E) :
    indicator α C = C.piecewise (0 : E → WithTopBot α) ⊤ := by
  rfl

/-- Helper for Defintion 4.8.1: unfolding the indicator of `C` at `x` gives `0` on `C` and
`+∞` outside. -/
@[simp] theorem indicator_def (C : Set E) (x : E) :
    δ[α](x | C) = if x ∈ C then 0 else ⊤ := by
  by_cases hx : x ∈ C <;> simp [hx]

/-- Helper for Defintion 4.8.1: the indicator of `C` vanishes on `C`. -/
@[simp] theorem indicator_of_mem (C : Set E) {x : E} (hx : x ∈ C) :
    δ[α](x | C) = 0 := by
  simp [hx]

/-- Helper for Defintion 4.8.1: the indicator of `C` is `+∞` outside `C`. -/
@[simp] theorem indicator_of_notMem (C : Set E) {x : E} (hx : x ∉ C) :
    δ[α](x | C) = ⊤ := by
  simp [hx]

-- Proof sketch: unfold `δ[α](x | C)` and split on whether `x ∈ C`; the outside branch is
-- `⊤`, so equality with `0` can occur only in the inside branch.
/-- Helper for Defintion 4.8.1: the indicator function takes the value `0` exactly on the
underlying set. -/
@[simp] theorem indicator_eq_zero_iff_mem {C : Set E} {x : E} :
    δ[α](x | C) = 0 ↔ x ∈ C := by
  by_cases hx : x ∈ C
  · simp [hx]
  · simp [hx]

variable [Preorder α]

-- Proof sketch: membership in `dom(δ[α](· | C))` is the same as the finiteness test
-- `δ[α](x | C) < ⊤`, and a direct branch split shows that this occurs exactly on `C`.
/-- Helper for Defintion 4.8.1: the effective domain of the indicator function is exactly the
original set. -/
@[simp] theorem effectiveDomain_indicator (C : Set E) :
    {x | indicator α C x < ⊤} = C := by
  ext x
  by_cases hx : x ∈ C
  · simp [hx]
  · simp [hx]

/-- Helper for Defintion 4.8.1: a long-name bridge alias for files still using
`effectiveDomain_indicatorFunction`. -/
@[simp] theorem effectiveDomain_indicatorFunction (C : Set E) :
    {x | indicatorFunction (α := α) C x < ⊤} = C := by
  simpa [indicatorFunction] using (effectiveDomain_indicator (α := α) C)

-- Proof sketch: this is the pointwise membership statement of
-- `effectiveDomain_indicator`.
/-- Helper for Defintion 4.8.1: the indicator is finite exactly on the underlying set. -/
@[simp] theorem indicator_lt_top_iff_mem {C : Set E} {x : E} :
    δ[α](x | C) < ⊤ ↔ x ∈ C := by
  by_cases hx : x ∈ C
  · simp [hx]
  · simp [hx]

end
