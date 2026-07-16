import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1

noncomputable section

universe u v w

/-- Source notation for the indicator bifunction attached to a set-valued map, with codomain
inferred from context. -/
scoped[Rockafellar] notation:70 "δᵇ(" S ")" =>
  (fun u ↦ Set.indicator (S u)ᶜ (fun _ ↦ (⊤ : WithTopBot _)))

/-- Source notation for the indicator bifunction attached to a set-valued map. -/
scoped[Rockafellar] notation:70 "δᵇ[" β "](" S ")" =>
  (fun u ↦ Set.indicator (S u)ᶜ (fun _ ↦ (⊤ : WithTopBot β)))

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [Zero α]
variable (S : U → Set X)

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.3 introduces the `(+∞)` indicator bifunction attached to the
  family of feasible slices `u ↦ S u`.
- `core/canonical`: the Chapter 1 set indicator `δ[α](x | C)` already owns the primitive
  `0/+∞` branch data on each slice, so no second bifunction owner is needed here.
- `bridge/view`: after fixing `u`, all slice formulas and `0`/`⊤` branch lemmas are immediate
  instances of the Chapter 1 indicator API.

Primary mathematical domain:
- slice-wise indicator functions of set-valued maps.

Domain-style sampling used here:
- `indicator`;
- `indicator_def`;
- `indicator_of_mem`;
- `indicator_of_notMem`.

Primitive data vs derived API:
- primitive data: only the family of sets `S : U → Set X`;
- derived API: evaluation at `(u, x)` and the branch lemmas, all inherited from the Chapter 1
  indicator after specializing to the slice `S u`.

Layer target: `source-facing`, by direct reuse of the Chapter 1 owner rather than a parallel local
wrapper.
-/

@[simp] theorem indicatorBifunction_apply (u : U) (x : X) :
    (δᵇ[α](S)) u x = δ[α](x | S u) := by
  by_cases hx : x ∈ S u <;> simp [indicator_def, hx]

@[simp] theorem indicatorBifunction_of_mem (u : U) {x : X} (hx : x ∈ S u) :
    (δᵇ[α](S)) u x = 0 := by
  simp [hx]

@[simp] theorem indicatorBifunction_of_notMem (u : U) {x : X} (hx : x ∉ S u) :
    (δᵇ[α](S)) u x = ⊤ := by
  simp [hx]

/- Definition 6.29.3: the indicator bifunction of a set-valued map `S` is the slice-wise Chapter 1
indicator. The canonical owner remains the set-indicator notation on each slice; this file uses
the direct source notation `δᵇ[α](S)` for that curried view. -/
#check (δᵇ(S) : U → X → WithTopBot α)
#check (δᵇ[α](S) : U → X → WithTopBot α)

end

end Bifunction
