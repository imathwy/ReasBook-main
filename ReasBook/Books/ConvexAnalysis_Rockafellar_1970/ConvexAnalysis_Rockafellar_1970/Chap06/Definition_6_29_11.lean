import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {α : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.11 introduces the bifunction attached to a constrained problem
  with objective `f₀` and feasible slices `u ↦ S u`, written in the source as
  `F u = f₀ + δ(· | S u)`.
- `core/canonical`: for each fixed `u`, the chapter already owns the canonical extension
  `Function.toWithBotTopOn f₀ (S u)` of the finite objective `f₀` by `+∞` outside the slice
  `S u`.
- `bridge/view`: the source formula `f₀.toWithBotTop + δ(· | S u)` is exactly the companion
  bridge `Function.toWithBotTopOn_eq_add_indicator` applied slice-wise.

Domain-style sampling used here:
- `Function.toWithBotTopOn`;
- `Function.toWithBotTopOn_eq_add_indicator`;
- `indicator` and the notation `δ(· | C)`.

Primitive data vs derived API:
- primitive data: an `α`-valued objective `f₀ : X → α` and feasible slices `S : U → Set X`;
- main owner: the associated bifunction as the direct canonical expression
  `fun u ↦ Function.toWithBotTopOn f₀ (S u)`;
- derived API: the slice formula `Function.toWithBotTopOn f₀ (S u) =
    f₀.toWithBotTop + δ(· | S u)`.

Layer target: `source-facing`, expressed by direct canonical recall/use of
`Function.toWithBotTopOn` rather than by a second Chapter 6 wrapper owner.
-/

variable (f₀ : X → α) (S : U → Set X)

/-- Definition 6.29.11, primitive slice rule: on the feasible slice `S u`, the associated
bifunction agrees with the finite objective branch `f₀`. -/
@[simp] theorem toWithBotTopOn_slice_of_mem
    (u : U) {x : X} (hx : x ∈ S u) :
    Function.toWithBotTopOn f₀ (S u) x = f₀ x := by
  simpa using Function.toWithBotTopOn_of_mem f₀ (S u) hx

/-- Definition 6.29.11, primitive slice rule: outside the feasible slice `S u`, the associated
bifunction takes value `+∞`. -/
@[simp] theorem toWithBotTopOn_slice_of_notMem
    (u : U) {x : X} (hx : x ∉ S u) :
    Function.toWithBotTopOn f₀ (S u) x = (⊤ : WithBotTop α) := by
  simpa using Function.toWithBotTopOn_of_notMem f₀ (S u) hx

section

variable [AddZeroClass α]

/-- Slice-wise bridge/view for Definition 6.29.11: evaluating the associated bifunction at a fixed
parameter `u` is the canonical source formula `f₀.toWithBotTop + δ(· | S u)`. -/
theorem toWithBotTopOn_slice_eq_add_indicator (u : U) :
    Function.toWithBotTopOn f₀ (S u) = f₀.toWithBotTop + (δ(· | S u)) := by
  simpa using Function.toWithBotTopOn_eq_add_indicator f₀ (S u)

/-- Definition 6.29.11 in bifunction owner form: the associated bifunction is the sum of the
constant finite branch `u ↦ f₀.toWithBotTop` and the indicator bifunction `δᵇ(S)`. -/
theorem toWithBotTopOn_eq_const_add_indicatorBifunction :
    (fun u ↦ Function.toWithBotTopOn f₀ (S u)) =
      (fun _ : U ↦ f₀.toWithBotTop) + δᵇ(S) := by
  funext u
  simpa [Pi.add_apply] using
    (toWithBotTopOn_slice_eq_add_indicator (f₀ := f₀) (S := S) u)

end

end

end Bifunction
