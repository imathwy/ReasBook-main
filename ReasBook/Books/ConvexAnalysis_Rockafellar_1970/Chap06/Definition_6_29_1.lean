import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_7_2

noncomputable section

open scoped Rockafellar
open Function

universe u v r

section

variable {U : Type u} {X : Type v} {α : Type r}

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: the opening definitions of §29 work with a bifunction
  `F : U → X → WithTopBot α` and the perturbation function `u ↦ inf_x F u x` attached to the
  associated generalized convex
  program.
- `core/canonical`: the project already owns the effective-domain operator `dom(·)` for
  `WithTopBot`-valued functions in Chapter 1, and for arbitrary ambient types it already owns
  the first-projection image operator `Function.linearImage (Prod.fst : U × X → U)`.
- `bridge/view`: the perturbation function is the pointwise infimum in the second variable, so
  it agrees with the Chapter 1 first-projection image operator;
  the source's consistency condition is then nonemptiness of the effective domain of the
  zero-slice `F 0`, equivalently membership of `0` in `dom(perturbationFunction F)` on the
  complete-lattice bridge layer.

Domain-style sampling used here:
- `Function.partialInfimum` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_7_2`;
- `Function.partialInfimum_apply` from the same file, which is the owner-side slice formula;
- `effectiveDomain` / `dom(·)` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4`;
- `mem_effectiveDomain` from the same file, which is the owner-side test `f x < ⊤`;
- `Function.linearImage_eq_sInf_image` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7`.

Primitive data vs derived API:
- primitive source data: the bifunction `F`;
- source-facing owner: `perturbationFunction F`;
- core owner reused from Chapter 1: `partialInfimum (Function.uncurry F)`;
- derived API: the indexed-infimum evaluation formula, the first-projection linear-image bridge,
  and the complete-lattice consistency bridge to `dom(perturbationFunction F)`.

Layer target: `source-facing`. The perturbation function is a genuine named source object, but it
is implemented as the thin curried specialization of the existing Chapter 1 owner
`Function.partialInfimum` rather than by duplicating the raw `sInf` construction.
-/

section

variable [InfSet α]

/-- The perturbation function attached to a bifunction `F`, defined by taking the pointwise
infimum in the second variable. -/
abbrev perturbationFunction (F : U → X → α) : U → α :=
  partialInfimum (Function.uncurry F)

/-- Rockafellar's source-facing notation for the perturbation function `inf F`. -/
scoped[Rockafellar] notation "infᵇ(" F ")" => Bifunction.perturbationFunction F

/-- Evaluating the perturbation function at `u` gives the infimum of the slice `F u` over the
`X`-variable, written as the infimum of its range in `α`. -/
@[simp] theorem perturbationFunction_apply_eq_sInf_range
    (F : U → X → α) (u : U) :
    infᵇ(F) u = sInf (Set.range (F u)) := by
  simp [perturbationFunction]

/-- Evaluating the perturbation function at `u` is the indexed infimum `inf_x F u x`. -/
@[simp] theorem perturbationFunction_apply (F : U → X → α) (u : U) :
    infᵇ(F) u = ⨅ x, F u x := by
  rw [perturbationFunction_apply_eq_sInf_range, ← sInf_range]

/-- The perturbation function of a bifunction is exactly the image of `Function.uncurry F` under
the intrinsic first-coordinate projection map. -/
theorem perturbationFunction_eq_linearImage_fst (F : U → X → α) :
    infᵇ(F) = (Prod.fst : U × X → U) ◁ Function.uncurry F := by
  funext u
  rw [perturbationFunction_apply_eq_sInf_range, linearImage_eq_sInf_image]
  congr 1
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(u, x), by simp, rfl⟩
  · rintro ⟨⟨u', x⟩, hu', ha⟩
    dsimp at hu'
    subst hu'
    exact ⟨x, by simpa [Function.uncurry] using ha⟩

end

section

variable {β : Type r}
variable [Zero U] [Top β] [LT β]

/-- The generalized convex program attached to `F` is consistent when the unperturbed problem has
at least one feasible decision for the zero-perturbation slice, i.e. some `x` with
`F 0 x < ⊤`. -/
def IsConsistent (F : U → X → β) : Prop :=
  (dom(F 0)).Nonempty

@[simp] theorem isConsistent_iff_exists_lt_top (F : U → X → β) :
    IsConsistent F ↔ ∃ x : X, F 0 x < ⊤ := by
  simp [IsConsistent]

end

section

variable {β : Type r}
variable [Zero U] [CompleteLattice β]

@[simp] theorem isConsistent_iff_lt_top (F : U → X → β) :
    IsConsistent F ↔ infᵇ(F) 0 < ⊤ := by
  rw [isConsistent_iff_exists_lt_top]
  rw [perturbationFunction_apply]
  exact
    (iInf_lt_top : (⨅ x : X, F 0 x) < ⊤ ↔ ∃ x : X, F 0 x < ⊤).symm

@[simp] theorem isConsistent_iff_zero_mem_dom_perturbationFunction
    (F : U → X → β) :
    IsConsistent F ↔ (0 : U) ∈ dom(infᵇ(F)) := by
  rw [isConsistent_iff_lt_top, _root_.mem_effectiveDomain]

end

end Bifunction

end
