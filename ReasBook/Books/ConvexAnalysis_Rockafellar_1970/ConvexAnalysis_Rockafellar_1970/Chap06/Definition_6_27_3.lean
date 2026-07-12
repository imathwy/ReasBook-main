import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {β : Type v} [Preorder β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.3 introduces the minimum set of an extended-order-valued
  function as the sublevel set at its infimum.
- `core/canonical`: the project already uses mathlib's extrema owner `IsMinOn` for global
  minimizers, while Definition 6.27.2 supplies the canonical infimum owner `⨅ x, f x`.
- `bridge/view`: the source minimum set is implemented as the set of global minimizers and then
  rewritten back to the textbook sublevel-set formula `f ⁻¹' Set.Iic (⨅ x, f x)`.

Domain-style sampling used here:
- `IsMinOn` and `isMinOn_univ_iff` from mathlib's extrema owner layer;
- the Chapter 6 infimum owner `⨅ x, f x` from `Definition_6_27_2`;
- the project sublevel-set pattern `f ⁻¹' Set.Iic a`, used for source-facing sublevel-set owners.

Primitive data vs derived API:
- primitive datum: only the function `f : X → β`;
- primitive owner: the set of points `x` with `IsMinOn f Set.univ x`;
- derived API: the source sublevel-set description at `⨅ x, f x` and the pointwise membership
  inequality `f x ≤ ⨅ y, f y`.
-/

/-- Definition 6.27.3: the minimum set of `f` is the set of global minimizers of `f`. -/
def minimumSet (f : X → β) : Set X :=
  {x | IsMinOn f Set.univ x}

end

scoped[Rockafellar] notation "argmin(" f ")" => minimumSet f

open scoped Rockafellar

section

variable {X : Type u} {β : Type v} [Preorder β]

/-- Textbook notation for Definition 6.27.3: `argmin(f)` is the minimum set of `f`. -/
@[simp] theorem argmin_eq_minimumSet (f : X → β) :
    argmin(f) = minimumSet f :=
  rfl

/-- Primitive membership criterion: `x` belongs to `argmin(f)` iff `f x` is below every value
of `f`. This keeps the theorem surface at the preorder layer. -/
@[simp] theorem mem_minimumSet_iff {f : X → β} {x : X} :
    x ∈ argmin(f) ↔ ∀ y, f x ≤ f y := by
  simpa [minimumSet] using (isMinOn_univ_iff (f := f) (a := x))

end

section

variable {X : Type u} {β : Type v} [CompleteSemilatticeInf β]

/-- The minimum set is exactly the sublevel-set owner of `f` at its infimum. -/
theorem minimumSet_def (f : X → β) :
    argmin(f) = f ⁻¹' Set.Iic (⨅ x, f x) := by
  ext x
  change IsMinOn f Set.univ x ↔ f x ≤ sInf (Set.range f)
  rw [isMinOn_univ_iff]
  constructor
  · intro hx
    exact le_sInf fun _ hy ↦ by
      rcases hy with ⟨y, rfl⟩
      exact hx y
  · intro hx y
    exact hx.trans (sInf_le ⟨y, rfl⟩)

/-- Derived infimum bridge: membership in `argmin(f)` can be rewritten as comparison
with `⨅ y, f y`. -/
theorem mem_minimumSet_iff_le_iInf {f : X → β} {x : X} :
    x ∈ argmin(f) ↔ f x ≤ ⨅ y, f y := by
  rw [minimumSet_def]
  rfl

end

section

variable {E : Type u} {β : Type v} [Preorder β] [Top β]

namespace IsMinOn

/-- Primitive bridge: if `x` is a global minimizer of `f` and `f` has a finite point, then `x`
is finite as well. -/
theorem mem_dom_of_nonempty_dom {f : E → β} {x : E}
    (hx : IsMinOn f Set.univ x) (hf : dom(f).Nonempty) :
    x ∈ dom(f) := by
  rcases hf with ⟨y, hy⟩
  rw [mem_effectiveDomain]
  exact lt_of_le_of_lt (isMinOn_univ_iff.mp hx y) (mem_effectiveDomain.mp hy)

end IsMinOn

/-- Canonical owner bridge: if `f` has a finite point, every point in `argmin(f)` is finite.
-/
theorem mem_dom_of_mem_minimumSet_of_nonempty_dom {f : E → β} {x : E}
    (hx : x ∈ argmin(f)) (hf : dom(f).Nonempty) :
    x ∈ dom(f) := by
  exact (show IsMinOn f Set.univ x from by simpa [minimumSet] using hx).mem_dom_of_nonempty_dom hf

/-- If `f` has some point strictly below `⊤`, then every point of its minimum set is below `⊤`. -/
theorem minimumSet_subset_dom_of_nonempty_dom {f : E → β} (hf : dom(f).Nonempty) :
    argmin(f) ⊆ dom(f) := by
  intro x hx
  exact mem_dom_of_mem_minimumSet_of_nonempty_dom hx hf

end
