import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {E : Type u}
variable {α : Type v}

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.5.1 says that for a proper convex function `f`, the recession
  function `f0⁺` is the least function `h` satisfying the translation inequality
  `f (x + y) ≤ f x + h y`.
- `core/canonical`: the owner is `Function.recessionFunction` on a `WithTopBot α`-valued function
  `f : E → WithTopBot α`, and the least-element conclusion is naturally expressed by `IsLeast` in
  the pointwise ordered function lattice `E → WithTopBot α`. The primitive leastness layer is the
  difference-bound surface `f (x + y) - f x ≤ h y` over base points `x ∈ dom(f)`; the
  translation-inequality form is a derived bridge requiring properness.
- `bridge/view`: the previous theorem's formula for `f0⁺` is rendered concretely as the supremum of
  the finite differences `f (x + y) - f x` over base points in `dom(f)`.

Domain-style sampling used here:
- the chapter owner `Function.IsProper` and its pointwise bridge
  `Function.isProper_iff` from `Definition_4_6`;
- the chapter effective-domain owner `dom(·)` with membership theorem `mem_effectiveDomain`;
- the complete-lattice least-element interface `IsLeast` on function spaces;
- the supremum construction `sSup` on `WithTopBot α`.

Primitive data vs derived API:
- primitive input: the function `f`;
- source-facing object introduced here: `recessionFunction f`;
- derived API: the translation-inequality least-element statement for `recessionFunction f` in
  the pointwise ordered function space, most canonically parameterized by the translation
  increment `y` in `f (x + y) ≤ f x + h y`; on additive groups, the textbook
  `f z ≤ f x + h (z - x)` form is the corresponding reindexing `y = z - x`.

Editorial note: the source text is truncated after the opening of a second sentence beginning
"Let `g` be the positively ...". Only the visible least-element clause is formalized here.
-/

/-- The recession function `f0⁺` is the supremum of the differences `f (x + y) - f x` over
points `x` in `dom(f)`. -/
noncomputable def recessionFunction [Add E] [AddGroup α]
    [ConditionallyCompleteLattice α] (f : E → WithTopBot α) (y : E) : WithTopBot α :=
  sSup {r : WithTopBot α | ∃ x ∈ dom(f), r = f (x + y) - f x}

end Function

namespace Rockafellar

/- Rockafellar's recession-function notation. In `open scoped Rockafellar`, a term `f` can be
written as `(f)₀⁺`. -/

scoped postfix:max "₀⁺" => Function.recessionFunction

end Rockafellar

namespace Function

open scoped Rockafellar

section

variable [Add E] [AddGroup α] [ConditionallyCompleteLattice α]
variable (f : E → WithTopBot α)

-- Proof sketch: unfold `recessionFunction`; the right-hand side is exactly its defining
-- supremum formula.
/-- The defining formula for the recession function is the supremum over the effective domain. -/
@[simp] theorem recessionFunction_apply (y : E) :
    ((f)₀⁺) y = sSup {r : WithTopBot α | ∃ x ∈ dom(f), r = f (x + y) - f x} :=
  rfl

end

section

variable [Add E]
variable [Preorder α] [AddGroup α]

/-- `h` is a difference upper bound for `f` when each finite base point `x ∈ dom(f)` satisfies
`f (x + y) - f x ≤ h y` for every translation increment `y`. This is the primitive surface
matching the defining supremum of `recessionFunction`. -/
def DifferenceUpperBound (f h : E → WithTopBot α) : Prop :=
  ∀ x ∈ dom(f), ∀ y, f (x + y) - f x ≤ h y

end

section

variable [Add E]
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable (f : E → WithTopBot α)

/-- The recession function is the least difference upper bound over the effective domain. -/
theorem recessionFunction_isLeast_differenceUpperBounds :
    IsLeast {h : E → WithTopBot α | DifferenceUpperBound f h} ((f)₀⁺) := by
  refine ⟨?_, ?_⟩
  · intro x hx y
    rw [recessionFunction_apply]
    exact le_sSup ⟨x, hx, rfl⟩
  · intro h hh y
    rw [recessionFunction_apply]
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact hh x hx y

end

section

variable [Add E]
variable [Preorder α] [Add α]

/-- `h` is a translation upper bound for `f` when every finite base point `x ∈ dom(f)` satisfies
`f (x + y) ≤ f x + h y` for every translation increment `y`. -/
def TranslationUpperBound (f h : E → WithTopBot α) : Prop :=
  ∀ x ∈ dom(f), ∀ y, f (x + y) ≤ f x + h y

end

section

variable [Add E]
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
variable (f : E → WithTopBot α)

/-- Translation and difference upper bounds are equivalent under the primitive local assumption
that finite base points are never mapped to `⊥`. -/
theorem translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α)) {h : E → WithTopBot α} :
    TranslationUpperBound f h ↔ DifferenceUpperBound f h := by
  constructor
  · intro hh x hx y
    have hx_ne_bot : f x ≠ (⊥ : WithTopBot α) := hf_ne_bot x hx
    have hx_ne_top : f x ≠ (⊤ : WithTopBot α) := ne_of_lt (mem_effectiveDomain.mp hx)
    have hxy : f (x + y) ≤ f x + h y := hh x hx y
    exact (WithBotTop.sub_le_iff_le_add (b := f x) (c := h y)
      (Or.inl hx_ne_bot) (Or.inl hx_ne_top)).2 (by simpa [add_comm] using hxy)
  · intro hh x hx y
    have hx_ne_bot : f x ≠ (⊥ : WithTopBot α) := hf_ne_bot x hx
    have hx_ne_top : f x ≠ (⊤ : WithTopBot α) := ne_of_lt (mem_effectiveDomain.mp hx)
    have hxy : f (x + y) - f x ≤ h y := hh x hx y
    simpa [add_comm] using
      (WithBotTop.sub_le_iff_le_add (b := f x) (c := h y)
        (Or.inl hx_ne_bot) (Or.inl hx_ne_top)).1 hxy

/-- Under properness, translation and difference upper bounds are equivalent. -/
theorem translationUpperBound_iff_differenceUpperBound
    (hf_proper : f.IsProper) {h : E → WithTopBot α} :
    TranslationUpperBound f h ↔ DifferenceUpperBound f h :=
  translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot
    (f := f) (h := h) (fun x _ => hf_proper.ne_bot x)

end

section

variable [Add E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable (f : E → WithTopBot α)

-- Proof sketch: use the preceding theorem's formula
-- `f0⁺ y = sSup {f (x + y) - f x | x ∈ dom(f)}`. If `h` satisfies the
-- translation inequality at every base point `x ∈ dom(f)`, specialize it to `z = x + y` to
-- obtain `f (x + y) - f x ≤ h y` for every admissible `x`, hence `f0⁺ y ≤ h y` after taking the
-- supremum. Applying the same formula with `h = f0⁺` gives the required translation inequality
-- for `f0⁺` itself, so it is the least such function.
/-- The recession function is the least translation upper bound under the primitive local
assumption that finite base points are never mapped to `⊥`. -/
theorem recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α)) :
    IsLeast {h : E → WithTopBot α | TranslationUpperBound f h} ((f)₀⁺) := by
  refine ⟨?_, ?_⟩
  · exact (translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot (f := f)
      (h := ((f)₀⁺)) hf_ne_bot).2
      (recessionFunction_isLeast_differenceUpperBounds (f := f)).1
  · intro h hh
    exact (recessionFunction_isLeast_differenceUpperBounds (f := f)).2
      ((translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot
        (f := f) (h := h) hf_ne_bot).1 hh)

-- Proof sketch: properness gives exactly the local finite-point non-`⊥` condition required by the
-- primitive theorem above, so the source-facing statement is an immediate specialization.
/-- Corollary 8.5.1: for a proper function `f`, the recession function `f0⁺` is the least
function `h` such that `f (x + y) ≤ f x + h y` for all base points `x ∈ dom(f)` and translation
increments `y`. On additive groups this is equivalent to the textbook form
`f z ≤ f x + h (z - x)` for all `z` and `x ∈ dom(f)`. -/
theorem recessionFunction_isLeast_translationUpperBounds
    (hf_proper : f.IsProper) :
    IsLeast {h : E → WithTopBot α | TranslationUpperBound f h} ((f)₀⁺) :=
  recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot (f := f)
    (fun x _ => hf_proper.ne_bot x)

/-- The recession function is itself a translation upper bound under the primitive local
finite-point non-`⊥` condition. -/
theorem recessionFunction_translationUpperBound_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α)) :
    TranslationUpperBound f ((f)₀⁺) :=
  (recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot (f := f) hf_ne_bot).1

/-- Any translation upper bound dominates the recession function pointwise under the primitive
local finite-point non-`⊥` condition. -/
theorem recessionFunction_le_of_translationUpperBound_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α))
    {h : E → WithTopBot α}
    (hh : TranslationUpperBound f h) :
    ((f)₀⁺) ≤ h :=
  (recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot (f := f) hf_ne_bot).2 hh

/-- The recession function is itself a translation upper bound. -/
theorem recessionFunction_translationUpperBound
    (hf_proper : f.IsProper) :
    TranslationUpperBound f ((f)₀⁺) :=
  recessionFunction_translationUpperBound_of_dom_ne_bot (f := f) (fun x _ => hf_proper.ne_bot x)

/-- Any translation upper bound dominates the recession function pointwise. -/
theorem recessionFunction_le_of_translationUpperBound
    (hf_proper : f.IsProper) {h : E → WithTopBot α}
    (hh : TranslationUpperBound f h) :
    ((f)₀⁺) ≤ h :=
  recessionFunction_le_of_translationUpperBound_of_dom_ne_bot (f := f)
    (fun x _ => hf_proper.ne_bot x) hh

end

end Function

end
