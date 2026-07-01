import Mathlib.Data.Set.Prod
import Mathlib.Order.Interval.Set.Defs

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}
variable {R : Type*} [Preorder R]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.10 introduces the auxiliary set `C₂` attached to the
  constrained minimum problem, namely the pairs `(x, μ)` with `x ∈ C` and `μ ≤ α`.
- `core/canonical`: the owner surface is the canonical product/interval object
  `C ×ˢ Set.Iic α`.
- `bridge/view`: the source-facing pair-membership reading `(x, μ) ∈ C₂ C α ↔ x ∈ C ∧ μ ≤ α`
  is a direct derived view of this canonical owner.
- Primitive data vs derived API: primitive data are the set `C` and the level `α`; the
  pointwise membership view is derived API.
- Domain-style sampling used here:
- `Set.prod`;
- `Set.mem_prod`;
- `Set.Iic` / `Set.mem_Iic`;
- the nearby product-form bridge `epi_indicator_eq_prod`.
- Layer target: `source-facing`, with `C₂` as a thin alias of the canonical set-product owner.
-/

/-- Definition 6.27.10: textbook symbol for the lower cylinder, implemented as a thin alias of
the canonical owner `C ×ˢ Set.Iic α`. -/
def C₂ (C : Set E) (α : R) : Set (E × R) :=
  C ×ˢ Set.Iic α

@[simp] theorem mem_C₂_iff
    {C : Set E} {α : R} {x : E} {μ : R} :
    (x, μ) ∈ C₂ C α ↔ x ∈ C ∧ μ ≤ α := by
  simp [C₂, Set.mem_Iic]

end
