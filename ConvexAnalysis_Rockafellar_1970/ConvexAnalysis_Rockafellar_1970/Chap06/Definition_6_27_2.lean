import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic.Recall

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.2 introduces the infimum `inf f` of an extended-order-valued
  function as the greatest lower bound of its values.
- `core/canonical`: the primitive expression owner is the indexed infimum `⨅ x, f x`; equivalently,
  the infimum of the value set `sInf (Set.range f)`.
- `bridge/view`: the theorem `sInf_range` is the exact bridge from the source's set-of-values
  presentation to the indexed-infimum owner form already used elsewhere in the project.

Domain-style sampling used here:
- the indexed-infimum owner surface `⨅ x, f x`;
- `sInf (Set.range f)` and the mathlib bridge theorem `sInf_range`;
- chapter-facing specializations such as codomain `WithTopBot α` obtained by direct
  instantiation.

Primitive data vs derived API:
- primitive data: only the function `f : E → β`;
- primitive owner: the indexed infimum `⨅ x, f x`;
- derived API: the equivalent source-facing set formula `sInf (Set.range f)` and the
  greatest-lower-bound owner `IsGLB (Set.range f) (⨅ x, f x)`.

Layer target: `core/canonical`, recall-shaped. The source item adds no new mathematics beyond the
existing canonical infimum owner layer, so the faithful refinement is direct reuse of mathlib's
indexed infimum and `IsGLB` interfaces rather than a local `infimum` wrapper.
-/

universe u v

section Primitive

variable {E : Sort u} {β : Type v}
variable [InfSet β]

/- Definition 6.27.2: the infimum of a chapter-facing function is already the canonical
indexed-infimum expression `⨅ x : E, f x`. -/
recall iInf

/- The source's equivalent set-of-values formula `inf {f(x) | x ∈ E}` is already the canonical
bridge theorem `sInf_range`. -/
recall sInf_range

end Primitive

section OrderSemantics

variable {E : Sort u} {β : Type v}
variable [CompleteSemilatticeInf β]

/-- Source semantic owner for Definition 6.27.2: the indexed infimum of `f` is the greatest lower
bound of the value set `Set.range f`. -/
theorem isGLB_range_iInf (f : E → β) : IsGLB (Set.range f) (⨅ x, f x) := by
  simpa [sInf_range] using (isGLB_sInf (s := Set.range f))

/-- Every value of `f` is above the infimum. -/
theorem iInf_le_apply (f : E → β) (x : E) : (⨅ y, f y) ≤ f x :=
  (isGLB_range_iInf f).1 ⟨x, rfl⟩

/-- Any common lower bound of all values of `f` lies below the infimum. -/
theorem le_iInf_of_forall_le_range {f : E → β} {a : β}
    (ha : ∀ y ∈ Set.range f, a ≤ y) :
    a ≤ (⨅ y, f y) :=
  (isGLB_range_iInf f).2 ha

end OrderSemantics
