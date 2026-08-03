import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Directed

-- Declarations for this item will be appended below by the statement pipeline.

-- Mathlib recall: `Prod.instPartialOrder` and `Prod.mk_le_mk` realize the textbook relation
-- `\preceq` on `ℝ²` as the canonical coordinatewise order on `ℝ × ℝ`.

/- Source/core/bridge triage:
- `source-facing`: Proposition 22.20 only recalls order-theoretic properties of the textbook
  coordinatewise order `\preceq` on `ℝ²`.
- `core/canonical`: mathlib's owner abstraction is the canonical product order on `ℝ × ℝ`,
  with `Prod.instPartialOrder`, `Prod.mk_le_mk`, and the generic directed-order instance coming
  from the product semilattice structure.
- `bridge/view`: none.

Primitive data: none.
Derived API: only the negative non-totality witness below. -/

/-- Helper for Proposition 22.20: the canonical coordinatewise order on `ℝ × ℝ` is not total. -/
theorem real_plane_coordinatewise_order_not_total :
    ¬ Std.Total ((· ≤ ·) : (ℝ × ℝ) → (ℝ × ℝ) → Prop) := by
  intro h
  rcases h.total ((0 : ℝ), 1) (1, 0) with h01 | h10
  · exact (not_le_of_gt zero_lt_one) h01.2
  · exact (not_le_of_gt zero_lt_one) h10.1

/-- Proposition 22.20: `(ℝ², \preceq)` is directed and partially ordered, but not totally
ordered, where `\preceq` is the canonical coordinatewise order on `ℝ × ℝ`. -/
theorem real_plane_coordinatewise_order_structure :
    IsDirectedOrder (ℝ × ℝ) ∧
      IsPartialOrder (ℝ × ℝ) ((· ≤ ·) : (ℝ × ℝ) → (ℝ × ℝ) → Prop) ∧
      ¬ IsTotal (ℝ × ℝ) ((· ≤ ·) : (ℝ × ℝ) → (ℝ × ℝ) → Prop) := by
  -- Directedness comes from taking coordinatewise maxima.
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun a b ↦ ?_⟩
    refine ⟨(max a.1 b.1, max a.2 b.2), ?_, ?_⟩
    · exact ⟨le_max_left _ _, le_max_left _ _⟩
    · exact ⟨le_max_right _ _, le_max_right _ _⟩
  -- The canonical product-order instance supplies the partial-order structure.
  · exact inferInstance
  · exact real_plane_coordinatewise_order_not_total
