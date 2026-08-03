module

public import Topology_Munkres_2000.Book.Exercise_3_1.Parabola
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.RelIso.Basic

@[expose] public section

/-- Exercise 3.6: Compare points of the real plane first by `y - x ^ 2`, and then
by `x` when those values agree. -/
def parabolaLt (p q : ℝ × ℝ) : Prop :=
  parabolaOffset p < parabolaOffset q ∨
    parabolaOffset p = parabolaOffset q ∧ p.1 < q.1

/-- Geometrically, `parabolaLt` orders the translated parabolas `y = x ^ 2 + c`
by `c`, and then orders the points on each parabola by `x`. -/
def parabolaRelIso : parabolaLt ≃r (fun a b : ℝ ×ₗ ℝ ↦ a < b) where
  toFun p := toLex (parabolaOffset p, p.1)
  invFun z := ((ofLex z).2, (ofLex z).1 + (ofLex z).2 ^ 2)
  left_inv := by
    rintro ⟨x, y⟩
    simp [parabolaOffset_apply]
  right_inv := by
    intro z
    apply toLex.injective
    simp [parabolaOffset_apply]
  map_rel_iff' := by
    intro p q
    simp [parabolaLt, parabolaOffset_apply, Prod.Lex.toLex_lt_toLex]

/-- The lexicographic coordinates of a point in the real plane. -/
@[simp]
theorem parabolaRelIso_apply (p : ℝ × ℝ) :
    parabolaRelIso p = toLex (parabolaOffset p, p.1) := rfl

/-- The point with prescribed translated-parabola coordinate and `x`-coordinate. -/
@[simp]
theorem parabolaRelIso_symm_apply (z : ℝ ×ₗ ℝ) :
    parabolaRelIso.symm z = ((ofLex z).2, (ofLex z).1 + (ofLex z).2 ^ 2) := rfl

/-- The relation `parabolaLt` is a strict total order on the real plane. -/
instance instIsStrictTotalOrderParabolaLt :
    IsStrictTotalOrder (ℝ × ℝ) parabolaLt :=
  parabolaRelIso.toRelEmbedding.isStrictTotalOrder

/-- The comparison transported by `parabolaRelIso`. -/
theorem parabolaRelIso_map_rel_iff (p q : ℝ × ℝ) :
    parabolaLt p q ↔ parabolaRelIso p < parabolaRelIso q :=
  parabolaRelIso.map_rel_iff.symm
