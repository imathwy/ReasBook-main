import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap23.Remark_23_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.24 asserts a separating graph point for a maximally monotone
  operator outside its graph.
- `core/canonical`: the owner abstraction for maximal monotonicity is `Maximal IsMonotone A`.
- `bridge/view`: the source conclusion yields the reusable strict-negativity companion and its
  `↔` reformulation against graph nonmembership, both phrased in the canonical graph language.
Semantic recall: `lean_leansearch` returned no item-specific hit, so the public surface was
verified against the local Chapter 20 owners `gra A` and `Maximal IsMonotone A`. -/

/-- Proposition 23.24: if `A` is maximally monotone and `(x, u) ∉ gra A`, then there exists a
graph point `(y, v) ∈ gra A` such that
`⟪x - y, u - v⟫_ℝ = -‖x - y‖ * ‖u - v‖` and `⟪x - y, u - v⟫_ℝ < 0`. -/
theorem Maximal.exists_graph_point_inner_eq_neg_mul_norm_of_not_mem_graph
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x u : H}
    (hxu : (x, u) ∉ gra A) :
    ∃ y v : H, (y, v) ∈ gra A ∧
      ⟪x - y, u - v⟫_ℝ = -‖x - y‖ * ‖u - v‖ ∧
      ⟪x - y, u - v⟫_ℝ < 0 := by
  let z := x + u
  let y := resolventMap A hA (1 : PosReal) z
  let v := z - y
  -- The Minty parameterization at `γ = 1` gives the required graph witness.
  have hyv : (y, v) ∈ gra A := by
    have hz : (resolventYosidaGraphParameterization hA (1 : PosReal) z).1 ∈ gra A :=
      (resolventYosidaGraphParameterization hA (1 : PosReal) z).2
    rw [resolventYosidaGraphParameterization_apply, yosidaApproximationMap_apply] at hz
    simp at hz
    simpa [y, v] using hz
  -- The residual witness satisfies the exact cancellation `u - v = -(x - y)`.
  have huv : u - v = -(x - y) := by
    simp [v, z]
    abel_nf
  -- Rewriting through the cancellation turns the pairing into a negative squared norm.
  have heq : ⟪x - y, u - v⟫_ℝ = -‖x - y‖ * ‖u - v‖ := by
    rw [huv, inner_neg_right, real_inner_self_eq_norm_sq, norm_neg]
    simp [pow_two]
  -- If `x - y = 0`, then the graph witness collapses back to `(x, u) ∈ gra A`, contradicting `hxu`.
  have hxy_ne : x - y ≠ 0 := by
    intro hxy
    have hxy' : x = y := sub_eq_zero.mp hxy
    have hvu : v = u := by
      simp [v, z, hxy']
    exact hxu (by simpa [hxy', hvu] using hyv)
  -- Positive norms force the explicit negative product in `heq` to be strictly negative.
  have hxy_norm_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr hxy_ne
  have huv_norm_pos : 0 < ‖u - v‖ := by
    rw [huv, norm_neg]
    exact hxy_norm_pos
  have hneg : ⟪x - y, u - v⟫_ℝ < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hxy_norm_pos) huv_norm_pos
  exact ⟨y, v, hyv, heq, hneg⟩

/-- Proposition 23.24, canonical strict-negativity companion: if `(x, u) ∉ gra A`, then there
exists a graph point `(y, v) ∈ gra A` with strictly negative monotonicity pairing against
`(x, u)`. -/
theorem Maximal.exists_graph_point_inner_neg_of_not_mem_graph
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {x u : H}
    (hxu : (x, u) ∉ gra A) :
    ∃ y v : H, (y, v) ∈ gra A ∧ ⟪x - y, u - v⟫_ℝ < 0 := by
  rcases Maximal.exists_graph_point_inner_eq_neg_mul_norm_of_not_mem_graph hA hxu with
    ⟨y, v, hyv, -, hneg⟩
  exact ⟨y, v, hyv, hneg⟩

/-- For a maximally monotone operator, a pair lies outside the graph exactly when some graph point
has strictly negative monotonicity pairing against it. -/
theorem Maximal.not_mem_graph_iff_exists_graph_point_inner_neg
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    (x, u) ∉ gra A ↔ ∃ y v : H, (y, v) ∈ gra A ∧ ⟪x - y, u - v⟫_ℝ < 0 := by
  constructor
  · exact Maximal.exists_graph_point_inner_neg_of_not_mem_graph hA
  · rintro ⟨y, v, hyv, hneg⟩ hxu
    have hxuA : u ∈ A x := by
      simpa [SetValuedOperator.mem_graph] using hxu
    have hnonneg : 0 ≤ ⟪x - y, u - v⟫_ℝ :=
      (Maximal.mem_iff hA x u).1 hxuA (by simpa [SetValuedOperator.mem_graph] using hyv)
    exact not_lt_of_ge hnonneg hneg

end SetValuedOperator
