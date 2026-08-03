import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap22.Definition_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall: `lean_leansearch` did not surface a more specific library theorem for this
-- equivalence, and local Chapter 22 precedent packages the target condition as
-- `SetValuedOperator.IsStronglyMonotone`.
/-- Example 22.7: for `T : D → H`, the map `T` is `β`-cocoercive if and only if the inverse of
the singleton-valued operator `ofFunction D T` is `β`-strongly monotone. -/
theorem cocoerciveOn_iff_inverseOfFunction_isStronglyMonotone
    {β : ℝ} {D : Set H} {T : D → H} :
    CocoerciveOn β D T ↔ ((ofFunction D T)⁻¹).IsStronglyMonotone β := by
  constructor
  · intro hT
    refine ⟨hT.pos, ?_⟩
    intro x u y v hu hv
    rw [mem_inverse_iff] at hu hv
    rcases hu with ⟨huD, rfl⟩
    rcases hv with ⟨hvD, rfl⟩
    simpa [real_inner_comm] using hT.ineq ⟨u, huD⟩ ⟨v, hvD⟩
  · intro hA
    refine ⟨hA.pos, ?_⟩
    intro x y
    have hx : (x : H) ∈ (ofFunction D T)⁻¹ (T x) := by
      rw [mem_inverse_iff]
      exact ⟨x.2, rfl⟩
    have hy : (y : H) ∈ (ofFunction D T)⁻¹ (T y) := by
      rw [mem_inverse_iff]
      exact ⟨y.2, rfl⟩
    simpa [real_inner_comm] using hA.ineq hx hy

/-- Example 22.7, forward direction: a `β`-cocoercive map yields a `β`-strongly monotone inverse
of the singleton-valued operator `ofFunction D T`. -/
theorem CocoerciveOn.inverseOfFunction_isStronglyMonotone
    {β : ℝ} {D : Set H} {T : D → H} (hT : CocoerciveOn β D T) :
    ((ofFunction D T)⁻¹).IsStronglyMonotone β :=
  cocoerciveOn_iff_inverseOfFunction_isStronglyMonotone.mp hT

/-- Example 22.7, reverse direction: if the inverse of the singleton-valued operator
`ofFunction D T` is `β`-strongly monotone, then `T` is `β`-cocoercive. -/
theorem cocoerciveOn_of_inverseOfFunction_isStronglyMonotone
    {β : ℝ} {D : Set H} {T : D → H}
    (hT : ((ofFunction D T)⁻¹).IsStronglyMonotone β) :
    CocoerciveOn β D T :=
  cocoerciveOn_iff_inverseOfFunction_isStronglyMonotone.mpr hT

end SetValuedOperator
