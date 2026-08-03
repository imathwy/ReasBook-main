import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap21.Proposition_21_12

open SetValuedOperator
open scoped InnerProductSpace Pointwise Set SetValuedOperator

universe u

namespace Set

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

-- Semantic recall note: `lean_leansearch` did not return an item-specific owner theorem for this
-- example; the verified local surfaces are `N[C]`, `F[N[C]]`,
-- `SetValuedOperator.fstImageDomFitzpatrick`, and `Set.normalCone_isMaximallyMonotone`.

/-- Example 21.13: for a nonempty closed convex subset `C` of a real Hilbert space, the
first-coordinate projection of the domain of the Fitzpatrick function of the normal cone operator
`N[C]` is exactly `C`, formalized by `fstImageDomFitzpatrick (N[C])`. -/
theorem fst_image_dom_fitzpatrick_normalCone_eq
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    fstImageDomFitzpatrick (N[C]) = C := by
  -- Identify the normal-cone domain with the set itself.
  -- This matches the textbook bridge `dom N_C = C`.
  have hdom : SetValuedOperator.dom (N[C] : SetValuedOperator H H) = C := by
    ext x
    by_cases hx : x ∈ C
    · constructor
      · intro _
        exact hx
      · intro _
        change (N[C] x).Nonempty
        refine ⟨0, ?_⟩
        rw [Set.normalCone_of_mem hx]
        simp
    · constructor
      · intro hxdom
        change (N[C] x).Nonempty at hxdom
        rw [Set.normalCone_of_not_mem hx] at hxdom
        simp at hxdom
      · intro hxC
        exact (hx hxC).elim
  -- Package maximal monotonicity so Proposition 21.12 applies directly to `N[C]`.
  have hmax :
      Maximal IsMonotone (N[C] : SetValuedOperator H H) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  -- The two inclusions from Proposition 21.12 collapse to equality after rewriting through `hdom`.
  refine Set.Subset.antisymm ?_ ?_
  · simpa [hdom, hC_closed.closure_eq] using
      fst_image_dom_fitzpatrick_subset_closure_dom (A := (N[C] : SetValuedOperator H H)) hmax
  · simpa [hdom] using
      dom_subset_fst_image_dom_fitzpatrick (A := (N[C] : SetValuedOperator H H)) hmax

end Set
