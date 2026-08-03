import BauschkeLean.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C D : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)

local notation "P_C" =>
  P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]

-- Semantic recall: `lean_leansearch` only surfaced orthogonal-projection lemmas for subspaces and
-- affine subspaces; the verified project owner for general nonempty closed convex sets remains
-- `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex`.
/-- If the projection of `x` onto `C` lies in `D`, then `C ∩ D` is nonempty. -/
theorem inter_nonempty_of_projectionPoint_mem
    (x : H) (hproj_mem : P_C x ∈ D) :
    (C ∩ D).Nonempty := by
  -- The source-proof witness is the projection point itself.
  refine ⟨P_C x, ?_⟩
  exact ⟨projectionPoint_mem C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x, hproj_mem⟩

local notation "hCD_nonempty" =>
  inter_nonempty_of_projectionPoint_mem hC_nonempty hC_closed hC_convex

/-- Proposition 29.5: let `C` and `D` be nonempty closed convex subsets of a real Hilbert space,
let `x ∈ H`, and suppose that `P_C x ∈ D`. Then the projection of `x` onto `C ∩ D` is `P_C x`.
The Lean statement omits a separate hypothesis `D.Nonempty`, since `P_C x ∈ D` already implies it.
-/
theorem projectionPoint_inter_eq_projectionPoint_of_projectionPoint_mem
    (x : H) (hproj_mem : P_C x ∈ D) :
    P[C ∩ D,
      isChebyshev_of_nonempty_isClosed_convex
        (hCD_nonempty x hproj_mem)
        (hC_closed.inter hD_closed)
        (hC_convex.inter hD_convex)] x =
      P_C x := by
  -- The same point `P_C x` is admissible for the intersection because it already lies in `C`
  -- and is assumed to lie in `D`.
  have hmem_inter : P_C x ∈ C ∩ D := by
    exact ⟨projectionPoint_mem C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x, hproj_mem⟩
  -- The Chapter 3 variational inequality on `C` restricts immediately to the smaller set `C ∩ D`.
  have hinner_nonpos : ∀ y ∈ C ∩ D, ⟪y - P_C x, x - P_C x⟫_ℝ ≤ 0 := by
    have hproj_char :
        P_C x ∈ C ∧ ∀ y ∈ C, ⟪y - P_C x, x - P_C x⟫_ℝ ≤ 0 := by
      exact
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mp rfl
    intro y hy
    exact hproj_char.2 y hy.1
  -- Applying the same characterization to `C ∩ D` identifies its projection with `P_C x`.
  have hproj_inter :
      P_C x =
        P[C ∩ D,
          isChebyshev_of_nonempty_isClosed_convex
            (hCD_nonempty x hproj_mem)
            (hC_closed.inter hD_closed)
            (hC_convex.inter hD_convex)] x := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (hCD_nonempty x hproj_mem)
        (hC_closed.inter hD_closed)
        (hC_convex.inter hD_convex)).mpr ⟨hmem_inter, hinner_nonpos⟩
  exact hproj_inter.symm

end
