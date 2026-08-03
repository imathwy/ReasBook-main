import BauschkeLean.Chap03.Proposition_3_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

/- Source/core/bridge triage:
- `source-facing`: Proposition 29.1 records the translation, nonzero-scaling, and negation rules
  for the projector onto a nonempty closed convex set.
- `core/canonical`: Chapter 3 already owns the translation formula as
  `projectionPoint_vadd_set_eq_add_projectionPoint`.
- `bridge/view`: this file therefore keeps clause `(1)` as a direct canonical recall and keeps the
  genuinely new scaled and negated-set formulas source-facing on the project-local projector
  notation `P[C, hC]`. -/

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

/- Proposition 29.1 (1): the translation formula is exactly the Chapter 3 owner
`projectionPoint_vadd_set_eq_add_projectionPoint`. -/
#check projectionPoint_vadd_set_eq_add_projectionPoint

/-- Companion theorem for Proposition 29.1: a nonzero scalar multiple of a nonempty closed convex
set in a real Hilbert space is Chebyshev. -/
theorem isChebyshev_smul_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    IsChebyshev (ρ • C) := sorry

/-- Companion theorem for Proposition 29.1: the negation of a nonempty closed convex set in a real
Hilbert space is Chebyshev. -/
theorem isChebyshev_neg_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    IsChebyshev (-C) := by
  have hneg : (-1 : ℝ) ≠ 0 := by
    norm_num
  simpa using
    (isChebyshev_smul_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex (-1) hneg)

/-- Proposition 29.1 (2): if `D = ρ C` with `ρ ∈ ℝ \\ {0}`, then the metric projection onto `D`
is
`P_D x = ρ P_C (ρ⁻¹ x)`. -/
theorem projectionPoint_smul_set_eq_smul_projectionPoint
    (x : H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    P[ρ • C, isChebyshev_smul_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex ρ hρ] x =
      ρ •
        P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]
          (ρ⁻¹ • x) := sorry

/-- Proposition 29.1 (3): if `D = -C`, then the metric projection onto `D` satisfies
`P_D x = -P_C (-x)`. -/
theorem projectionPoint_neg_set_eq_neg_projectionPoint
    (x : H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    P[-C, isChebyshev_neg_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] x =
      -P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] (-x) := by
  have hneg : (-1 : ℝ) ≠ 0 := by
    norm_num
  simpa using
    (projectionPoint_smul_set_eq_smul_projectionPoint x hC_nonempty hC_closed hC_convex
      (-1) hneg)

end
