import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap23.Example_23_4
import BauschkeLean.Chap25.Corollary_25_34

open scoped InnerProductSpace Pointwise Set SetValuedOperator
open ERealFunction SetValuedOperator

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C D : Set H}

/- Source/core/bridge triage:
- `source-facing`: Corollary 25.36 is the projection identity for `C ∩ D`.
- `core/canonical`: the Chapter 23/25 operator calculus is expressed through `J[...]`, `□`, and
  `.comp`.
- `bridge/view`: Example 23.4 is the owner bridge from the single-valued Chebyshev projector
  `P[C, hC]` to the resolvent surface. This corollary should reuse that bridge rather than
  restating a parallel set-valued version. -/

/-- Corollary 25.36: if `C` and `D` are closed convex subsets of a real Hilbert space,
`C ∩ D ≠ ∅`, and `N[C] + N[D] = N[C ∩ D]`, then the set-valued projector onto `C ∩ D` is the
parallel sum of the projectors `P[C]` and `P[D]`, precomposed with `x ↦ (2 : ℝ) • x`. This is
the source identity `(25.40)` on the canonical projector surface. -/
theorem setValuedProjector_inter_eq_parallelSum_comp_double_of_normalCone_add_eq
    (hCD_nonempty : (C ∩ D).Nonempty) (hC_closed : IsClosed C) (hD_closed : IsClosed D)
    (hC_convex : Convex ℝ C) (hD_convex : Convex ℝ D)
    (hnormal : N[C] + N[D] = N[C ∩ D]) :
    P[C ∩ D] = (P[C] □ P[D]).comp (((2 : ℝ) • (id : H → H)).toSetValuedOperator) := by
  have hC_nonempty : C.Nonempty := hCD_nonempty.mono Set.inter_subset_left
  have hD_nonempty : D.Nonempty := hCD_nonempty.mono Set.inter_subset_right
  have hCD_closed : IsClosed (C ∩ D) := hC_closed.inter hD_closed
  have hCD_convex : Convex ℝ (C ∩ D) := hC_convex.inter hD_convex
  let hC_cheb : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let hD_cheb : IsChebyshev D :=
    isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
  let hCD_cheb : IsChebyshev (C ∩ D) :=
    isChebyshev_of_nonempty_isClosed_convex hCD_nonempty hCD_closed hCD_convex
  have hsetValued {S : Set H} (hS : IsChebyshev S) :
      P[S] = (P[S, hS]).toSetValuedOperator := by
    ext x u
    rw [setValuedProjector_eq_singleton_projectionPoint S hS x, Function.toSetValuedOperator_apply]
  have hP_inter : P[C ∩ D] = J[N[C ∩ D]] := by
    rw [hsetValued hCD_cheb]
    have howner : (P[C ∩ D, hCD_cheb]).toSetValuedOperator = J[N[C ∩ D]] :=
      projectionPoint_toSetValuedOperator_eq_resolvent_normalCone_of_nonempty_isClosed_convex
        hCD_nonempty hCD_closed hCD_convex
    simpa [hCD_cheb] using howner
  let twoPos : PosReal := ⟨2, by positivity⟩
  have hPC : P[C] = J[((2 : ℝ) • N[C])] := by
    rw [hsetValued hC_cheb]
    have howner : (P[C, hC_cheb]).toSetValuedOperator = J[((2 : ℝ) • N[C])] := by
      simpa [hC_cheb, twoPos] using
        projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex twoPos
    exact howner
  have hPD : P[D] = J[((2 : ℝ) • N[D])] := by
    rw [hsetValued hD_cheb]
    have howner : (P[D, hD_cheb]).toSetValuedOperator = J[((2 : ℝ) • N[D])] := by
      simpa [hD_cheb, twoPos] using
        projectionPoint_toSetValuedOperator_eq_resolvent_smul_normalCone_of_nonempty_isClosed_convex
          hD_nonempty hD_closed hD_convex twoPos
    exact howner
  rw [hP_inter]
  have hres :
      J[N[C ∩ D]] =
        (J[((2 : ℝ) • N[C])] □ J[((2 : ℝ) • N[D])]).comp
          (((2 : ℝ) • (id : H → H)).toSetValuedOperator) := by
    calc
    J[N[C ∩ D]] = J[(N[C] + N[D])] := by rw [hnormal.symm]
    _ =
        (J[((2 : ℝ) • N[C])] □ J[((2 : ℝ) • N[D])]).comp
          (((2 : ℝ) • (id : H → H)).toSetValuedOperator) := by
        have hres :
            J[(N[C] + N[D])] =
              (J[((2 : ℝ) • N[C])] □ J[((2 : ℝ) • N[D])]).comp
                (((2 : ℝ) • (id : H → H)).toSetValuedOperator) :=
          resolvent_add_eq_parallelSum_double_resolvents_comp_double
        exact hres
  rw [← hPC, ← hPD] at hres
  exact hres

end
