import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap17.Example_17_8
import BauschkeLean.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousLinearMap ERealFunction InnerProduct InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Example 20.54 identifies the Fitzpatrick function of the singleton-valued
  operator induced by a bounded linear map.
- `core/canonical`: the owner abstractions are `F[_]` for Fitzpatrick functions and `q[_]` for
  quadratic potentials.
- `bridge/view`: `A.toSetValuedOperator` is the thin continuous-linear-map bridge to the canonical
  function-level singleton-valued operator owner. -/

-- Proof sketch: expand the Fitzpatrick supremum for the singleton-valued operator induced by `A`.
-- At a graph point `(y, A y)`, the supremand becomes
-- `⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ = 2 * (⟪y, (u + A† x) / 2⟫_ℝ - q[A] y)`.
-- The remaining supremum is exactly twice the conjugate of `q_A` at
-- `(1 / 2) • u + (1 / 2) • A† x`.
/-- Helper for Example 20.54: reindex the Fitzpatrick supremum of the singleton-valued operator
induced by `A` by its base point `y`. -/
lemma fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup
    (A : H →L[ℝ] H) (x u : H) :
    F[A.toSetValuedOperator] (x, u) =
      ⨆ y : H, ((⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ : ℝ) : EReal) := by
  -- Expand the Fitzpatrick owner and rewrite each graph point `(y, v)` through the singleton
  -- graph equation `v = A y`.
  rw [SetValuedOperator.fitzpatrickFunction]
  apply le_antisymm
  · refine iSup_le fun p => ?_
    have hp_mem : p.1.2 ∈ A.toSetValuedOperator p.1.1 := by
      exact (SetValuedOperator.mem_graph A.toSetValuedOperator p.1.1 p.1.2).1 p.2
    have hp : p.1.2 = A p.1.1 := by
      simpa [Function.toSetValuedOperator_apply] using hp_mem
    rw [hp]
    exact le_iSup
      (fun y : H ↦ ((⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ : ℝ) : EReal))
      p.1.1
  · refine iSup_le fun y => ?_
    simpa using
      (le_iSup
        (fun p : gra A.toSetValuedOperator ↦
          ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal))
        ⟨(y, A y), by
          exact (SetValuedOperator.mem_graph A.toSetValuedOperator y (A y)).2
            (by simp [Function.toSetValuedOperator_apply])⟩)

/-- Helper for Example 20.54: the singleton-graph Fitzpatrick supremand is twice the shifted
quadratic-potential affine defect from the source proof. -/
lemma fitzpatrick_singleton_supremand_eq_two_mul_affine_defect
    (A : H →L[ℝ] H) (x u y : H) :
    ⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ =
      2 * (⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y) := by
  -- Rewrite the mixed term through the adjoint so the whole expression depends on the single
  -- shifted pairing `⟪y, (u + A† x) / 2⟫`.
  have hadj : ⟪x, A y⟫_ℝ = ⟪y, ((A†) x)⟫_ℝ := by
    calc
      ⟪x, A y⟫_ℝ = ⟪A y, x⟫_ℝ := by
        rw [real_inner_comm]
      _ = ⟪y, ((A†) x)⟫_ℝ := by
        simpa using (ContinuousLinearMap.adjoint_inner_right (A := A) y x).symm
  -- Unfold `q[A]` and normalize the resulting real scalar identity.
  rw [hadj, ContinuousLinearMap.quadraticPotential_apply, inner_add_right,
    real_inner_smul_right, real_inner_smul_right]
  ring

/-- Helper for Example 20.54: after the scalar normalization, the Fitzpatrick function is twice
the supremum of the shifted quadratic-potential affine defect. -/
lemma fitzpatrickFunction_toSetValuedOperator_eq_two_mul_iSup_shifted_quadratic_defect
    (A : H →L[ℝ] H) (x u : H) :
    F[A.toSetValuedOperator] (x, u) =
      ((2 : ℝ) : EReal) *
        (⨆ y : H,
          (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y : ℝ)) : EReal)) := by
  -- First expose the singleton graph supremum from the source proof, then rewrite each term by
  -- the adjoint-shifted affine defect identity.
  calc
    F[A.toSetValuedOperator] (x, u)
        = ⨆ y : H, ((⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ : ℝ) : EReal) :=
            fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup A x u
    _ = ⨆ y : H,
          (((2 *
              (⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x) )⟫_ℝ - q[A] y) : ℝ)) : EReal) := by
            refine iSup_congr fun y ↦ ?_
            exact congrArg (fun t : ℝ ↦ (t : EReal))
              (fitzpatrick_singleton_supremand_eq_two_mul_affine_defect A x u y)
    _ = ((2 : ℝ) : EReal) *
          (⨆ y : H,
            (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y : ℝ)) : EReal)) := by
          let α : Set.Ioi (0 : ℝ) := ⟨2, by norm_num⟩
          calc
            (⨆ y : H,
                (((2 *
                    (⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y) : ℝ)) :
                  EReal))
                = ⨆ y : H,
                    (((α : ℝ) : EReal) *
                      (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y : ℝ)) :
                        EReal)) := by
                      refine iSup_congr fun y ↦ ?_
                      simp [α, EReal.coe_mul]
            _ = (((α : ℝ) : EReal)) *
                  (⨆ y : H,
                    (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y : ℝ)) :
                      EReal)) := by
                    symm
                    simpa [α] using
                      ERealFunction.ereal_mul_iSup_of_pos α
                        (fun y : H ↦
                          (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y :
                              ℝ)) : EReal))
            _ = ((2 : ℝ) : EReal) *
                  (⨆ y : H,
                    (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y : ℝ)) :
                      EReal)) := by
                    rfl

/-- Example 20.54: for a bounded linear operator `A`, the Fitzpatrick function of the
singleton-valued operator induced by `A` is `2 q_A^* ((u + A† x) / 2)`. -/
theorem fitzpatrickFunction_eq_two_mul_conjugate_quadraticPotential
    (A : H →L[ℝ] H) (x u : H) :
    F[A.toSetValuedOperator] (x, u) =
      ((2 : ℝ) : EReal) * ((q[A]).toEReal.asEReal∗)
        (((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • (A†) x)) := by
  -- Follow the textbook route: first rewrite `F_A` as twice the shifted affine-defect supremum.
  calc
    F[A.toSetValuedOperator] (x, u)
        = ((2 : ℝ) : EReal) *
            (⨆ y : H,
              (((⟪y, ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x))⟫_ℝ - q[A] y : ℝ)) :
                EReal)) :=
          fitzpatrickFunction_toSetValuedOperator_eq_two_mul_iSup_shifted_quadratic_defect A x u
    _ = ((2 : ℝ) : EReal) *
          (((q[A]).toEReal.asEReal∗)
            (((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • ((A†) x)))) := by
          -- The remaining supremum is exactly the conjugate of the quadratic potential at the
          -- shifted dual point.
          refine congrArg (fun t : EReal ↦ ((2 : ℝ) : EReal) * t) ?_
          rw [ERealFunction.conjugate_apply]
          refine iSup_congr fun y ↦ ?_
          rw [Function.asEReal_apply, Function.toEReal_apply, ← EReal.coe_sub]

end

end ContinuousLinearMap
