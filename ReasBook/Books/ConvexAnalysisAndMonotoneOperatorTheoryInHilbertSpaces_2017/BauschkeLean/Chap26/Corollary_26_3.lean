import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap26.Proposition_26_1

-- Semantic recall note: `lean_leansearch` only surfaced generic `fixedPoints` lemmas, so the
-- statements below follow the verified local Chapter 26/23 owners `fixedPoints` and
-- `resolventMap`, with `resolventMap A γ` realizing `J_{γA}`.

/- Source/core/bridge triage:
- `source-facing`: Corollary 26.3 identifies the two source fixed-point formulations
  `Fix (J_A ∘ (Id + γ (B - Id)))` and `Fix (J_{γ⁻¹ A} ∘ B)`.
- `core/canonical`: the reusable owner in this repository is
  `primal_inclusion_solution_set`, together with
  `primal_inclusion_solution_set_eq_fixedPoints_forwardBackwardSplittingOperator`.
- `bridge/view`: the two source fixed-point maps are companion views of the same forward-backward
  problem for `((γ : ℝ)⁻¹) • A` and `Id - B`. -/

open Function
open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Corollary 26.3, left-hand side: the fixed points of
`J_A ∘ (Id + γ(B - Id))` are exactly the primal solutions of the forward-backward problem for
`((γ : ℝ)⁻¹) • A` and `Id - B`. -/
theorem fixedPoints_resolvent_comp_id_add_smul_sub_eq_primal_inclusion_solution_set
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) :
    fixedPoints ((resolventMap A hA (1 : PosReal)).comp
      (fun x ↦ x + (γ : ℝ) • (B x - x))) =
      primal_inclusion_solution_set (((γ : ℝ)⁻¹) • A) (id - B).toSetValuedOperator := by
  let Aγ : SetValuedOperator H H := ((γ : ℝ)⁻¹) • A
  let C : H → H := id - B
  let hγA : Maximal IsMonotone Aγ := by
    simpa using maximal_isMonotone_smul hA γ⁻¹
  have hresolvent :
      resolventMap Aγ hγA γ = resolventMap A hA (1 : PosReal) := by
    funext x
    apply Set.singleton_injective
    have htoSet :
        (resolventMap Aγ hγA γ).toSetValuedOperator =
          (resolventMap A hA (1 : PosReal)).toSetValuedOperator := by
      calc
        (resolventMap Aγ hγA γ).toSetValuedOperator = J[((γ : ℝ) • Aγ)] := by
          exact resolventMap_toSetValuedOperator_eq Aγ hγA γ
        _ = J[A] := by
          congr 1
          ext y z
          simp [Aγ, Pi.smul_apply, γ.2.ne']
        _ = (resolventMap A hA (1 : PosReal)).toSetValuedOperator := by
          symm
          simpa using resolventMap_toSetValuedOperator_eq A hA (1 : PosReal)
    have hxset := congrArg (fun T : SetValuedOperator H H ↦ T x) htoSet
    simpa using hxset
  have hcomp :
      forwardBackwardSplittingOperator Aγ hγA C γ =
        (resolventMap A hA (1 : PosReal)).comp
          (fun x ↦ x + (γ : ℝ) • (B x - x)) := by
    funext x
    rw [forwardBackwardSplittingOperator_apply, Function.comp_apply, hresolvent]
    congr 1
    calc
      x - (γ : ℝ) • C x = x - (γ : ℝ) • (x - B x) := by
        simp [C]
      _ = x - ((γ : ℝ) • x - (γ : ℝ) • B x) := by rw [smul_sub]
      _ = x + ((γ : ℝ) • B x - (γ : ℝ) • x) := by
            abel_nf
      _ = x + (γ : ℝ) • (B x - x) := by rw [smul_sub]
  calc
    fixedPoints ((resolventMap A hA (1 : PosReal)).comp
        (fun x ↦ x + (γ : ℝ) • (B x - x))) =
      fixedPoints (forwardBackwardSplittingOperator Aγ hγA C γ) := by
            rw [hcomp]
    _ = primal_inclusion_solution_set Aγ C.toSetValuedOperator := by
            symm
            exact primal_inclusion_solution_set_eq_fixedPoints_forwardBackwardSplittingOperator
              Aγ hγA C γ

/-- Corollary 26.3, right-hand side: the fixed points of `J_{γ⁻¹ A} ∘ B` are the same primal
solution set for the scaled operator `((γ : ℝ)⁻¹) • A` and residual map `Id - B`. -/
theorem fixedPoints_resolvent_inv_smul_comp_eq_primal_inclusion_solution_set
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) :
    fixedPoints
      ((resolventMap (((γ : ℝ)⁻¹) • A) (maximal_isMonotone_smul hA γ⁻¹)
        (1 : PosReal)).comp B) =
      primal_inclusion_solution_set (((γ : ℝ)⁻¹) • A) (id - B).toSetValuedOperator := by
  let Aγ : SetValuedOperator H H := ((γ : ℝ)⁻¹) • A
  let C : H → H := id - B
  let hγA : Maximal IsMonotone Aγ := by
    simpa using maximal_isMonotone_smul hA γ⁻¹
  have hcomp :
      forwardBackwardSplittingOperator Aγ hγA C (1 : PosReal) =
        (resolventMap Aγ hγA (1 : PosReal)).comp B := by
    funext x
    rw [forwardBackwardSplittingOperator_apply, Function.comp_apply]
    congr 1
    calc
      x - (1 : ℝ) • C x = x - (x - B x) := by
        simp [C]
      _ = B x := by
        abel_nf
  rw [← hcomp]
  symm
  exact primal_inclusion_solution_set_eq_fixedPoints_forwardBackwardSplittingOperator
    Aγ hγA C (1 : PosReal)

/-- Corollary 26.3: if `A : H → 2^H` is maximally monotone, `B : H → H`, and `γ ∈ ℝ_{++}`, then
`Fix J_A ∘ (Id + γ(B - Id)) = Fix J_{γ⁻¹ A} ∘ B`, realized using the canonical single-valued
resolvent map owner `resolventMap`. -/
theorem fixedPoints_resolvent_comp_id_add_smul_sub_eq_fixedPoints_resolvent_inv_smul_comp
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) :
    fixedPoints ((resolventMap A hA (1 : PosReal)).comp
      (fun x ↦ x + (γ : ℝ) • (B x - x))) =
      fixedPoints
        ((resolventMap (((γ : ℝ)⁻¹) • A) (maximal_isMonotone_smul hA γ⁻¹)
          (1 : PosReal)).comp B) := by
  rw [fixedPoints_resolvent_comp_id_add_smul_sub_eq_primal_inclusion_solution_set A hA B γ,
    fixedPoints_resolvent_inv_smul_comp_eq_primal_inclusion_solution_set A hA B γ]

end SetValuedOperator
