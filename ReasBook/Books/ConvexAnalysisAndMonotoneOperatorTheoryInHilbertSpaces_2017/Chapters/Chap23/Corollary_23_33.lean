import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap23.Example_23_4
import BauschkeLean.Chap23.Proposition_23_20
import BauschkeLean.Chap23.Proposition_23_32
import BauschkeLean.Chap25.Theorem_25_3

open Set
open scoped InnerProductSpace Pointwise Set SetValuedOperator
open ERealFunction SetValuedOperator

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {A : SetValuedOperator H H} {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

local notation "σ_C" =>
  properIoi (σ[C]) (isProper_supportFunction_of_nonempty C hC_nonempty)

local notation "hσ_C" =>
  properIoi_mem_gammaZero_of_mem_gamma
    (isProper_supportFunction_of_nonempty C hC_nonempty)
    (supportFunction_mem_gamma_local C)

-- Semantic recall: `lean_leansearch` returned only unrelated support-spectrum hits, so this item
-- uses the verified local Chapter 23/25 owners `J[...]`, `N[C]`, `P[C, hC]`, and Example 23.4's
-- support-function proximal rewrite.

/-- Corollary 23.33: let `A : H → 2^H` be maximally monotone and satisfy
`({x} : Set H) + A x ⊆ Set.Ici (0 : ℝ) • ({x} : Set H)` for every `x : H`; let `C` be a nonempty
closed convex subset of `H` such that
`cone (dom A - ran N_C) = closure (span (dom A - ran N_C))`. Then, with `B = N_C⁻¹`, the
resolvent `J_{A+B}` is the composition of `J_A` with the projection residual `Id - P_C`. -/
theorem resolvent_add_inverse_normalCone_eq_resolvent_comp_projectionResidual
    (hA : Maximal IsMonotone A)
    (hray : ∀ x : H, ({x} : Set H) + A x ⊆ Set.Ici (0 : ℝ) • ({x} : Set H))
    (hcone :
      cone (A.dom - SetValuedOperator.range (N[C])) =
        ((Submodule.span ℝ (A.dom - SetValuedOperator.range (N[C]))).topologicalClosure :
          Set H)) :
    J[(A + (N[C])⁻¹)] =
      J[A].comp ((id - P_C).toSetValuedOperator) := by
  have hNC : Maximal IsMonotone (N[C]) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hNCinv : Maximal IsMonotone ((N[C])⁻¹) :=
    SetValuedOperator.Maximal.inverse hNC
  have hidAdjImage : (ContinuousLinearMap.id ℝ H).adjointImage A = A := by
    ext x u
    simp [ContinuousLinearMap.adjointImage]
  have hAaddNCinv : Maximal IsMonotone (A + (N[C])⁻¹) := by
    have hAaddNCinv' :
        Maximal IsMonotone ((ContinuousLinearMap.id ℝ H).adjointImage A + (N[C])⁻¹) := by
      simpa [ContinuousLinearMap.adjointImage, add_comm] using
        (Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span
          hNCinv hA (ContinuousLinearMap.id ℝ H)
          (by simpa [SetValuedOperator.dom_inverse] using hcone))
    simpa [hidAdjImage] using hAaddNCinv'
  have hsubset :
      ∀ ⦃x u : H⦄, (x, u) ∈ gra A → ((N[C])⁻¹) x ⊆ ((N[C])⁻¹) (x + u) := by
    intro x u hxu z hz
    have hx_normal : x ∈ N[C] z := by
      simpa [SetValuedOperator.mem_inverse_iff] using hz
    have hzC : z ∈ C := by
      by_contra hzC
      simp [Set.normalCone_of_not_mem hzC] at hx_normal
    have hsmul_normal :
        ∀ {a : ℝ}, 0 ≤ a → a • x ∈ N[C] z := by
      intro a ha
      rw [Set.normalCone_of_mem hzC] at hx_normal ⊢
      refine innerSupremumOn_sub_singleton_le_zero_iff.2 ?_
      intro y hy
      have hx_nonpos :=
        (innerSupremumOn_sub_singleton_le_zero_iff.1 hx_normal) y hy
      simpa [real_inner_smul_right] using mul_nonpos_of_nonneg_of_nonpos ha hx_nonpos
    have hxu_mem : x + u ∈ ({x} : Set H) + A x := by
      rw [Set.mem_add]
      exact ⟨x, by simp, u, by simpa [SetValuedOperator.mem_graph] using hxu, by simp⟩
    have hxu_ray : x + u ∈ Set.Ici (0 : ℝ) • ({x} : Set H) :=
      hray x hxu_mem
    rcases hxu_ray with ⟨a, ha, y, hy, hxy⟩
    have hyx : y = x := by simpa using hy
    subst hyx
    rw [← hxy]
    exact hsmul_normal ha
  have hcompose :
      J[(A + (N[C])⁻¹)] = J[A].comp J[(N[C])⁻¹] := by
    exact
      resolvent_add_eq_resolvent_comp_of_maximal_add_and_graph_step_superset
        hA hNCinv hAaddNCinv hsubset
  have hresolventNCinv : J[(N[C])⁻¹] = (id - P_C).toSetValuedOperator := by
    have hprojection : (P_C).toSetValuedOperator = J[N[C]] := by
      simpa using
        projectionPoint_toSetValuedOperator_eq_resolvent_normalCone_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex
    rw [resolvent_inverse_eq_id_sub_resolvent]
    rw [← hprojection]
    ext x u
    simp [sub_eq_add_neg]
  rw [hcompose, hresolventNCinv]

/-- Companion bridge for Corollary 23.33: Example 23.4 identifies the projection residual
`Id - P_C` with the proximal operator of the support function `σ_C`, so composing either one with
`J[A]` yields the same set-valued operator. -/
theorem resolvent_comp_projectionResidual_eq_resolvent_comp_supportFunctionProx
    :
    J[A].comp ((id - P_C).toSetValuedOperator) =
      J[A].comp (Prox[σ_C, hσ_C]).toSetValuedOperator := by
  simpa using
    congrArg (fun f : H → H ↦ J[A].comp f.toSetValuedOperator)
      (projectionResidual_eq_scaled_prox_supportFunction_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex (1 : PosReal))

end
