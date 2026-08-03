import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap20.Proposition_20_10
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap25.Definition_25_29
import BauschkeLean.Chap25.Definition_25_39
import BauschkeLean.Chap25.Corollary_25_6

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v

namespace ContinuousLinearMap

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 25.41 concerns the Chapter 25 parallel composition `L ▷ A` and the
  parallel sum `A □ B`.
- `core/canonical`: the reusable owners are `ContinuousLinearMap.adjointImage`,
  `SetValuedOperator.IsMonotone`, and `Maximal SetValuedOperator.IsMonotone`.
- `bridge/view`: the source operators are handled through the inverse identities
  `L ▷ A = (L.adjoint.adjointImage A⁻¹)⁻¹` and
  `(L ▷ A) □ B = ((L.adjoint.adjointImage A⁻¹) + B⁻¹)⁻¹`.
Semantic recall: the owner/API choices below are verified locally against `Definition_25_39`,
`Proposition_20_10`, `Proposition_20_22`, `Example_20_34`, and `Theorem_25_3`. -/

/-- Proposition 25.41 (1): the inverse of the parallel sum `((L ▷ A) □ B)` is
`L ∘ A⁻¹ ∘ L^* + B⁻¹`, realized by the Chapter 16 owner `L.adjoint.adjointImage A⁻¹ + B⁻¹`. -/
theorem inverse_parallelComposition_parallelSum_eq_adjointImage_add_inverse
    (L : H →L[ℝ] K) (A : SetValuedOperator H H) (B : SetValuedOperator K K) :
    ((L ▷ A) □ B)⁻¹ = L.adjoint.adjointImage A⁻¹ + B⁻¹ := by
  rfl

/-- Proposition 25.41 (2): if `A` and `B` are monotone, then `((L ▷ A) □ B)` is monotone. -/
theorem parallelComposition_parallelSum_isMonotone
    (L : H →L[ℝ] K) {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : A.IsMonotone) (hB : B.IsMonotone) :
    ((L ▷ A) □ B).IsMonotone := by
  have hAinv : A⁻¹.IsMonotone := SetValuedOperator.IsMonotone.inverse hA
  have hBinv : B⁻¹.IsMonotone := SetValuedOperator.IsMonotone.inverse hB
  have hsum :
      (L.adjoint.adjointImage A⁻¹ + B⁻¹).IsMonotone := by
    have hsum' :
        (B⁻¹ + L.adjoint.adjointImage A⁻¹).IsMonotone :=
      SetValuedOperator.IsMonotone.add_adjointImage hBinv L.adjoint hAinv
    simpa [add_comm] using hsum'
  have hinv : (((L ▷ A) □ B)⁻¹ : SetValuedOperator K K).IsMonotone := by
    simpa [inverse_parallelComposition_parallelSum_eq_adjointImage_add_inverse] using hsum
  simpa using SetValuedOperator.IsMonotone.inverse hinv

/-- Proposition 25.41 (3): if `A` and `B` are maximally monotone and
`cone (ran A - L^* (ran B)) = closure (span (ran A - L^* (ran B)))`, then
`((L ▷ A) □ B)` is maximally monotone. -/
theorem maximal_parallelComposition_parallelSum_of_cone_range_sub_adjointImage_eq_closure_span
    (L : H →L[ℝ] K) {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hcone :
      cone (A.range - L.adjoint '' B.range) =
        ((Submodule.span ℝ (A.range - L.adjoint '' B.range)).topologicalClosure :
          Set H)) :
    Maximal SetValuedOperator.IsMonotone ((L ▷ A) □ B) := by
  have hAinv : Maximal SetValuedOperator.IsMonotone A⁻¹ := SetValuedOperator.Maximal.inverse hA
  have hBinv : Maximal SetValuedOperator.IsMonotone B⁻¹ := SetValuedOperator.Maximal.inverse hB
  have hcone' :
      cone (A⁻¹.dom - L.adjoint '' B⁻¹.dom) =
        ((Submodule.span ℝ (A⁻¹.dom - L.adjoint '' B⁻¹.dom)).topologicalClosure : Set H) := by
    simpa [SetValuedOperator.dom_inverse] using hcone
  have hsum :
      Maximal SetValuedOperator.IsMonotone (B⁻¹ + L.adjoint.adjointImage A⁻¹) := by
    simpa using
      (SetValuedOperator.Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span
        hBinv hAinv L.adjoint hcone')
  have hinv :
      Maximal SetValuedOperator.IsMonotone (((L ▷ A) □ B)⁻¹ : SetValuedOperator K K) := by
    simpa [inverse_parallelComposition_parallelSum_eq_adjointImage_add_inverse, add_comm] using
      hsum
  simpa using SetValuedOperator.Maximal.inverse hinv

/-- Proposition 25.41 (4): if `A` is maximally monotone and
`cone (ran A - ran L^*) = closure (span (ran A - ran L^*))`, then `L ▷ A` is maximally
monotone. -/
theorem maximal_parallelComposition_of_cone_range_sub_range_adjoint_eq_closure_span
    (L : H →L[ℝ] K) {A : SetValuedOperator H H}
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hcone :
      cone (A.range - Set.range L.adjoint) =
        ((Submodule.span ℝ (A.range - Set.range L.adjoint)).topologicalClosure :
          Set H)) :
    Maximal SetValuedOperator.IsMonotone (L ▷ A) := by
  have hAinv : Maximal SetValuedOperator.IsMonotone A⁻¹ := SetValuedOperator.Maximal.inverse hA
  have hcone' :
      cone (Set.range L.adjoint - A⁻¹.dom) =
        ((Submodule.span ℝ (Set.range L.adjoint - A⁻¹.dom)).topologicalClosure :
          Set H) := by
    have hsub :
        Set.range L.adjoint - A.range = -(A.range - Set.range L.adjoint) := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_neg]
        rcases Set.mem_sub.mp hx with ⟨u, hu, v, hv, huv⟩
        exact Set.mem_sub.mpr ⟨v, hv, u, hu, by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg huv⟩
      · intro hx
        rw [Set.mem_neg] at hx
        rcases Set.mem_sub.mp hx with ⟨u, hu, v, hv, huv⟩
        exact Set.mem_sub.mpr ⟨v, hv, u, hu, by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg huv⟩
    have hclosure_sub :
        ((Submodule.span ℝ (Set.range L.adjoint - A.range)).topologicalClosure : Set H) =
          ((Submodule.span ℝ (-(A.range - Set.range L.adjoint))).topologicalClosure :
            Set H) := by
      exact
        congrArg
          (fun s : Set H ↦ ((Submodule.span ℝ s).topologicalClosure : Set H))
          hsub
    have hneg_closure :
        ((Submodule.span ℝ (-(A.range - Set.range L.adjoint))).topologicalClosure :
            Set H) =
          (((Submodule.span ℝ (A.range - Set.range L.adjoint)).topologicalClosure :
            Submodule ℝ H) : Set H) := by
      rw [Submodule.span_neg]
    let S : Submodule ℝ H :=
      (Submodule.span ℝ (A.range - Set.range L.adjoint)).topologicalClosure
    have hS :
        ((Submodule.span ℝ (A.range - Set.range L.adjoint)).topologicalClosure : Set H) =
          (S : Set H) := by
      rfl
    have hmain :
        cone (Set.range L.adjoint - A.range) =
          ((Submodule.span ℝ (-(A.range - Set.range L.adjoint))).topologicalClosure :
            Set H) := by
      rw [hsub]
      calc
        cone (-(A.range - Set.range L.adjoint)) =
            -cone (A.range - Set.range L.adjoint) := Set.cone_neg_eq_neg_cone
        _ =
            -(S : Set H) := by rw [hcone, hS]
        _ = (S : Set H) := by
              ext x
              constructor
              · intro hx
                rw [Set.mem_neg] at hx
                simpa using S.neg_mem hx
              · intro hx
                rw [Set.mem_neg]
                exact S.neg_mem hx
        _ =
            ((Submodule.span ℝ (-(A.range - Set.range L.adjoint))).topologicalClosure :
              Set H) := hneg_closure.symm
    rw [SetValuedOperator.dom_inverse]
    exact hmain.trans hclosure_sub.symm
  have hadjointImage :
      Maximal SetValuedOperator.IsMonotone (L.adjoint.adjointImage A⁻¹) :=
    SetValuedOperator.Maximal.adjointImage_of_cone_range_sub_eq_closure_span hAinv L.adjoint
      hcone'
  have hparallelInv :
      Maximal SetValuedOperator.IsMonotone ((L ▷ A)⁻¹ : SetValuedOperator K K) := by
    simpa [ContinuousLinearMap.parallelComposition] using hadjointImage
  simpa using SetValuedOperator.Maximal.inverse hparallelInv

end ContinuousLinearMap
