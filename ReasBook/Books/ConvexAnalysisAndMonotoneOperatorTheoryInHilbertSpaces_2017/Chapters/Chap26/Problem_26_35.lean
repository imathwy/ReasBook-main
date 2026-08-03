import Mathlib
import BauschkeLean.Chap19.Example_19_3
import BauschkeLean.Chap23.Proposition_23_18
import BauschkeLean.Chap26.Problem_26_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator

universe u v

noncomputable section

namespace SetValuedOperator

open ContinuousLinearMap

variable {I : Type v} {H : Type u} {K : I → Type u}
variable [Fintype I]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

-- Semantic recall: Chapter 19 already packages a finite family `Lᵢ : H →L[ℝ] Kᵢ` into the
-- canonical direct-sum owner `ContinuousLinearMap.toLpOperator`, Chapter 23 already owns the
-- coordinatewise direct-sum operator `SetValuedOperator.familyOperator`, and Problem 26.28
-- provides the single-operator primal/dual solution-set owners. This file should reuse those
-- owners directly.

/- Source/core/bridge triage:
- `source-facing`: the primal and dual solution sets for the finite-family inclusion problem.
- `core/canonical`: the single-operator owner from `Problem_26_28`, together with the chapter's
  canonical `translate`, `inverse`, `adjointImage`, `toLpOperator`, and `familyOperator` APIs.
- `bridge/view`: the primal side uses the single-operator owner through `toLpOperator` and
  `familyOperator`, then rewrites the resulting adjoint image as the explicit finite sum.
  The dual side keeps the source-facing coordinatewise quantifier because collapsing it to the
  single-operator dual owner would strengthen the semantics to a common primal witness. -/

private def lpFamily (w : ∀ i, K i) : lp K 2 :=
  (lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 w)

omit [∀ i, CompleteSpace (K i)] in
@[simp] private theorem lpFamily_apply (w : ∀ i, K i) (i : I) :
    lpFamily w i = w i := by
  change ((lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 w)) i = w i
  rw [coe_lpPiLpₗᵢ_symm]

private def adjointImageFinsetSum
    (s : Finset I) (L : ∀ i, H →L[ℝ] K i) (C : ∀ i, Set (K i)) : Set H :=
  s.sum fun i ↦ (L i).adjoint '' C i

omit [Fintype I] in
private theorem sum_adjoint_image_mem_finsetSum
    (s : Finset I) (L : ∀ i, H →L[ℝ] K i) (C : ∀ i, Set (K i)) (w : ∀ i, K i)
    (hw : ∀ i ∈ s, w i ∈ C i) :
    s.sum (fun i ↦ (L i).adjoint (w i)) ∈ adjointImageFinsetSum s L C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [adjointImageFinsetSum]
  | @insert i s hi ih =>
      have hs :
          (L i).adjoint (w i) + s.sum (fun j ↦ (L j).adjoint (w j)) ∈
            ((L i).adjoint '' C i + adjointImageFinsetSum s L C) := by
        refine Set.mem_add.2 ?_
        refine ⟨(L i).adjoint (w i), ?_, s.sum (fun j ↦ (L j).adjoint (w j)), ?_, rfl⟩
        · exact ⟨w i, hw i (by simp), rfl⟩
        · exact ih (fun j hj ↦ hw j (by simp [hj]))
      simpa [adjointImageFinsetSum, Finset.sum_insert, hi] using hs

omit [Fintype I] in
private theorem exists_family_of_mem_finsetSum_adjoint_image
    (s : Finset I) (L : ∀ i, H →L[ℝ] K i) (C : ∀ i, Set (K i)) (u : H)
    (hu : u ∈ adjointImageFinsetSum s L C) :
    ∃ w : ∀ i, K i,
      (∀ i ∈ s, w i ∈ C i) ∧
      (∀ i ∉ s, w i = 0) ∧
      s.sum (fun i ↦ (L i).adjoint (w i)) = u := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty =>
      have hu0 : u = 0 := by
        simpa [adjointImageFinsetSum] using hu
      refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
      · intro i hi
        simp at hi
      · intro i hi
        rfl
      · simp [hu0]
  | @insert i s hi ih =>
      have hu' : u ∈ ((L i).adjoint '' C i + adjointImageFinsetSum s L C) := by
        simpa [adjointImageFinsetSum, Finset.sum_insert, hi] using hu
      rw [Set.mem_add] at hu'
      rcases hu' with ⟨ui, hui, us, hus, hu_eq⟩
      rcases hui with ⟨wi, hwi, rfl⟩
      rcases ih us hus with ⟨w, hw_mem, hw_zero, hw_sum⟩
      let w' : ∀ j, K j := fun j ↦ if h : j = i then h ▸ wi else w j
      refine ⟨w', ?_, ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa [w'] using hwi
        · have hjs : j ∈ s := by
            simpa [hji] using hj
          simpa [w', hji] using hw_mem j hjs
      · intro j hj
        by_cases hji : j = i
        · exact (hj (hji ▸ Finset.mem_insert_self i s)).elim
        · have hjs : j ∉ s := by
            intro hjs
            exact hj (Finset.mem_insert.mpr <| Or.inr hjs)
          simpa [w', hji] using hw_zero j hjs
      · calc
          (insert i s).sum (fun j ↦ (L j).adjoint (w' j))
              = (L i).adjoint wi + s.sum (fun j ↦ (L j).adjoint (w j)) := by
                  rw [Finset.sum_insert hi]
                  congr 1
                  · simp [w']
                  · refine Finset.sum_congr rfl ?_
                    intro j hj
                    have hji : j ≠ i := by
                      intro hji
                      exact hi (hji ▸ hj)
                    simp [w', hji]
          _ = (L i).adjoint wi + us := by
                rw [hw_sum]
          _ = u := hu_eq

/-- Problem 26.35 (1): for a finite family of real Hilbert spaces `Kᵢ`, the primal
solution set consists of the points `x : H` solving
`z ∈ A x + ∑ᵢ Lᵢ^*(Bᵢ(Lᵢx - rᵢ))`. -/
def finite_family_composite_primal_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i) : Set H :=
  composite_primal_inclusion_solution_set z A r (familyOperator B) (toLpOperator L)

/-- Membership in `finite_family_composite_primal_inclusion_solution_set` is exactly the primal
inclusion `z ∈ A x + ∑ᵢ Lᵢ^*(Bᵢ(Lᵢx - rᵢ))`. -/
@[simp] theorem mem_finite_family_composite_primal_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i) (x : H) :
    x ∈ finite_family_composite_primal_inclusion_solution_set z A r B L ↔
      z ∈ A x + ∑ i, (L i).adjoint '' (B i (L i x - r i)) := by
  constructor
  · intro hx
    have hx' :
        z ∈ A x + (toLpOperator L).adjoint ''
          familyOperator B (toLpOperator L x - r) := by
      simpa [finite_family_composite_primal_inclusion_solution_set] using
        (mem_composite_primal_inclusion_solution_set
          z A r (familyOperator B) (toLpOperator L) x).1 hx
    rw [Set.mem_add] at hx' ⊢
    rcases hx' with ⟨a, ha, b, hb, hab⟩
    rcases hb with ⟨v, hv, rfl⟩
    refine ⟨a, ha, ∑ i, (L i).adjoint (v i), ?_, ?_⟩
    · exact sum_adjoint_image_mem_finsetSum Finset.univ L
        (fun i ↦ B i (L i x - r i)) (fun i ↦ v i)
        (fun i _ ↦ by
          simpa [mem_familyOperator_iff, toLpOperator_apply] using hv i)
    · simpa [toLpOperator_adjoint_apply_eq_sum] using hab
  · intro hx
    rw [Set.mem_add] at hx
    rcases hx with ⟨a, ha, b, hb, hab⟩
    rcases exists_family_of_mem_finsetSum_adjoint_image
        Finset.univ L (fun i ↦ B i (L i x - r i)) b hb with
      ⟨w, hw_mem, _, hw_sum⟩
    let v : lp K 2 := lpFamily w
    have hv :
        v ∈ familyOperator B (toLpOperator L x - r) := by
      rw [mem_familyOperator_iff]
      intro i
      simpa [v, toLpOperator_apply] using hw_mem i (by simp)
    have hx' :
        z ∈ A x + (toLpOperator L).adjoint ''
          familyOperator B (toLpOperator L x - r) := by
      refine ⟨a, ha, (toLpOperator L).adjoint v, ⟨v, hv, rfl⟩, ?_⟩
      calc
        a + (toLpOperator L).adjoint v
            = a + ∑ i, (L i).adjoint (w i) := by
                simp [v, toLpOperator_adjoint_apply_eq_sum]
        _ = a + b := by simp [hw_sum]
        _ = z := hab
    exact
      (mem_composite_primal_inclusion_solution_set
        z A r (familyOperator B) (toLpOperator L) x).2 <| by
      simpa [finite_family_composite_primal_inclusion_solution_set] using hx'

/-- Problem 26.35 (2): for the same finite family, the dual solution set consists of the points
`v : lp K 2`, viewed as the canonical Hilbert direct sum `⨁ᵢ Kᵢ`, such that
`∀ i, -rᵢ ∈ -Lᵢ(A⁻¹(z - ∑ⱼ Lⱼ^* vⱼ)) + Bᵢ⁻¹(vᵢ)`. -/
def finite_family_composite_dual_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i) : Set (lp K 2) :=
  {v | ∀ i : I,
    -r i ∈ ((-L i) '' (A⁻¹ (z - (toLpOperator L).adjoint v))) + ((B i)⁻¹ (v i))}

/-- Membership in `finite_family_composite_dual_inclusion_solution_set` is exactly the dual
inclusion `∀ i, -rᵢ ∈ -Lᵢ(A⁻¹(z - ∑ⱼ Lⱼ^* vⱼ)) + Bᵢ⁻¹(vᵢ)`. -/
@[simp] theorem mem_finite_family_composite_dual_inclusion_solution_set
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i) (v : lp K 2) :
    v ∈ finite_family_composite_dual_inclusion_solution_set z A r B L ↔
      ∀ i : I,
        -r i ∈ ((-L i) '' (A⁻¹ (z - ∑ j, (L j).adjoint (v j)))) + ((B i)⁻¹ (v i)) := by
  simp [finite_family_composite_dual_inclusion_solution_set, toLpOperator_adjoint_apply_eq_sum]

end SetValuedOperator
