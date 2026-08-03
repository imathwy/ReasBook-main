import BauschkeLean.Chap20.Example_20_34
import BauschkeLean.Chap25.Theorem_25_3

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v

namespace Set

variable {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Negating a set negates its conic hull. -/
theorem cone_neg_eq_neg_cone {C : Set K} :
    cone (-C) = -cone C := by
  have hmap :
      (((ConvexCone.hull ℝ C).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) = -cone C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_neg]
      simpa [Set.cone_def] using hy
    · intro hx
      rw [Set.mem_neg] at hx
      exact ⟨-x, by simpa [Set.cone_def] using hx, by simp⟩
  have hmap' :
      (((ConvexCone.hull ℝ (-C)).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) = -cone (-C) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_neg]
      simpa [Set.cone_def] using hy
    · intro hx
      rw [Set.mem_neg] at hx
      exact ⟨-x, by simpa [Set.cone_def] using hx, by simp⟩
  have hsubset :
      (-C) ⊆ (((ConvexCone.hull ℝ C).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
    intro x hx
    rw [Set.mem_neg] at hx
    exact ⟨-x, by simpa [Set.cone_def] using (ConvexCone.subset_hull hx), by simp⟩
  have hsubset' :
      C ⊆ (((ConvexCone.hull ℝ (-C)).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
    intro x hx
    exact ⟨-x, by simpa using (ConvexCone.subset_hull (by simpa)), by simp⟩
  have hneg :
      cone (-C) ⊆ -cone C := by
    have hneg_map :
        cone (-C) ⊆ (((ConvexCone.hull ℝ C).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
      exact ConvexCone.hull_min hsubset
    exact hneg_map.trans (by simp [hmap])
  have hneg' :
      cone C ⊆ -cone (-C) := by
    have hneg_map :
        cone C ⊆ (((ConvexCone.hull ℝ (-C)).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
      exact ConvexCone.hull_min hsubset'
    exact hneg_map.trans (by simp [hmap'])
  refine Set.Subset.antisymm hneg ?_
  intro x hx
  rw [Set.mem_neg] at hx
  have hx' : -x ∈ cone C := hx
  have hx'' : -x ∈ -cone (-C) := hneg' hx'
  rw [Set.mem_neg] at hx''
  simpa using hx''

end Set

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Corollary 25.6 is the maximal monotonicity of the composite operator `L^* A L`
  under the regularity condition `cone (ran L - dom A) = closure (span (ran L - dom A))`.
- `core/canonical`: the reusable owner is maximal monotonicity, written
  `Maximal IsMonotone`.
- `bridge/view`: the composite operator `L^* A L` is represented by the Chapter 16/20 canonical
  bridge `ContinuousLinearMap.adjointImage`, written `L.adjointImage A`.

Domain-style sampling:
- `Chap20/Definition_20_20.lean`: the owner abstraction is `Maximal IsMonotone`.
- `Chap16/Proposition_16_6.lean`: `ContinuousLinearMap.adjointImage` is the canonical `L^* A L`
  bridge.
- `Chap20/Example_20_34.lean`: the singleton-valued zero operator should come from the canonical
  linear-map owner `(0 : H →L[ℝ] H).toSetValuedOperator`, not from a local wrapper.
- `Chap25/Theorem_25_3.lean`: the present corollary is a source-facing specialization of the
  chapter owner theorem for `A + L^* B L`.

Primitive data: `A`, `L`, maximal monotonicity of `A`, and the regularity hypothesis on
`Set.range L - A.dom`.
Derived API: the maximally monotone conclusion for the canonical bridge `L.adjointImage A`. -/

/-- Corollary 25.6: let `A : K → 2^K` be maximally monotone on a real Hilbert space, let
`L : H →L[ℝ] K`, and suppose
`cone (Set.range L - A.dom) = closure (span (Set.range L - A.dom))`; then `L^* A L`, realized as
`L.adjointImage A`, is maximally monotone. -/
theorem Maximal.adjointImage_of_cone_range_sub_eq_closure_span
    {A : SetValuedOperator K K} (hA : Maximal IsMonotone A)
    (L : H →L[ℝ] K)
    (hcone :
      cone (Set.range L - A.dom) =
        ((Submodule.span ℝ (Set.range L - A.dom)).topologicalClosure : Set K)) :
    Maximal IsMonotone (L.adjointImage A) := by
  let Z : SetValuedOperator H H := (0 : H →L[ℝ] H).toSetValuedOperator
  have hZ : Maximal IsMonotone Z := by
    simpa [Z] using
      ContinuousLinearMap.toSetValuedOperator_isMaximallyMonotone_of_isMonotone
        (0 : H →L[ℝ] H) (by simp [LinearMap.IsMonotone])
  have hZ_dom : Z.dom = Set.univ := by
    ext x
    rw [SetValuedOperator.mem_dom_iff]
    simp [Z, Function.toSetValuedOperator_apply]
  have himage : L '' Z.dom = Set.range L := by
    rw [hZ_dom, Set.image_univ]
  have hsub :
      A.dom - L '' Z.dom = -(Set.range L - A.dom) := by
    rw [himage]
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
  have hcone' :
      cone (A.dom - L '' Z.dom) =
        ((Submodule.span ℝ (A.dom - L '' Z.dom)).topologicalClosure : Set K) := by
    have hclosure_sub :
        ((Submodule.span ℝ (A.dom - L '' Z.dom)).topologicalClosure : Set K) =
          ((Submodule.span ℝ (-(Set.range L - A.dom))).topologicalClosure : Set K) := by
      exact
        congrArg
          (fun s : Set K ↦ ((Submodule.span ℝ s).topologicalClosure : Set K))
          hsub
    have hneg_closure :
        ((Submodule.span ℝ (-(Set.range L - A.dom))).topologicalClosure : Set K) =
          ((Submodule.span ℝ (Set.range L - A.dom)).topologicalClosure : Set K) := by
      rw [Submodule.span_neg]
    have hmain :
        cone (A.dom - L '' Z.dom) =
          ((Submodule.span ℝ (-(Set.range L - A.dom))).topologicalClosure : Set K) := by
      rw [hsub]
      calc
        cone (-(Set.range L - A.dom)) = -cone (Set.range L - A.dom) :=
            Set.cone_neg_eq_neg_cone
        _ = -((Submodule.span ℝ (Set.range L - A.dom)).topologicalClosure : Set K) := by
          rw [hcone]
        _ = ((Submodule.span ℝ (Set.range L - A.dom)).topologicalClosure : Set K) := by
          ext x
          constructor
          · intro hx
            rw [Set.mem_neg] at hx
            simpa using ((Submodule.span ℝ (Set.range L - A.dom)).topologicalClosure.neg_mem hx)
          · intro hx
            rw [Set.mem_neg]
            exact ((Submodule.span ℝ (Set.range L - A.dom)).topologicalClosure.neg_mem hx)
        _ = ((Submodule.span ℝ (-(Set.range L - A.dom))).topologicalClosure : Set K) := by
          exact hneg_closure.symm
    exact hmain.trans hclosure_sub.symm
  have hzero_add : Z + L.adjointImage A = L.adjointImage A := by
    ext x u
    constructor
    · intro hu
      rcases Set.mem_add.mp hu with ⟨u₀, hu₀, v, hv, huv⟩
      have hu₀' : u₀ = 0 := by
        simpa [Z, Function.toSetValuedOperator_apply] using hu₀
      rcases hu₀' with rfl
      have huv' : v = u := by simpa using huv
      simpa [huv'] using hv
    · intro hu
      exact Set.mem_add.mpr ⟨0, by simp [Z, Function.toSetValuedOperator_apply], u, hu, by simp⟩
  simpa [hzero_add] using
    Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span hZ hA L hcone'

end SetValuedOperator
