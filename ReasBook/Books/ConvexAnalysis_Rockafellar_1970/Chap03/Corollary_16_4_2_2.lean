import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_16_4_2_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise PolarCone

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜]

/-!
Source/core/bridge triage:
- source-facing statement: Corollary 16.4.2.2, phrased with intersections, closure, and finite
  sums of polars.
- core/canonical: a scalar-generic pairing-layer corollary that takes the bipolar-closure bridge
  as primitive input.
-/

-- Proof sketch:
-- - Nonempty case: apply `polarCone_sum_eq_iInter` to `P i := (K i)ᵒ[𝕜]`, rewrite each double
--   polar by `hbipolar`, then apply `hbipolar` once more to `∑ i, P i`.
-- - Empty-index case: if some `K i = ∅`, then `⋂ i, closure (K i) = ∅`, so the left side is
--   `∅ᵒ = univ`; the right side is also `univ` because `(K i)ᵒ = univ` and a finite sum with one
--   `univ` summand is `univ`.
/-- Corollary 16.4.2.2 at the scalar-generic pairing layer: for a finite family of convex cones,
the polar of the intersection of their closures is the closure of the finite sum of their polar
cones, provided the bipolar-closure bridge is available at this scalar layer. -/
theorem polarCone_iInter_closure_eq_closure_sum_polarCone
    (hbipolar : ∀ {S : Set E}, S.Nonempty → Set.IsConvexCone 𝕜 S →
      ((Sᵒ[𝕜] : Set E)ᵒ[𝕜] = closure S))
    (K : ι → Set E)
    (hK : ∀ i, Set.IsConvexCone 𝕜 (K i)) :
    (⋂ i, closure (K i))ᵒ[𝕜] = closure (∑ i, ((K i)ᵒ[𝕜] : Set E)) := by
  classical
  let P : ι → Set E := fun i ↦ (K i)ᵒ[𝕜]
  have hP_nonempty : ∀ i, (P i).Nonempty := fun i ↦ ⟨0, by
    simp [P]⟩
  have hP_zero : ∀ i, (0 : E) ∈ P i := fun i ↦ by
    simp [P]
  have hP_convex : ∀ i, Convex 𝕜 (P i) := fun i ↦ by
    simpa [P] using convex_polarCone (K i)
  have hP_cone : ∀ i, Set.IsCone 𝕜 (P i) := fun i ↦ by
    simpa [P] using isCone_polarCone (K i)
  by_cases hK_nonempty : ∀ i, (K i).Nonempty
  · have hdouble : ∀ i, ((K i)ᵒ[𝕜])ᵒ[𝕜] = closure (K i) := fun i ↦ by
      exact hbipolar (hK_nonempty i) (hK i)
    have hsum : (∑ i, P i)ᵒ[𝕜] = ⋂ i, closure (K i) := by
      calc
        (∑ i, P i)ᵒ[𝕜] = ⋂ i, ((K i)ᵒ[𝕜])ᵒ[𝕜] := by
          simpa [P] using polarCone_sum_eq_iInter P (fun i ↦ ⟨hP_nonempty i, hP_cone i⟩)
        _ = ⋂ i, closure (K i) := by
          ext x
          simp [hdouble]
    have hsum_nonempty : (∑ i, P i).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Set.mem_fintype_sum]
      exact ⟨fun _ ↦ 0, hP_zero, by simp⟩
    have hsum_convex : Convex 𝕜 (∑ i, P i) := by
      exact convex_sum P (fun i _ ↦ hP_convex i)
    have hsum_cone : Set.IsCone 𝕜 (∑ i, P i) := by
      exact Set.IsCone.fintype_sum hP_cone
    have hsum_convexCone : Set.IsConvexCone 𝕜 (∑ i, P i) := ⟨hsum_cone, hsum_convex⟩
    calc
      (⋂ i, closure (K i))ᵒ[𝕜] = ((∑ i, P i)ᵒ[𝕜])ᵒ[𝕜] := by
        rw [hsum.symm]
      _ = closure (∑ i, P i) := by
        exact hbipolar hsum_nonempty hsum_convexCone
      _ = closure (∑ i, (K i)ᵒ[𝕜]) := by
        simp [P]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (K i).Nonempty := by
      simpa only [not_forall] using hK_nonempty
    have hKi : K i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    have hInter_empty : (⋂ j, closure (K j)) = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ closure (K i) := Set.mem_iInter.mp hx i
        simp [hKi] at hx'
      · simp
    have hsum_univ : (∑ j, P j) = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rw [Set.mem_fintype_sum]
        refine ⟨Pi.single i x, ?_, ?_⟩
        · intro j
          by_cases hj : j = i
          · subst hj
            simp [P, hKi]
          · simpa [Pi.single, hj] using hP_zero j
        · simp
    calc
      (⋂ j, closure (K j))ᵒ[𝕜] = Set.univ := by
        ext x
        rw [mem_polarCone_iff]
        simp [hInter_empty]
      _ = closure (∑ j, P j) := by
        rw [hsum_univ]
        simp
      _ = closure (∑ j, (K j)ᵒ[𝕜]) := by
        simp [P]

end
