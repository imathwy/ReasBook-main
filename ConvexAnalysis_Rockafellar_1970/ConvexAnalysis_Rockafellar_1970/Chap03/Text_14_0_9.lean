import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped PolarCone Rockafellar

universe u v w

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {M : Type u} [AddCommGroup M] [Module 𝕜 M]
variable {N : Type v} [AddCommMonoid N] [Module 𝕜 N]
variable [HasLinearPairing M N 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.9 identifies the polar cone `Kᵒ` of a nonempty closed convex cone
  `K` with the normal cone to `K` at the origin, and then states the converse identification of
  `K` with the normal cone to `Kᵒ` at the origin.
- `core/canonical`: the owner abstractions already present in the project are the source-facing
  set-valued constructions `polarCone` and `normalCone`, together with the chapter owner predicate
  `Set.IsConvexCone ℝ K` for the converse bipolar clause.
- `bridge/view`: the theorem is already an equality between these two canonical source-level set
  constructions, with the chapter bipolar theorem `polarCone_polarCone_eq` providing the converse
  clause. No extra wrapper or packaged interface is mathematically justified.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff` from `Text_14_0_1`;
- `normalCone` and `mem_normalCone_iff` from `Definition_2_7_10`;
- `polarCone_polarCone_eq` from `Theorem_14_1` as the chapter bipolar owner behind the converse
  clause;
- the closure argument `IsClosed.closure_subset_iff` and the continuity owner
  `ContinuousWithinAt.mem_closure_image` used to recover `0 ∈ K` from nonemptiness, closedness,
  and the cone property.

Primitive data vs derived API:
- primitive input for the first clause: a set `K : Set M` together with the canonical datum
  `0 ∈ K`;
- textbook route to that primitive data: nonemptiness and closedness of the cone, used only to
  recover `0 ∈ K`;
- derived content: the two source-facing equalities identifying `Kᵒ` and `K` as normal cones at
  the origin.

Layer target: `source-facing`.

The public API is split into the two atomic source clauses and uses the chapter notation `Kᵒ`
directly on the theorem surface. The first clause is stated at the weakest canonical level
`0 ∈ K`; the textbook nonempty/closed-cone assumptions are kept only in a thin companion theorem
that derives this membership. The first clause therefore lives directly at the pairing owner layer
`[HasLinearPairing M N 𝕜]`, while the converse bipolar clause is isolated below in the stronger
real complete-inner-product setting forced by the currently available upstream theorem
`polarCone_polarCone_eq`.
-/

/-- Text 14.0.9 (1): if a cone `K` contains the origin, then its polar cone `Kᵒ` is the normal
cone to `K` at the origin. The textbook nonempty/closed-cone formulation is recovered by the
companion theorem `polarCone_eq_normalCone_at_zero_of_nonempty_closed_cone`. -/
-- Proof sketch: unfold `normalCone K 0`; once `0 ∈ K`, the defining inequalities reduce directly
-- to the polar inequalities from `polarCone`.
theorem polarCone_eq_normalCone_at_zero
    (K : Set M) (h0 : (0 : M) ∈ K) :
    (Kᵒ[𝕜] : Set N) = N[𝕜](0 | K) := by
  ext xStar
  rw [mem_polarCone_iff, mem_normalCone_iff]
  simp [h0]

end

section

open scoped PolarCone Rockafellar

universe u v

variable {M : Type u} [TopologicalSpace M] [AddCommGroup M] [Module ℝ M] [ContinuousSMul ℝ M]
variable {N : Type v} [AddCommMonoid N] [Module ℝ N]
variable [HasLinearPairing M N ℝ]

private theorem zero_mem_of_nonempty_closed_cone
    (K : Set M) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_cone : Set.IsCone ℝ K) :
    (0 : M) ∈ K := by
  obtain ⟨x, hx⟩ := hK_nonempty
  let f : ℝ → M := fun t ↦ t • x
  have hfK : closure (f '' Set.Ioi (0 : ℝ)) ⊆ K :=
    hK_closed.closure_subset_iff.2 <| by
      rintro _ ⟨t, ht, rfl⟩
      exact hK_cone ht hx
  have hf_cont : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 := by
    fun_prop
  simpa [f] using hfK (hf_cont.mem_closure_image <| by simp)

/-- Text 14.0.9 (1), textbook hypothesis form: a nonempty closed cone contains the origin, so the
main origin-based normal-cone identification applies. -/
theorem polarCone_eq_normalCone_at_zero_of_nonempty_closed_cone
    (K : Set M) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_cone : Set.IsCone ℝ K) :
    (Kᵒ[ℝ] : Set N) = N[ℝ](0 | K) := by
  exact polarCone_eq_normalCone_at_zero K
    (zero_mem_of_nonempty_closed_cone K hK_nonempty hK_closed hK_cone)

end

section

open scoped PolarCone Rockafellar

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Text 14.0.9 (2): for a nonempty closed convex cone `K ⊆ R^n`, the normal cone to `Kᵒ` at the
origin is `K`. -/
-- Proof sketch: rewrite `normalCone Kᵒ 0` as `Kᵒᵒ` using the first clause applied to `Kᵒ`, then
-- apply the bipolar theorem `polarCone_polarCone_eq`.
theorem normalCone_polarCone_at_zero_eq
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK : Set.IsConvexCone ℝ K) :
    N[ℝ]((0 : E) | Kᵒ[ℝ]) = K := by
  calc
    N[ℝ]((0 : E) | Kᵒ[ℝ]) = ((Kᵒ[ℝ] : Set E)ᵒ[ℝ] : Set E) := by
      symm
      exact polarCone_eq_normalCone_at_zero (K := (Kᵒ[ℝ] : Set E))
        (zero_mem_polarCone K)
    _ = K := polarCone_polarCone_eq K hK_nonempty hK_closed hK

end
