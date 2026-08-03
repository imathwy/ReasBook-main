import Mathlib
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap18.Theorem_18_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section FrechetDifferentiabilityLocus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 21.28 is the existential subset statement inside
  `interior (effectiveDomain f)`.
- `core/canonical`: Chapter 18 already owns this locus as `sourceDifferentiabilitySet f` and its
  closure-subtype view `sourceDifferentiabilitySetInClosure f`.
- `bridge/view`: Proposition 16.27 identifies interior effective-domain points of a `Γ₀(H)`
  function as source continuity points, which is exactly the extra input needed to invoke the
  Chapter 18 dense-`Gδ` owner theorem.

This file therefore keeps the source-facing existential corollary but witnesses it with the
canonical Chapter 18 differentiability locus instead of rebuilding a parallel subset API. -/

/-- Corollary 21.28: if `f ∈ Γ₀(H)` and `interior (effectiveDomain f)` is nonempty, then there
exists a subset `C ⊆ interior (effectiveDomain f)` whose closure-subtype view is a dense `Gδ`
subset of `closure (effectiveDomain f)`, and such that the finite representative of `f` is
Fréchet differentiable at every point of `C`. -/
theorem exists_dense_isGδ_subset_interior_effectiveDomain_differentiableAt_toReal_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hinter : (interior (effectiveDomain f)).Nonempty) :
    ∃ C : Set H,
      C ⊆ interior (effectiveDomain f) ∧
      ∃ hDense : Dense (Subtype.val ⁻¹' C : Set (closure (effectiveDomain f))),
        ∃ hIsGδ : IsGδ (Subtype.val ⁻¹' C : Set (closure (effectiveDomain f))),
          ∀ x ∈ C, DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := by
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  have hcont : (cont f).Nonempty := by
    rcases hinter with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [ContinuousPoint, ContinuousAtInEffectiveDomain] using
      continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
  have hdiff :
      Dense (sourceDifferentiabilitySetInClosure f) ∧
        IsGδ (sourceDifferentiabilitySetInClosure f) :=
    dense_isGδ_differentiableAt_toReal_in_closure_effectiveDomain_of_exists_continuityPoint
      f hconv hcont
  refine ⟨sourceDifferentiabilitySet f, ?_, ?_⟩
  · intro x hx
    exact mem_interior_effectiveDomain_of_mem_cont ((mem_sourceDifferentiabilitySet_iff f x).1 hx).1
  · refine ⟨?_, ?_, ?_⟩
    · simpa [sourceDifferentiabilitySetInClosure] using hdiff.1
    · simpa [sourceDifferentiabilitySetInClosure] using hdiff.2
    · intro x hx
      exact ((mem_sourceDifferentiabilitySet_iff f x).1 hx).2

end FrechetDifferentiabilityLocus

end ERealFunction
