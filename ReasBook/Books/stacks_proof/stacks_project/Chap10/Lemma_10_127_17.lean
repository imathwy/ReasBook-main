import stacks_proof.stacks_project.Chap10.Lemma_10_127_17.Index
import Mathlib.Tactic.StacksAttribute

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

-- Proof sketch: the verified prefix above gives the descended stage model `P₀` over one source
-- stage `Rᵢ₀`. The remaining source-faithful step is to replace the raw tensor stages
-- `P₀ ⊗[Rᵢ₀] Rⱼ` by canonical target stages in the universe of `S` and transport the tensor-tail
-- transition isomorphisms through those stage identifications.
/-- Chap10 Lemma 10 127 17: if `f : R →+* S` is of finite presentation, then `f` is the direct limit of a
directed system of ring maps `R_λ → S_λ` such that each `R_λ` is of finite type over `ℤ`, each
`S_λ` is of finite type over `R_λ`, and for every `λ ≤ μ` the canonical map
`S_λ ⊗[R_λ] R_μ → S_μ` is bijective, hence an isomorphism. -/
@[stacks 00R0]
theorem exists_directedFinitePresentationHomApproximation (f : R →+* S)
    (hf : f.FinitePresentation) :
    ∃ A : DirectedFiniteTypeHomApproximation.{u, v, u} f, A.HasBijectiveBaseChangeTransitions := by
  classical
  letI := f.toAlgebra
  obtain ⟨A₀, i₀, P₀, _, _, _, eNonempty⟩ := exists_descended_finitePresentation_stage_model f hf
  obtain ⟨e⟩ := eNonempty
  refine ⟨by
      simpa [RingHom.algebraMap_toAlgebra] using
        (shrinkRawTailApproximation A₀ i₀ P₀ e), ?_⟩
  -- Route correction: the old range-kernel route asks for an over-strong kernel transport
  -- equality. The replacement witness keeps the raw tensor stages and moves them into the target
  -- universe by `Shrink`, so base change is inherited from raw tensor cancellation.
  intro i j h
  -- Proof comment: the helper identifies this shrunken base-change map with a conjugate of the
  -- raw tensor-cancellation equivalence.
  simpa [RingHom.algebraMap_toAlgebra] using
    (shrinkRawTailStageBaseChangeMap_bijective A₀ i₀ P₀ e h)
