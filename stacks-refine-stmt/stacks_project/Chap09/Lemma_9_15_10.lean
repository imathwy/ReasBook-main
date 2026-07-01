import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {K : Type u} {L : Type v} {E : Type w}
variable [Field K] [Field L] [Field E]
variable [Algebra K L] [Algebra K E]

/-- Any two `K`-embeddings of a normal extension `L/K` into a common extension field differ by a
`K`-automorphism of `L`. This is the source-facing bridge obtained by applying
`Normal.algHomEquivAut` after using one embedding `τ` to view `E` as an `L`-algebra. -/
theorem algHom_eq_comp_gal_of_normal [Normal K L] (τ ψ : L →ₐ[K] E) :
    ∃ σ : Gal(L/K), ψ = τ.comp σ.toAlgHom := by
  letI : Algebra L E := τ.toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x ↦ (τ.commutes x).symm
  refine ⟨Normal.algHomEquivAut K E L ψ, ?_⟩
  change ψ = τ.comp ((Normal.algHomEquivAut K E L) ψ).toAlgHom
  simpa using ((Normal.algHomEquivAut K E L).symm_apply_apply ψ).symm

/-- Lemma 9.15.10: for an algebraic normal extension `L/K` and any field extension `E/K`, either
there is no `K`-embedding `L →ₐ[K] E`, or there is one embedding `τ` such that every
`K`-embedding `L →ₐ[K] E` is of the form `τ ∘ σ` for some `σ ∈ Gal(L/K)`. -/
theorem isEmpty_or_exists_embedding_generating_all_by_galois [Normal K L] :
    IsEmpty (L →ₐ[K] E) ∨
      ∃ τ : L →ₐ[K] E, ∀ ψ : L →ₐ[K] E, ∃ σ : Gal(L/K), ψ = τ.comp σ.toAlgHom := by
  classical
  by_cases h : IsEmpty (L →ₐ[K] E)
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨τ⟩ := not_isEmpty_iff.mp h
    refine ⟨τ, ?_⟩
    intro ψ
    exact algHom_eq_comp_gal_of_normal τ ψ

end
