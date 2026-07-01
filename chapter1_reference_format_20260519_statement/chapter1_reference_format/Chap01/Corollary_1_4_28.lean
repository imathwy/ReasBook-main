import chapter1_reference_format.Chap01.Proposition_1_4_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open List

section

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Corollary 1.4.28: for two subspaces `V₁` and `V₂` of a finite-dimensional `K`-space `V`, the
following are equivalent: `V = V₁ ⊕ V₂`; the dimensions add and `V₁ ∩ V₂ = {0}`; the dimensions
add and `V = V₁ + V₂`. -/
-- Proof sketch: reuse the chapter bridge
-- `subspace_isCompl_iff_sup_eq_top_and_inf_eq_bot` for the direct-sum condition. If `V₁` and `V₂`
-- are complementary, `Submodule.finrank_add_eq_of_isCompl` gives the dimension formula. Conversely,
-- if the dimensions add and the intersection is trivial, `Submodule.eq_top_of_disjoint` forces the
-- sum to be the whole space; if the dimensions add and the sum is the whole space, then
-- `Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂` forces the intersection to have dimension zero.
theorem subspace_isCompl_tfae_finrank_criteria (V₁ V₂ : Submodule K V) :
    List.TFAE
      [ IsCompl V₁ V₂
      , Module.finrank K V = Module.finrank K V₁ + Module.finrank K V₂ ∧ V₁ ⊓ V₂ = ⊥
      , Module.finrank K V = Module.finrank K V₁ + Module.finrank K V₂ ∧ V₁ ⊔ V₂ = ⊤
      ] := by
  rw [tfae_cons_cons]
  constructor
  · constructor
    · intro h
      exact ⟨(Submodule.finrank_add_eq_of_isCompl h).symm, h.inf_eq_bot⟩
    · rintro ⟨hfin, hinf⟩
      have hsup : V₁ ⊔ V₂ = ⊤ :=
        Submodule.eq_top_of_disjoint V₁ V₂ (le_of_eq hfin) <| by
          rw [disjoint_iff, hinf]
      exact (subspace_isCompl_iff_sup_eq_top_and_inf_eq_bot V₁ V₂).2 ⟨hsup, hinf⟩
  · rw [tfae_cons_cons]
    constructor
    · constructor
      · rintro ⟨hfin, hinf⟩
        refine ⟨hfin, Submodule.eq_top_of_disjoint V₁ V₂ (le_of_eq hfin) ?_⟩
        rw [disjoint_iff, hinf]
      · rintro ⟨hfin, hsup⟩
        refine ⟨hfin, ?_⟩
        rw [← Submodule.finrank_eq_zero]
        have h := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
        rw [hsup, finrank_top, ← hfin] at h
        omega
    · exact tfae_singleton _

end
