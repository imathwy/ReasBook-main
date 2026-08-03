module

public import Topology_Munkres_2000.Book.Definition_38_1.Equivalence

@[expose] public section

universe u v w₁ w₂

namespace Compactification

variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
  [T2Space Z]

/-- Helper for Lemma 38.1: an embedded compactification extending `h` has range equal to the
closure of the range of `h`. -/
lemma range_eq_closure_range_of_isEmbedding_extension (h : X → Z)
    (C : Compactification.{u, w₁} X) (H : C → Z) (hH : Topology.IsEmbedding H)
    (hExt : ∀ x, H (C x) = h x) : Set.range H = closure (Set.range h) := by
  -- Density forces every value of `H` into the closed set `closure (range h)`.
  apply Set.Subset.antisymm
  · rintro z ⟨y, rfl⟩
    have hclosed : IsClosed {y : C | H y ∈ closure (Set.range h)} :=
      isClosed_closure.preimage hH.continuous
    exact isClosed_property C.isDenseEmbedding.dense hclosed (fun x ↦ by
      rw [hExt x]
      exact subset_closure (Set.mem_range_self x)) y
  -- Conversely, the compact range of `H` is closed and contains `range h`.
  · apply closure_minimal
    · rintro z ⟨x, rfl⟩
      exact ⟨C x, hExt x⟩
    · exact (isCompact_range hH.continuous).isClosed

/-- Compactifications embedded in the same Hausdorff space are equivalent when their
embeddings agree on the original space. -/
theorem equivalent_of_isEmbedding_extensions (h : X → Z)
    (C₁ : Compactification.{u, w₁} X) (C₂ : Compactification.{u, w₂} X)
    (H₁ : C₁ → Z) (H₂ : C₂ → Z) (hH₁ : Topology.IsEmbedding H₁)
    (hH₂ : Topology.IsEmbedding H₂) (h₁ : ∀ x, H₁ (C₁ x) = h x)
    (h₂ : ∀ x, H₂ (C₂ x) = h x) : Equivalent C₁ C₂ := by
  classical
  -- Both embeddings identify their compactifications with the same closed subset of `Z`.
  have hrange₁ := range_eq_closure_range_of_isEmbedding_extension h C₁ H₁ hH₁ h₁
  have hrange₂ := range_eq_closure_range_of_isEmbedding_extension h C₂ H₂ hH₂ h₂
  have hranges : Set.range H₁ = Set.range H₂ := hrange₁.trans hrange₂.symm
  let e : C₁ ≃ₜ C₂ :=
    (hH₁.toHomeomorph.trans (Homeomorph.setCongr hranges)).trans hH₂.toHomeomorph.symm
  -- The common-range homeomorphism carries each embedded point of `X` to the matching point.
  rw [equivalent_iff]
  refine ⟨e, ?_⟩
  intro x
  apply hH₂.toHomeomorph.injective
  ext
  simp only [e, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    Topology.IsEmbedding.toHomeomorph_apply_coe, Homeomorph.setCongr]
  exact h₁ x |>.trans (h₂ x).symm

end Compactification

end
