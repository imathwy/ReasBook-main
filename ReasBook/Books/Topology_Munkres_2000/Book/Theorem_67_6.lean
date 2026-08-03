module

public import Topology_Munkres_2000.Book.Lemma_67_5

public section

universe u v w x

namespace AddMonoidHom.IsExternalDirectSum

/-- Helper for Theorem 67.6: mutually inverse restrictions on an external direct-sum family
force the corresponding composite to be the identity. -/
private lemma comp_eq_id_of_restrictions
    {J : Type v} {G : Type u} {G' : Type w} {Gα : J → Type x}
    [∀ α, AddCommGroup (Gα α)] [AddCommGroup G] [AddCommGroup G']
    (i : ∀ α, Gα α →+ G) [IsExternalDirectSum i]
    (i' : ∀ α, Gα α →+ G') (f : G →+ G') (g : G' →+ G)
    (hf : ∀ α, f.comp (i α) = i' α) (hg : ∀ α, g.comp (i' α) = i α) :
    g.comp f = AddMonoidHom.id G := by
  obtain ⟨h, -, h_unique⟩ := existsUnique_extension i i
  -- Both the composite and the identity restrict to `i α`, so uniqueness identifies them.
  calc
    g.comp f = h := h_unique (g.comp f) fun α ↦ by
      rw [AddMonoidHom.comp_assoc, hf α, hg α]
    _ = AddMonoidHom.id G := (h_unique (AddMonoidHom.id G) fun α ↦ by
      rw [AddMonoidHom.id_comp]).symm

/-- Theorem 67.6 (Uniqueness of direct sums). Two external direct-sum presentations of
the same family of abelian groups are related by a unique additive equivalence commuting
with every inclusion. -/
theorem existsUnique_addEquiv
    {J : Type v} {G : Type u} {G' : Type w} {Gα : J → Type x}
    [∀ α, AddCommGroup (Gα α)] [AddCommGroup G] [AddCommGroup G']
    (i : ∀ α, Gα α →+ G) [IsExternalDirectSum i]
    (i' : ∀ α, Gα α →+ G') [IsExternalDirectSum i'] :
    ∃! φ : G ≃+ G', ∀ α, φ.toAddMonoidHom.comp (i α) = i' α := by
  obtain ⟨f, hf, hf_unique⟩ := existsUnique_extension i i'
  obtain ⟨g, hg, -⟩ := existsUnique_extension i' i
  -- The restriction equations determine both composites as identity maps.
  have hgf : g.comp f = AddMonoidHom.id G :=
    comp_eq_id_of_restrictions i i' f g hf hg
  have hfg : f.comp g = AddMonoidHom.id G' :=
    comp_eq_id_of_restrictions i' i g f hg hf
  let φ : G ≃+ G' := AddMonoidHom.toAddEquiv f g hgf hfg
  have hφ_forward : φ.toAddMonoidHom = f := by
    rfl
  have hφ_restrict : ∀ α, φ.toAddMonoidHom.comp (i α) = i' α := by
    intro α
    rw [hφ_forward, hf α]
  refine ⟨φ, hφ_restrict, ?_⟩
  intro ψ hψ
  -- A competing equivalence has the same forward homomorphism, hence is equal to `φ`.
  have hψf : ψ.toAddMonoidHom = f := hf_unique ψ.toAddMonoidHom hψ
  apply AddEquiv.ext
  intro z
  calc
    ψ z = ψ.toAddMonoidHom z := rfl
    _ = f z := DFunLike.congr_fun hψf z
    _ = φ.toAddMonoidHom z := (DFunLike.congr_fun hφ_forward z).symm
    _ = φ z := rfl

end AddMonoidHom.IsExternalDirectSum

end
