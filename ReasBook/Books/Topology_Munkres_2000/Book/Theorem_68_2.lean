module

public import Topology_Munkres_2000.Book.Definition_68_5

public section

universe u v

/-- Theorem 68.2. Every indexed family of groups embeds in a group as an external free product. -/
theorem exists_externalFreeProduct {ι : Type u} (G : ι → Type v) [∀ α, Group (G α)] :
    ∃ (H : Type (max u v)) (_ : Group H) (i : ∀ α, G α →* H),
      MonoidHom.IsExternalFreeProduct i :=
  ⟨Monoid.CoprodI G, inferInstance, fun _ ↦ Monoid.CoprodI.of, inferInstance⟩
