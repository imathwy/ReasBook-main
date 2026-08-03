module

public import Topology_Munkres_2000.Book.Definition_67_4.ExternalDirectSum

public section

universe u v

/-- Theorem 67.4. Given an indexed family of abelian groups, there exists an abelian
group and a family of monomorphisms exhibiting it as their external direct sum. -/
theorem exists_externalDirectSum {J : Type v} (Gα : J → Type u)
    [∀ α, AddCommGroup (Gα α)] :
    ∃ (G : Type (max u v)) (_ : AddCommGroup G) (i : ∀ α, Gα α →+ G),
      AddMonoidHom.IsExternalDirectSum i := by
  -- Choose the canonical group of finitely supported tuples and its coordinate inclusions.
  refine ⟨DirectSum J Gα, inferInstance, DirectSum.inclusion Gα, ?_⟩
  -- The canonical inclusions already carry the external-direct-sum instance.
  infer_instance

end
