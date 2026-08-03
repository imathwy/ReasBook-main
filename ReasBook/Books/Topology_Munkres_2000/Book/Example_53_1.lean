module

public import Topology_Munkres_2000.Book.Example_53_1.Projection

public section

universe u

/-- Example 53.1 (1). The identity map of any topological space is a covering map
in Munkres's surjective sense. -/
theorem isCoveringMap_id {X : Type u} [TopologicalSpace X] :
    IsCoveringMap (id : X → X) ∧ Function.Surjective (id : X → X) := by
  constructor
  · -- Identify the identity with projection from the one-point product.
    have projection_comp :
        (Prod.fst : X × PUnit.{u + 1} → X) ∘ (Homeomorph.prodPUnit X).symm = id := by
      funext x
      rfl
    rw [← projection_comp]
    exact
      (isCoveringMap_fst X PUnit.{u + 1}).comp_homeomorph (Homeomorph.prodPUnit X).symm
  · -- Every point is its own preimage under the identity.
    exact Function.surjective_id

/-- Example 53.1 (2). The product `X × Fin n` represents `n` disjoint copies of `X`,
and projection onto `X` is a covering map in Munkres's surjective sense when `0 < n`. -/
theorem isCoveringMap_fst_fin {X : Type u} [TopologicalSpace X] (n : ℕ) (hn : 0 < n) :
    IsCoveringMap (Prod.fst : X × Fin n → X) ∧
      Function.Surjective (Prod.fst : X × Fin n → X) :=
  ⟨isCoveringMap_fst X (Fin n), fun x ↦ ⟨(x, ⟨0, hn⟩), rfl⟩⟩
