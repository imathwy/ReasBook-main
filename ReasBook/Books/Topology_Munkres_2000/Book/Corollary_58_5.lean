module

public import Topology_Munkres_2000.Book.Lemma_58_4

public section

universe u v

open FundamentalGroup.LeftToRight

/-- Corollary 58.5 (1). Injectivity of the induced fundamental-group homomorphism
passes to a homotopic continuous map. -/
theorem fundamentalGroupMap_injective_of_homotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h k : C(X, Y)) (x₀ : X) (homotopic : h.Homotopic k)
    (h_injective : Function.Injective (h₍x₀₎)₊) :
    Function.Injective (k₍x₀₎)₊ := by
  -- Factor the induced map through the basepoint-change equivalence supplied by the homotopy.
  obtain ⟨α, inducedMap_eq⟩ :=
    FundamentalGroup.exists_path_map_eq_basepointChange_comp_of_homotopic
      h k x₀ homotopic
  rw [inducedMap_eq]
  -- Both factors are injective, since basepoint change is an equivalence.
  exact (mulEquivOfPath α).injective.comp h_injective

/-- Corollary 58.5 (2). Surjectivity of the induced fundamental-group homomorphism
passes to a homotopic continuous map. -/
theorem fundamentalGroupMap_surjective_of_homotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h k : C(X, Y)) (x₀ : X) (homotopic : h.Homotopic k)
    (h_surjective : Function.Surjective (h₍x₀₎)₊) :
    Function.Surjective (k₍x₀₎)₊ := by
  -- Factor the induced map through the basepoint-change equivalence supplied by the homotopy.
  obtain ⟨α, inducedMap_eq⟩ :=
    FundamentalGroup.exists_path_map_eq_basepointChange_comp_of_homotopic
      h k x₀ homotopic
  rw [inducedMap_eq]
  -- Both factors are surjective, since basepoint change is an equivalence.
  exact (mulEquivOfPath α).surjective.comp h_surjective

/-- Corollary 58.5 (3). Triviality of the induced fundamental-group homomorphism
passes to a homotopic continuous map. -/
theorem fundamentalGroupMap_eq_one_of_homotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h k : C(X, Y)) (x₀ : X) (homotopic : h.Homotopic k)
    (h_trivial : (h₍x₀₎)₊ = 1) :
    (k₍x₀₎)₊ = 1 := by
  -- Factor the induced map through basepoint change, then replace the first
  -- factor by the trivial map.
  obtain ⟨α, inducedMap_eq⟩ :=
    FundamentalGroup.exists_path_map_eq_basepointChange_comp_of_homotopic
      h k x₀ homotopic
  rw [inducedMap_eq, h_trivial]
  -- Basepoint change preserves the identity element, so the composite is again trivial.
  ext g
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply, map_one]
