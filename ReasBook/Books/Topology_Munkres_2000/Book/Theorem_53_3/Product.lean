module

public import Mathlib.Topology.Covering.Basic

public section

universe u₁ u₂ v₁ v₂

/-- Helper for Theorem 53.3: the product of two local covering homeomorphisms, with
the base and fiber coordinates grouped together. -/
private def prodEvenlyCoveredHomeomorph {E : Type u₁} {B : Type u₂}
    {E' : Type v₁} {B' : Type v₂} {I I' : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace I] [TopologicalSpace I'] {p : E → B} {p' : E' → B'}
    {U : Set B} {U' : Set B'} (H : p ⁻¹' U ≃ₜ U × I) (H' : p' ⁻¹' U' ≃ₜ U' × I') :
    Prod.map p p' ⁻¹' (U ×ˢ U') ≃ₜ (U ×ˢ U') × (I × I') :=
  (Homeomorph.setCongr (Set.preimage_prod_map_prod p p' U U')).trans
    ((Homeomorph.Set.prod (p ⁻¹' U) (p' ⁻¹' U')).trans
      ((H.prodCongr H').trans
        ((Homeomorph.prodProdProdComm U I U' I').trans
          ((Homeomorph.Set.prod U U').symm.prodCongr (Homeomorph.refl (I × I'))))))

/-- Helper for Theorem 53.3: the base coordinate of the product local homeomorphism
is the product of the original covering maps. -/
private lemma prodEvenlyCoveredHomeomorph_apply {E : Type u₁} {B : Type u₂}
    {E' : Type v₁} {B' : Type v₂} {I I' : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace I] [TopologicalSpace I'] {p : E → B} {p' : E' → B'}
    {U : Set B} {U' : Set B'} (H : p ⁻¹' U ≃ₜ U × I) (H' : p' ⁻¹' U' ≃ₜ U' × I')
    (hH : ∀ x, (H x).1.1 = p x) (hH' : ∀ x, (H' x).1.1 = p' x)
    (z : Prod.map p p' ⁻¹' (U ×ˢ U')) :
    (prodEvenlyCoveredHomeomorph H H' z).1.1 = Prod.map p p' z := by
  -- The composite sends each base coordinate through its original local model.
  rcases z with ⟨⟨x, x'⟩, hx, hx'⟩
  exact Prod.ext (hH ⟨x, hx⟩) (hH' ⟨x', hx'⟩)

/-- Helper for Theorem 53.3: products of evenly covered points are evenly covered by
the product map, with the product of the two fibers. -/
lemma IsEvenlyCovered.prodMap {E : Type u₁} {B : Type u₂}
    {E' : Type v₁} {B' : Type v₂} {I I' : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    [TopologicalSpace I] [TopologicalSpace I'] {p : E → B} {p' : E' → B'}
    {b : B} {b' : B'} (h : IsEvenlyCovered p b I) (h' : IsEvenlyCovered p' b' I') :
    IsEvenlyCovered (Prod.map p p') (b, b') (I × I') := by
  rcases h with ⟨hI, U, hbU, hU, hpU, H, hH⟩
  rcases h' with ⟨hI', U', hbU', hU', hpU', H', hH'⟩
  letI : DiscreteTopology I := hI
  letI : DiscreteTopology I' := hI'
  -- Product the two neighborhoods and their local covering models.
  refine ⟨inferInstance, U ×ˢ U', ⟨hbU, hbU'⟩, hU.prod hU', ?_,
    prodEvenlyCoveredHomeomorph H H', ?_⟩
  · exact hpU.prod hpU'
  · exact prodEvenlyCoveredHomeomorph_apply H H' hH hH'

/-- Helper for Theorem 53.3: the product of two covering maps is a covering map. -/
theorem IsCoveringMap.prodMap {E : Type u₁} {B : Type u₂} {E' : Type v₁} {B' : Type v₂}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
    {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p') :
    IsCoveringMap (Prod.map p p') := by
  intro b
  -- Product the local models and normalize their fiber to the actual product-map fiber.
  exact ((hp b.1).prodMap (hp' b.2)).to_isEvenlyCovered_preimage

end
