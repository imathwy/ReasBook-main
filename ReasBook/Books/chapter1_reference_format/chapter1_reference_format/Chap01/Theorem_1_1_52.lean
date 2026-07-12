import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G']

/- Theorem 1.1.52 (1): For a group homomorphism, the kernel is a normal subgroup. -/
#check MonoidHom.normal_ker

/- Theorem 1.1.52 (2): For a group homomorphism, the image is a subgroup of the codomain. -/
#check MonoidHom.range

/- Theorem 1.1.52 (3): The first isomorphism theorem gives a canonical group isomorphism
`G ⧸ φ.ker ≃* φ.range`. -/
#check QuotientGroup.quotientKerEquivRange

/- Theorem 1.1.52 (4): For a normal subgroup `N`, the quotient map induces an order isomorphism
between subgroups of `G ⧸ N` and subgroups of `G` containing `N`. -/
#check QuotientGroup.comapMk'OrderIso

-- Proof sketch: normality pulls back along any homomorphism by `Subgroup.Normal.comap`, and it
-- pushes forward along the quotient map by `Subgroup.Normal.map` together with the surjectivity of
-- `QuotientGroup.mk' N`.
/-- Theorem 1.1.52: Under the correspondence theorem for `G ⧸ N`, normal subgroups correspond
exactly to normal subgroups of `G` that contain `N`. -/
theorem quotient_subgroup_normal_iff (N : Subgroup G) [N.Normal] (H' : Subgroup (G ⧸ N)) :
    H'.Normal ↔ (H'.comap (QuotientGroup.mk' N)).Normal := by
  constructor
  · intro hH'
    -- Pull normality back along the quotient map to reach the subgroup of `G`.
    exact hH'.comap _
  · intro hH'
    -- Push the pulled-back normal subgroup forward again through the surjective quotient map.
    have hmap :
        (Subgroup.map (QuotientGroup.mk' N) (Subgroup.comap (QuotientGroup.mk' N) H')).Normal :=
      hH'.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    -- The image of the pullback is the original subgroup, so the pushed-forward normality is
    -- exactly normality of `H'`.
    simpa [Subgroup.map_comap_eq_self] using hmap

/- Theorem 1.1.52 (6): If `N ≤ H` are normal subgroups of `G`, then
`(G ⧸ N) ⧸ H.map (QuotientGroup.mk' N) ≃* G ⧸ H`. -/
#check QuotientGroup.quotientQuotientEquivQuotient

/- Theorem 1.1.52 (7): If `N` is a normal subgroup of `G`, then
`H ⧸ N.subgroupOf H ≃* (H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)`, i.e. `HN/N ≃ H/(H ∩ N)`. -/
#check QuotientGroup.quotientInfEquivProdNormalQuotient
