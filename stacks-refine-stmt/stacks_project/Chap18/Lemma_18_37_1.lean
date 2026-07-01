import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Φ : GrothendieckTopology.Point J)

/- Domain-style sampling:
- primary domain: the stalk/skyscraper adjunction attached to a site point and the resulting
  exactness statement for the direct image on abelian sheaves;
- sampled owner declarations:
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.skyscraperSheafFunctor`,
  `GrothendieckTopology.Point.skyscraperSheafAdjunction`,
  `exactFunctor`;
- best owner abstraction: the adjunction `Φ.skyscraperSheafAdjunction`, with source-facing
  functor `Φ.skyscraperSheafFunctor`;
- primitive data: the point `Φ`, together with the canonical fiber functor and its
  skyscraper-sheaf right adjoint;
- derived API: exactness of `Φ.skyscraperSheafFunctor` and the split-epi property of the counit;
- source/core/bridge triage:
  `source-facing`: the two Stacks statements below;
  `core/canonical`: `Φ.skyscraperSheafFunctor` and `Φ.skyscraperSheafAdjunction`;
  `bridge/view`: none.

The deleted public abbreviations for `p⁻¹ p_*`, its counit, and the kernel complement were only
derived wrappers around this owner API, so the public surface is refined to the owner declarations
directly. -/

-- Proof sketch: `Φ.skyscraperSheafFunctor` is right adjoint to `Φ.sheafFiber`, hence left exact.
-- For right exactness, use that the counit `p⁻¹ p_* A ⟶ A` admits a functorial section, so
-- `p⁻¹ p_*` splits as `𝟭 ⊞ I`; this forces `p_*` to carry epimorphisms to epimorphisms.
/-- Lemma 18.37.1: for a point `p` of a site, the skyscraper-sheaf functor
`p_* : Ab ⥤ Ab(\mathcal C)` is exact. -/
theorem point_skyscraper_sheaf_functor_exact :
    exactFunctor AddCommGrpCat.{max u v} (Sheaf J AddCommGrpCat.{max u v})
      Φ.skyscraperSheafFunctor := sorry

-- Proof sketch: the unit-counit identities give a functorial section of the counit
-- `p⁻¹ p_* ⟶ 𝟭`; in an abelian category, this split epimorphism is equivalent to a functorial
-- biproduct decomposition.
/-- The counit `p⁻¹ p_* ⟶ 𝟭` of the skyscraper-sheaf adjunction is a split epimorphism. -/
theorem point_skyscraper_counit_isSplitEpi :
    IsSplitEpi
      (Φ.skyscraperSheafAdjunction.counit : _ ⟶ 𝟭 AddCommGrpCat.{max u v}) := sorry
