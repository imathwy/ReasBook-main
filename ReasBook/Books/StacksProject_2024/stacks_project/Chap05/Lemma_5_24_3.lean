import StacksProject_2024.Chap05.Lemma_5_24_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

universe u v

/- Domain-style sampling for cofiltered inverse limits of spectral spaces:
- primary domain: constructible-topology descent along cofiltered inverse systems of spectral
  spaces;
- sampled owner declarations:
  `limit.π`,
  `CategoryTheory.Functor.stableSubsetDiagram`,
  `compactSpace_limit_of_constructibleClosed_stableSubsetDiagram`,
  `nonempty_limit_of_constructibleClosed_stableSubsetDiagram`;
- best owner abstraction: the source-facing restricted diagram
  `X.stableSubsetDiagram Z hZ_maps`, with eventual stagewise statements derived by applying the
  canonical nonemptiness theorem to the constructibly closed family cut out by the failure of the
  desired inclusion.

Primitive-vs-derived split:
- primitive data: the ambient cofiltered spectral diagram `X`, the chosen stage `i`, and the
  constructibly closed/open subsets `E` and `F` of `X.obj i`;
- derived API: the eventual-stage criterion for the pullback inclusion on the limit, obtained by
  comparing the empty pullback of `E \\ F` on the limit with eventual emptiness after pullback to a
  stage over `i`.

Layer triage:
- `source-facing`: the Stacks eventual-stage inclusion criterion;
- `core/canonical`: `limit.π` for the limit projection and
  `nonempty_limit_of_constructibleClosed_stableSubsetDiagram` for the cofiltered nonemptiness
  owner theorem;
- `bridge/view`: the passage from inclusion `p⁻¹' E ⊆ p⁻¹' F` to emptiness of the inverse-image
  family of `E \\ F` on the cofiltered over-category of `i`.
-/

section

variable {I : Type u} [Category I] [CategoryTheory.IsCofiltered I]
variable (X : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(X.obj j)]
variable (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
variable (i : I) (E F : Set (X.obj i))
variable (hE : IsClosed[constructibleTopology (X.obj i)] E)
variable (hF : IsOpen[constructibleTopology (X.obj i)] F)

-- Proof sketch: apply Lemma 5.24.2 to the cofiltered inverse system over `Over i` whose stage at
-- `a : j ⟶ i` is `f_a ⁻¹' E \ f_a ⁻¹' F`. Spectral maps are continuous for constructible
-- topologies, so these stagewise differences are constructible-topology closed, and emptiness of
-- the inverse limit is equivalent to eventual stagewise emptiness.
/-- Lemma 5.24.3: for a cofiltered inverse system of spectral spaces with spectral transition maps,
the inverse-image inclusion `p_i ⁻¹' E ⊆ p_i ⁻¹' F` for a constructibly closed subset `E` and a
constructibly open subset `F` of `X_i` holds if and only if the corresponding inclusion already
holds after pullback along some morphism `a : j ⟶ i`. -/
theorem limit_projection_preimage_subset_iff_exists_stage_preimage_subset :
    (limit.π X i) ⁻¹' E ⊆ (limit.π X i) ⁻¹' F ↔
      ∃ (j : I) (a : j ⟶ i), (X.map a) ⁻¹' E ⊆ (X.map a) ⁻¹' F := sorry

end
