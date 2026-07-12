import StacksProject_2024.Chap05.Lemma_5_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

section

variable {I : Type v} [Category.{w} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v})
variable [∀ i : I, SpectralSpace (F.obj i)]
variable (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
variable (Z : ∀ i, Set (F.obj i))
variable (hZ_nonempty : ∀ i, (Z i).Nonempty)
variable (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
variable (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))

/- Domain-style sampling for nonempty cofiltered limits of spectral spaces:
- primary domain: inverse limits of spectral spaces, constructible-topology closed subspaces, and
  the induced stable subdiagram on chosen subsets;
- sampled owner-level declarations:
  `CategoryTheory.Functor.stableSubsetDiagram`,
  `compactSpace_limit_of_constructibleClosed_stableSubsetDiagram`,
  `spectralSpace_subtype_of_isClosed_constructibleTopology`,
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- best owner abstraction: the source-facing restricted diagram `F.stableSubsetDiagram Z hZ_maps`,
  with nonemptiness obtained from the canonical `TopCat` cofiltered-limit theorem after upgrading
  each stage to the constructible-topology compact Hausdorff owner.

Primitive-vs-derived split:
- primitive data: the ambient spectral diagram `F`, the subsets `Z i`, their constructible-topology
  closedness, nonemptiness, and stability under transition maps;
- derived API: spectrality of each subtype, compactness of the resulting limit, and the final
  nonemptiness statement for that limit.

Layer triage:
- `source-facing`: nonemptiness of the inverse limit of stable constructibly closed subsets, and
  the special case of the whole spectral diagram;
- `core/canonical`: `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system` and the
  chapter-level compactness theorem for `stableSubsetDiagram`;
- `bridge/view`: passing from stagewise constructible-topology closed subsets to the canonical
  compact Hausdorff theorem on the restricted diagram.
-/

-- Proof sketch: endow each subtype `Z i` with the constructible topology inherited from `F.obj i`.
-- By Lemma `5.23.5` these are spectral, hence compact Hausdorff in the constructible topology, and
-- the restricted transition maps are spectral because `hF` is spectral. The canonical owner
-- theorem `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system` then gives a point of the
-- inverse limit. Forgetting the auxiliary constructible topologies identifies that point with a
-- point of the canonical limit of the subspace diagram `F.stableSubsetDiagram Z hZ_maps`.
/-- Lemma 5.24.2 (1): for a cofiltered diagram of spectral spaces with spectral transition maps,
nonempty subsets that are closed in the constructible topology and stable under the transition maps
have a nonempty inverse limit. -/
theorem nonempty_limit_of_constructibleClosed_stableSubsetDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i)) :
    Nonempty ↥(limit (F.stableSubsetDiagram Z hZ_maps)) := sorry

-- Proof sketch: apply part `(1)` to the constant family `Z i = Set.univ`; these subsets are
-- nonempty by assumption, closed in every topology, and stable under all transition maps.
/-- Lemma 5.24.2 (2): if every space in a cofiltered diagram of spectral spaces is nonempty, then
the inverse limit space is nonempty. -/
theorem nonempty_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    [∀ i : I, Nonempty (F.obj i)] :
    Nonempty ↥(limit F) := sorry

end
