import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

/-
Domain-style sampling for Lemma 5.24.1:
- inspected owner declarations:
  `WithConstructibleTopology`,
  `compactSpace_withConstructibleTopology`,
  `CompHaus.limitCone`,
  `CompHaus.limitConeIsLimit`
- primary domain: inverse limits of spectral spaces and constructible-topology subspaces
- `source-facing`: the restricted inverse-system obtained from a diagram `F` and stable subsets
  `Z i`
- `core/canonical`: compactness of the constructible-topology stages is owned by
  `WithConstructibleTopology`, and compactness of the limit is owned by `CompHaus.limitCone`
- `bridge/view`: the restricted `TopCat` diagram of the subsets, then the comparison between its
  categorical limit and the compact-Hausdorff limit built from the constructible topologies

Primitive data is only the ambient diagram `F`, the subsets `Z`, and the stability proof `hZ`.
The restricted diagram is the source-facing owner built from that data; compactness is derived API
coming from the canonical constructible-topology and compact-Hausdorff owners upstream.
-/

section

variable {I : Type v} [Category.{w} I]
variable {F : I ⥤ TopCat.{max u v}}
variable (Z : ∀ i, Set (F.obj i))
variable (hZ : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))

namespace CategoryTheory.Functor

/-- The morphism on subspaces induced by a map of the ambient diagram that preserves the chosen
subsets. -/
private def stableSubsetDiagramMap {i j : I} (a : i ⟶ j) : TopCat.of (Z i) ⟶ TopCat.of (Z j) :=
  TopCat.ofHom
    ⟨Set.MapsTo.restrict (F.map a) (Z i) (Z j) (hZ a),
      Continuous.restrict (hZ a) (F.map a).hom.continuous⟩

-- Proof sketch: both morphisms are restrictions of the identity map on `F.obj i` to the subtype
-- `Z i`, so they agree pointwise on the underlying subtype.
/-- Restricting the identity morphism of the ambient diagram gives the identity on the stable
subset. -/
private theorem stableSubsetDiagramMap_id (i : I) :
    stableSubsetDiagramMap Z hZ (𝟙 i) = 𝟙 (TopCat.of (Z i)) := sorry

-- Proof sketch: both sides are the same restricted function `x ↦ F.map b (F.map a x)` on the
-- subtype `Z i`; pointwise equality follows from functoriality of `F`.
/-- Restricting a composite morphism agrees with composing the restricted morphisms on the stable
subspaces. -/
private theorem stableSubsetDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    stableSubsetDiagramMap Z hZ (a ≫ b) =
      stableSubsetDiagramMap Z hZ a ≫
        stableSubsetDiagramMap Z hZ b := sorry

/-- The diagram of subspaces cut out by a family of subsets stable under the transition maps. -/
def stableSubsetDiagram : I ⥤ TopCat.{max u v} where
  obj i := TopCat.of (Z i)
  map a := stableSubsetDiagramMap Z hZ a
  map_id i := stableSubsetDiagramMap_id Z hZ i
  map_comp a b := stableSubsetDiagramMap_comp Z hZ a b

end CategoryTheory.Functor

end

section

variable {I : Type v} [Category.{w} I]
variable (F : I ⥤ TopCat.{max u v})
variable [∀ i, SpectralSpace ↥(F.obj i)]

-- Proof sketch: endow each `F.obj i` with its constructible topology, so it becomes compact
-- Hausdorff because `F.obj i` is spectral. A subset closed in that constructible topology is then
-- compact Hausdorff as a subspace. The restricted transition maps are continuous between these
-- compact Hausdorff subspaces, so Lemma `5.14.5` applies to the restricted diagram. Finally,
-- compare the constructible-topology limit with the original inverse limit of the same underlying
-- subsets and use surjective continuous image compactness.
/-- Lemma 5.24.1: for a diagram of spectral spaces with spectral transition maps, any inverse limit
of subsets that are closed in the constructible topology and stable under the transition maps is
quasi-compact. -/
theorem compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace ↥(limit (F.stableSubsetDiagram Z hZ_maps)) := sorry

-- Proof sketch: apply the previous theorem to the constant family of subsets `Z i = Set.univ`,
-- which is closed in every constructible topology and is trivially stable under every transition
-- map.
/-- The inverse limit of a diagram of spectral spaces is quasi-compact. -/
theorem compactSpace_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a)) :
    CompactSpace ↥(limit F) := sorry

end
