import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_24_1 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

noncomputable section

/-
Domain-style sampling for Lemma 5.24.1:
- inspected owner declarations:
  `WithConstructibleTopology`,
  `constructibleTopology_compactSpace_of_spectralSpace`,
  `constructibleTopology_t2Space_of_spectralSpace`,
  `compactSpace_limit_of_compactSpace_t2Space`,
  `Types.limitEquivSections`
- primary domain: inverse limits of spectral spaces and constructible-topology closed subspaces
- `source-facing`: the restricted inverse system obtained from a diagram `F` and stable subsets
  `Z i`
- `core/canonical`: patch-topology compactness is owned by the constructible-topology package, and
  limit compactness is owned by the compact-Hausdorff limit theorem
- `bridge/view`: a second restricted diagram built from the same subsets with the patch subspace
  topologies, together with the comparison map from that compact limit to the original limit

Primitive data is only the ambient diagram `F`, the subsets `Z`, and the stability proofs. The
patch-subspace diagram is the faithful translation of the source proof; compactness is then
transported back to the original inverse limit through the identity-on-points comparison map.
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

-- This is just the restricted identity map on the subtype `Z i`.
/-- Restricting the identity morphism of the ambient diagram gives the identity on the stable
subset. -/
private theorem stableSubsetDiagramMap_id (i : I) :
    stableSubsetDiagramMap Z hZ (𝟙 i) = 𝟙 (TopCat.of (Z i)) := by
  apply ConcreteCategory.ext
  ext x
  simp [stableSubsetDiagramMap]

-- Both sides act by the same composite function on points of `Z i`.
/-- Restricting a composite morphism agrees with composing the restricted morphisms on the stable
subspaces. -/
private theorem stableSubsetDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    stableSubsetDiagramMap Z hZ (a ≫ b) =
      stableSubsetDiagramMap Z hZ a ≫
        stableSubsetDiagramMap Z hZ b := by
  apply ConcreteCategory.ext
  ext x
  simp [stableSubsetDiagramMap]

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

/-- Helper for Lemma 5.24.1: every open subset of a spectral space is open for the constructible
topology. -/
private theorem isOpen_constructibleTopology_of_isOpen {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] {s : Set X} (hs : IsOpen s) : IsOpen[constructibleTopology X] s := by
  -- The compact-open basis of a spectral space consists of constructible opens.
  refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hs
  · intro U hU
    exact hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  · intro S hS
    let _ : TopologicalSpace X := constructibleTopology X
    exact isOpen_sUnion fun U hU ↦ hS U hU

section ConstructibleDiagram

/-- Helper for Lemma 5.24.1: the same subset `Z i`, but endowed with the subspace topology coming
from the constructible topology on `F.obj i`. -/
private abbrev PatchSubtype (Z : ∀ i, Set (F.obj i)) (i : I) : Type (max u v) :=
  { x : WithConstructibleTopology (F.obj i) | (x : F.obj i) ∈ Z i }

/-- Helper for Lemma 5.24.1: the restricted transition map is continuous for the patch subspace
topologies. -/
private theorem patchSubsetDiagramMap_continuous
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    Continuous
      (fun x : PatchSubtype (F := F) Z i ↦
        (⟨F.map a x.1, hZ_maps a x.2⟩ : PatchSubtype (F := F) Z j)) := by
  -- The ambient spectral map is continuous for the constructible topologies on the wrapper types.
  have hAmbient :
      @Continuous (WithConstructibleTopology (F.obj i)) (WithConstructibleTopology (F.obj j))
        _ _
        (fun x ↦ ((F.map a : F.obj i → F.obj j) x : F.obj j)) := by
    simpa [WithConstructibleTopology] using (hF a).continuous_constructibleTopology
  -- Restrict that continuous ambient map to the chosen stable subsets.
  exact (hAmbient.comp continuous_subtype_val).subtype_mk fun x ↦ hZ_maps a x.2

/-- Helper for Lemma 5.24.1: the transition map on the patch subspace diagram. -/
private def patchSubsetDiagramMap
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    TopCat.of (PatchSubtype (F := F) Z i) ⟶
      TopCat.of (PatchSubtype (F := F) Z j) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨F.map a x.1, hZ_maps a x.2⟩,
      patchSubsetDiagramMap_continuous (F := F) Z hF hZ_maps a⟩

/-- Helper for Lemma 5.24.1: restricting the identity map on the patch subspaces gives the
identity morphism. -/
private theorem patchSubsetDiagramMap_id
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (i : I) :
    patchSubsetDiagramMap (F := F) Z hF hZ_maps (𝟙 i) =
      𝟙 (TopCat.of (PatchSubtype (F := F) Z i)) := by
  -- Both morphisms are the identity on the underlying subtype points.
  apply ConcreteCategory.ext
  ext x
  change (F.map (𝟙 i)) x.1 = x.1
  simpa using congrArg (fun f : F.obj i ⟶ F.obj i ↦ f x.1) (F.map_id i)

/-- Helper for Lemma 5.24.1: the patch restricted maps compose exactly as the ambient diagram
maps do. -/
private theorem patchSubsetDiagramMap_comp
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    patchSubsetDiagramMap (F := F) Z hF hZ_maps (a ≫ b) =
      patchSubsetDiagramMap (F := F) Z hF hZ_maps a ≫
        patchSubsetDiagramMap (F := F) Z hF hZ_maps b := by
  -- Both sides evaluate to the same composite restricted map on each point.
  apply ConcreteCategory.ext
  ext x
  change (F.map (a ≫ b)) x.1 = (F.map b) ((F.map a) x.1)
  simpa using congrArg (fun f : F.obj i ⟶ F.obj k ↦ f x.1) (F.map_comp a b)

/-- Helper for Lemma 5.24.1: the inverse system obtained from the stable subsets equipped with the
subspace topologies coming from the constructible topologies on the ambient spaces. -/
private def constructibleClosedStableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    I ⥤ TopCat.{max u v} where
  obj i := TopCat.of (PatchSubtype (F := F) Z i)
  map a := patchSubsetDiagramMap (F := F) Z hF hZ_maps a
  map_id i := patchSubsetDiagramMap_id (F := F) Z hF hZ_maps i
  map_comp a b := patchSubsetDiagramMap_comp (F := F) Z hF hZ_maps a b

/-- Helper for Lemma 5.24.1: each patch subspace `Z i` is compact because it is closed in the
compact constructible topology on `F.obj i`. -/
private theorem patchSubtype_compactSpace
    (Z : ∀ i, Set (F.obj i))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (i : I) : CompactSpace (PatchSubtype (F := F) Z i) := by
  -- The ambient constructible-topology space is compact by spectrality.
  have hPatchCompact : @CompactSpace (F.obj i) (constructibleTopology (F.obj i)) :=
    constructibleTopology_compactSpace_of_spectralSpace
  let _ : TopologicalSpace (F.obj i) := constructibleTopology (F.obj i)
  let _ : CompactSpace (F.obj i) := hPatchCompact
  -- A closed subset of that compact patch space is compact.
  have hClosed : IsClosed (Z i) := by
    simpa using hZ_closed i
  have hCompact : IsCompact (Z i) := hClosed.isCompact
  -- Rewrite the subtype in the owner topology back to the wrapper notation used here.
  simpa [PatchSubtype, WithConstructibleTopology] using
    (isCompact_iff_compactSpace.mp hCompact : CompactSpace (Z i))

/-- Helper for Lemma 5.24.1: each patch subspace `Z i` is Hausdorff because it is a subspace of
the Hausdorff constructible topology on `F.obj i`. -/
private theorem patchSubtype_t2Space
    (Z : ∀ i, Set (F.obj i))
    (i : I) : T2Space (PatchSubtype (F := F) Z i) := by
  -- A subtype of a Hausdorff space is Hausdorff, so it is enough to switch the ambient topology
  -- to the constructible topology on `F.obj i`.
  letI : T2Space (WithConstructibleTopology (F.obj i)) := inferInstance
  simpa [PatchSubtype, WithConstructibleTopology] using
    (inferInstance : T2Space { x : WithConstructibleTopology (F.obj i) | (x : F.obj i) ∈ Z i })

/-- Helper for Lemma 5.24.1: the identity on `Z i` is continuous from the patch subspace topology
to the original subspace topology. -/
private theorem patchToOriginalComponent_continuous
    (Z : ∀ i, Set (F.obj i)) (i : I) :
    Continuous
      (fun x : PatchSubtype (F := F) Z i ↦
        ((⟨x.1, x.2⟩ : Z i) : Z i)) := by
  -- Every original open is constructible-open, so the identity from the patch topology is
  -- continuous to the original topology.
  have hContToOriginal :
      @Continuous (WithConstructibleTopology (F.obj i)) (F.obj i) _ _
        (fun x ↦ (x : F.obj i)) := by
    simpa [WithConstructibleTopology] using
      (continuous_id_of_le
        (fun U hU ↦ isOpen_constructibleTopology_of_isOpen (X := F.obj i) hU) :
          @Continuous (F.obj i) (F.obj i) (constructibleTopology (F.obj i)) _ id)
  -- Restrict that identity map to the stable subset.
  exact (hContToOriginal.comp continuous_subtype_val).subtype_mk fun x ↦ x.2

/-- Helper for Lemma 5.24.1: the stagewise identity maps from the patch subspace diagram to the
original subspace diagram. -/
private def patchToOriginalComponent
    (Z : ∀ i, Set (F.obj i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (i : I) :
    TopCat.of (PatchSubtype (F := F) Z i) ⟶ (F.stableSubsetDiagram Z hZ_maps).obj i :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2⟩,
      patchToOriginalComponent_continuous (F := F) Z i⟩

/-- Helper for Lemma 5.24.1: the stagewise identity maps commute with the restricted transition
maps after forgetting the auxiliary constructible topologies. -/
private theorem patchToOriginalComponent_naturality
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    patchToOriginalComponent (F := F) Z hZ_maps i ≫
        (F.stableSubsetDiagram Z hZ_maps).map a =
      patchSubsetDiagramMap (F := F) Z hF hZ_maps a ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
  -- Both sides are the same restricted ambient map, viewed with different source topologies.
  apply ConcreteCategory.ext
  ext x
  rfl

/-- Helper for Lemma 5.24.1: the stagewise identity maps from the patch limit point satisfy the
cone compatibility relations for the original stable-subset diagram. -/
private theorem patchLimitConeToOriginalCone_naturality
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : I} (a : i ⟶ j) :
    ((TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        patchToOriginalComponent (F := F) Z hZ_maps i) ≫
        (F.stableSubsetDiagram Z hZ_maps).map a =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app j ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
  -- First move the stagewise identity map across the restricted transition map.
  calc
    ((TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        patchToOriginalComponent (F := F) Z hZ_maps i) ≫
        (F.stableSubsetDiagram Z hZ_maps).map a
        =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        (patchToOriginalComponent (F := F) Z hZ_maps i ≫
          (F.stableSubsetDiagram Z hZ_maps).map a) := by
          rw [Category.assoc]
    _ =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        (patchSubsetDiagramMap (F := F) Z hF hZ_maps a ≫
          patchToOriginalComponent (F := F) Z hZ_maps j) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦
                (TopCat.limitCone
                    (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫ f)
              (patchToOriginalComponent_naturality (F := F) Z hF hZ_maps a)
    _ =
      ((TopCat.limitCone
            (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
          patchSubsetDiagramMap (F := F) Z hF hZ_maps a) ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
          rw [← Category.assoc]
    _ =
      (TopCat.limitCone
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app j ≫
        patchToOriginalComponent (F := F) Z hZ_maps j := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ f ≫ patchToOriginalComponent (F := F) Z hZ_maps j)
              ((TopCat.limitCone
                (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).w a)

/-- Helper for Lemma 5.24.1: the stagewise identity maps assemble to a cone from the explicit
patch limit cone point to the original stable-subset diagram. -/
private def patchLimitConeToOriginalCone
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    Cone (F.stableSubsetDiagram Z hZ_maps) where
  pt := (TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt
  π :=
    { app := fun i ↦
        (TopCat.limitCone
            (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
          patchToOriginalComponent (F := F) Z hZ_maps i
      naturality := fun {i j} a ↦
        (patchLimitConeToOriginalCone_naturality (F := F) Z hF hZ_maps a).symm }

/-- Helper for Lemma 5.24.1: a compatible family in the original stable-subset diagram is also a
compatible family in the patch diagram, since only the topology changes. -/
private theorem original_limitCone_point_to_patch_limitCone_point_compatible
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (x : (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :
    ∀ {i j : I} (a : i ⟶ j),
      patchSubsetDiagramMap (F := F) Z hF hZ_maps a ⟨(x.1 i).1, (x.1 i).2⟩ =
        ⟨(x.1 j).1, (x.1 j).2⟩ := by
  -- The patch and original diagrams have the same underlying pointwise compatibility relation.
  intro i j a
  apply Subtype.ext
  simpa [patchSubsetDiagramMap, CategoryTheory.Functor.stableSubsetDiagram,
    CategoryTheory.Functor.stableSubsetDiagramMap] using congrArg Subtype.val (x.2 a)

/-- Helper for Lemma 5.24.1: a compatible family in the original stable-subset diagram is also a
compatible family in the patch diagram, since only the topology changes. -/
private def original_limitCone_point_to_patch_limitCone_point
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (x : (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :
    (TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt :=
  ⟨fun i ↦ ⟨(x.1 i).1, (x.1 i).2⟩,
    original_limitCone_point_to_patch_limitCone_point_compatible
      (F := F) Z hF hZ_maps x⟩

/-- Helper for Lemma 5.24.1: the stagewise identity maps assemble to a morphism from the explicit
patch limit cone point to the explicit original limit cone point. -/
private def patchLimitConeToOriginalLimitCone
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    (TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt ⟶
      (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt :=
  (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps)).lift
    (patchLimitConeToOriginalCone (F := F) Z hF hZ_maps)

/-- Helper for Lemma 5.24.1: the map between the explicit limit cone points evaluates
coordinatewise by the stagewise identity maps. -/
private theorem patchLimitConeToOriginalLimitCone_π
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (i : I) :
    patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps ≫
        (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).π.app i =
      (TopCat.limitCone
        (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).π.app i ≫
        patchToOriginalComponent (F := F) Z hZ_maps i := by
  -- This is exactly the defining `fac` equation of the lifted cone morphism.
  simpa [patchLimitConeToOriginalLimitCone, patchLimitConeToOriginalCone] using
    (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps)).fac
      (patchLimitConeToOriginalCone (F := F) Z hF hZ_maps) i

/-- Helper for Lemma 5.24.1: the comparison map from the patch limit to the original limit is
surjective because both limits classify the same compatible families of points. -/
private theorem patchLimitConeToOriginalLimitCone_surjective
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    Function.Surjective
      (patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps) := by
  -- Use the explicit pointwise reinterpretation of a compatible family as the right inverse.
  intro x
  refine ⟨original_limitCone_point_to_patch_limitCone_point (F := F) Z hF hZ_maps x, ?_⟩
  apply Subtype.ext
  funext i
  have hπ :=
    congrArg
      (fun f ↦ f (original_limitCone_point_to_patch_limitCone_point (F := F) Z hF hZ_maps x))
      (patchLimitConeToOriginalLimitCone_π (F := F) Z hF hZ_maps i)
  simpa [patchToOriginalComponent, original_limitCone_point_to_patch_limitCone_point,
    Category.assoc] using hπ

/-- Helper for Lemma 5.24.1: for `Z i = univ`, the stable-subset diagram is naturally isomorphic
to the original diagram. -/
private theorem mapsTo_univ_subset :
    ∀ ⦃i j : I⦄ (a : i ⟶ j),
      Set.MapsTo (F.map a)
        ((fun i ↦ (Set.univ : Set (F.obj i))) i)
        ((fun j ↦ (Set.univ : Set (F.obj j))) j) := by
  intro i j a x hx
  simp

/-- Helper for Lemma 5.24.1: the stagewise identifications for the universal-subset diagram are
natural in the diagram index. -/
private theorem stable_subset_diagram_univ_iso_naturality
    {i j : I} (a : i ⟶ j) :
    (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
          (mapsTo_univ_subset (F := F))).map a ≫
        (TopCat.isoOfHomeo (Homeomorph.Set.univ (F.obj j))).hom =
      (TopCat.isoOfHomeo (Homeomorph.Set.univ (F.obj i))).hom ≫
        F.map a := by
  -- For the universal subset, every restricted transition map is just the original map on points.
  apply ConcreteCategory.ext
  ext x
  rfl

/-- Helper for Lemma 5.24.1: for `Z i = univ`, the stable-subset diagram is naturally isomorphic
to the original diagram. -/
private def stable_subset_diagram_univ_iso :
    F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
        (mapsTo_univ_subset (F := F)) ≅
      F :=
  NatIso.ofComponents (fun i ↦ TopCat.isoOfHomeo (Homeomorph.Set.univ (F.obj i)))
    (fun {i j} a ↦ stable_subset_diagram_univ_iso_naturality (F := F) a)

end ConstructibleDiagram

section

attribute [local instance] uliftCategory

/-- Helper for Lemma 5.24.1: Lemma 5.14.5 extends to arbitrary index-universe categories after
lifting the codomain to `CompHaus` without changing the index category. -/
private theorem compactSpace_limit_of_compactSpace_t2Space_large
    {J : Type v} [Category.{w} J] (G : J ⥤ TopCat.{max u v})
    [∀ j, CompactSpace ↥(G.obj j)] [∀ j, T2Space ↥(G.obj j)] :
    CompactSpace ↥(limit G) := by
  -- Route correction: enlarge only the codomain universe, using `uliftFunctor` so the index
  -- category stays fixed while the compact-Hausdorff owner can supply a limit of this shape.
  let H : J ⥤ TopCat.{max u v w} := G ⋙ TopCat.uliftFunctor.{w, max u v}
  haveI : ∀ j, CompactSpace ↥(H.obj j) := by
    intro j
    change CompactSpace (ULift.{w} (G.obj j))
    infer_instance
  haveI : ∀ j, T2Space ↥(H.obj j) := by
    intro j
    change T2Space (ULift.{w} (G.obj j))
    infer_instance
  -- Transfer `CompHaus` limits from a same-universe shape equivalent to `J`.
  haveI : HasLimitsOfShape J CompHaus.{max u v w} := by
    haveI :
        HasLimitsOfShape (ULiftHom.{max u v w} (ULift.{max u v w} J))
          CompHaus.{max u v w} := by
      let _ : HasLimits CompHaus.{max u v w} := inferInstance
      exact HasLimits.has_limits_of_shape
        (J := ULiftHom.{max u v w} (ULift.{max u v w} J))
        (C := CompHaus.{max u v w})
    exact hasLimitsOfShape_of_equivalence
      (ULiftHomULiftCategory.equiv.{max u v w, max u v w, w, v} J).symm
  let Gc : J ⥤ CompHaus.{max u v w} := {
    obj := fun j ↦ CompHaus.of ↥(H.obj j)
    map := fun f ↦ CompHausLike.ofHom (fun _ ↦ True) (H.map f).hom
    map_id := by
      intro j
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (H.map_id j)
    map_comp := by
      intro i j k f g
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (H.map_comp f g) }
  -- The forgotten `CompHaus` limit computes the `TopCat` limit of the lifted diagram `H`.
  have hCompactLifted : CompactSpace ↥(limit H) := by
    let hGc : IsLimit (compHausToTop.mapCone (limit.cone Gc)) := by
      simpa using isLimitOfPreserves compHausToTop (limit.isLimit Gc)
    have hCompactCone : CompactSpace ↥(compHausToTop.mapCone (limit.cone Gc)).pt := by
      change CompactSpace ↥(limit Gc)
      infer_instance
    letI : CompactSpace ↥(compHausToTop.mapCone (limit.cone Gc)).pt := hCompactCone
    simpa [H, Gc] using
      (TopCat.homeoOfIso
        (IsLimit.conePointUniqueUpToIso hGc (limit.isLimit (Gc ⋙ compHausToTop)))).compactSpace
  letI : CompactSpace ↥(limit H) := hCompactLifted
  -- Since `uliftFunctor` preserves limits, compactness descends from `limit H` to the lifted
  -- copy of `limit G`, and then across the explicit `ULift` homeomorphism back to `limit G`.
  have hCompactUliftedLimit :
      CompactSpace ↥(TopCat.uliftFunctor.{w, max u v}.obj (limit G)) := by
    simpa [H] using
      (TopCat.homeoOfIso
        (preservesLimitIso (TopCat.uliftFunctor.{w, max u v}) G)).symm.compactSpace
  letI : CompactSpace ↥(TopCat.uliftFunctor.{w, max u v}.obj (limit G)) :=
    hCompactUliftedLimit
  simpa using (TopCat.uliftFunctorObjHomeo.{w, max u v} (limit G)).symm.compactSpace

end

/-- Helper for Lemma 5.24.1: the explicit patch-topology limit cone point is compact because it
is homeomorphic to the limit of a diagram of compact Hausdorff patch subspaces. -/
private theorem patch_limitCone_compactSpace
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace
      ↥((TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt) := by
  haveI : ∀ i,
      CompactSpace
        ↥((constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps).obj i) := by
    -- Each stage is a closed subspace of the compact constructible topology on `F.obj i`.
    intro i
    simpa [constructibleClosedStableSubsetDiagram] using
      patchSubtype_compactSpace (F := F) Z hZ_closed i
  haveI : ∀ i,
      T2Space ↥((constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps).obj i) := by
    -- The constructible topology is Hausdorff, and subspaces preserve Hausdorffness.
    intro i
    simpa [constructibleClosedStableSubsetDiagram] using patchSubtype_t2Space (F := F) Z i
  haveI :
      CompactSpace
        ↥(limit (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)) :=
    compactSpace_limit_of_compactSpace_t2Space_large
      (G := constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)
  -- The explicit `TopCat.limitCone` point is the same limit space up to the canonical isomorphism.
  let e :=
    (TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso
        (TopCat.limitConeIsLimit
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps))
        (limit.isLimit
          (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)))).symm
  letI :
      CompactSpace
        ↥((limit.cone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt) := by
    change CompactSpace ↥(limit (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps))
    infer_instance
  exact e.compactSpace

/-- Helper for Lemma 5.24.1: the explicit original limit cone point is compact as the continuous
surjective image of the compact patch-topology limit cone point. -/
private theorem original_limitCone_compactSpace_of_patch_surjective
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) := by
  let f := patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps
  letI :
      CompactSpace
        ↥((TopCat.limitCone (constructibleClosedStableSubsetDiagram (F := F) Z hF hZ_maps)).pt) :=
    patch_limitCone_compactSpace (F := F) Z hF hZ_closed hZ_maps
  have hCompactUniv :
      IsCompact (Set.univ : Set ((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt)) := by
    -- The image of the compact patch limit is all of the original limit because the comparison
    -- map is surjective on the underlying compatible families.
    simpa [f, Set.image_univ,
      Set.range_eq_univ.2 (patchLimitConeToOriginalLimitCone_surjective (F := F) Z hF hZ_maps)] using
      (isCompact_univ.image
        (patchLimitConeToOriginalLimitCone (F := F) Z hF hZ_maps).hom.continuous)
  letI :
      CompactSpace
        (Set.univ : Set ((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt)) :=
    isCompact_iff_compactSpace.mp hCompactUniv
  -- Passing from the compact subtype `univ` back to the ambient space is just the universal-set
  -- homeomorphism.
  simpa using
    (Homeomorph.Set.univ
      ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt)).compactSpace

-- Proof sketch: endow each `F.obj i` with its constructible topology, restrict to the closed
-- subsets `Z i`, and apply the compact-Hausdorff limit theorem to that patch-topology diagram.
-- The resulting limit maps continuously and surjectively onto the original inverse limit because
-- both limits classify the same compatible families of points.
/-- Lemma 5.24.1: for a diagram of spectral spaces with spectral transition maps, any inverse limit
of subsets that are closed in the constructible topology and stable under the transition maps is
quasi-compact. -/
theorem compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
    (Z : ∀ i, Set (F.obj i))
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    CompactSpace ↥(limit (F.stableSubsetDiagram Z hZ_maps)) := by
  -- Route correction: the only missing step was the large-universe compact-Hausdorff limit
  -- wrapper. With that in place, the source proof now runs exactly through the patch diagram.
  have hCompactOriginalCone :
      CompactSpace ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :=
    original_limitCone_compactSpace_of_patch_surjective (F := F) Z hF hZ_closed hZ_maps
  letI : CompactSpace ↥((TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt) :=
    hCompactOriginalCone
  -- The explicit original cone point is canonically homeomorphic to `limit (F.stableSubsetDiagram
  -- Z hZ_maps)`, so compactness transports back to the abstract limit.
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso
        (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps))
        (limit.isLimit (F.stableSubsetDiagram Z hZ_maps)))
  simpa using e.compactSpace

-- Proof sketch: specialize the previous theorem to the family `Z i = univ`, then transport the
-- resulting compactness across the natural isomorphism from the stable-subset diagram back to the
-- original diagram.
/-- The inverse limit of a diagram of spectral spaces is quasi-compact. -/
theorem compactSpace_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a)) :
    CompactSpace ↥(limit F) := by
  have hUnivClosed :
      ∀ i, IsClosed[constructibleTopology (F.obj i)]
        ((fun i ↦ (Set.univ : Set (F.obj i))) i) := by
    intro i
    simp
  have hCompactStable :
      CompactSpace ↥(limit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
          (mapsTo_univ_subset (F := F)))) :=
    compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
      (F := F)
      (Z := fun i ↦ (Set.univ : Set (F.obj i)))
      (hF := hF)
      (hZ_closed := hUnivClosed)
      (hZ_maps := mapsTo_univ_subset (F := F))
  -- For the universal family, the restricted diagram is naturally isomorphic to the original one.
  letI :
      CompactSpace ↥(limit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i)))
          (mapsTo_univ_subset (F := F)))) := hCompactStable
  let e :=
    TopCat.homeoOfIso
      (HasLimit.isoOfNatIso (stable_subset_diagram_univ_iso (F := F)))
  simpa using e.compactSpace

end

/-! ### Lemma_5_24_2 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v w

noncomputable section

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
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- best owner abstraction: the source-facing restricted diagram `F.stableSubsetDiagram Z hZ_maps`,
  with nonemptiness obtained from the canonical `TopCat` cofiltered-limit theorem after upgrading
  each stage to the constructible-topology compact Hausdorff owner.
-/

-- Proof sketch: the source proof passes to the constructible-topology subdiagram `Z'_i`,
-- reindexes along `AsSmall.down`, applies the compact-Hausdorff cofiltered-limit nonemptiness
-- theorem there, and then forgets the auxiliary topology stagewise to obtain a point of the
-- original stable-subset inverse limit.
omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: the family `Z i = univ` is stable under every transition map. -/
private theorem mapsTo_univ_subset :
    ∀ ⦃i j : I⦄ (a : i ⟶ j),
      Set.MapsTo (F.map a)
        ((fun i ↦ (Set.univ : Set (F.obj i))) i)
        ((fun j ↦ (Set.univ : Set (F.obj j))) j) := by
  intro i j a x hx
  simp

/-- Helper for Lemma 5.24.2: the subset `Z i` with the subspace topology induced from the
constructible topology on `F.obj i`. -/
private abbrev ConstructibleStableSubtype (i : I) : Type (max u v) :=
  { x : WithConstructibleTopology (F.obj i) | (x : F.obj i) ∈ Z i }

/-- Helper for Lemma 5.24.2: a small cofinal reindexing of the original cofiltered category. -/
private abbrev ConstructibleSmallIndex :=
  AsSmall.{max w v} I

omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: every stage of the constructible-topology subdiagram is nonempty. -/
private theorem constructible_stage_nonempty
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (i : ConstructibleSmallIndex (I := I)) :
    Nonempty (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) := by
  -- The witness is the same point of `Z i`, now regarded inside the constructible-topology owner.
  rcases hZ_nonempty (AsSmall.down.obj i) with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

omit [IsCofiltered I] in
/-- Helper for Lemma 5.24.2: every stage of the constructible-topology subdiagram is compact. -/
private theorem constructible_stage_compactSpace
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i))
    (i : ConstructibleSmallIndex (I := I)) :
    CompactSpace (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) := by
  -- A constructibly closed subset of a compact constructible topology is compact.
  let _ : CompactSpace (WithConstructibleTopology (F.obj (AsSmall.down.obj i))) := inferInstance
  have hClosed :
      IsClosed { x : WithConstructibleTopology (F.obj (AsSmall.down.obj i)) |
        (x : F.obj (AsSmall.down.obj i)) ∈ Z (AsSmall.down.obj i) } := by
    simpa [WithConstructibleTopology] using hZ_closed (AsSmall.down.obj i)
  exact isCompact_iff_compactSpace.mp hClosed.isCompact

omit [IsCofiltered I] in
/-- Helper for Lemma 5.24.2: every stage of the constructible-topology subdiagram is Hausdorff. -/
private theorem constructible_stage_t2Space
    (i : ConstructibleSmallIndex (I := I)) :
    T2Space (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) := by
  -- The ambient constructible topology is Hausdorff, and subspaces of Hausdorff spaces are
  -- Hausdorff.
  let _ : T2Space (WithConstructibleTopology (F.obj (AsSmall.down.obj i))) := inferInstance
  infer_instance

omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: the restricted transition maps are continuous for the constructible
subspace topologies. -/
private theorem constructible_reindexed_stableSubsetDiagramMap_continuous
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    {i j : ConstructibleSmallIndex (I := I)} (a : i ⟶ j) :
    Continuous (fun x : ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i) ↦
      (⟨(F.map a.down) x.1, hZ_maps a.down x.2⟩ :
        ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj j))) := by
  -- The ambient map is constructibly continuous, so it restricts continuously to the closed
  -- subspaces `Z i`.
  let g : ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i) →
      WithConstructibleTopology (F.obj (AsSmall.down.obj j)) :=
    fun x ↦ (F.map a.down) x.1
  have hg : Continuous g := by
    let g' : WithConstructibleTopology (F.obj (AsSmall.down.obj i)) →
        WithConstructibleTopology (F.obj (AsSmall.down.obj j)) := F.map a.down
    have hg' : Continuous g' := by
      simpa [g', WithConstructibleTopology] using (hF a.down).continuous_constructibleTopology
    simpa [g, g'] using hg'.comp continuous_subtype_val
  simpa [g] using hg.subtype_mk
    (fun x : ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i) ↦ hZ_maps a.down x.2)

/-- Helper for Lemma 5.24.2: the constructible-topology restricted diagram, reindexed on
`AsSmall I`. -/
private def constructible_reindexed_stableSubsetDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    ConstructibleSmallIndex (I := I) ⥤ TopCat.{max u v} where
  obj i := TopCat.of (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i))
  map a := TopCat.ofHom
    ⟨fun x ↦ ⟨(F.map a.down) x.1, hZ_maps a.down x.2⟩,
      constructible_reindexed_stableSubsetDiagramMap_continuous (F := F) (Z := Z) hF hZ_maps a⟩
  map_id i := by
    apply ConcreteCategory.ext
    ext x
    -- After restricting to the subtype, the identity map is still pointwise the identity.
    change
      ((ConcreteCategory.hom (F.map (𝟙 (AsSmall.down.obj i)))) x.1 :
        WithConstructibleTopology (F.obj (AsSmall.down.obj i))) = x.1
    simp
    rfl
  map_comp a b := by
    rename_i X Y Z' a b
    apply ConcreteCategory.ext
    ext x
    -- The restricted maps compose exactly as the ambient diagram maps do.
    change
      (ConcreteCategory.hom (F.map (a.down ≫ b.down))) x.1 =
        (ConcreteCategory.hom (F.map b.down)) ((ConcreteCategory.hom (F.map a.down)) x.1)
    simp

omit [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] in
/-- Helper for Lemma 5.24.2: the transition maps of the lifted small constructible diagram are
continuous. -/
private theorem constructible_reindexed_stableSubsetDiagram_liftedMap_continuous
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    ∀ {i j : ConstructibleSmallIndex (I := I)} (a : i ⟶ j),
      Continuous (fun x : ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) ↦
        (ULift.up
          (⟨(F.map a.down) x.down.1, hZ_maps a.down x.down.2⟩ :
            ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj j)))) := by
  intro i j a
  -- The lifted map is `ULift.up` after the already constructed continuous restricted map.
  exact
    continuous_uliftUp.comp
      ((constructible_reindexed_stableSubsetDiagramMap_continuous (F := F) (Z := Z) hF hZ_maps a).comp
        continuous_uliftDown)

/-- Helper for Lemma 5.24.2: the lifted small constructible-topology diagram used to apply
Kőnig's lemma in the required universe. -/
private def constructible_reindexed_stableSubsetDiagram_lifted
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j)) :
    ConstructibleSmallIndex (I := I) ⥤ TopCat.{max u v w} :=
  { obj := fun i ↦ TopCat.of (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    map := fun a ↦
      TopCat.ofHom
        ⟨fun x ↦
          ULift.up
            (⟨(F.map a.down) x.down.1, hZ_maps a.down x.down.2⟩ :
              ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj _)),
          constructible_reindexed_stableSubsetDiagram_liftedMap_continuous
            (F := F) (Z := Z) hF hZ_maps a⟩
    map_id := by
      intro i
      apply ConcreteCategory.ext
      ext x
      change
        ((ConcreteCategory.hom (F.map (𝟙 (AsSmall.down.obj i)))) x.down.1 :
          WithConstructibleTopology (F.obj (AsSmall.down.obj i))) = x.down.1
      simp
      rfl
    map_comp := by
      intro X Y Z' a b
      apply ConcreteCategory.ext
      ext x
      change
        (ConcreteCategory.hom (F.map (a.down ≫ b.down))) x.down.1 =
          (ConcreteCategory.hom (F.map b.down)) ((ConcreteCategory.hom (F.map a.down)) x.down.1)
      simp }

/-- Helper for Lemma 5.24.2: forget the auxiliary constructible topology on a stagewise point. -/
private def forget_constructible_point {i : I} :
    ConstructibleStableSubtype (F := F) Z i → Z i :=
  fun x ↦ ⟨(x.1 : F.obj i), x.2⟩

/-- Helper for Lemma 5.24.2: a point of the lifted constructible chosen limit cone gives a point
of the original stable-subset chosen limit cone. -/
private def constructible_reindexed_limitCone_point_to_stableSubset_limitCone_point
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_maps : ∀ ⦃i j : I⦄ (a : i ⟶ j), Set.MapsTo (F.map a) (Z i) (Z j))
    (x : (TopCat.limitCone
      (constructible_reindexed_stableSubsetDiagram_lifted (F := F) (Z := Z) hF hZ_maps)).pt) :
    (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt := by
  -- A limit point is a compatible family, so we simply evaluate it at `⟨i⟩` and forget the
  -- auxiliary topology.
  let D := constructible_reindexed_stableSubsetDiagram (F := F) (Z := Z) hF hZ_maps
  refine ⟨fun i ↦ forget_constructible_point (F := F) (Z := Z) ((x.1 ⟨i⟩).down), ?_⟩
  intro i j a
  apply Subtype.ext
  -- The compatibility relation is exactly the same after removing `ULift` and the constructible
  -- topology wrapper.
  have hx : D.map ⟨a⟩ ((x.1 ⟨i⟩).down) = (x.1 ⟨j⟩).down := by
    exact congrArg ULift.down (x.2 ⟨a⟩)
  simpa [D, forget_constructible_point, CategoryTheory.Functor.stableSubsetDiagram] using
    congrArg Subtype.val hx

/-- Helper for Lemma 5.24.2: the chosen limit cone of the original stable-subset diagram is
nonempty. -/
private theorem nonempty_limitCone_of_constructibleClosed_stableSubsetDiagram_aux
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i)) :
    Nonempty (TopCat.limitCone (F.stableSubsetDiagram Z hZ_maps)).pt := by
  -- We apply Kőnig's lemma to the small lifted constructible-topology diagram.
  let Dlift : ConstructibleSmallIndex (I := I) ⥤ TopCat.{max u v w} :=
    constructible_reindexed_stableSubsetDiagram_lifted (F := F) (Z := Z) hF hZ_maps
  let _ : ∀ i : ConstructibleSmallIndex (I := I), Nonempty (Dlift.obj i) := by
    intro i
    haveI : Nonempty (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) :=
      constructible_stage_nonempty (F := F) (Z := Z) hZ_nonempty i
    change Nonempty (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    infer_instance
  let _ : ∀ i : ConstructibleSmallIndex (I := I), CompactSpace (Dlift.obj i) := by
    intro i
    haveI : CompactSpace (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) :=
      constructible_stage_compactSpace (F := F) (Z := Z) hZ_closed i
    change CompactSpace (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    infer_instance
  let _ : ∀ i : ConstructibleSmallIndex (I := I), T2Space (Dlift.obj i) := by
    intro i
    haveI : T2Space (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)) :=
      constructible_stage_t2Space (F := F) (Z := Z) i
    change T2Space (ULift (ConstructibleStableSubtype (F := F) Z (AsSmall.down.obj i)))
    infer_instance
  obtain ⟨x⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} Dlift
  exact
    ⟨constructible_reindexed_limitCone_point_to_stableSubset_limitCone_point
      (F := F) (Z := Z) hF hZ_maps x⟩

/-- Lemma 5.24.2 (1): for a cofiltered diagram of spectral spaces with spectral transition maps,
nonempty subsets that are closed in the constructible topology and stable under the transition maps
have a nonempty inverse limit. -/
theorem nonempty_limit_of_constructibleClosed_stableSubsetDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_closed : ∀ i, IsClosed[constructibleTopology (F.obj i)] (Z i)) :
    Nonempty ↥(limit (F.stableSubsetDiagram Z hZ_maps)) := by
  -- Route correction: the intended proof is to pass to the constructible-topology subdiagram,
  -- apply Kőnig there after an `AsSmall` reindex, and then forget the auxiliary topology.
  obtain ⟨x⟩ :=
    nonempty_limitCone_of_constructibleClosed_stableSubsetDiagram_aux
      (F := F) (Z := Z) (hZ_maps := hZ_maps) hF hZ_nonempty hZ_closed
  -- The chosen `TopCat.limitCone` point maps to the categorical limit point via the universal
  -- comparison isomorphism.
  exact
    ⟨(IsLimit.conePointUniqueUpToIso
      (TopCat.limitConeIsLimit (F.stableSubsetDiagram Z hZ_maps))
      (limit.isLimit (F.stableSubsetDiagram Z hZ_maps))).hom x⟩

-- Proof sketch: apply part `(1)` to the constant family `Z i = Set.univ`; these subsets are
-- nonempty by assumption, closed in every topology, and stable under all transition maps.
/-- Lemma 5.24.2 (2): if every space in a cofiltered diagram of spectral spaces is nonempty, then
the inverse limit space is nonempty. -/
theorem nonempty_limit_of_spectralSpaceDiagram
    (hF : ∀ ⦃i j : I⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    [∀ i : I, Nonempty (F.obj i)] :
    Nonempty ↥(limit F) := by
  classical
  have hUnivNonempty :
      ∀ i, ((fun i ↦ (Set.univ : Set (F.obj i))) i).Nonempty := by
    intro i
    exact ⟨Classical.choice inferInstance, by simp⟩
  have hUnivClosed :
      ∀ i, IsClosed[constructibleTopology (F.obj i)]
        ((fun i ↦ (Set.univ : Set (F.obj i))) i) := by
    intro i
    simp
  -- Apply part `(1)` to the stable family `Z i = univ`.
  obtain ⟨x⟩ :=
    nonempty_limit_of_constructibleClosed_stableSubsetDiagram
      (F := F)
      (Z := fun i ↦ (Set.univ : Set (F.obj i)))
      (hZ_maps := mapsTo_univ_subset (F := F)) hF hUnivNonempty hUnivClosed
  let e :
      (TopCat.limitCone
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F)))).pt ≅
        limit (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F))) :=
    IsLimit.conePointUniqueUpToIso
      (TopCat.limitConeIsLimit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F))))
      (limit.isLimit
        (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F))))
  let x' : (TopCat.limitCone
      (F.stableSubsetDiagram (fun i ↦ (Set.univ : Set (F.obj i))) (mapsTo_univ_subset (F := F)))).pt :=
    e.inv x
  let y : (TopCat.limitCone F).pt := by
    refine ⟨fun i ↦ (x'.1 i).1, ?_⟩
    intro i j a
    -- For `Z i = univ`, forgetting the subtype proof recovers the original compatibility.
    simpa [CategoryTheory.Functor.stableSubsetDiagram] using
      congrArg (fun z : ((fun j ↦ (Set.univ : Set (F.obj j))) j) ↦ (z : F.obj j)) (x'.2 a)
  -- Transport the compatible family from the chosen limit cone to the categorical limit.
  exact
    ⟨(IsLimit.conePointUniqueUpToIso
      (TopCat.limitConeIsLimit F)
      (limit.isLimit F)).hom y⟩

end

/-! ### Lemma_5_24_3 (from Chap05) -/
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

variable {I : Type u} [Category.{v} I] [CategoryTheory.IsCofiltered I]
variable (X : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(X.obj j)]
variable (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
variable (i : I) (E F : Set (X.obj i))
variable (hE : IsClosed[constructibleTopology (X.obj i)] E)
variable (hF : IsOpen[constructibleTopology (X.obj i)] F)

/-- Helper for Lemma 5.24.3: the original diagram reindexed on the over-category of `i`. -/
private abbrev overDiagram : Over i ⥤ TopCat.{max u v} :=
  (Over.forget i) ⋙ X

/-- Helper for Lemma 5.24.3: the stagewise pullback of the difference `E \ F` along an object of
`Over i`. -/
private abbrev overStageDifference (a : Over i) : Set (X.obj a.left) :=
  (X.map a.hom) ⁻¹' (E \ F)

/-- Helper for Lemma 5.24.3: every over-stage pullback of `E \ F` is constructibly closed. -/
private theorem over_stage_difference_closed
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
    (hE : IsClosed[constructibleTopology (X.obj i)] E)
    (hF : IsOpen[constructibleTopology (X.obj i)] F)
    (a : Over i) :
    IsClosed[constructibleTopology (X.obj a.left)] (overStageDifference (X := X) i E F a) := by
  -- The source proof works with the single constructibly closed set `E \ F`.
  have hDiffClosed : IsClosed[constructibleTopology (X.obj i)] (E \ F) := by
    letI : TopologicalSpace (X.obj i) := constructibleTopology (X.obj i)
    simpa [Set.diff_eq, inter_comm] using hE.inter hF.isClosed_compl
  -- Spectral maps are continuous for constructible topologies, so closedness pulls back.
  exact @IsClosed.preimage (X.obj a.left) (X.obj i)
    (constructibleTopology (X.obj a.left)) (constructibleTopology (X.obj i))
    (X.map a.hom) (hX a.hom).continuous_constructibleTopology _ hDiffClosed

/-- Helper for Lemma 5.24.3: the over-stage differences are stable under morphisms in `Over i`. -/
private theorem over_stage_difference_mapsTo {a b : Over i} (u : a ⟶ b) :
    Set.MapsTo (X.map u.left) (overStageDifference (X := X) i E F a)
      (overStageDifference (X := X) i E F b) := by
  intro x hx
  -- Compatibility in the over-category identifies the two ways to map `x` into stage `i`.
  change (X.map b.hom) ((X.map u.left) x) ∈ E \ F
  have hmap : X.map (u.left ≫ b.hom) = X.map a.hom := by
    simpa using congrArg (fun f ↦ X.map f) (Over.w u)
  have hcomp : (X.map b.hom) ((X.map u.left) x) = (X.map a.hom) x := by
    simpa [Functor.map_comp] using congrArg (fun f ↦ f x) hmap
  rw [hcomp]
  exact hx

/-- Helper for Lemma 5.24.3: inclusion of two inverse images is equivalent to emptiness of the
inverse image of the difference. -/
private theorem preimage_subset_iff_preimage_difference_empty
    {α β : Type*} (f : α → β) (E F : Set β) :
    f ⁻¹' E ⊆ f ⁻¹' F ↔ f ⁻¹' (E \ F) = ∅ := by
  constructor
  · intro h
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    exact hx.2 (h hx.1)
  · intro h x hxE
    by_contra hxF
    have hxDiff : x ∈ f ⁻¹' (E \ F) := ⟨hxE, hxF⟩
    have hxEmpty : x ∈ (∅ : Set α) := by
      simpa [h] using hxDiff
    simpa using hxEmpty

/-- Helper for Lemma 5.24.3: the pullback of `E \ F` to the inverse limit is nonempty exactly
when all pullbacks over objects of `Over i` are nonempty. -/
private theorem limit_preimage_difference_nonempty_iff_forall_over_stage_nonempty
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
    (hE : IsClosed[constructibleTopology (X.obj i)] E)
    (hF : IsOpen[constructibleTopology (X.obj i)] F) :
    ((limit.π X i) ⁻¹' (E \ F)).Nonempty ↔
      ∀ a : Over i, ((X.map a.hom) ⁻¹' (E \ F)).Nonempty := by
  let D₀ : Over i ⥤ TopCat.{max u v} := overDiagram (X := X) i
  let Z : ∀ a : Over i, Set (D₀.obj a) := fun a ↦ (X.map a.hom) ⁻¹' (E \ F)
  have hZ_maps :
      ∀ ⦃a b : Over i⦄ (u : a ⟶ b), Set.MapsTo (D₀.map u) (Z a) (Z b) := by
    intro a b u
    change Set.MapsTo (X.map u.left) ((X.map a.hom) ⁻¹' (E \ F)) ((X.map b.hom) ⁻¹' (E \ F))
    exact over_stage_difference_mapsTo (X := X) i E F u
  have hZ_closed :
      ∀ a : Over i, IsClosed[constructibleTopology (D₀.obj a)] (Z a) := by
    intro a
    change IsClosed[constructibleTopology (X.obj a.left)] ((X.map a.hom) ⁻¹' (E \ F))
    exact over_stage_difference_closed (X := X) i E F hX hE hF a
  let D := D₀.stableSubsetDiagram Z hZ_maps
  constructor
  · rintro ⟨x, hx⟩ a
    refine ⟨(limit.π X a.left) x, ?_⟩
    -- A limit point lying over `E \ F` at stage `i` lies over the same difference at every
    -- object mapping to `i`.
    change X.map a.hom ((limit.π X a.left) x) ∈ E \ F
    have hπ :
        X.map a.hom ((limit.π X a.left) x) = (limit.π X i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w X a.hom)) x
    exact hπ.symm ▸ hx
  · intro hNonempty
    -- Lemma 5.24.2 gives a point of the stable inverse limit over `Over i`.
    let _ : ∀ a : Over i, SpectralSpace ↥(D₀.obj a) := by
      intro a
      change SpectralSpace ↥(X.obj a.left)
      infer_instance
    obtain ⟨x⟩ :=
      nonempty_limit_of_constructibleClosed_stableSubsetDiagram
        (F := D₀) (Z := Z) (hZ_maps := hZ_maps)
        (hF := fun a b u ↦ by simpa using hX u.left)
        hNonempty hZ_closed
    let eStable :
        limit D ≅ (TopCat.limitCone D).pt :=
      IsLimit.conePointUniqueUpToIso (limit.isLimit D) (TopCat.limitConeIsLimit D)
    let x' : (TopCat.limitCone D).pt := eStable.hom x
    let y : (TopCat.limitCone D₀).pt := by
      -- A point of the stable-subset limit is already a compatible family; we only forget
      -- membership in the chosen subsets.
      refine ⟨fun a ↦ (x'.1 a).1, ?_⟩
      intro a b u
      -- The compatibility relation is unchanged after forgetting the subtype proof.
      change D₀.map u ((x'.1 a).1) = (x'.1 b).1
      simpa [D, D₀, CategoryTheory.Functor.stableSubsetDiagram] using
        congrArg Subtype.val (x'.2 u)
    let c : Cone X :=
      (Functor.Initial.extendCone (F := Over.forget i) (G := X)).obj (TopCat.limitCone D₀)
    let hc : IsLimit c :=
      (Functor.Initial.isLimitExtendConeEquiv (F := Over.forget i) (G := X)
        (TopCat.limitCone D₀)).symm
          (TopCat.limitConeIsLimit D₀)
    let z : ↥(limit X) := (limit.isoLimitCone ⟨c, hc⟩).inv y
    refine ⟨z, ?_⟩
    -- Evaluate the extended cone at the identity object of `Over i` to recover a point of `E \ F`.
    have hz_proj :
        (limit.π X i) z = c.π.app i y := by
      change (((limit.isoLimitCone ⟨c, hc⟩).inv ≫ limit.π X i) y) = c.π.app i y
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom (limit.isoLimitCone_inv_π ⟨c, hc⟩ i)) y
    have hy_proj :
        c.π.app i y =
          (TopCat.limitCone D₀).π.app (Over.mk (𝟙 i)) y := by
      simpa using
        congrArg
          (fun g : c.pt ⟶ X.obj i ↦ g y)
          (Functor.Initial.extendCone_obj_π_app'
            (F := Over.forget i) (G := X)
            (c := TopCat.limitCone D₀)
            (X := Over.mk (𝟙 i)) (Y := i) (f := 𝟙 i))
    have hy_mem :
        (TopCat.limitCone D₀).π.app (Over.mk (𝟙 i)) y ∈ E \ F := by
      -- At the identity object, the stable-family coordinate is exactly a point of `E \ F`.
      change ((x'.1 (Over.mk (𝟙 i))).1 : X.obj i) ∈ E \ F
      simpa [D, Z, overStageDifference, Functor.map_id] using (x'.1 (Over.mk (𝟙 i))).2
    change (limit.π X i) z ∈ E \ F
    rw [hz_proj, hy_proj]
    exact hy_mem

-- Proof sketch: apply Lemma 5.24.2 to the cofiltered inverse system over `Over i` whose stage at
-- `a : j ⟶ i` is `f_a ⁻¹' E \ f_a ⁻¹' F`. Spectral maps are continuous for constructible
-- topologies, so these stagewise differences are constructible-topology closed, and emptiness of
-- the inverse limit is equivalent to eventual stagewise emptiness.
/-- Lemma 5.24.3: for a cofiltered inverse system of spectral spaces with spectral transition maps,
the inverse-image inclusion `p_i ⁻¹' E ⊆ p_i ⁻¹' F` for a constructibly closed subset `E` and a
constructibly open subset `F` of `X_i` holds if and only if the corresponding inclusion already
holds after pullback along some morphism `a : j ⟶ i`. -/
theorem limit_projection_preimage_subset_iff_exists_stage_preimage_subset :
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a)) →
    (hE : IsClosed[constructibleTopology (X.obj i)] E) →
    (hF : IsOpen[constructibleTopology (X.obj i)] F) →
    (limit.π X i) ⁻¹' E ⊆ (limit.π X i) ⁻¹' F ↔
      ∃ (j : I) (a : j ⟶ i), (X.map a) ⁻¹' E ⊆ (X.map a) ⁻¹' F := by
  classical
  intro hX hE hF
  -- The source proof reduces everything to the single constructibly closed family `E \ F`.
  have hNonemptyIff :
      ((limit.π X i) ⁻¹' (E \ F)).Nonempty ↔
        ∀ a : Over i, (overStageDifference (X := X) i E F a).Nonempty :=
    limit_preimage_difference_nonempty_iff_forall_over_stage_nonempty
      (X := X) (hX := hX) i E F hE hF
  constructor
  · intro hLimitSubset
    have hLimitEmpty :
        (limit.π X i) ⁻¹' (E \ F) = ∅ :=
      (preimage_subset_iff_preimage_difference_empty (limit.π X i) E F).mp hLimitSubset
    by_contra hNoStage
    have hNoStage' :
        ∀ (j : I) (a : j ⟶ i), ¬ (X.map a) ⁻¹' E ⊆ (X.map a) ⁻¹' F := by
      intro j a haSubset
      exact hNoStage ⟨j, a, haSubset⟩
    have hAllNonempty :
        ∀ a : Over i, (overStageDifference (X := X) i E F a).Nonempty := by
      intro a
      by_contra ha
      exact hNoStage' a.left a.hom
        ((preimage_subset_iff_preimage_difference_empty (X.map a.hom) E F).mpr
          (Set.not_nonempty_iff_eq_empty.mp ha))
    exact
      (Set.not_nonempty_iff_eq_empty.mpr hLimitEmpty)
        (hNonemptyIff.mpr hAllNonempty)
  · rintro ⟨j, a, haSubset⟩
    have haEmpty :
        overStageDifference (X := X) i E F (Over.mk a) = ∅ :=
      (preimage_subset_iff_preimage_difference_empty (X.map a) E F).mp haSubset
    have hLimitEmpty :
        (limit.π X i) ⁻¹' (E \ F) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hLimitNonempty
      have hStageNonempty := (hNonemptyIff.mp hLimitNonempty) (Over.mk a)
      exact (Set.not_nonempty_iff_eq_empty.mpr haEmpty) hStageNonempty
    exact
      (preimage_subset_iff_preimage_difference_empty (limit.π X i) E F).mpr
        hLimitEmpty

end

/-! ### Lemma_5_24_4 (from Chap05) -/
universe u v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} {C : Cone F}
variable [∀ j : J, SpectralSpace (F.obj j)]

/- Domain-style sampling for constructible descent in cofiltered limits of spectral spaces:
- primary domain: constructible subsets, compact opens, and spectral maps in inverse limits of
  spectral spaces;
- sampled owner-level declarations:
  `Topology.IsConstructible.empty_union_induction`,
  `IsSpectralMap.isConstructible_preimage`,
  `compact_open_eq_preimage_of_isLimit`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction: the predicate `Topology.IsConstructible` on subsets, together with the
  canonical `CompactOpens` owner for open constructible subsets and `Closeds` for the closed
  companion case;
- primitive-vs-derived split:
  primitive data: a subset of the limit together with the owner predicate `IsConstructible`;
  derived API: the compact-open and closed refinements of the descended stage subset.

Layer triage:
- `source-facing`: a constructible subset of the limit comes via pullback from some stage;
- `core/canonical`: the owner predicate `Topology.IsConstructible`, together with the chapter-level
  compact-open descent theorem and spectral-limit owner for the ambient spaces;
- `bridge/view`: the open and closed companion forms, which should use `CompactOpens` and
  `Closeds` rather than storing openness or closedness as primitive fields.
-/

/-- Helper for Lemma 5.24.4: a constructible open subset of the limit descends to a compact open
subset on some stage. -/
private lemma exists_stage_compact_open_of_constructible_open
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt} (hE : IsConstructible E) (hE_open : IsOpen E) :
    ∃ (i : J) (Ei : CompactOpens (F.obj i)), C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  let _ : SpectralSpace C.pt :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (F := F) (C := C) hC
      (fun {j k} a ↦ hF a)
  -- On the compact spectral limit, retrocompactness upgrades constructible openness to compactness.
  have hE_compact : IsCompact E := by
    exact hE.isRetrocompact.isCompact
  let W : CompactOpens C.pt := ⟨⟨E, hE_compact⟩, hE_open⟩
  obtain ⟨i, Ui, hUi⟩ := compact_open_eq_preimage_of_isLimit (C := C) hC W
  have hUi' : E = C.π.app i ⁻¹' (Ui : Set (F.obj i)) := by
    simpa [W] using hUi
  let S : Set (Set (F.obj i)) := {s | IsOpen s ∧ IsCompact s ∧ s ⊆ (Ui : Set (F.obj i))}
  have hUi_eq : (Ui : Set (F.obj i)) = ⋃₀ S := by
    simpa [S, and_left_comm, and_assoc] using
      (PrespectralSpace.isTopologicalBasis (X := F.obj i)).open_eq_sUnion' Ui.isOpen
  let V : {s : Set (F.obj i) // s ∈ S} → CompactOpens (F.obj i) :=
    fun s ↦ ⟨⟨s.1, s.2.2.1⟩, s.2.1⟩
  have hOpen : ∀ s : {s : Set (F.obj i) // s ∈ S},
      IsOpen (C.π.app i ⁻¹' (V s : Set (F.obj i))) := by
    intro s
    exact (V s).isOpen.preimage (C.π.app i).hom.continuous
  have hCover : E ⊆ ⋃ s : {s : Set (F.obj i) // s ∈ S}, C.π.app i ⁻¹' (V s : Set (F.obj i)) := by
    intro x hx
    rw [hUi'] at hx
    change C.π.app i x ∈ (Ui : Set (F.obj i)) at hx
    rw [hUi_eq] at hx
    rcases mem_sUnion.1 hx with ⟨s, hsS, hsx⟩
    exact mem_iUnion.2 ⟨⟨s, hsS⟩, hsx⟩
  obtain ⟨t, ht⟩ := hE_compact.elim_finite_subcover
    (fun s : {s : Set (F.obj i) // s ∈ S} ↦ C.π.app i ⁻¹' (V s : Set (F.obj i))) hOpen hCover
  let Ei : CompactOpens (F.obj i) := t.sup V
  refine ⟨i, Ei, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, C.π.app i ⁻¹' (V s : Set (F.obj i)) := by
      simpa [Ei] using hx
    rw [hUi']
    rw [Set.mem_preimage]
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨s, hx'⟩
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨hs, hsx⟩
    exact s.2.2.2 hsx
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, C.π.app i ⁻¹' (V s : Set (F.obj i)) := by
      have htx := ht hx
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨s, htx⟩
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨hs, hsx⟩
      exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs, hsx⟩⟩
    simpa [Ei] using hx'

/-- Helper for Lemma 5.24.4: two constructible subsets that already descend to stages can be
pulled back to a common refinement stage and united there. -/
private lemma merge_constructible_stage_descents
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E E' : Set C.pt} {i j : J} {Ei : Set (F.obj i)} {Ej : Set (F.obj j)}
    (hEi_constructible : IsConstructible Ei) (hEj_constructible : IsConstructible Ej)
    (hEi : C.π.app i ⁻¹' Ei = E) (hEj : C.π.app j ⁻¹' Ej = E') :
    ∃ (k : J) (Ek : Set (F.obj k)), IsConstructible Ek ∧ C.π.app k ⁻¹' Ek = E ∪ E' := by
  obtain ⟨k, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Ek : Set (F.obj k) := (F.map a) ⁻¹' Ei ∪ (F.map b) ⁻¹' Ej
  refine ⟨k, Ek, ?_, ?_⟩
  · -- Spectral transition maps preserve constructibility, so the common-refinement union stays constructible.
    exact ((hF a).isConstructible_preimage hEi_constructible).union
      ((hF b).isConstructible_preimage hEj_constructible)
  · have hπ {k l : J} (f : k ⟶ l) (x : C.pt) :
        C.π.app l x = F.map f (C.π.app k x) := by
      rw [← CategoryTheory.comp_apply]
      exact congrArg (fun g : C.pt ⟶ F.obj l ↦ g x) (C.w f).symm
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · left
        rw [← hEi]
        change C.π.app i x ∈ Ei
        rw [hπ a x]
        exact hx
      · right
        rw [← hEj]
        change C.π.app j x ∈ Ej
        rw [hπ b x]
        exact hx
    · intro hx
      rcases hx with hx | hx
      · left
        rw [← hEi] at hx
        change C.π.app i x ∈ Ei at hx
        change F.map a (C.π.app k x) ∈ Ei
        rw [← hπ a x]
        exact hx
      · right
        rw [← hEj] at hx
        change C.π.app j x ∈ Ej at hx
        change F.map b (C.π.app k x) ∈ Ej
        rw [← hπ b x]
        exact hx

/-- Helper for Lemma 5.24.4: a constructible closed subset of the limit descends to a closed
constructible subset on some stage. -/
private lemma exists_stage_closed_of_constructible_closed
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt} (hE : IsConstructible E) (hE_closed : IsClosed E) :
    ∃ (i : J) (Ei : Closeds (F.obj i)),
      IsConstructible (Ei : Set (F.obj i)) ∧ C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  -- Descend the open complement first, then take the stagewise complement.
  obtain ⟨i, Ui, hUi⟩ :=
    exists_stage_compact_open_of_constructible_open (C := C) hC hF hE.compl hE_closed.isOpen_compl
  have hUi_closed : IsClosed ((Ui : Set (F.obj i))ᶜ) := Ui.isOpen.isClosed_compl
  let Ei : Closeds (F.obj i) := ⟨(Ui : Set (F.obj i))ᶜ, hUi_closed⟩
  refine ⟨i, Ei, ?_, ?_⟩
  · -- Complements of compact opens are constructible on each spectral stage.
    exact (Ui.isCompact.isConstructible Ui.isOpen).compl
  · ext x
    constructor
    · intro hx
      change C.π.app i x ∉ (Ui : Set (F.obj i)) at hx
      by_contra hxE
      have hxE' : x ∈ Eᶜ := hxE
      rw [← hUi] at hxE'
      exact hx (by simpa using hxE')
    · intro hxE
      change C.π.app i x ∉ (Ui : Set (F.obj i))
      intro hxUi
      have hxEcompl : x ∈ Eᶜ := by
        rw [← hUi]
        exact hxUi
      exact hxEcompl hxE

-- Proof sketch: argue first for constructible opens by upgrading them to compact opens on the
-- spectral limit and descending them to a single stage after refining the stagewise open cover by
-- finitely many compact-open basis pieces; then pass to constructible closed sets by complements,
-- and finally use constructible induction with a common-refinement union step.
/-- Lemma 5.24.4: a constructible subset of the limit of a cofiltered diagram of spectral spaces
with spectral transition maps comes by pullback from a constructible subset on some stage. -/
theorem constructible_eq_preimage_of_isLimit
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) :
    ∃ (i : J) (Ei : Set (F.obj i)), IsConstructible Ei ∧ C.π.app i ⁻¹' Ei = E := by
  -- Generate constructible subsets from open retrocompact pieces, unions, and complements.
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hU_open hU_retro =>
      have hU_constructible : IsConstructible U := hU_retro.isConstructible hU_open
      obtain ⟨i, Ei, hEi⟩ :=
        exists_stage_compact_open_of_constructible_open (C := C) hC hF hU_constructible hU_open
      refine ⟨i, Ei, ?_, hEi⟩
      -- Compact opens on spectral spaces are constructible.
      exact Ei.isCompact.isConstructible Ei.isOpen
  | union s hs t ht hs' ht' =>
      rcases hs' with ⟨i, Ei, hEi_constructible, hEi⟩
      rcases ht' with ⟨j, Ej, hEj_constructible, hEj⟩
      -- Merge the two descended pieces on a common refinement stage.
      exact merge_constructible_stage_descents (C := C) hF hEi_constructible hEj_constructible hEi hEj
  | compl s hs hs' =>
      rcases hs' with ⟨i, Ei, hEi_constructible, hEi⟩
      refine ⟨i, Eiᶜ, hEi_constructible.compl, ?_⟩
      -- Complements stay on the same stage because inverse image commutes with complement.
      ext x
      constructor
      · intro hx
        change C.π.app i x ∉ Ei at hx
        intro hsx
        have hsx' : x ∈ C.π.app i ⁻¹' Ei := by
          rw [hEi]
          exact hsx
        exact hx (by simpa using hsx')
      · intro hx
        change C.π.app i x ∉ Ei
        intro hxEi
        apply hx
        rw [← hEi]
        exact hxEi

-- Proof sketch: package the open constructible subset as a compact open on the spectral limit,
-- descend it by the helper above, and return the resulting compact-open stage subset.
/-- If the constructible subset in Lemma 5.24.4 is open, then the descended constructible subset
can be chosen compact open. -/
theorem open_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_open : IsOpen E) :
    ∃ (i : J) (Ei : CompactOpens (F.obj i)), C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  -- Reuse the compact-open descent helper proved above.
  simpa using exists_stage_compact_open_of_constructible_open (C := C) hC hF hE hE_open

-- Proof sketch: apply the open descent result to the complement and then complement the stagewise
-- compact open.
/-- If the constructible subset in Lemma 5.24.4 is closed, then the descended constructible subset
can be chosen closed. -/
theorem closed_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_closed : IsClosed E) :
    ∃ (i : J) (Ei : Closeds (F.obj i)),
      IsConstructible (Ei : Set (F.obj i)) ∧ C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := by
  -- Reuse the closed-case helper obtained by complementing the open descent.
  simpa using exists_stage_closed_of_constructible_closed (C := C) hC hF hE hE_closed

end
