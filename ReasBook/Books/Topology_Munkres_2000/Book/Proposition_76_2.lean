module

public import Topology_Munkres_2000.Book.Proposition_76_2.Pasting
public import Topology_Munkres_2000.Book.Proposition_76_2.BoundaryConcatenation
public import Topology_Munkres_2000.Book.Proposition_74_1
public import Topology_Munkres_2000.Book.Definition_76_2.Translation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Homeomorph.TransferInstance
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Proposition_76_2.Pasting

public section

universe u v w

open LabellingScheme
open LabellingScheme.PolygonalRegions
open LabellingScheme.PolygonalRegions.Pasting
open scoped Pointwise

namespace Relation

/-- Helper for Proposition 76.2: an equivalence carrying the generators of one
relation to another also carries their generated equivalence relations. -/
theorem eqvGen_iff_map_equiv {A : Type u} {B : Type v} (e : A ≃ B)
    {r : A → A → Prop} {s : B → B → Prop}
    (hgenerators : ∀ x y, r x y ↔ s (e x) (e y)) (x y : A) :
    EqvGen r x y ↔ EqvGen s (e x) (e y) := by
  constructor
  · intro hxy
    -- Push each generator through `e`, preserving the closure constructors.
    induction hxy with
    | rel a b hab => exact EqvGen.rel _ _ ((hgenerators a b).mp hab)
    | refl a => exact EqvGen.refl _
    | symm a b _ ih => exact EqvGen.symm _ _ ih
    | trans a b d _ _ hab hbd => exact EqvGen.trans _ _ _ hab hbd
  · intro hxy
    -- Pull the generated relation back through `e.symm`, then cancel both transports.
    have hpull : ∀ {a b}, EqvGen s a b → EqvGen r (e.symm a) (e.symm b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
          exact EqvGen.rel _ _ ((hgenerators (e.symm a) (e.symm b)).mpr (by
            simpa only [e.apply_symm_apply] using hab))
      | refl a => exact EqvGen.refl _
      | symm a b _ ih => exact EqvGen.symm _ _ ih
      | trans a b d _ _ hab hbd => exact EqvGen.trans _ _ _ hab hbd
    simpa only [e.symm_apply_apply] using hpull hxy

end Relation

namespace Topology.IsQuotientMap

universe u₁ u₂ u₃ u₄

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃} {W : Type u₄}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

/-- Helper for Proposition 76.2: the sum of two quotient maps is a quotient map. -/
lemma sumMap {f : X → Y} {g : Z → W}
    (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g) :
    Topology.IsQuotientMap (Sum.map f g) := by
  -- Test the quotient topology separately on the two open summands.
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_,
    hf.surjective.sumMap hg.surjective⟩
  intro subset
  rw [isOpen_sum_iff, isOpen_sum_iff]
  change
    (IsOpen (f ⁻¹' (Sum.inl ⁻¹' subset)) ∧ IsOpen (g ⁻¹' (Sum.inr ⁻¹' subset))) ↔
      IsOpen (Sum.inl ⁻¹' subset) ∧ IsOpen (Sum.inr ⁻¹' subset)
  -- Each component is open exactly when its inverse image under the corresponding map is.
  exact and_congr hf.isCoinducing.isOpen_preimage hg.isCoinducing.isOpen_preimage

end Topology.IsQuotientMap

namespace LabellingScheme.PolygonalRegions.Pasting

/-- Helper for Proposition 76.2: a dependent family over `Option` splits into
its distinguished `none` fibre and the sigma of its `some` fibres. -/
private def sigmaOptionEquiv {I : Type u} (X : Option I → Type v) :
    ((i : Option I) × X i) ≃ X none ⊕ ((i : I) × X (some i)) :=
  { toFun := fun
      | ⟨none, x⟩ => Sum.inl x
      | ⟨some i, x⟩ => Sum.inr ⟨i, x⟩
    invFun := fun
      | Sum.inl x => ⟨none, x⟩
      | Sum.inr ⟨i, x⟩ => ⟨some i, x⟩
    left_inv := fun
      | ⟨none, _⟩ => rfl
      | ⟨some _, _⟩ => rfl
    right_inv := fun
      | Sum.inl _ => rfl
      | Sum.inr ⟨_, _⟩ => rfl }

/-- Helper for Proposition 76.2: the dependent option splitting is continuous
for the canonical disjoint-union topologies. -/
private theorem continuous_sigmaOptionEquiv {I : Type u} (X : Option I → Type v)
    [familyTopology : ∀ i, TopologicalSpace (X i)] :
    Continuous (sigmaOptionEquiv X) := by
  -- Check continuity separately on the `none` fibre and every `some` fibre.
  rw [continuous_sigma_iff]
  intro i
  cases i with
  | none =>
      change Continuous
        (Sum.inl : X none → X none ⊕ ((i : I) × X (some i)))
      exact continuous_inl
  | some i =>
      have hmk : Continuous
          (fun x : X (some i) ↦ (⟨i, x⟩ : (j : I) × X (some j))) :=
        @continuous_sigmaMk I (fun j ↦ X (some j))
          (fun j ↦ familyTopology (some j)) i
      change Continuous (fun x : X (some i) ↦
        (Sum.inr ⟨i, x⟩ : X none ⊕ ((j : I) × X (some j))))
      exact continuous_inr.comp hmk

/-- Helper for Proposition 76.2: the inverse dependent option splitting is
continuous for the canonical disjoint-union topologies. -/
private theorem continuous_sigmaOptionEquiv_symm {I : Type u}
    (X : Option I → Type v) [familyTopology : ∀ i, TopologicalSpace (X i)] :
    Continuous (sigmaOptionEquiv X).symm := by
  -- The two inverse branches are canonical sigma inclusions.
  have hnone : Continuous (fun x : X none ↦ (⟨none, x⟩ : (i : Option I) × X i)) :=
    @continuous_sigmaMk (Option I) X familyTopology none
  have hsome : Continuous
      (fun z : (i : I) × X (some i) ↦
        (⟨some z.1, z.2⟩ : (i : Option I) × X i)) := by
    apply continuous_sigma
    intro i
    exact @continuous_sigmaMk (Option I) X familyTopology (some i)
  let inverse : X none ⊕ ((i : I) × X (some i)) → (i : Option I) × X i :=
    Sum.elim (fun x ↦ ⟨none, x⟩) (fun z ↦ ⟨some z.1, z.2⟩)
  have hinverse : ⇑(sigmaOptionEquiv X).symm = inverse := by
    funext z
    cases z with
    | inl x => rfl
    | inr z => rcases z with ⟨i, x⟩; rfl
  rw [hinverse]
  exact hnone.sumElim hsome

/-- Helper for Proposition 76.2: the dependent option splitting as a homeomorphism. -/
private noncomputable def sigmaOptionHomeomorph {I : Type u}
    (X : Option I → Type v) [∀ i, TopologicalSpace (X i)] :
    ((i : Option I) × X i) ≃ₜ X none ⊕ ((i : I) × X (some i)) :=
  ⟨sigmaOptionEquiv X, continuous_sigmaOptionEquiv X,
    continuous_sigmaOptionEquiv_symm X⟩

/-- Helper for Proposition 76.2: expose the canonical finite enumeration carried
by a labelling scheme's multiset of occurrences. -/
@[reducible] private noncomputable def occurrenceFintype {α : Type u}
    (scheme : LabellingScheme α) : Fintype (Occurrence scheme) :=
  @Multiset.fintypeCoe (PolygonWord α) (Classical.decEq _) scheme

/-- Helper for Proposition 76.2: the number of retained occurrences, computed
using their canonical multiset enumeration. -/
private noncomputable def retainedOccurrenceCount {α : Type u}
    (scheme : LabellingScheme α) : ℕ :=
  @Fintype.card (Occurrence scheme) (occurrenceFintype scheme)

/-- Helper for Proposition 76.2: retained occurrences are enumerated by a finite
index in the lowest universe. -/
private noncomputable def retainedOccurrenceEquiv {α : Type u}
    (scheme : LabellingScheme α) :
    Occurrence scheme ≃ Fin (retainedOccurrenceCount scheme) :=
  @Fintype.equivFin (Occurrence scheme) (occurrenceFintype scheme)

/-- Helper for Proposition 76.2: classify the two distinguished occurrences first,
then enumerate all retained occurrences by a finite low-universe index. -/
private noncomputable def splitOccurrenceEquiv {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    Occurrence (word₁ ::ₘ word₂ ::ₘ rest) ≃
      Option (Option (Fin (retainedOccurrenceCount rest))) :=
  (consOccurrenceEquiv word₁ (word₂ ::ₘ rest)).trans
    (Equiv.optionCongr
      ((consOccurrenceEquiv word₂ rest).trans
        (Equiv.optionCongr (retainedOccurrenceEquiv rest))))

/-- Helper for Proposition 76.2: equality of region indices induces the canonical
equivalence between their dependent component types. -/
private noncomputable def regionCastEquiv {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {left right : Occurrence scheme} (h : left = right) :
    regions.Point left ≃ regions.Point right :=
  match h with
  | rfl => Equiv.refl (regions.Point left)

/-- Helper for Proposition 76.2: the region-cast equivalence acts by the
ordinary dependent transport along the region equality. -/
private theorem regionCastEquiv_apply {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {left right : Occurrence scheme} (h : left = right)
    (x : regions.Point left) :
    regionCastEquiv regions h x = h ▸ x := by
  -- Identifying the region indices reduces both maps to the identity.
  subst right
  rfl

/-- Helper for Proposition 76.2: a dependent sigma point transported backward
along a component-index equality represents the original point. -/
private theorem sigmaMk_regionCastEquiv_symm {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {left right : Occurrence scheme} (h : left = right)
    (x : regions.Point right) :
    (⟨right, x⟩ : regions.Source) =
      ⟨left, (regionCastEquiv regions h).symm x⟩ := by
  subst right
  rfl

/-- Helper for Proposition 76.2: transport between equal region indices is a
homeomorphism for the corresponding stored component topologies. -/
private theorem regionCastEquiv_isHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {left right : Occurrence scheme} (h : left = right) :
    @IsHomeomorph (regions.Point left) (regions.Point right)
      (regions.topology left) (regions.topology right) (regionCastEquiv regions h) := by
  -- After identifying the indices, this is the identity homeomorphism.
  subst right
  exact @IsHomeomorph.id (regions.Point left) (regions.topology left)

/-- Helper for Proposition 76.2: the canonical sigma topology after reindexing
occurrences keeps the stored topology on each transported component. -/
@[reducible] private def canonicalReindexedSourceTopology {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    TopologicalSpace ((i : I) × regions.Point (indexEquiv.symm i)) :=
  ⨆ i, TopologicalSpace.coinduced (Sigma.mk i)
    (regions.topology (indexEquiv.symm i))

/-- Helper for Proposition 76.2: reindexing occurrences and transporting each
dependent component gives the underlying equivalence of split sources. -/
private noncomputable def sourceReindexingEquiv {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {ι : Type w} (indexEquiv : Occurrence scheme ≃ ι) :
    regions.Source ≃ ((i : ι) × regions.Point (indexEquiv.symm i)) :=
  Equiv.sigmaCongr indexEquiv fun region ↦
    regionCastEquiv regions (indexEquiv.symm_apply_apply region).symm

/-- Helper for Proposition 76.2: source reindexing agrees with the canonical
base-change equivalence whose inverse has a direct sigma computation rule. -/
private theorem sourceReindexingEquiv_eq_sigmaCongrLeft {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    sourceReindexingEquiv regions indexEquiv =
      Equiv.sigmaCongrLeft' indexEquiv := by
  -- Both equivalences change only the sigma index; proof irrelevance identifies
  -- their dependent fibre transports.
  apply Equiv.ext
  rintro ⟨region, x⟩
  apply Sigma.ext
  · rfl
  · have hproof : indexEquiv.symm.right_inv' region =
        indexEquiv.symm_apply_apply region := Subsingleton.elim _ _
    simp [sourceReindexingEquiv, Equiv.sigmaCongrLeft', Equiv.sigmaCongr,
      Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft, regionCastEquiv_apply]

/-- Helper for Proposition 76.2: source reindexing is continuous for the
canonical sigma topology on the reindexed components. -/
private theorem continuous_sourceReindexingEquiv {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    @Continuous regions.Source
      ((i : I) × regions.Point (indexEquiv.symm i))
      regions.sourceTopology (canonicalReindexedSourceTopology regions indexEquiv)
      (sourceReindexingEquiv regions indexEquiv) := by
  -- Check the sigma map on one original component at a time.
  letI sourceComponentTopology : ∀ region, TopologicalSpace (regions.Point region) :=
    regions.topology
  letI targetComponentTopology : ∀ i,
      TopologicalSpace (regions.Point (indexEquiv.symm i)) :=
    fun i ↦ regions.topology (indexEquiv.symm i)
  rw [regions.sourceTopology_eq_sigma]
  refine @continuous_sigma
    ((i : I) × regions.Point (indexEquiv.symm i))
    (Occurrence scheme) (fun region ↦ regions.Point region)
    sourceComponentTopology (canonicalReindexedSourceTopology regions indexEquiv)
    (sourceReindexingEquiv regions indexEquiv) ?_
  intro region
  let fiberMap : regions.Point region →
      ((i : I) × regions.Point (indexEquiv.symm i)) :=
    fun x ↦ ⟨indexEquiv region,
      regionCastEquiv regions (indexEquiv.symm_apply_apply region).symm x⟩
  have hfiber :
      (fun x ↦ sourceReindexingEquiv regions indexEquiv ⟨region, x⟩) =
        fiberMap := by
    funext x
    rfl
  rw [hfiber]
  exact continuous_sigmaMk.comp ((regionCastEquiv_isHomeomorph regions
    (indexEquiv.symm_apply_apply region).symm).continuous)

/-- Helper for Proposition 76.2: reindexing the dependent source is a
homeomorphism for the canonical component topologies. -/
private theorem sourceReindexingEquiv_isHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    @IsHomeomorph regions.Source
      ((i : I) × regions.Point (indexEquiv.symm i))
      regions.sourceTopology (canonicalReindexedSourceTopology regions indexEquiv)
      (sourceReindexingEquiv regions indexEquiv) := by
  let sourceComponentTopology : ∀ region,
      TopologicalSpace (regions.Point region) := regions.topology
  let targetComponentTopology : ∀ i,
      TopologicalSpace (regions.Point (indexEquiv.symm i)) :=
    fun i ↦ regions.topology (indexEquiv.symm i)
  let fiberMap : ∀ region, regions.Point region →
      regions.Point (indexEquiv.symm (indexEquiv region)) :=
    fun region ↦ regionCastEquiv regions
      (indexEquiv.symm_apply_apply region).symm
  have hfibers : ∀ region,
      @IsHomeomorph _ _ (sourceComponentTopology region)
        (targetComponentTopology (indexEquiv region)) (fiberMap region) := by
    intro region
    exact regionCastEquiv_isHomeomorph regions
      (indexEquiv.symm_apply_apply region).symm
  have hsigma := @IsHomeomorph.sigmaMap
    (Occurrence scheme) I (fun region ↦ regions.Point region)
    (fun i ↦ regions.Point (indexEquiv.symm i))
    sourceComponentTopology targetComponentTopology indexEquiv
    indexEquiv.bijective fiberMap hfibers
  have hfunction : ⇑(sourceReindexingEquiv regions indexEquiv) =
      Sigma.map indexEquiv fiberMap := by
    funext point
    rcases point with ⟨region, x⟩
    rfl
  rw [regions.sourceTopology_eq_sigma, hfunction]
  exact hsigma

/-- Helper for Proposition 76.2: the inverse-computable sigma reindexing is
continuous for the canonical component topologies. -/
private theorem continuous_sigmaCongrLeftSourceReindexing {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    @Continuous regions.Source
      ((i : I) × regions.Point (indexEquiv.symm i))
      regions.sourceTopology (canonicalReindexedSourceTopology regions indexEquiv)
      (Equiv.sigmaCongrLeft' indexEquiv) := by
  -- Replace the canonical base-change map by the already checked source map.
  rw [← sourceReindexingEquiv_eq_sigmaCongrLeft regions indexEquiv]
  exact continuous_sourceReindexingEquiv regions indexEquiv

/-- Helper for Proposition 76.2: the inverse-computable sigma reindexing is a
homeomorphism for the canonical component topologies. -/
private theorem sigmaCongrLeftSourceReindexing_isHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    @IsHomeomorph regions.Source
      ((i : I) × regions.Point (indexEquiv.symm i))
      regions.sourceTopology (canonicalReindexedSourceTopology regions indexEquiv)
      (Equiv.sigmaCongrLeft' indexEquiv) := by
  -- Transport the homeomorphism property along equality of the two reindexings.
  rw [← sourceReindexingEquiv_eq_sigmaCongrLeft regions indexEquiv]
  exact sourceReindexingEquiv_isHomeomorph regions indexEquiv

/-- Helper for Proposition 76.2: the inverse-computable sigma reindexing has a
continuous inverse for the canonical component topologies. -/
private theorem continuous_sigmaCongrLeftSourceReindexing_symm {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    @Continuous ((i : I) × regions.Point (indexEquiv.symm i)) regions.Source
      (canonicalReindexedSourceTopology regions indexEquiv) regions.sourceTopology
      (Equiv.sigmaCongrLeft' indexEquiv).symm := by
  -- Extract inverse continuity from the already established homeomorphism property.
  exact ((@Equiv.isHomeomorph_iff _ _
    regions.sourceTopology (canonicalReindexedSourceTopology regions indexEquiv)
    (Equiv.sigmaCongrLeft' indexEquiv)).mp
      (sigmaCongrLeftSourceReindexing_isHomeomorph regions indexEquiv)).2

/-- Helper for Proposition 76.2: the canonical source reindexing bundled as a
homeomorphism with explicit stored component topologies. -/
private noncomputable def canonicalSourceReindexingHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {I : Type w} (indexEquiv : Occurrence scheme ≃ I) :
    @Homeomorph regions.Source
      ((i : I) × regions.Point (indexEquiv.symm i))
      regions.sourceTopology (canonicalReindexedSourceTopology regions indexEquiv) :=
  -- Route correction: bundle the explicit sigma equivalence itself so its inverse
  -- computes by branches; `IsHomeomorph.homeomorph` chose an opaque `surjInv`.
  @Homeomorph.mk _ _ regions.sourceTopology
    (canonicalReindexedSourceTopology regions indexEquiv)
    (Equiv.sigmaCongrLeft' indexEquiv)
    (continuous_sigmaCongrLeftSourceReindexing regions indexEquiv)
    (continuous_sigmaCongrLeftSourceReindexing_symm regions indexEquiv)

/-- Helper for Proposition 76.2: transport the source topology across the explicit
reindexing equivalence, avoiding any cross-module unfolding of `sourceTopology`. -/
@[reducible] private noncomputable def reindexedSourceTopology {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {ι : Type w} (indexEquiv : Occurrence scheme ≃ ι) :
    TopologicalSpace ((i : ι) × regions.Point (indexEquiv.symm i)) :=
  (sourceReindexingEquiv regions indexEquiv).symm.topologicalSpace

/-- Helper for Proposition 76.2: reindexing the occurrences of a polygonal family
gives a homeomorphism of its disjoint-union source, including dependent fibres. -/
private noncomputable def sourceReindexingHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {ι : Type w} (indexEquiv : Occurrence scheme ≃ ι) :
    @Homeomorph regions.Source
      ((i : ι) × regions.Point (indexEquiv.symm i))
      regions.sourceTopology (reindexedSourceTopology regions indexEquiv) :=
  -- Local instance justification (transported source): this topology is not globally
  -- inferable because it depends on the chosen occurrence equivalence.
  letI : TopologicalSpace ((i : ι) × regions.Point (indexEquiv.symm i)) :=
    reindexedSourceTopology regions indexEquiv
  ((sourceReindexingEquiv regions indexEquiv).symm.homeomorph).symm

/-- Helper for Proposition 76.2: the source reindexing records exactly the image
of the original occurrence in the first sigma projection. -/
private theorem sourceReindexingHomeomorph_fst {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {ι : Type w} (indexEquiv : Occurrence scheme ≃ ι) (point : regions.Source) :
    (sourceReindexingHomeomorph regions indexEquiv point).1 = indexEquiv point.1 := by
  -- The transported topology changes no data in the underlying sigma equivalence.
  rfl

/-- Helper for Proposition 76.2: the split source has a low-universe finite
decomposition whose three branches are the left, right, and retained regions. -/
private theorem existsSplitSourceDecomposition {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) :
    ∃ sourceHomeomorph : @Homeomorph regions.Source
        ((i : Option (Option (Fin (retainedOccurrenceCount rest)))) ×
          regions.Point ((splitOccurrenceEquiv word₁ word₂ rest).symm i))
        regions.sourceTopology
        (reindexedSourceTopology (ι :=
          Option (Option (Fin (retainedOccurrenceCount rest)))) regions
          (splitOccurrenceEquiv word₁ word₂ rest)),
      (∀ x : regions.Point (firstOccurrence word₁ word₂ rest),
        (sourceHomeomorph ⟨firstOccurrence word₁ word₂ rest, x⟩).1 = none) ∧
      (∀ x : regions.Point (secondOccurrence word₁ word₂ rest),
        (sourceHomeomorph ⟨secondOccurrence word₁ word₂ rest, x⟩).1 = some none) ∧
      ∀ (region : Occurrence rest)
        (x : regions.Point (splitRestOccurrence word₁ word₂ rest region)),
        (sourceHomeomorph ⟨splitRestOccurrence word₁ word₂ rest region, x⟩).1 =
          some (some (retainedOccurrenceEquiv rest region)) := by
  let sourceHomeomorph :=
    sourceReindexingHomeomorph regions (splitOccurrenceEquiv word₁ word₂ rest)
  refine ⟨sourceHomeomorph, ?_, ?_, ?_⟩
  · intro x
    -- The outer `none` branch is exactly the first adjoined occurrence.
    rw [sourceReindexingHomeomorph_fst]
    simp only [splitOccurrenceEquiv, firstOccurrence, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_none]
  · intro x
    -- The outer `some` and inner `none` branches select the second occurrence.
    rw [sourceReindexingHomeomorph_fst]
    simp only [splitOccurrenceEquiv, secondOccurrence, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_some, Option.map_none]
  · intro region x
    -- Retained occurrences pass through both cons splittings and the finite enumeration.
    rw [sourceReindexingHomeomorph_fst]
    simp only [splitOccurrenceEquiv, splitRestOccurrence, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_some]

/-- Helper for Proposition 76.2: transport the equivalence relation generated by
the `c`-edge pairings across a source equivalence. -/
private def transportedLabelSetoid {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (c : α) {Y : Type w}
    (sourceEquiv : regions.Source ≃ Y) : Setoid Y :=
  Relation.EqvGen.setoid fun a b ↦
    regions.EdgeRelatedAt c (sourceEquiv.symm a) (sourceEquiv.symm b)

/-- Helper for Proposition 76.2: quotienting any low-universe reindexing of the
source by the transported `c`-edge relation performs exactly the first paste. -/
private theorem existsLabelQuotientOfSourceHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme) (c : α)
    {Y : Type v} [TopologicalSpace Y] (sourceHomeomorph : regions.Source ≃ₜ Y) :
    ∃ (intermediate : TopCat.{v}) (firstPaste : regions.Source → intermediate),
      regions.PastesLabel c firstPaste := by
  let labelSetoid := transportedLabelSetoid regions c sourceHomeomorph.toEquiv
  let intermediate : TopCat.{v} := TopCat.of (Quotient labelSetoid)
  let firstPaste : regions.Source → intermediate :=
    fun point ↦ Quotient.mk' (sourceHomeomorph point)
  refine ⟨intermediate, firstPaste, ?_⟩
  constructor
  · -- A homeomorphism followed by the canonical quotient is again a quotient map.
    exact isQuotientMap_quotient_mk'.comp sourceHomeomorph.isQuotientMap
  · intro x y
    -- Quotient equality is the transported generated relation; pull it back through the source map.
    change Quotient.mk' (sourceHomeomorph x) = Quotient.mk' (sourceHomeomorph y) ↔ _
    calc
      Quotient.mk' (sourceHomeomorph x) = Quotient.mk' (sourceHomeomorph y) ↔
          labelSetoid.r (sourceHomeomorph x) (sourceHomeomorph y) := Quotient.eq''
      _ ↔ Relation.EqvGen (regions.EdgeRelatedAt c) x y :=
        (Relation.eqvGen_iff_map_equiv sourceHomeomorph.toEquiv
          (fun a b ↦ by
            simp only [Equiv.symm_apply_apply]) x y).symm

/-- Helper for Proposition 76.2: the explicit finite source decomposition yields
a first-paste intermediate living in the polygon-point universe. -/
private theorem existsLowUniverseFirstPaste {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α) :
    ∃ (intermediate : TopCat.{v}) (firstPaste : regions.Source → intermediate),
      regions.PastesLabel c firstPaste := by
  obtain ⟨sourceHomeomorph, _, _, _⟩ :=
    existsSplitSourceDecomposition word₁ word₂ rest regions
  -- The decomposition's transported topology makes the canonical quotient universe-correct.
  -- Local instance justification (chosen decomposition): the codomain topology depends on
  -- the equivalence returned by the preceding existential and is therefore not inferable.
  letI : TopologicalSpace
      ((i : Option (Option (Fin (retainedOccurrenceCount rest)))) ×
        regions.Point ((splitOccurrenceEquiv word₁ word₂ rest).symm i)) :=
    reindexedSourceTopology regions (splitOccurrenceEquiv word₁ word₂ rest)
  exact existsLabelQuotientOfSourceHomeomorph regions c sourceHomeomorph

/-- Helper for Proposition 76.2: the retained components, with their canonical
disjoint-union topology, form the unchanged summand after the selected edge paste. -/
private noncomputable def selectedEdgeRetainedSource {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) : TopCat.{v} :=
  @TopCat.of
    ((i : Fin (retainedOccurrenceCount rest)) ×
      regions.Point
        ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some i))))
    (⨆ i, TopologicalSpace.coinduced (Sigma.mk i)
      (regions.topology
        ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some i)))))

/-- Helper for Proposition 76.2: the distinguished first occurrence is the
outer `none` branch of the canonical source enumeration. -/
private theorem splitOccurrenceEquiv_first {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    splitOccurrenceEquiv word₁ word₂ rest (firstOccurrence word₁ word₂ rest) =
      none := by
  -- Cancel the outer multiset-cons equivalence at its distinguished inverse image.
  simp only [splitOccurrenceEquiv, firstOccurrence, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_none]

/-- Helper for Proposition 76.2: the inverse source enumeration sends its
outer distinguished branch back to the first occurrence. -/
private theorem splitOccurrenceEquiv_symm_first {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    (splitOccurrenceEquiv word₁ word₂ rest).symm none =
      firstOccurrence word₁ word₂ rest := by
  -- Apply the forward enumeration and cancel the equivalence.
  apply (splitOccurrenceEquiv word₁ word₂ rest).injective
  rw [Equiv.apply_symm_apply, splitOccurrenceEquiv_first]

/-- Helper for Proposition 76.2: the distinguished second occurrence is the
inner `none` branch of the canonical source enumeration. -/
private theorem splitOccurrenceEquiv_second {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    splitOccurrenceEquiv word₁ word₂ rest (secondOccurrence word₁ word₂ rest) =
      some none := by
  -- Cancel both multiset-cons equivalences, retaining the outer `some` branch.
  simp only [splitOccurrenceEquiv, secondOccurrence, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_some,
    Option.map_none]

/-- Helper for Proposition 76.2: the inverse source enumeration sends its
inner distinguished branch back to the second occurrence. -/
private theorem splitOccurrenceEquiv_symm_second {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    (splitOccurrenceEquiv word₁ word₂ rest).symm (some none) =
      secondOccurrence word₁ word₂ rest := by
  -- Apply the forward enumeration and cancel the equivalence.
  apply (splitOccurrenceEquiv word₁ word₂ rest).injective
  rw [Equiv.apply_symm_apply, splitOccurrenceEquiv_second]

/-- Helper for Proposition 76.2: every retained occurrence occupies the doubly
`some` branch of the canonical three-way source enumeration. -/
private theorem splitOccurrenceEquiv_retained {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (region : Occurrence rest) :
    splitOccurrenceEquiv word₁ word₂ rest
        (splitRestOccurrence word₁ word₂ rest region) =
      some (some (retainedOccurrenceEquiv rest region)) := by
  simp only [splitOccurrenceEquiv, splitRestOccurrence, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_some]

/-- Helper for Proposition 76.2: the full source is canonically the sum of the
two geometric regions carrying the selected edges and all retained components. -/
private noncomputable def selectedEdgeSourceHomeomorph {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest)) :
    regions.Source ≃ₜ
      ((leftRegion.polygon.region ⊕ rightRegion.polygon.region) ⊕
        selectedEdgeRetainedSource word₁ word₂ rest regions) :=
  -- Local instance justification (dependent component topology): the source family
  -- stores these topologies as data, so no global instance can infer them.
  letI _componentTopology : ∀ i : Option (Option (Fin (retainedOccurrenceCount rest))),
      TopologicalSpace
        (regions.Point ((splitOccurrenceEquiv word₁ word₂ rest).symm i)) :=
    fun i ↦ regions.topology ((splitOccurrenceEquiv word₁ word₂ rest).symm i)
  let reindex := canonicalSourceReindexingHomeomorph regions
    (splitOccurrenceEquiv word₁ word₂ rest)
  let outerSplit := sigmaOptionHomeomorph
    (fun i : Option (Option (Fin (retainedOccurrenceCount rest))) ↦
      regions.Point ((splitOccurrenceEquiv word₁ word₂ rest).symm i))
  let innerSplit := sigmaOptionHomeomorph
    (fun i : Option (Fin (retainedOccurrenceCount rest)) ↦
      regions.Point ((splitOccurrenceEquiv word₁ word₂ rest).symm (some i)))
  reindex |>.trans outerSplit |>.trans
    (Homeomorph.sumCongr (.refl _) innerSplit) |>.trans
    (Homeomorph.sumAssoc _ _ _).symm |>.trans
    (Homeomorph.sumCongr
      (Homeomorph.sumCongr leftRegion.homeomorph rightRegion.homeomorph)
      (.refl _))

/-- Helper for Proposition 76.2: the inverse source decomposition recovers a
first-component point from the geometric left summand. -/
private theorem selectedEdgeSourceHomeomorph_symm_first {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (x : leftRegion.polygon.region) :
    (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion).symm
        (Sum.inl (Sum.inl x)) =
      ⟨firstOccurrence word₁ word₂ rest,
        (@Homeomorph.toEquiv _ _ (regions.topology (firstOccurrence word₁ word₂ rest))
          inferInstance leftRegion.homeomorph).symm x⟩ := by
  apply Sigma.ext
  · exact splitOccurrenceEquiv_symm_first word₁ word₂ rest
  · exact HEq.rfl

/-- Helper for Proposition 76.2: the inverse source decomposition recovers a
second-component point from the geometric right summand. -/
private theorem selectedEdgeSourceHomeomorph_symm_second {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (x : rightRegion.polygon.region) :
    (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion).symm
        (Sum.inl (Sum.inr x)) =
      ⟨secondOccurrence word₁ word₂ rest,
        (@Homeomorph.toEquiv _ _ (regions.topology (secondOccurrence word₁ word₂ rest))
          inferInstance rightRegion.homeomorph).symm x⟩ := by
  apply Sigma.ext
  · exact splitOccurrenceEquiv_symm_second word₁ word₂ rest
  · exact HEq.rfl

/-- Helper for Proposition 76.2: the source decomposition sends a point of the
first distinguished component to the geometric left summand. -/
private theorem selectedEdgeSourceHomeomorph_first {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (x : regions.Point (firstOccurrence word₁ word₂ rest)) :
    selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion
        ⟨firstOccurrence word₁ word₂ rest, x⟩ =
      Sum.inl (Sum.inl (leftRegion.homeomorph x)) := by
  -- Compare inverse images, where the source reindexing has a direct branch rule.
  apply (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
    rightRegion).symm.injective
  rw [Homeomorph.symm_apply_apply, selectedEdgeSourceHomeomorph_symm_first]
  exact congrArg (Sigma.mk (firstOccurrence word₁ word₂ rest))
    ((@Homeomorph.toEquiv _ _
      (regions.topology (firstOccurrence word₁ word₂ rest)) inferInstance
      leftRegion.homeomorph).symm_apply_apply x).symm

/-- Helper for Proposition 76.2: the source decomposition sends a point of the
second distinguished component to the geometric right summand. -/
private theorem selectedEdgeSourceHomeomorph_second {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (x : regions.Point (secondOccurrence word₁ word₂ rest)) :
    selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion
        ⟨secondOccurrence word₁ word₂ rest, x⟩ =
      Sum.inl (Sum.inr (rightRegion.homeomorph x)) := by
  -- Compare inverse images, where the source reindexing has a direct branch rule.
  apply (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
    rightRegion).symm.injective
  rw [Homeomorph.symm_apply_apply, selectedEdgeSourceHomeomorph_symm_second]
  exact congrArg (Sigma.mk (secondOccurrence word₁ word₂ rest))
    ((@Homeomorph.toEquiv _ _
      (regions.topology (secondOccurrence word₁ word₂ rest)) inferInstance
      rightRegion.homeomorph).symm_apply_apply x).symm

/-- Helper for Proposition 76.2: quotient the distinguished geometric pair by
the edge adjunction while leaving every retained component unchanged. -/
private noncomputable def selectedEdgeFirstPaste {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon) :
    regions.Source →
      (gluing.Realization ⊕ selectedEdgeRetainedSource word₁ word₂ rest regions) :=
  fun point ↦ Sum.map
    (AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap) id
    (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion point)

/-- Helper for Proposition 76.2: on the first component, the direct paste is
the quotient representative of the geometric left summand. -/
private theorem selectedEdgeFirstPaste_first {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (x : regions.Point (firstOccurrence word₁ word₂ rest)) :
    selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing
        ⟨firstOccurrence word₁ word₂ rest, x⟩ =
      Sum.inl (AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
        (Sum.inl (leftRegion.homeomorph x))) := by
  -- Normalize the source branch; the sum map then exposes its quotient representative.
  rw [selectedEdgeFirstPaste, selectedEdgeSourceHomeomorph_first]
  rfl

/-- Helper for Proposition 76.2: on the second component, the direct paste is
the quotient representative of the geometric right summand. -/
private theorem selectedEdgeFirstPaste_second {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (x : regions.Point (secondOccurrence word₁ word₂ rest)) :
    selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing
        ⟨secondOccurrence word₁ word₂ rest, x⟩ =
      Sum.inl (AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
        (Sum.inr (rightRegion.homeomorph x))) := by
  -- Normalize the source branch; the sum map then exposes its quotient representative.
  rw [selectedEdgeFirstPaste, selectedEdgeSourceHomeomorph_second]
  rfl

/-- Helper for Proposition 76.2: the direct selected-edge paste is a quotient
map onto the geometric adjunction space plus the retained components. -/
private theorem selectedEdgeFirstPaste_isQuotientMap {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon) :
    Topology.IsQuotientMap
      (selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing) := by
  -- Sum the adjunction quotient with the identity, then precompose by the source homeomorphism.
  exact ((AdjunctionSpace.quotientMap_isQuotientMap gluing.attachingSubset
    gluing.attachingMap).sumMap Topology.IsQuotientMap.id).comp
      (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
        rightRegion).isQuotientMap

end LabellingScheme.PolygonalRegions.Pasting

namespace CyclicPolygon

end CyclicPolygon

namespace LabellingScheme.PolygonalRegions.CyclicRegion

/-- Helper for Proposition 76.2: ambient translation gives a homeomorphism from a
presented component to the translated polygonal region. -/
noncomputable def translatedHomeomorph {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme} {region : Occurrence scheme}
    (presentation : CyclicRegion regions region) (offset : EuclideanSpace ℝ (Fin 2)) :
    RegionHomeomorph regions region (presentation.polygon.translate offset).region :=
  @Homeomorph.trans _ _ _ (regions.topology region) inferInstance inferInstance
    presentation.homeomorph
    ((Homeomorph.addRight offset).image presentation.polygon.region |>.trans
      (Homeomorph.setCongr (presentation.polygon.translate_region offset).symm))

/-- Helper for Proposition 76.2: translated vertices retain the original affine
edge parametrization after applying ambient translation. -/
theorem translatedEdgeCompatibility {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme} {region : Occurrence scheme}
    (presentation : CyclicRegion regions region) (offset : EuclideanSpace ℝ (Fin 2))
    (edge : Fin region.1.1.length) (t : unitInterval) :
    ((presentation.translatedHomeomorph offset (regions.edge region edge t) :
        (presentation.polygon.translate offset).region) : EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap ((presentation.polygon.translate offset).toPolygon.vertices edge)
        ((presentation.polygon.translate offset).toPolygon.vertices
          (finRotate region.1.1.length edge)) (t : ℝ) := by
  -- Move to ambient points, then use the original edge compatibility and translated vertices.
  change Homeomorph.addRight offset
    (presentation.homeomorph (regions.edge region edge t) : EuclideanSpace ℝ (Fin 2)) = _
  rw [presentation.edgeCompatibility, CyclicPolygon.translate_apply,
    CyclicPolygon.translate_apply]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [Homeomorph.coe_addRight]
  module

/-- Helper for Proposition 76.2: translating a cyclic presentation preserves its
edge-compatible presentation of the same abstract component. -/
noncomputable def translate {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme} {region : Occurrence scheme}
    (presentation : CyclicRegion regions region) (offset : EuclideanSpace ℝ (Fin 2)) :
    CyclicRegion regions region :=
  ⟨presentation.polygon.translate offset, presentation.translatedHomeomorph offset,
    presentation.translatedEdgeCompatibility offset⟩

/-- Helper for Proposition 76.2: the translated presentation stores the translated polygon. -/
theorem translate_polygon {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme} {region : Occurrence scheme}
    (presentation : CyclicRegion regions region) (offset : EuclideanSpace ℝ (Fin 2)) :
    (presentation.translate offset).polygon = presentation.polygon.translate offset := by
  rfl

/-- Helper for Proposition 76.2: the image under right translation is the pointwise
left translate, using commutativity of the ambient Euclidean additive group. -/
theorem image_addRight_eq_vadd (offset : EuclideanSpace ℝ (Fin 2))
    (s : Set (EuclideanSpace ℝ (Fin 2))) :
    Homeomorph.addRight offset '' s = offset +ᵥ s := by
  ext point
  simp only [Homeomorph.coe_addRight, Set.mem_image, Set.mem_vadd_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa only [vadd_eq_add] using add_comm offset x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa only [vadd_eq_add] using add_comm x offset⟩
/-- Helper for Proposition 76.2: compact cyclic regions can be separated by translating
the left region, after which any chosen directed edges define an edge gluing. -/
theorem existsTranslatedEdgeGluing {α : Type u} {scheme : LabellingScheme α}
    {regions : PolygonalRegions.{u, v} scheme}
    {leftOccurrence rightOccurrence : Occurrence scheme}
    (left : CyclicRegion regions leftOccurrence) (right : CyclicRegion regions rightOccurrence)
    (leftIndex : Fin leftOccurrence.1.1.length) (rightIndex : Fin rightOccurrence.1.1.length)
    (leftForward rightForward : Bool) :
    ∃ offset, ∃ gluing : CyclicPolygon.EdgeGluing
        (left.translate offset).polygon right.polygon,
      gluing.leftEdge.index = leftIndex ∧
      gluing.rightEdge.index = rightIndex ∧
      gluing.leftEdge.forward = leftForward ∧
      gluing.rightEdge.forward = rightForward := by
  -- Both filled polygonal regions are compact convex hulls of finite vertex sets.
  have hleftCompact : IsCompact left.polygon.region := by
    rw [left.polygon.region_eq_convexHull]
    exact Set.finite_range left.polygon.toPolygon.vertices |>.isCompact_convexHull ℝ
  have hrightCompact : IsCompact right.polygon.region := by
    rw [right.polygon.region_eq_convexHull]
    exact Set.finite_range right.polygon.toPolygon.vertices |>.isCompact_convexHull ℝ
  -- Translate the left polygon away from the fixed right polygon.
  obtain ⟨offset, hdisjoint⟩ := exists_disjoint_vadd_of_isCompact hrightCompact hleftCompact
  refine ⟨offset, ⟨⟨leftIndex, leftForward⟩, ⟨rightIndex, rightForward⟩, ?_⟩, rfl, rfl, rfl, rfl⟩
  rw [translate_polygon, CyclicPolygon.translate_region]
  rw [image_addRight_eq_vadd]
  exact hdisjoint.symm

end LabellingScheme.PolygonalRegions.CyclicRegion


namespace LabellingScheme.PolygonalRegions.PasteResult

/-- Helper for Proposition 76.2: a completed first paste transports any realization
of the split family to a realization of the merged family. -/
theorem existsRealization {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {mergedFirst : Occurrence mergedScheme}
    {ι : Type u} {splitRest : ι → Occurrence splitScheme}
    {mergedRest : ι → Occurrence mergedScheme}
    (result : PasteResult splitRegions c mergedFirst splitRest mergedRest)
    {X : Type w} [TopologicalSpace X] (q : splitRegions.Source → X)
    (hsplit : splitRegions.Realizes q) :
    ∃ mergedQuotient : Source result.pasting.mergedRegions → X,
      Realizes result.pasting.mergedRegions mergedQuotient := by
  -- The original realization is constant on every fibre of the first paste.
  have hfactor : Function.FactorsThrough q result.firstPaste := by
    intro x y hxy
    apply (hsplit.fibers x y).mpr
    apply (identified_iff_remainingIdentified_pullback splitRegions c result.firstPaste
      result.pasting.pastesLabel x y).mpr
    rw [hxy]
  let splitMap : C(splitRegions.Source, X) :=
    ⟨q, hsplit.isQuotientMap.continuous⟩
  let firstPasteMap : C(splitRegions.Source, result.Intermediate) :=
    ⟨result.firstPaste, result.pasting.pastesLabel.isQuotientMap.continuous⟩
  have hfirstPasteMap : Topology.IsQuotientMap firstPasteMap :=
    result.pasting.pastesLabel.isQuotientMap
  let remainingPastes : C(result.Intermediate, X) :=
    hfirstPasteMap.lift splitMap (fun x y hxy ↦ hfactor hxy)
  -- The quotient lift has the original realization as its composite with `firstPaste`.
  have htriangle : remainingPastes ∘ result.firstPaste = q := by
    funext x
    exact DFunLike.congr_fun
      (hfirstPasteMap.lift_comp splitMap
        (fun a d had ↦ hfactor had)) x
  refine ⟨remainingPastes ∘ result.pasting.sourceHomeomorph.symm, ?_⟩
  -- Apply the generic realization transport theorem after rewriting the lift triangle.
  apply result.pasting.realizes remainingPastes
  simpa only [htriangle] using hsplit

/-- Helper for Proposition 76.2: cyclic presentations of the distinguished merged
component and every retained component make the whole merged family polygonal. -/
theorem isPolygonal_cons {α : Type u} [DecidableEq α]
    {splitScheme : LabellingScheme α} {splitRegions : PolygonalRegions.{u, v} splitScheme}
    {c : α} (word : PolygonWord α) (rest : LabellingScheme α)
    {splitRest : Occurrence rest → Occurrence splitScheme}
    (result : PasteResult splitRegions c (mergedFirstOccurrence word rest) splitRest
      (mergedRestOccurrence word rest)) :
    IsPolygonal result.pasting.mergedRegions := by
  classical
  -- Decompose an arbitrary occurrence into the merged first component or the remainder.
  rw [isPolygonal_iff]
  intro region
  cases hposition : consOccurrenceEquiv word rest region with
  | none =>
      have hregion : region = mergedFirstOccurrence word rest := by
        apply (consOccurrenceEquiv word rest).injective
        simpa only [mergedFirstOccurrence, Equiv.apply_symm_apply] using hposition
      subst region
      exact ⟨result.mergedFirstRegion⟩
  | some retainedRegion =>
      have hregion : region = mergedRestOccurrence word rest retainedRegion := by
        apply (consOccurrenceEquiv word rest).injective
        simpa only [mergedRestOccurrence, Equiv.apply_symm_apply] using hposition
      subst region
      exact ⟨result.retainedCyclicRegion retainedRegion⟩

/-- Helper for Proposition 76.2: polygonality of a completed paste and the generic
quotient transport together give the two conclusions required by the proposition. -/
theorem existsPolygonalRealization {α : Type u} [DecidableEq α]
    {splitScheme mergedScheme : LabellingScheme α}
    {splitRegions : PolygonalRegions.{u, v} splitScheme} {c : α}
    {mergedFirst : Occurrence mergedScheme}
    {ι : Type u} {splitRest : ι → Occurrence splitScheme}
    {mergedRest : ι → Occurrence mergedScheme}
    (result : PasteResult splitRegions c mergedFirst splitRest mergedRest)
    (hpolygonal : IsPolygonal result.pasting.mergedRegions)
    {X : Type w} [TopologicalSpace X] (q : splitRegions.Source → X)
    (hsplit : splitRegions.Realizes q) :
    IsPolygonal result.pasting.mergedRegions ∧
      ∃ mergedQuotient : Source result.pasting.mergedRegions → X,
        Realizes result.pasting.mergedRegions mergedQuotient := by
  -- Keep the geometric conclusion and transport the original quotient realization.
  exact ⟨hpolygonal, result.existsRealization q hsplit⟩

end LabellingScheme.PolygonalRegions.PasteResult

namespace LabellingScheme.PolygonalRegions.CyclicRegion

/-- Helper for Proposition 76.2: the last edge of the left distinguished word and
the first edge of the right distinguished word admit a translated edge gluing with
the required labels and opposite orientations. -/
theorem existsDistinguishedLabelledEdgeGluing {α : Type u}
    (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool) (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (splitRegions : PolygonalRegions.{u, v}
      (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest))
    (leftRegion : CyclicRegion splitRegions
      (firstOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest))
    (rightRegion : CyclicRegion splitRegions
      (secondOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest)) :
    ∃ offset, ∃ gluing : CyclicPolygon.EdgeGluing
        (leftRegion.translate offset).polygon rightRegion.polygon,
      (firstOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
        rest).1.1.get gluing.leftEdge.index = (c, !b) ∧
      (secondOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
        rest).1.1.get gluing.rightEdge.index = (c, b) ∧
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward := by
  let leftWord : PolygonWord α :=
    ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
  let rightWord : PolygonWord α :=
    ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
  have hleftWord : (firstOccurrence leftWord rightWord rest).1 = leftWord :=
    firstOccurrence_fst leftWord rightWord rest
  have hrightWord : (secondOccurrence leftWord rightWord rest).1 = rightWord :=
    secondOccurrence_fst leftWord rightWord rest
  -- Select the last letter of the left word and the head of the right word before transport.
  let nativeLeftIndex : Fin leftWord.1.length :=
    ⟨y₀.length, by simp only [leftWord, List.length_append, List.length_singleton]; omega⟩
  let nativeRightIndex : Fin rightWord.1.length :=
    ⟨0, by simp only [rightWord, List.length_cons]; omega⟩
  let leftIndex : Fin (firstOccurrence leftWord rightWord rest).1.1.length :=
    Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hleftWord).symm
      nativeLeftIndex
  let rightIndex : Fin (secondOccurrence leftWord rightWord rest).1.1.length :=
    Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hrightWord).symm
      nativeRightIndex
  -- Translate the left polygon away from the right and glue the selected directed edges.
  obtain ⟨offset, gluing, hleft, hright, hleftForward, hrightForward⟩ :=
    leftRegion.existsTranslatedEdgeGluing rightRegion leftIndex rightIndex (!b) b
  refine ⟨offset, gluing, ?_, ?_, ?_⟩
  · rw [hleft]
    calc
      (firstOccurrence leftWord rightWord rest).1.1.get leftIndex =
          leftWord.1.get nativeLeftIndex := get_cast_fst_eq hleftWord nativeLeftIndex
      _ = (c, !b) := by
        simp only [leftWord, nativeLeftIndex, List.get_eq_getElem]
        exact List.getElem_concat_length rfl _
  · rw [hright]
    calc
      (secondOccurrence leftWord rightWord rest).1.1.get rightIndex =
          rightWord.1.get nativeRightIndex := get_cast_fst_eq hrightWord nativeRightIndex
      _ = (c, b) := by
        simp only [rightWord, nativeRightIndex, List.get_eq_getElem,
          List.getElem_cons_zero]
  · rw [hleftForward, hrightForward]
    cases b <;> decide

end LabellingScheme.PolygonalRegions.CyclicRegion

namespace CyclicPolygon.Cut

/-- Helper for Proposition 76.2: every nonclosing edge of the left cut inherits
the original polygon's affine edge parameter without reparameterization. -/
theorem left_edgePoint_coe {n : ℕ} (poly : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (i : Fin (k.val + 1)) (hi : i ≠ Fin.last k.val)
    (t : unitInterval) :
    ((left poly k hk₁).edgePoint i t : EuclideanSpace ℝ (Fin 2)) =
      (poly.edgePoint (leftIndex k i) t : EuclideanSpace ℝ (Fin 2)) := by
  -- Rewrite both affine endpoints through the cut index map; the nonclosing
  -- hypothesis makes cyclic successor commute with that map.
  rw [(left poly k hk₁).edgePoint_coe_eq_lineMap,
    poly.edgePoint_coe_eq_lineMap, left_apply, left_apply,
    leftIndex_finRotate k i hi]

/-- Helper for Proposition 76.2: every noninitial edge of the right cut inherits
the original polygon's affine edge parameter without reparameterization. -/
theorem right_edgePoint_coe {n : ℕ} (poly : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1)
    (i : Fin (n - k.val + 1)) (hi : i ≠ 0) (t : unitInterval) :
    ((right poly k hk₁ hk₂).edgePoint i t : EuclideanSpace ℝ (Fin 2)) =
      (poly.edgePoint (rightIndex k i) t : EuclideanSpace ℝ (Fin 2)) := by
  -- Rewrite both affine endpoints through the cut index map; away from the
  -- diagonal, cyclic successor is preserved as well.
  rw [(right poly k hk₁ hk₂).edgePoint_coe_eq_lineMap,
    poly.edgePoint_coe_eq_lineMap, right_apply, right_apply,
    rightIndex_finRotate k i hi]

end CyclicPolygon.Cut

namespace CyclicPolygon

/-- Helper for Proposition 76.2: transporting a cyclic polygon's vertex count
preserves the affine parameter on every edge. -/
theorem castVertexCount_edgePoint_coe {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) (i : Fin first) (t : unitInterval) :
    ((castVertexCount h poly).edgePoint (Fin.cast h i) t :
        EuclideanSpace ℝ (Fin 2)) =
      (poly.edgePoint i t : EuclideanSpace ℝ (Fin 2)) := by
  -- Cast the two affine endpoints together, commuting the cast with cyclic successor.
  rw [(castVertexCount h poly).edgePoint_coe_eq_lineMap,
    poly.edgePoint_coe_eq_lineMap, castVertexCount_vertices,
    ← finCast_finRotate, castVertexCount_vertices]

/-- Helper for Proposition 76.2: first-gap insertion preserves every surviving
edge parameter on the left prefix and on the reindexed original right polygon. -/
theorem insertInFirstGap_edgePoint_decomposition {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) :
    (∀ (i : Fin ((sharedIndex hm poly).val + 1)),
      i ≠ Fin.last (sharedIndex hm poly).val → ∀ t : unitInterval,
        ((Cut.left (insertInFirstGap hm poly) (sharedIndex hm poly)
            (sharedIndex_one_lt hm poly)).edgePoint i t :
              EuclideanSpace ℝ (Fin 2)) =
          ((insertInFirstGap hm poly).edgePoint
            (Cut.leftIndex (sharedIndex hm poly) i) t :
              EuclideanSpace ℝ (Fin 2))) ∧
    ∀ (i : Fin n) (t : unitInterval),
      ((Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
          (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)).edgePoint
          (Fin.cast (insertedRightCount hm poly).symm i) t :
            EuclideanSpace ℝ (Fin 2)) =
        (poly.edgePoint i t : EuclideanSpace ℝ (Fin 2)) := by
  constructor
  · intro i hi t
    -- The left-prefix formula is the generic inherited-edge law for the canonical cut.
    exact Cut.left_edgePoint_coe _ _ _ i hi t
  · intro i t
    -- Both endpoints of a right-cut edge are the corresponding original vertices;
    -- the named cast/rotation law aligns the successor endpoint.
    rw [(Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
        (sharedIndex_one_lt hm poly)
        (sharedIndex_lt_last hm poly)).edgePoint_coe_eq_lineMap,
      poly.edgePoint_coe_eq_lineMap, insertedRightCut_vertices,
      insertedRightCut_vertices, finCast_finRotate]
    rfl

/-- Helper for Proposition 76.2: first-gap insertion yields a replacement left
polygon and a concatenated polygon whose prefix and suffix edges retain their
original affine parameters under `Fin.castAdd` and `Fin.natAdd`. -/
theorem existsFirstGapBoundaryConcatenation {p q : ℕ} (hp : 2 ≤ p)
    (right : CyclicPolygon (q + 1)) :
    ∃ (replacement : CyclicPolygon (p + 1)) (combined : CyclicPolygon (p + q)),
      (∀ (i : Fin p) (t : unitInterval),
        (replacement.edgePoint i.castSucc t : EuclideanSpace ℝ (Fin 2)) =
          (combined.edgePoint (Fin.castAdd q i) t : EuclideanSpace ℝ (Fin 2))) ∧
      ∀ (j : Fin q) (t : unitInterval),
        (combined.edgePoint (Fin.natAdd p j) t : EuclideanSpace ℝ (Fin 2)) =
          (right.edgePoint j.succ t : EuclideanSpace ℝ (Fin 2)) := by
  have hm : 3 ≤ p + 1 := by omega
  let rawCombined : CyclicPolygon ((p + 1) + (q + 1) - 2) :=
    insertInFirstGap hm right
  let shared : Fin ((p + 1) + (q + 1) - 2) := sharedIndex hm right
  have hsharedLeft : 1 < shared.val := sharedIndex_one_lt hm right
  have hsharedRight : shared.val < (p + 1) + (q + 1) - 2 - 1 :=
    sharedIndex_lt_last hm right
  let rawReplacement : CyclicPolygon (shared.val + 1) :=
    Cut.left rawCombined shared hsharedLeft
  have hcombinedCount : (p + 1) + (q + 1) - 2 = p + q := by omega
  have hreplacementCount : shared.val + 1 = p + 1 := by
    dsimp only [shared]
    rw [sharedIndex_val]
    omega
  let replacement : CyclicPolygon (p + 1) :=
    castVertexCount hreplacementCount rawReplacement
  let combined : CyclicPolygon (p + q) :=
    castVertexCount hcombinedCount rawCombined
  refine ⟨replacement, combined, ?_, ?_⟩
  · intro i t
    let rawIndex : Fin (shared.val + 1) :=
      Fin.cast hreplacementCount.symm i.castSucc
    have hrawIndexNe : rawIndex ≠ Fin.last shared.val := by
      intro hlast
      have hval := congrArg Fin.val hlast
      simp only [rawIndex, Fin.val_cast, Fin.val_castSucc, Fin.val_last] at hval
      dsimp only [shared] at hval
      rw [sharedIndex_val] at hval
      have hpValue : (p + 1) - 1 = p := by omega
      rw [hpValue] at hval
      exact (Nat.ne_of_lt i.isLt) hval
    have hcastRawIndex : Fin.cast hreplacementCount rawIndex = i.castSucc := by
      apply Fin.ext
      rfl
    have hcombinedIndex : Cut.leftIndex shared rawIndex =
        Fin.cast hcombinedCount.symm (Fin.castAdd q i) := by
      apply Fin.ext
      simp only [Cut.leftIndex_val, rawIndex, Fin.val_cast, Fin.val_castSucc,
        Fin.val_castAdd]
    calc
      (replacement.edgePoint i.castSucc t : EuclideanSpace ℝ (Fin 2)) =
          (rawReplacement.edgePoint rawIndex t : EuclideanSpace ℝ (Fin 2)) := by
        dsimp only [replacement]
        rw [← hcastRawIndex]
        exact castVertexCount_edgePoint_coe hreplacementCount rawReplacement rawIndex t
      _ = (rawCombined.edgePoint (Cut.leftIndex shared rawIndex) t :
          EuclideanSpace ℝ (Fin 2)) := by
        exact Cut.left_edgePoint_coe rawCombined shared hsharedLeft rawIndex hrawIndexNe t
      _ = (rawCombined.edgePoint
          (Fin.cast hcombinedCount.symm (Fin.castAdd q i)) t :
            EuclideanSpace ℝ (Fin 2)) := by rw [hcombinedIndex]
      _ = (combined.edgePoint (Fin.castAdd q i) t :
          EuclideanSpace ℝ (Fin 2)) := by
        dsimp only [combined]
        symm
        simpa using castVertexCount_edgePoint_coe hcombinedCount rawCombined
          (Fin.cast hcombinedCount.symm (Fin.castAdd q i)) t
  · intro j t
    let rawRightIndex : Fin ((p + 1) + (q + 1) - 2 - shared.val + 1) :=
      Fin.cast (insertedRightCount hm right).symm j.succ
    have hrawRightIndexNe : rawRightIndex ≠ 0 := by
      intro hzero
      have hval := congrArg Fin.val hzero
      simp only [rawRightIndex, Fin.val_cast, Fin.val_succ, Fin.val_zero] at hval
      omega
    have hcombinedIndex : Cut.rightIndex shared rawRightIndex =
        Fin.cast hcombinedCount.symm (Fin.natAdd p j) := by
      apply Fin.ext
      rw [Cut.rightIndex_val]
      simp only [rawRightIndex, Fin.val_cast, Fin.val_succ, Nat.succ_ne_zero,
        if_false, Fin.val_natAdd]
      dsimp only [shared]
      rw [sharedIndex_val]
      omega
    calc
      (combined.edgePoint (Fin.natAdd p j) t : EuclideanSpace ℝ (Fin 2)) =
          (rawCombined.edgePoint
            (Fin.cast hcombinedCount.symm (Fin.natAdd p j)) t :
              EuclideanSpace ℝ (Fin 2)) := by
        dsimp only [combined]
        simpa using castVertexCount_edgePoint_coe hcombinedCount rawCombined
          (Fin.cast hcombinedCount.symm (Fin.natAdd p j)) t
      _ = (rawCombined.edgePoint (Cut.rightIndex shared rawRightIndex) t :
          EuclideanSpace ℝ (Fin 2)) := by rw [hcombinedIndex]
      _ = ((Cut.right rawCombined shared hsharedLeft hsharedRight).edgePoint
          rawRightIndex t : EuclideanSpace ℝ (Fin 2)) := by
        symm
        exact Cut.right_edgePoint_coe rawCombined shared hsharedLeft hsharedRight
          rawRightIndex hrawRightIndexNe t
      _ = (right.edgePoint j.succ t : EuclideanSpace ℝ (Fin 2)) := by
        exact (insertInFirstGap_edgePoint_decomposition hm right).2 j.succ t

end CyclicPolygon

namespace CyclicPolygon.EdgeGluing

/-- Helper for Proposition 76.2: deleting one edge from each of two polygons
gives the vertex count of their concatenated boundary. -/
theorem concatenatedBoundaryCount {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    (m - 1) + (n - 1) = m + n - 2 := by
  omega

/-- Helper for Proposition 76.2: restoring the deleted final slot recovers the
original positive vertex count. -/
theorem predAddOne_eq {m : ℕ} (hm : 3 ≤ m) : m - 1 + 1 = m := by
  omega

/-- Helper for Proposition 76.2: gluing the last edge of the left polygon to the
first edge of the right polygon admits a cyclic reassembly built by first-gap insertion. -/
theorem existsLastFirstReassembly {m n : ℕ} {left : CyclicPolygon m}
    {right : CyclicPolygon n} (gluing : EdgeGluing left right)
    (hleftIndex : gluing.leftEdge.index.val = m - 1)
    (hrightIndex : gluing.rightEdge.index.val = 0)
    (h_oppositeOrientation :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward) :
    ∃ (replacement : CyclicPolygon m) (combined : CyclicPolygon (m + n - 2))
      (leftHomeomorph : left.region ≃ₜ replacement.region)
      (realizationHomeomorph : gluing.Realization ≃ₜ combined.region),
      (∀ i : Fin m,
        (leftHomeomorph (left.vertexPoint i) : EuclideanSpace ℝ (Fin 2)) =
          replacement.vertexPoint i) ∧
      (∀ (i : Fin m) (t : unitInterval),
        leftHomeomorph (left.boundaryToRegion (left.edgePoint i t)) =
          replacement.boundaryToRegion (replacement.edgePoint i t)) ∧
      (∀ x : gluing.attachingSubset,
        (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap x) ∧
      combined.region = replacement.region ∪ right.region ∧
      (∀ x : left.region,
        (realizationHomeomorph (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) =
          leftHomeomorph x) ∧
      (∀ y : right.region,
        (realizationHomeomorph (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) = y) ∧
      (∀ (i : Fin (m - 1)) (t : unitInterval),
        realizationHomeomorph
            (gluing.includeLeft (left.boundaryToRegion
              (left.edgePoint (Fin.cast (predAddOne_eq left.three_le) i.castSucc) t))) =
          combined.boundaryToRegion
            (combined.edgePoint
              (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
                (Fin.castAdd (n - 1) i)) t)) ∧
      ∀ (j : Fin (n - 1)) (t : unitInterval),
        realizationHomeomorph
            (gluing.includeRight (right.boundaryToRegion
              (right.edgePoint (Fin.cast (predAddOne_eq right.three_le) j.succ) t))) =
          combined.boundaryToRegion
            (combined.edgePoint
              (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
                (Fin.natAdd (m - 1) j)) t) := by
  -- Insert the left polygon's unglued vertices into the first gap of the right polygon.
  let combined : CyclicPolygon (m + n - 2) :=
    CyclicPolygon.insertInFirstGap left.three_le right
  let shared : Fin (m + n - 2) :=
    CyclicPolygon.sharedIndex left.three_le right
  have hsharedLeft : 1 < shared.val :=
    CyclicPolygon.sharedIndex_one_lt left.three_le right
  have hsharedRight : shared.val < m + n - 2 - 1 :=
    CyclicPolygon.sharedIndex_lt_last left.three_le right
  let replacementRaw : CyclicPolygon (shared.val + 1) :=
    CyclicPolygon.Cut.left combined shared hsharedLeft
  have hreplacementCount : shared.val + 1 = m := by
    dsimp only [shared]
    rw [CyclicPolygon.sharedIndex_val]
    omega
  let replacement : CyclicPolygon m :=
    CyclicPolygon.castVertexCount hreplacementCount replacementRaw
  have hreplacementRegion : replacement.region = replacementRaw.region := by
    exact CyclicPolygon.castVertexCount_region hreplacementCount replacementRaw
  -- Normalize the two selected indices to the closing and initial cut indices.
  have hleftLast : gluing.leftEdge.index =
      Fin.cast hreplacementCount (Fin.last shared.val) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last]
    dsimp only [shared]
    rw [CyclicPolygon.sharedIndex_val]
    exact hleftIndex
  have hrightZero : gluing.rightEdge.index = CyclicPolygon.Cut.indexZero right := by
    apply Fin.ext
    rw [hrightIndex, CyclicPolygon.Cut.indexZero_val]
  have hrawLeftLast :
      CyclicPolygon.Cut.leftIndex shared (Fin.last shared.val) = shared := by
    apply Fin.ext
    simp only [CyclicPolygon.Cut.leftIndex_val, Fin.val_last]
  have hrawLeftZero :
      CyclicPolygon.Cut.leftIndex shared 0 = CyclicPolygon.Cut.indexZero combined := by
    apply Fin.ext
    simp only [CyclicPolygon.Cut.leftIndex_val, Fin.val_zero,
      CyclicPolygon.Cut.indexZero_val]
  -- The closing replacement edge is exactly the right polygon's first edge in reverse.
  have hinitial : replacement.toPolygon.vertices gluing.leftEdge.index =
      right.toPolygon.vertices (finRotate n gluing.rightEdge.index) := by
    rw [hleftLast]
    calc
      replacement.toPolygon.vertices
          (Fin.cast hreplacementCount (Fin.last shared.val)) =
          replacementRaw.toPolygon.vertices (Fin.last shared.val) :=
        CyclicPolygon.castVertexCount_vertices hreplacementCount replacementRaw
          (Fin.last shared.val)
      _ = combined.toPolygon.vertices shared := by
        rw [CyclicPolygon.Cut.left_apply, hrawLeftLast]
      _ = right.toPolygon.vertices (CyclicPolygon.firstVertexIndex right) := by
        exact CyclicPolygon.insertInFirstGap_vertex_shared left.three_le right
      _ = right.toPolygon.vertices (finRotate n gluing.rightEdge.index) := by
        -- Normalize the initial edge through the polygon-owned successor lemma.
        rw [hrightZero, CyclicPolygon.firstVertexIndex_eq_finRotate_indexZero]
  have hfinal : replacement.toPolygon.vertices
      (finRotate m gluing.leftEdge.index) =
      right.toPolygon.vertices gluing.rightEdge.index := by
    have hrotateLeft : finRotate m gluing.leftEdge.index =
        Fin.cast hreplacementCount 0 := by
      -- The selected edge is the last edge, so its cyclic successor is zero.
      have hmPositive : 0 < m := by
        omega
      -- Local instance justification (finite cyclic arithmetic): `finRotate_apply`
      -- requires `NeZero m`, supplied here directly by the polygon's side bound.
      letI : NeZero m := ⟨Nat.ne_of_gt hmPositive⟩
      apply Fin.ext
      rw [finRotate_apply]
      simp only [Fin.val_add, Fin.val_one' m, Fin.val_cast, Fin.val_zero,
        hleftIndex]
      have hmThree : 3 ≤ m := left.three_le
      have hOneMod : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
      have hmOne : 1 ≤ m := by omega
      rw [hOneMod, Nat.sub_add_cancel hmOne, Nat.mod_self]
    rw [hrotateLeft]
    calc
      replacement.toPolygon.vertices (Fin.cast hreplacementCount 0) =
          replacementRaw.toPolygon.vertices 0 :=
        CyclicPolygon.castVertexCount_vertices hreplacementCount replacementRaw 0
      _ = combined.toPolygon.vertices (CyclicPolygon.Cut.indexZero combined) := by
        rw [CyclicPolygon.Cut.left_apply, hrawLeftZero]
      _ = right.toPolygon.vertices (CyclicPolygon.Cut.indexZero right) := by
        exact CyclicPolygon.insertInFirstGap_vertex_zero left.three_le right
      _ = right.toPolygon.vertices gluing.rightEdge.index := by rw [← hrightZero]
  -- The cut theorem supplies the union and exact common-edge intersection.
  have hrightCutRegion :
      (CyclicPolygon.Cut.right combined shared hsharedLeft hsharedRight).region =
        right.region := by
    exact CyclicPolygon.insertedRightCut_region left.three_le right
  have hunion : combined.region = replacement.region ∪ right.region := by
    rw [hreplacementRegion, ← hrightCutRegion]
    exact CyclicPolygon.Cut.region_eq_union combined shared hsharedLeft hsharedRight
  have hrawDiagonal : replacementRaw.edgeSet (Fin.last shared.val) =
      right.edgeSet gluing.rightEdge.index := by
    unfold CyclicPolygon.edgeSet Polygon.edgeSet
    rw [finRotate_last, CyclicPolygon.Cut.left_apply,
      CyclicPolygon.Cut.left_apply, hrawLeftLast, hrawLeftZero]
    rw [CyclicPolygon.insertInFirstGap_vertex_shared,
      CyclicPolygon.insertInFirstGap_vertex_zero]
    rw [hrightZero, CyclicPolygon.firstVertexIndex_eq_finRotate_indexZero]
    exact affineSegment_comm _ _ _
  have hinter : replacement.region ∩ right.region =
      right.edgeSet gluing.rightEdge.index := by
    rw [hreplacementRegion, ← hrightCutRegion]
    rw [CyclicPolygon.Cut.regionsInterEqDiagonal combined shared hsharedLeft hsharedRight]
    exact hrawDiagonal
  -- Use the canonical edge-preserving comparison, then descend through the adjunction quotient.
  obtain ⟨leftHomeomorph, hvertices, hparameters⟩ :=
    CyclicPolygon.existsVertexAndEdgeParameterPreservingRegionHomeomorph left replacement
  have hverticesAmbient : ∀ i : Fin m,
      (leftHomeomorph (left.vertexPoint i) : EuclideanSpace ℝ (Fin 2)) =
        replacement.vertexPoint i := by
    intro i
    exact congrArg Subtype.val (hvertices i)
  have hattaching :=
    gluing.regionHomeomorphAgreesWithAttachingMapOfReversedEdge replacement
      leftHomeomorph hparameters hinitial hfinal h_oppositeOrientation
  obtain ⟨realizationHomeomorph, hrealLeft, hrealRight⟩ :=
    gluing.existsRealizationHomeomorphOfRegionUnion replacement combined
      leftHomeomorph h_oppositeOrientation hattaching hunion hinter
  have hleftBoundary : ∀ (i : Fin (m - 1)) (t : unitInterval),
      realizationHomeomorph
          (gluing.includeLeft (left.boundaryToRegion
            (left.edgePoint
              (Fin.cast (predAddOne_eq left.three_le) i.castSucc) t))) =
        combined.boundaryToRegion
          (combined.edgePoint
            (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
              (Fin.castAdd (n - 1) i)) t) := by
    intro i t
    let leftIndex : Fin m := Fin.cast (predAddOne_eq left.three_le) i.castSucc
    let rawIndex : Fin (shared.val + 1) :=
      Fin.cast hreplacementCount.symm leftIndex
    have hrawIndexNe : rawIndex ≠ Fin.last shared.val := by
      intro hlast
      have hval := congrArg Fin.val hlast
      simp only [rawIndex, Fin.val_cast, Fin.val_last] at hval
      dsimp only [shared] at hval
      rw [CyclicPolygon.sharedIndex_val] at hval
      dsimp only [leftIndex] at hval
      simp only [Fin.val_cast, Fin.val_castSucc] at hval
      omega
    have hcastRawIndex : Fin.cast hreplacementCount rawIndex = leftIndex := by
      apply Fin.ext
      rfl
    have hcombinedIndex : CyclicPolygon.Cut.leftIndex shared rawIndex =
        Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
          (Fin.castAdd (n - 1) i) := by
      apply Fin.ext
      simp only [CyclicPolygon.Cut.leftIndex_val, rawIndex, Fin.val_cast,
        Fin.val_castAdd]
      dsimp only [leftIndex]
      simp only [Fin.val_cast, Fin.val_castSucc]
    apply Subtype.ext
    calc
      (realizationHomeomorph
          (gluing.includeLeft (left.boundaryToRegion (left.edgePoint leftIndex t))) :
          EuclideanSpace ℝ (Fin 2)) =
          (leftHomeomorph (left.boundaryToRegion (left.edgePoint leftIndex t)) :
            EuclideanSpace ℝ (Fin 2)) := hrealLeft _
      _ = (replacement.boundaryToRegion (replacement.edgePoint leftIndex t) :
          EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val (hparameters leftIndex t)
      _ = (replacementRaw.edgePoint rawIndex t : EuclideanSpace ℝ (Fin 2)) := by
        rw [replacement.boundaryToRegion_coe]
        dsimp only [replacement]
        rw [← hcastRawIndex]
        exact CyclicPolygon.castVertexCount_edgePoint_coe hreplacementCount
          replacementRaw rawIndex t
      _ = (combined.edgePoint (CyclicPolygon.Cut.leftIndex shared rawIndex) t :
          EuclideanSpace ℝ (Fin 2)) :=
        CyclicPolygon.Cut.left_edgePoint_coe combined shared hsharedLeft rawIndex
          hrawIndexNe t
      _ = (combined.edgePoint
          (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
            (Fin.castAdd (n - 1) i)) t : EuclideanSpace ℝ (Fin 2)) := by
        rw [hcombinedIndex]
      _ = (combined.boundaryToRegion
          (combined.edgePoint
            (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
              (Fin.castAdd (n - 1) i)) t) : EuclideanSpace ℝ (Fin 2)) := by
        rw [combined.boundaryToRegion_coe]
  have hrightBoundary : ∀ (j : Fin (n - 1)) (t : unitInterval),
      realizationHomeomorph
          (gluing.includeRight (right.boundaryToRegion
            (right.edgePoint
              (Fin.cast (predAddOne_eq right.three_le) j.succ) t))) =
        combined.boundaryToRegion
          (combined.edgePoint
            (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
              (Fin.natAdd (m - 1) j)) t) := by
    intro j t
    let rightIndex : Fin n := Fin.cast (predAddOne_eq right.three_le) j.succ
    let rawRightIndex : Fin (m + n - 2 - shared.val + 1) :=
      Fin.cast (CyclicPolygon.insertedRightCount left.three_le right).symm rightIndex
    have hrawRightIndexNe : rawRightIndex ≠ 0 := by
      intro hzero
      have hval := congrArg Fin.val hzero
      simp only [rawRightIndex, Fin.val_cast, Fin.val_zero] at hval
      dsimp only [rightIndex] at hval
      simp only [Fin.val_cast, Fin.val_succ] at hval
      omega
    have hcombinedIndex : CyclicPolygon.Cut.rightIndex shared rawRightIndex =
        Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
          (Fin.natAdd (m - 1) j) := by
      apply Fin.ext
      rw [CyclicPolygon.Cut.rightIndex_val]
      have hrawRightIndexValue : rawRightIndex.val ≠ 0 := by
        intro hzero
        exact hrawRightIndexNe (Fin.ext hzero)
      rw [if_neg hrawRightIndexValue]
      simp only [rawRightIndex, Fin.val_cast, Fin.val_natAdd]
      dsimp only [rightIndex]
      simp only [Fin.val_cast, Fin.val_succ]
      dsimp only [shared]
      rw [CyclicPolygon.sharedIndex_val]
      omega
    apply Subtype.ext
    calc
      (realizationHomeomorph
          (gluing.includeRight (right.boundaryToRegion (right.edgePoint rightIndex t))) :
          EuclideanSpace ℝ (Fin 2)) =
          (right.boundaryToRegion (right.edgePoint rightIndex t) :
            EuclideanSpace ℝ (Fin 2)) := hrealRight _
      _ = (right.edgePoint rightIndex t : EuclideanSpace ℝ (Fin 2)) := by
        rw [right.boundaryToRegion_coe]
      _ = ((CyclicPolygon.Cut.right combined shared hsharedLeft hsharedRight).edgePoint
          rawRightIndex t : EuclideanSpace ℝ (Fin 2)) := by
        symm
        exact (CyclicPolygon.insertInFirstGap_edgePoint_decomposition left.three_le right).2
          rightIndex t
      _ = (combined.edgePoint (CyclicPolygon.Cut.rightIndex shared rawRightIndex) t :
          EuclideanSpace ℝ (Fin 2)) :=
        CyclicPolygon.Cut.right_edgePoint_coe combined shared hsharedLeft hsharedRight
          rawRightIndex hrawRightIndexNe t
      _ = (combined.edgePoint
          (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
            (Fin.natAdd (m - 1) j)) t : EuclideanSpace ℝ (Fin 2)) := by
        rw [hcombinedIndex]
      _ = (combined.boundaryToRegion
          (combined.edgePoint
            (Fin.cast (concatenatedBoundaryCount left.three_le right.three_le)
              (Fin.natAdd (m - 1) j)) t) : EuclideanSpace ℝ (Fin 2)) := by
        rw [combined.boundaryToRegion_coe]
  exact ⟨replacement, combined, leftHomeomorph, realizationHomeomorph,
    hverticesAmbient, hparameters, hattaching, hunion, hrealLeft, hrealRight,
    hleftBoundary, hrightBoundary⟩

end CyclicPolygon.EdgeGluing

namespace LabellingScheme.PolygonalRegions.Pasting

/-- Helper for Proposition 76.2: a fresh label in a list followed by one
labelled letter occurs only at the final index. -/
theorem appendSingletonLabelIndex_eq_length {α : Type u}
    (letters : List (α × Bool)) (c : α) (b : Bool)
    (index : Fin (letters ++ [(c, b)]).length)
    (havoid : ∀ letter ∈ letters, letter.1 ≠ c)
    (hlabel : ((letters ++ [(c, b)]).get index).1 = c) :
    index.val = letters.length := by
  -- An index in the prefix would exhibit the forbidden label there.
  by_contra hne
  have hlt : index.val < letters.length := by
    have hbound := index.isLt
    simp only [List.length_append, List.length_singleton] at hbound
    omega
  have hmem : (letters ++ [(c, b)]).get index ∈ letters := by
    rw [List.get_eq_getElem, List.getElem_append_left hlt]
    exact List.getElem_mem _
  exact havoid _ hmem hlabel

/-- Helper for Proposition 76.2: a fresh label consed onto a list occurs only
at the initial index. -/
theorem consLabelIndex_eq_zero {α : Type u} (letters : List (α × Bool))
    (c : α) (b : Bool) (index : Fin ((c, b) :: letters).length)
    (havoid : ∀ letter ∈ letters, letter.1 ≠ c)
    (hlabel : (((c, b) :: letters).get index).1 = c) :
    index.val = 0 := by
  -- A successor index lies in the tail and contradicts freshness there.
  rcases index with ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ i =>
      exfalso
      have hiTail : i < letters.length := by
        simp only [List.length_cons] at hi
        omega
      have hlabelTail : letters[i].1 = c := by
        simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hlabel
      exact havoid letters[i] (List.getElem_mem _) hlabelTail

/-- Helper for Proposition 76.2: under the freshness hypotheses, every edge
carrying `c` is the final edge of the first occurrence or the initial edge of
the second occurrence. -/
theorem cEdgeOccurrence_eq_firstOrSecond {α : Type u}
    (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool)
    (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c)
    (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c)
    (region : Occurrence
      (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest))
    (edge : Fin region.1.1.length)
    (hlabel : (region.1.1.get edge).1 = c) :
    (region = firstOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest ∧
      edge.val = y₀.length) ∨
    (region = secondOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest ∧
      edge.val = 0) := by
  classical
  let leftWord : PolygonWord α :=
    ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
  let rightWord : PolygonWord α :=
    ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
  cases houter : consOccurrenceEquiv leftWord (rightWord ::ₘ rest) region with
  | none =>
      left
      have hregion : region = firstOccurrence leftWord rightWord rest := by
        apply (consOccurrenceEquiv leftWord (rightWord ::ₘ rest)).injective
        simpa only [firstOccurrence, Equiv.apply_symm_apply] using houter
      subst region
      refine ⟨rfl, ?_⟩
      have hword := firstOccurrence_fst leftWord rightWord rest
      let selected : Fin leftWord.1.length :=
        Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hword) edge
      have hselectedLabel : (leftWord.1.get selected).1 = c := by
        rw [get_cast_fst_eq hword.symm edge]
        exact hlabel
      have hselected := appendSingletonLabelIndex_eq_length y₀ c (!b) selected hy₀
        (by simpa only [leftWord] using hselectedLabel)
      simpa only [selected, Fin.val_cast] using hselected
  | some remainderOccurrence =>
      cases hinner : consOccurrenceEquiv rightWord rest remainderOccurrence with
      | none =>
          right
          have hregion : region = secondOccurrence leftWord rightWord rest := by
            apply (consOccurrenceEquiv leftWord (rightWord ::ₘ rest)).injective
            rw [houter]
            simp only [secondOccurrence, Equiv.apply_symm_apply, Option.some.injEq]
            apply (consOccurrenceEquiv rightWord rest).injective
            simpa only [Equiv.apply_symm_apply] using hinner
          subst region
          refine ⟨rfl, ?_⟩
          have hword := secondOccurrence_fst leftWord rightWord rest
          let selected : Fin rightWord.1.length :=
            Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hword) edge
          have hselectedLabel : (rightWord.1.get selected).1 = c := by
            rw [get_cast_fst_eq hword.symm edge]
            exact hlabel
          have hselected := consLabelIndex_eq_zero y₁ c b selected hy₁
            (by simpa only [rightWord] using hselectedLabel)
          simpa only [selected, Fin.val_cast] using hselected
      | some retainedOccurrence =>
          exfalso
          have hregion : region =
              splitRestOccurrence leftWord rightWord rest retainedOccurrence := by
            apply (consOccurrenceEquiv leftWord (rightWord ::ₘ rest)).injective
            rw [houter]
            simp only [splitRestOccurrence, Equiv.apply_symm_apply, Option.some.injEq]
            apply (consOccurrenceEquiv rightWord rest).injective
            simpa only [Equiv.apply_symm_apply] using hinner
          subst region
          have hword := splitRestOccurrence_fst leftWord rightWord rest retainedOccurrence
          let selected : Fin retainedOccurrence.1.1.length :=
            Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hword) edge
          have hselectedLabel : (retainedOccurrence.1.1.get selected).1 = c := by
            rw [get_cast_fst_eq hword.symm edge]
            exact hlabel
          exact (LabellingScheme.avoidsLabel_iff.mp hrest)
            retainedOccurrence.1
            (@Multiset.coe_mem (PolygonWord α) (Classical.decEq _) rest retainedOccurrence)
            (retainedOccurrence.1.1.get selected) (List.get_mem _ _) hselectedLabel

end LabellingScheme.PolygonalRegions.Pasting

namespace LabellingScheme.PolygonalRegions.CyclicRegion

/-- Helper for Proposition 76.2: a cyclic presentation sends every abstract
region edge point to the canonical point on the corresponding polygon edge. -/
theorem homeomorph_edge_eq_boundaryToRegion {α : Type u}
    {scheme : LabellingScheme α} {regions : PolygonalRegions.{u, v} scheme}
    {region : Occurrence scheme} (presentation : CyclicRegion regions region)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    presentation.homeomorph (regions.edge region edge t) =
      presentation.polygon.boundaryToRegion
        (presentation.polygon.edgePoint edge t) := by
  -- Equality in the filled region follows from the stored affine edge formula.
  apply Subtype.ext
  rw [presentation.edgeCompatibility, presentation.polygon.boundaryToRegion_coe,
    presentation.polygon.edgePoint_coe_eq_lineMap]

end LabellingScheme.PolygonalRegions.CyclicRegion

namespace CyclicPolygon.EdgeGluing

/-- Helper for Proposition 76.2: the adjunction quotient identifies the selected
left edge parameter with the reversed right edge parameter when orientations differ. -/
theorem includeLeft_edgePoint_eq_includeRight_symm {m n : ℕ}
    {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right)
    (h_oppositeOrientation :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (t : unitInterval) :
    gluing.includeLeft
        (left.boundaryToRegion (left.edgePoint gluing.leftEdge.index t)) =
      gluing.includeRight
        (right.boundaryToRegion
          (right.edgePoint gluing.rightEdge.index (unitInterval.symm t))) := by
  -- Replace the left boundary point by the attaching-subset representative, glue,
  -- and compute the attaching map using the opposite orientation.
  calc
    gluing.includeLeft
        (left.boundaryToRegion (left.edgePoint gluing.leftEdge.index t)) =
        gluing.includeLeft (gluing.leftEdge.regionEdgePoint t : left.region) := by
          rw [gluing.leftEdge.regionEdgePoint_coe]
    _ = gluing.includeRight
        (gluing.attachingMap (gluing.leftEdge.regionEdgePoint t)) :=
      by
        rw [gluing.includeLeft_eq_includeX, gluing.includeRight_eq_includeY]
        exact AdjunctionSpace.glue gluing.attachingSubset gluing.attachingMap
          (gluing.leftEdge.regionEdgePoint t)
    _ = gluing.includeRight
        (right.boundaryToRegion
          (right.edgePoint gluing.rightEdge.index (unitInterval.symm t))) := by
      apply congrArg gluing.includeRight
      simpa only [if_neg h_oppositeOrientation] using
        gluing.attachingMap_regionEdgePoint t

end CyclicPolygon.EdgeGluing

namespace LabellingScheme.PolygonalRegions.Pasting

/-- Helper for Proposition 76.2: an unrestricted edge relation that cannot occur
away from `c` must be a direct pairing at `c`. -/
theorem edgeRelatedAt_of_edgeRelated_of_not_awayFrom {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (c : α) {x y : regions.Source} (hrelated : regions.EdgeRelated x y)
    (hnotAway : ¬regions.EdgeRelatedAwayFrom c x y) :
    regions.EdgeRelatedAt c x y := by
  -- Split the direct relation at `c`; the away-from branch is excluded explicitly.
  rcases (regions.edgeRelated_iff_at_or_awayFrom c x y).mp hrelated with hAt | hAway
  · exact hAt
  · exact False.elim (hnotAway hAway)

/-- Helper for Proposition 76.2: an attaching point and its image have the selected
left-edge parameter and the oppositely oriented right-edge parameter. -/
theorem existsEdgeParameters_of_adjunctionIdentifies {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {leftOccurrence rightOccurrence : Occurrence scheme}
    (leftRegion : CyclicRegion regions leftOccurrence)
    (rightRegion : CyclicRegion regions rightOccurrence)
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (a : gluing.attachingSubset) :
    ∃ s : unitInterval,
      (@Homeomorph.toEquiv _ _ (regions.topology leftOccurrence) inferInstance
        leftRegion.homeomorph).symm (a : leftRegion.polygon.region) =
          regions.edge leftOccurrence gluing.leftEdge.index s ∧
      (@Homeomorph.toEquiv _ _ (regions.topology rightOccurrence) inferInstance
        rightRegion.homeomorph).symm (gluing.attachingMap a) =
          regions.edge rightOccurrence gluing.rightEdge.index (unitInterval.symm s) := by
  obtain ⟨s, hs⟩ := leftRegion.polygon.exists_boundaryToRegion_edgePoint_eq
    gluing.leftEdge.index a a.property
  -- Pull the selected left boundary parameter back through its cyclic presentation.
  have hleftPoint :
      (@Homeomorph.toEquiv _ _ (regions.topology leftOccurrence) inferInstance
        leftRegion.homeomorph).symm (a : leftRegion.polygon.region) =
        regions.edge leftOccurrence gluing.leftEdge.index s := by
    apply (@Homeomorph.toEquiv _ _ (regions.topology leftOccurrence) inferInstance
      leftRegion.homeomorph).symm_apply_eq.mpr
    calc
      (a : leftRegion.polygon.region) = leftRegion.polygon.boundaryToRegion
          (leftRegion.polygon.edgePoint gluing.leftEdge.index s) := hs.symm
      _ = leftRegion.homeomorph
          (regions.edge leftOccurrence gluing.leftEdge.index s) :=
        (leftRegion.homeomorph_edge_eq_boundaryToRegion
          gluing.leftEdge.index s).symm
      _ = (@Homeomorph.toEquiv _ _ (regions.topology leftOccurrence) inferInstance
          leftRegion.homeomorph)
          (regions.edge leftOccurrence gluing.leftEdge.index s) := rfl
  -- The attaching map and opposite orientations put the right point at parameter `symm s`.
  have hrightPoint :
      (@Homeomorph.toEquiv _ _ (regions.topology rightOccurrence) inferInstance
        rightRegion.homeomorph).symm (gluing.attachingMap a) =
        regions.edge rightOccurrence gluing.rightEdge.index (unitInterval.symm s) := by
    apply (@Homeomorph.toEquiv _ _ (regions.topology rightOccurrence) inferInstance
      rightRegion.homeomorph).symm_apply_eq.mpr
    calc
      gluing.attachingMap a =
          gluing.attachingMap (gluing.leftEdge.cyclicRegionPoint s) := by
        apply congrArg gluing.attachingMap
        apply Subtype.ext
        rw [gluing.leftEdge.cyclicRegionPoint_coe]
        exact hs.symm
      _ = rightRegion.polygon.boundaryToRegion
          (rightRegion.polygon.edgePoint gluing.rightEdge.index
            (unitInterval.symm s)) := by
        simpa only [if_neg hOppositeOrientations] using
          gluing.attachingMap_cyclicRegionPoint s
      _ = rightRegion.homeomorph
          (regions.edge rightOccurrence gluing.rightEdge.index
            (unitInterval.symm s)) :=
        (rightRegion.homeomorph_edge_eq_boundaryToRegion
          gluing.rightEdge.index (unitInterval.symm s)).symm
      _ = (@Homeomorph.toEquiv _ _ (regions.topology rightOccurrence) inferInstance
          rightRegion.homeomorph)
          (regions.edge rightOccurrence gluing.rightEdge.index
            (unitInterval.symm s)) := rfl
  exact ⟨s, hleftPoint, hrightPoint⟩

/-- Helper for Proposition 76.2: an adjunction pair supplies the complete explicit
witness package defining the selected labelled-edge relation. -/
theorem existsEdgePairingWitness_of_adjunctionIdentifies {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (c : α) {leftOccurrence rightOccurrence : Occurrence scheme}
    (leftRegion : CyclicRegion regions leftOccurrence)
    (rightRegion : CyclicRegion regions rightOccurrence)
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hleftLabel : (leftOccurrence.1.1.get gluing.leftEdge.index).1 = c)
    (hrightLabel : (rightOccurrence.1.1.get gluing.rightEdge.index).1 = c)
    (hOppositeSigns :
      (leftOccurrence.1.1.get gluing.leftEdge.index).2 ≠
        (rightOccurrence.1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (a : gluing.attachingSubset) :
    ∃ (region₁ region₂ : Occurrence scheme)
      (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
      (t : unitInterval),
      (region₁.1.1.get edge₁).1 = c ∧
      (region₂.1.1.get edge₂).1 = c ∧
      (⟨leftOccurrence,
        (@Homeomorph.toEquiv _ _ (regions.topology leftOccurrence) inferInstance
          leftRegion.homeomorph).symm (a : leftRegion.polygon.region)⟩ :
          regions.Source) = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
      (⟨rightOccurrence,
        (@Homeomorph.toEquiv _ _ (regions.topology rightOccurrence) inferInstance
          rightRegion.homeomorph).symm (gluing.attachingMap a)⟩ :
          regions.Source) =
        ⟨region₂, regions.edge region₂ edge₂
          (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
            else unitInterval.symm t)⟩ := by
  obtain ⟨s, hleftPoint, hrightPoint⟩ :=
    existsEdgeParameters_of_adjunctionIdentifies regions leftRegion rightRegion gluing
      hOppositeOrientations a
  -- Choose the distinguished occurrences and edges, then normalize the sign branch.
  refine ⟨leftOccurrence, rightOccurrence, gluing.leftEdge.index,
    gluing.rightEdge.index, s, hleftLabel, hrightLabel, ?_, ?_⟩
  · exact congrArg (Sigma.mk leftOccurrence) hleftPoint
  · have hrightSigma := congrArg (Sigma.mk rightOccurrence) hrightPoint
    simpa only [if_neg hOppositeSigns] using hrightSigma

/-- Helper for Proposition 76.2: every elementary adjunction of the selected
edges gives a direct pairing in the canonical `EdgeRelatedAt` relation. -/
theorem edgeRelatedAt_of_adjunctionIdentifies {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (c : α) {leftOccurrence rightOccurrence : Occurrence scheme}
    (leftRegion : CyclicRegion regions leftOccurrence)
    (rightRegion : CyclicRegion regions rightOccurrence)
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hleftLabel : (leftOccurrence.1.1.get gluing.leftEdge.index).1 = c)
    (hrightLabel : (rightOccurrence.1.1.get gluing.rightEdge.index).1 = c)
    (hOppositeSigns :
      (leftOccurrence.1.1.get gluing.leftEdge.index).2 ≠
        (rightOccurrence.1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (a : gluing.attachingSubset) :
    regions.EdgeRelatedAt c
      ⟨leftOccurrence,
        (@Homeomorph.toEquiv _ _ (regions.topology leftOccurrence) inferInstance
          leftRegion.homeomorph).symm (a : leftRegion.polygon.region)⟩
      ⟨rightOccurrence,
        (@Homeomorph.toEquiv _ _ (regions.topology rightOccurrence) inferInstance
          rightRegion.homeomorph).symm (gluing.attachingMap a)⟩ :=
    by
  -- Route correction: introduce the owner relation through its canonical witness API,
  -- instead of requiring callers to provide a duplicate constructor callback.
  apply (regions.edgeRelatedAt_iff c _ _).mpr
  exact existsEdgePairingWitness_of_adjunctionIdentifies regions c
    leftRegion rightRegion gluing hleftLabel hrightLabel hOppositeSigns
    hOppositeOrientations a

/-- Helper for Proposition 76.2: the adjunction setoid on the selected geometric
pair maps into the generated labelled-edge relation on the original source. -/
private theorem eqvGen_edgeRelatedAt_of_adjunctionSetoid {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α)
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hleftLabel :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).1 = c)
    (hrightLabel :
      ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).1 = c)
    (hOppositeSigns :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    {x y : leftRegion.polygon.region ⊕ rightRegion.polygon.region}
    (hxy : (AdjunctionSpace.setoid gluing.attachingSubset gluing.attachingMap).r x y) :
    Relation.EqvGen (regions.EdgeRelatedAt c)
      ((selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
        rightRegion).symm (Sum.inl x))
      ((selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
        rightRegion).symm (Sum.inl y)) := by
  let sourceHomeomorph :=
    selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion
  let labelSetoid := Relation.EqvGen.setoid (regions.EdgeRelatedAt c)
  let leftMap : leftRegion.polygon.region → Quotient labelSetoid :=
    fun z ↦ Quotient.mk' (sourceHomeomorph.symm (Sum.inl (Sum.inl z)))
  let rightMap : rightRegion.polygon.region → Quotient labelSetoid :=
    fun z ↦ Quotient.mk' (sourceHomeomorph.symm (Sum.inl (Sum.inr z)))
  -- Route correction: consume the opaque adjunction setoid through its public
  -- universal-property eliminator instead of trying to unfold its generators here.
  have hgenerator : ∀ a : gluing.attachingSubset,
      leftMap a = rightMap (gluing.attachingMap a) := by
    intro a
    -- The owner-level edge witness gives one generator of the labelled quotient.
    apply Quotient.sound
    apply Relation.EqvGen.rel
    dsimp only [leftMap, rightMap, sourceHomeomorph]
    rw [selectedEdgeSourceHomeomorph_symm_first,
      selectedEdgeSourceHomeomorph_symm_second]
    exact edgeRelatedAt_of_adjunctionIdentifies regions c leftRegion rightRegion gluing
      hleftLabel hrightLabel hOppositeSigns hOppositeOrientations a
  have hquotient := AdjunctionSpace.lift_respects gluing.attachingSubset
    gluing.attachingMap leftMap rightMap hgenerator x y hxy
  -- Equality in the labelled quotient is exactly the required generated relation.
  cases x <;> cases y <;>
    exact (Quotient.eq'').mp hquotient

/-- Helper for Proposition 76.2: equality under the direct geometric paste
implies the equivalence relation generated by the selected labelled edges. -/
private theorem eqvGen_edgeRelatedAt_of_selectedEdgeFirstPaste_eq {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α)
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hleftLabel :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).1 = c)
    (hrightLabel :
      ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).1 = c)
    (hOppositeSigns :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    {x y : regions.Source}
    (hxy : selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion
      gluing x = selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion
        rightRegion gluing y) :
    Relation.EqvGen (regions.EdgeRelatedAt c) x y := by
  let sourceHomeomorph :=
    selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion
  let quotientMap :=
    AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
  have hcore : ∀ a b,
      Sum.map quotientMap id a = Sum.map quotientMap id b →
        Relation.EqvGen (regions.EdgeRelatedAt c)
          (sourceHomeomorph.symm a) (sourceHomeomorph.symm b) := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            apply eqvGen_edgeRelatedAt_of_adjunctionSetoid word₁ word₂ rest
              regions c leftRegion rightRegion gluing hleftLabel hrightLabel
              hOppositeSigns hOppositeOrientations
            apply (AdjunctionSpace.quotientMap_eq_iff gluing.attachingSubset
              gluing.attachingMap a b).mp
            exact Sum.inl.inj hab
        | inr b =>
            have hfalse : False := by
              have hcontra : Sum.inl (quotientMap a) = Sum.inr b := by
                simpa only [Sum.map_inl, Sum.map_inr, id_eq] using hab
              exact Sum.inl_ne_inr hcontra
            exact hfalse.elim
    | inr a =>
        cases b with
        | inl b =>
            have hfalse : False := by
              have hcontra : Sum.inr a = Sum.inl (quotientMap b) := by
                simpa only [Sum.map_inl, Sum.map_inr, id_eq] using hab
              exact Sum.inr_ne_inl hcontra
            exact hfalse.elim
        | inr b =>
            have habRetained : a = b := Sum.inr.inj hab
            subst b
            exact Relation.EqvGen.refl _
  have hmapped : Sum.map quotientMap id (sourceHomeomorph x) =
      Sum.map quotientMap id (sourceHomeomorph y) := by
    simpa only [selectedEdgeFirstPaste, sourceHomeomorph, quotientMap] using hxy
  have hpulled := hcore (sourceHomeomorph x) (sourceHomeomorph y) hmapped
  -- Cancel the source homeomorphism after the branchwise kernel comparison.
  simpa only [sourceHomeomorph, Homeomorph.symm_apply_apply] using hpulled

/-- Helper for Proposition 76.2: if the only `c`-edges are the selected opposite
pair, any map induced from their edge-gluing realization identifies every
`EdgeRelatedAt c` generator. -/
theorem edgePairingAt_maps_eq_of_edgeGluing {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (c : α) {leftOccurrence rightOccurrence : Occurrence scheme}
    (leftRegion : CyclicRegion regions leftOccurrence)
    (rightRegion : CyclicRegion regions rightOccurrence)
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hOppositeSigns :
      (leftOccurrence.1.1.get gluing.leftEdge.index).2 ≠
        (rightOccurrence.1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (classify : ∀ (region : Occurrence scheme)
        (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 = c →
        (region = leftOccurrence ∧ edge.val = gluing.leftEdge.index.val) ∨
        (region = rightOccurrence ∧ edge.val = gluing.rightEdge.index.val))
    {Y : Type w} (firstPaste : regions.Source → Y)
    (comparison : gluing.Realization → Y)
    (hleft : ∀ x : regions.Point leftOccurrence,
      firstPaste ⟨leftOccurrence, x⟩ =
        comparison (gluing.includeLeft (leftRegion.homeomorph x)))
    (hright : ∀ x : regions.Point rightOccurrence,
      firstPaste ⟨rightOccurrence, x⟩ =
        comparison (gluing.includeRight (rightRegion.homeomorph x)))
    {x y : regions.Source}
    (hxy : regions.EdgeRelatedAt c x y) :
    firstPaste x = firstPaste y := by
  -- Eliminate the owner relation once, then run the four selected-edge cases.
  rcases (regions.edgeRelatedAt_iff c x y).mp hxy with
    ⟨region₁, region₂, edge₁, edge₂, t, hc₁, hc₂, rfl, rfl⟩
  have hleftBoundary (edge : Fin leftOccurrence.1.1.length)
      (hedge : edge.val = gluing.leftEdge.index.val) (s : unitInterval) :
      firstPaste ⟨leftOccurrence, regions.edge leftOccurrence edge s⟩ =
        comparison (gluing.includeLeft
          (leftRegion.polygon.boundaryToRegion
            (leftRegion.polygon.edgePoint gluing.leftEdge.index s))) := by
    have hedgeEq : edge = gluing.leftEdge.index := Fin.ext hedge
    subst edge
    calc
      firstPaste ⟨leftOccurrence,
          regions.edge leftOccurrence gluing.leftEdge.index s⟩ =
          comparison (gluing.includeLeft
            (leftRegion.homeomorph
              (regions.edge leftOccurrence gluing.leftEdge.index s))) :=
        hleft _
      _ = comparison (gluing.includeLeft
          (leftRegion.polygon.boundaryToRegion
            (leftRegion.polygon.edgePoint gluing.leftEdge.index s))) :=
        congrArg comparison (congrArg gluing.includeLeft
          (leftRegion.homeomorph_edge_eq_boundaryToRegion gluing.leftEdge.index s))
  have hrightBoundary (edge : Fin rightOccurrence.1.1.length)
      (hedge : edge.val = gluing.rightEdge.index.val) (s : unitInterval) :
      firstPaste ⟨rightOccurrence, regions.edge rightOccurrence edge s⟩ =
        comparison (gluing.includeRight
          (rightRegion.polygon.boundaryToRegion
            (rightRegion.polygon.edgePoint gluing.rightEdge.index s))) := by
    have hedgeEq : edge = gluing.rightEdge.index := Fin.ext hedge
    subst edge
    calc
      firstPaste ⟨rightOccurrence,
          regions.edge rightOccurrence gluing.rightEdge.index s⟩ =
          comparison (gluing.includeRight
            (rightRegion.homeomorph
              (regions.edge rightOccurrence gluing.rightEdge.index s))) :=
        hright _
      _ = comparison (gluing.includeRight
          (rightRegion.polygon.boundaryToRegion
            (rightRegion.polygon.edgePoint gluing.rightEdge.index s))) :=
        congrArg comparison (congrArg gluing.includeRight
          (rightRegion.homeomorph_edge_eq_boundaryToRegion gluing.rightEdge.index s))
  rcases classify region₁ edge₁ hc₁ with
      ⟨hregion₁, hedge₁⟩ | ⟨hregion₁, hedge₁⟩ <;>
    rcases classify region₂ edge₂ hc₂ with
      ⟨hregion₂, hedge₂⟩ | ⟨hregion₂, hedge₂⟩
  · subst region₁
    subst region₂
    have hedge₁Eq : edge₁ = gluing.leftEdge.index := Fin.ext hedge₁
    have hedge₂Eq : edge₂ = gluing.leftEdge.index := Fin.ext hedge₂
    subst edge₁
    subst edge₂
    have hparameter :
        (if (leftOccurrence.1.1.get gluing.leftEdge.index).2 =
            (leftOccurrence.1.1.get gluing.leftEdge.index).2 then t
          else unitInterval.symm t) = t := if_pos rfl
    exact congrArg
      (fun s ↦ firstPaste ⟨leftOccurrence,
        regions.edge leftOccurrence gluing.leftEdge.index s⟩) hparameter.symm
  · subst region₁
    subst region₂
    have hedge₁Eq : edge₁ = gluing.leftEdge.index := Fin.ext hedge₁
    have hedge₂Eq : edge₂ = gluing.rightEdge.index := Fin.ext hedge₂
    subst edge₁
    subst edge₂
    rw [if_neg hOppositeSigns]
    calc
      firstPaste ⟨leftOccurrence,
          regions.edge leftOccurrence gluing.leftEdge.index t⟩ =
          comparison (gluing.includeLeft
            (leftRegion.polygon.boundaryToRegion
              (leftRegion.polygon.edgePoint gluing.leftEdge.index t))) :=
        hleftBoundary gluing.leftEdge.index rfl t
      _ = comparison (gluing.includeRight
          (rightRegion.polygon.boundaryToRegion
            (rightRegion.polygon.edgePoint gluing.rightEdge.index
              (unitInterval.symm t)))) := congrArg comparison
        (gluing.includeLeft_edgePoint_eq_includeRight_symm hOppositeOrientations t)
      _ = firstPaste ⟨rightOccurrence,
          regions.edge rightOccurrence gluing.rightEdge.index
            (unitInterval.symm t)⟩ :=
        (hrightBoundary gluing.rightEdge.index rfl (unitInterval.symm t)).symm
  · subst region₁
    subst region₂
    have hedge₁Eq : edge₁ = gluing.rightEdge.index := Fin.ext hedge₁
    have hedge₂Eq : edge₂ = gluing.leftEdge.index := Fin.ext hedge₂
    subst edge₁
    subst edge₂
    rw [if_neg hOppositeSigns.symm]
    calc
      firstPaste ⟨rightOccurrence,
          regions.edge rightOccurrence gluing.rightEdge.index t⟩ =
          comparison (gluing.includeRight
            (rightRegion.polygon.boundaryToRegion
              (rightRegion.polygon.edgePoint gluing.rightEdge.index t))) :=
        hrightBoundary gluing.rightEdge.index rfl t
      _ = comparison (gluing.includeLeft
          (leftRegion.polygon.boundaryToRegion
            (leftRegion.polygon.edgePoint gluing.leftEdge.index
              (unitInterval.symm t)))) := by
        have hglue := congrArg comparison
          (gluing.includeLeft_edgePoint_eq_includeRight_symm
            hOppositeOrientations (unitInterval.symm t)).symm
        simpa only [unitInterval.symm_symm] using hglue
      _ = firstPaste ⟨leftOccurrence,
          regions.edge leftOccurrence gluing.leftEdge.index
            (unitInterval.symm t)⟩ :=
        (hleftBoundary gluing.leftEdge.index rfl (unitInterval.symm t)).symm
  · subst region₁
    subst region₂
    have hedge₁Eq : edge₁ = gluing.rightEdge.index := Fin.ext hedge₁
    have hedge₂Eq : edge₂ = gluing.rightEdge.index := Fin.ext hedge₂
    subst edge₁
    subst edge₂
    have hparameter :
        (if (rightOccurrence.1.1.get gluing.rightEdge.index).2 =
            (rightOccurrence.1.1.get gluing.rightEdge.index).2 then t
          else unitInterval.symm t) = t := if_pos rfl
    exact congrArg
      (fun s ↦ firstPaste ⟨rightOccurrence,
        regions.edge rightOccurrence gluing.rightEdge.index s⟩) hparameter.symm

/-- Helper for Proposition 76.2: under the canonical inclusion computation rules,
the direct geometric paste identifies every elementary selected-edge pairing. -/
private theorem selectedEdgeFirstPaste_eq_of_edgeRelatedAt {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α)
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hOppositeSigns :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (classify : ∀ (region : Occurrence (word₁ ::ₘ word₂ ::ₘ rest))
        (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 = c →
        (region = firstOccurrence word₁ word₂ rest ∧
          edge.val = gluing.leftEdge.index.val) ∨
        (region = secondOccurrence word₁ word₂ rest ∧
          edge.val = gluing.rightEdge.index.val))
    (hleftQuotient : ∀ z : regions.Point (firstOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inl (leftRegion.homeomorph z)) =
        gluing.includeLeft (leftRegion.homeomorph z))
    (hrightQuotient : ∀ z : regions.Point (secondOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inr (rightRegion.homeomorph z)) =
        gluing.includeRight (rightRegion.homeomorph z))
    {x y : regions.Source} (hxy : regions.EdgeRelatedAt c x y) :
    selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing x =
      selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing y := by
  -- Route correction: compare through the public adjunction inclusions instead of
  -- attempting to unfold the owner-opaque generated setoid in this target module.
  apply edgePairingAt_maps_eq_of_edgeGluing regions c leftRegion rightRegion gluing
    hOppositeSigns hOppositeOrientations classify
    (selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing)
    Sum.inl
  · intro z
    rw [selectedEdgeFirstPaste_first]
    -- Use the supplied computation rule for the opaque named inclusion.
    exact congrArg Sum.inl (hleftQuotient z)
  · intro z
    rw [selectedEdgeFirstPaste_second]
    -- Use the supplied computation rule for the opaque named inclusion.
    exact congrArg Sum.inl (hrightQuotient z)
  · exact hxy

/-- Helper for Proposition 76.2: under the canonical inclusion computation rules,
the direct geometric paste identifies the generated selected-edge relation. -/
private theorem selectedEdgeFirstPaste_eq_of_eqvGen_edgeRelatedAt {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α)
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hOppositeSigns :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (classify : ∀ (region : Occurrence (word₁ ::ₘ word₂ ::ₘ rest))
        (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 = c →
        (region = firstOccurrence word₁ word₂ rest ∧
          edge.val = gluing.leftEdge.index.val) ∨
        (region = secondOccurrence word₁ word₂ rest ∧
          edge.val = gluing.rightEdge.index.val))
    (hleftQuotient : ∀ z : regions.Point (firstOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inl (leftRegion.homeomorph z)) =
        gluing.includeLeft (leftRegion.homeomorph z))
    (hrightQuotient : ∀ z : regions.Point (secondOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inr (rightRegion.homeomorph z)) =
        gluing.includeRight (rightRegion.homeomorph z))
    {x y : regions.Source}
    (hxy : Relation.EqvGen (regions.EdgeRelatedAt c) x y) :
    selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing x =
      selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing y := by
  -- Extend the generator computation through reflexivity, symmetry, and transitivity.
  induction hxy with
  | rel a b hab =>
      exact selectedEdgeFirstPaste_eq_of_edgeRelatedAt word₁ word₂ rest regions c
        leftRegion rightRegion gluing hOppositeSigns hOppositeOrientations classify
        hleftQuotient hrightQuotient hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b d _ _ hab hbd => exact hab.trans hbd

/-- Helper for Proposition 76.2: under the canonical inclusion computation rules,
the direct paste fibers are exactly the generated selected-edge relation. -/
private theorem selectedEdgeFirstPaste_fibers {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α)
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hleftLabel :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).1 = c)
    (hrightLabel :
      ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).1 = c)
    (hOppositeSigns :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (classify : ∀ (region : Occurrence (word₁ ::ₘ word₂ ::ₘ rest))
        (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 = c →
        (region = firstOccurrence word₁ word₂ rest ∧
          edge.val = gluing.leftEdge.index.val) ∨
        (region = secondOccurrence word₁ word₂ rest ∧
          edge.val = gluing.rightEdge.index.val))
    (hleftQuotient : ∀ z : regions.Point (firstOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inl (leftRegion.homeomorph z)) =
        gluing.includeLeft (leftRegion.homeomorph z))
    (hrightQuotient : ∀ z : regions.Point (secondOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inr (rightRegion.homeomorph z)) =
        gluing.includeRight (rightRegion.homeomorph z))
    (x y : regions.Source) :
    selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing x =
        selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing y ↔
      Relation.EqvGen (regions.EdgeRelatedAt c) x y := by
  constructor
  · -- Pull equality back through the geometric quotient and source decomposition.
    exact eqvGen_edgeRelatedAt_of_selectedEdgeFirstPaste_eq word₁ word₂ rest regions c
      leftRegion rightRegion gluing hleftLabel hrightLabel hOppositeSigns
      hOppositeOrientations
  · -- Push every selected-edge generator through the adjunction quotient.
    exact selectedEdgeFirstPaste_eq_of_eqvGen_edgeRelatedAt word₁ word₂ rest regions c
      leftRegion rightRegion gluing hOppositeSigns hOppositeOrientations classify
      hleftQuotient hrightQuotient

/-- Helper for Proposition 76.2: under the canonical inclusion computation rules,
the direct geometric quotient is a certified paste of the selected label. -/
private theorem selectedEdgeFirstPaste_pastesLabel {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest)) (c : α)
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (hleftLabel :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).1 = c)
    (hrightLabel :
      ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).1 = c)
    (hOppositeSigns :
      ((firstOccurrence word₁ word₂ rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence word₁ word₂ rest).1.1.get gluing.rightEdge.index).2)
    (hOppositeOrientations :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (classify : ∀ (region : Occurrence (word₁ ::ₘ word₂ ::ₘ rest))
        (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 = c →
        (region = firstOccurrence word₁ word₂ rest ∧
          edge.val = gluing.leftEdge.index.val) ∨
        (region = secondOccurrence word₁ word₂ rest ∧
          edge.val = gluing.rightEdge.index.val))
    (hleftQuotient : ∀ z : regions.Point (firstOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inl (leftRegion.homeomorph z)) =
        gluing.includeLeft (leftRegion.homeomorph z))
    (hrightQuotient : ∀ z : regions.Point (secondOccurrence word₁ word₂ rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inr (rightRegion.homeomorph z)) =
        gluing.includeRight (rightRegion.homeomorph z)) :
    regions.PastesLabel c
      (selectedEdgeFirstPaste word₁ word₂ rest regions leftRegion rightRegion gluing) := by
  constructor
  · -- Quotientness was established directly from the sum of quotient maps.
    exact selectedEdgeFirstPaste_isQuotientMap word₁ word₂ rest regions leftRegion
      rightRegion gluing
  · intro x y
    -- Supply the exact two-direction fiber theorem.
    exact selectedEdgeFirstPaste_fibers word₁ word₂ rest regions c leftRegion
      rightRegion gluing hleftLabel hrightLabel hOppositeSigns hOppositeOrientations
      classify hleftQuotient hrightQuotient x y

/-- Helper for Proposition 76.2: the point type of a reassembled family is the
combined polygon on its first occurrence and the retained polygon thereafter. -/
@[reducible] private noncomputable def reassembledPoint {α : Type u}
    (word : PolygonWord α)
    (rest : LabellingScheme α) (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest)) : Type v :=
  match consOccurrenceEquiv word rest region with
  | none => ULift.{v, 0} combined.region
  | some retained => ULift.{v, 0} (retainedPolygon retained).region

/-- Helper for Proposition 76.2: selecting the distinguished branch identifies
the reassembled point type with the lifted combined region. -/
private theorem reassembledPoint_eq_of_eq_none {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest))
    (hbranch : consOccurrenceEquiv word rest region = none) :
    reassembledPoint word rest combined retainedPolygon region =
      ULift.{v, 0} combined.region := by
  simp only [reassembledPoint, hbranch]

/-- Helper for Proposition 76.2: selecting a retained branch identifies the
reassembled point type with the lifted retained region. -/
private theorem reassembledPoint_eq_of_eq_some {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest))
    (retained : Occurrence rest)
    (hbranch : consOccurrenceEquiv word rest region = some retained) :
    reassembledPoint word rest combined retainedPolygon region =
      ULift.{v, 0} (retainedPolygon retained).region := by
  simp only [reassembledPoint, hbranch]

/-- Helper for Proposition 76.2: each reassembled component carries its canonical
polygon-region topology. -/
@[reducible] private noncomputable def reassembledTopology {α : Type u}
    (word : PolygonWord α)
    (rest : LabellingScheme α) (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest)) :
    TopologicalSpace (reassembledPoint word rest combined retainedPolygon region) :=
  match hbranch : consOccurrenceEquiv word rest region with
  | none =>
      (reassembledPoint_eq_of_eq_none word rest combined retainedPolygon region
        hbranch).symm ▸
        (inferInstance : TopologicalSpace (ULift.{v, 0} combined.region))
  | some retained =>
      (reassembledPoint_eq_of_eq_some word rest combined retainedPolygon region retained
        hbranch).symm ▸
        (inferInstance : TopologicalSpace
          (ULift.{v, 0} (retainedPolygon retained).region))

/-- Helper for Proposition 76.2: the outer distinguished branch has the newly
adjoined polygon word. -/
private theorem occurrenceWord_eq_of_consOccurrenceEquiv_eq_none {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (region : Occurrence (word ::ₘ rest))
    (hregion : consOccurrenceEquiv word rest region = none) :
    region.1 = word := by
  have hoccurrence : region = mergedFirstOccurrence word rest := by
    apply (consOccurrenceEquiv word rest).injective
    simpa only [mergedFirstOccurrence, Equiv.apply_symm_apply] using hregion
  exact (congrArg Sigma.fst hoccurrence).trans
    (mergedFirstOccurrence_fst word rest)

/-- Helper for Proposition 76.2: a retained branch keeps the polygon word of
the corresponding retained occurrence. -/
private theorem occurrenceWord_eq_of_consOccurrenceEquiv_eq_some {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (region : Occurrence (word ::ₘ rest)) (retained : Occurrence rest)
    (hregion : consOccurrenceEquiv word rest region = some retained) :
    region.1 = retained.1 := by
  have hoccurrence : region = mergedRestOccurrence word rest retained := by
    apply (consOccurrenceEquiv word rest).injective
    simpa only [mergedRestOccurrence, Equiv.apply_symm_apply] using hregion
  exact (congrArg Sigma.fst hoccurrence).trans
    (mergedRestOccurrence_fst word rest retained)

/-- Helper for Proposition 76.2: the boundary maps of the reassembled family
are the canonical boundary maps of its component polygons. -/
private noncomputable def reassembledEdge {α : Type u} (word : PolygonWord α)
    (rest : LabellingScheme α) (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest))
    (index : Fin region.1.1.length) (t : unitInterval) :
    reassembledPoint word rest combined retainedPolygon region :=
  match hbranch : consOccurrenceEquiv word rest region with
  | none =>
      (reassembledPoint_eq_of_eq_none word rest combined retainedPolygon region
        hbranch).symm ▸
        ULift.up.{v, 0} (combined.boundaryToRegion
          (combined.edgePoint
            (Fin.cast (congrArg (fun polygonWord : PolygonWord α ↦
              polygonWord.1.length)
                (occurrenceWord_eq_of_consOccurrenceEquiv_eq_none word rest region hbranch))
              index) t))
  | some retained =>
      (reassembledPoint_eq_of_eq_some word rest combined retainedPolygon region retained
        hbranch).symm ▸
        ULift.up.{v, 0} ((retainedPolygon retained).boundaryToRegion
          ((retainedPolygon retained).edgePoint
            (Fin.cast (congrArg (fun polygonWord : PolygonWord α ↦
              polygonWord.1.length)
                (occurrenceWord_eq_of_consOccurrenceEquiv_eq_some word rest region retained
                  hbranch)) index) t))

/-- Helper for Proposition 76.2: package the combined first polygon and all
retained polygons as regions for the merged labelling scheme. -/
private noncomputable def reassembledRegions {α : Type u} (word : PolygonWord α)
    (rest : LabellingScheme α) (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) : PolygonalRegions.{u, v} (word ::ₘ rest) :=
  { Point := reassembledPoint word rest combined retainedPolygon
    topology := reassembledTopology word rest combined retainedPolygon
    edge := reassembledEdge word rest combined retainedPolygon }

/-- Helper for Proposition 76.2: the distinguished component of the reassembled
family has the lifted combined polygon as its point type. -/
private theorem reassembledPoint_first_eq {α : Type u} (word : PolygonWord α)
    (rest : LabellingScheme α) (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) :
    reassembledPoint word rest combined retainedPolygon
        (mergedFirstOccurrence word rest) =
      ULift.{v, 0} combined.region := by
  exact reassembledPoint_eq_of_eq_none word rest combined retainedPolygon _
    (Equiv.apply_symm_apply (consOccurrenceEquiv word rest) none)

/-- Helper for Proposition 76.2: a retained component of the reassembled family
has the lifted retained polygon as its point type. -/
private theorem reassembledPoint_rest_eq {α : Type u} (word : PolygonWord α)
    (rest : LabellingScheme α) (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest) :
    reassembledPoint word rest combined retainedPolygon
        (mergedRestOccurrence word rest region) =
      ULift.{v, 0} (retainedPolygon region).region := by
  exact reassembledPoint_eq_of_eq_some word rest combined retainedPolygon _ region
    (Equiv.apply_symm_apply (consOccurrenceEquiv word rest) (some region))

/-- Helper for Proposition 76.2: the merged first occurrence selects the
distinguished branch of the one-word occurrence splitting. -/
private theorem consOccurrenceEquiv_mergedFirst {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α) :
    consOccurrenceEquiv word rest (mergedFirstOccurrence word rest) = none := by
  simp only [mergedFirstOccurrence, Equiv.apply_symm_apply]

/-- Helper for Proposition 76.2: an embedded retained occurrence selects its
corresponding retained branch of the one-word occurrence splitting. -/
private theorem consOccurrenceEquiv_mergedRest {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (region : Occurrence rest) :
    consOccurrenceEquiv word rest (mergedRestOccurrence word rest region) =
      some region := by
  simp only [mergedRestOccurrence, Equiv.apply_symm_apply]

/-- Helper for Proposition 76.2: on the distinguished branch, the stored
reassembled topology is the transported topology of the combined polygon. -/
private theorem reassembledTopology_eq_of_eq_none {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest))
    (hbranch : consOccurrenceEquiv word rest region = none) :
    reassembledTopology word rest combined retainedPolygon region =
      (reassembledPoint_eq_of_eq_none word rest combined retainedPolygon region
        hbranch).symm ▸
        (inferInstance : TopologicalSpace (ULift.{v, 0} combined.region)) := by
  unfold reassembledTopology
  split
  · rename_i heq
    have hproof : heq = hbranch := Subsingleton.elim _ _
    cases hproof
    rfl
  · rename_i retained hsome
    rw [hbranch] at hsome
    contradiction

/-- Helper for Proposition 76.2: on a retained branch, the stored reassembled
topology is the transported topology of the corresponding retained polygon. -/
private theorem reassembledTopology_eq_of_eq_some {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence (word ::ₘ rest))
    (retained : Occurrence rest)
    (hbranch : consOccurrenceEquiv word rest region = some retained) :
    reassembledTopology word rest combined retainedPolygon region =
      (reassembledPoint_eq_of_eq_some word rest combined retainedPolygon region retained
        hbranch).symm ▸
        (inferInstance : TopologicalSpace
          (ULift.{v, 0} (retainedPolygon retained).region)) := by
  unfold reassembledTopology
  split
  · rename_i hnone
    rw [hbranch] at hnone
    contradiction
  · rename_i retained' hsome
    have hretained : retained' = retained := Option.some.inj (hsome.symm.trans hbranch)
    subst retained'
    have hproof : hsome = hbranch := Subsingleton.elim _ _
    cases hproof
    rfl

/-- Helper for Proposition 76.2: a type cast is a homeomorphism when the source
topology is transported from the target topology along the same equality. -/
private theorem isHomeomorph_equivCast {X Y : Type v} (h : X = Y)
    (targetTopology : TopologicalSpace Y) :
    @IsHomeomorph X Y (h.symm ▸ targetTopology) targetTopology (Equiv.cast h) := by
  subst Y
  exact IsHomeomorph.id

/-- Helper for Proposition 76.2: casting back along the inverse of a type
equality cancels the corresponding dependent transport. -/
private theorem equivCast_symm_transport {X Y : Type v} (h : X = Y) (y : Y) :
    Equiv.cast h (h.symm ▸ y) = y := by
  subst Y
  rfl

/-- Helper for Proposition 76.2: the canonical cast from the distinguished
reassembled component to the lifted combined polygon is a homeomorphism. -/
private theorem reassembledFirstCast_isHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) : @IsHomeomorph
      (reassembledPoint word rest combined retainedPolygon
        (mergedFirstOccurrence word rest))
      (ULift.{v, 0} combined.region)
      (reassembledTopology word rest combined retainedPolygon
        (mergedFirstOccurrence word rest)) inferInstance
      (Equiv.cast (reassembledPoint_first_eq word rest combined retainedPolygon)) := by
  have hbranch := consOccurrenceEquiv_mergedFirst word rest
  rw [reassembledTopology_eq_of_eq_none word rest combined retainedPolygon
    (mergedFirstOccurrence word rest) hbranch]
  exact isHomeomorph_equivCast
    (reassembledPoint_eq_of_eq_none word rest combined retainedPolygon
      (mergedFirstOccurrence word rest) hbranch) inferInstance

/-- Helper for Proposition 76.2: normalize the distinguished component point
type of a reassembled family. -/
private noncomputable def reassembledFirstHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) :
    @Homeomorph
      (reassembledPoint word rest combined retainedPolygon
        (mergedFirstOccurrence word rest))
      (ULift.{v, 0} combined.region)
      (reassembledTopology word rest combined retainedPolygon
        (mergedFirstOccurrence word rest)) inferInstance :=
  @IsHomeomorph.homeomorph _ _
    (reassembledTopology word rest combined retainedPolygon
      (mergedFirstOccurrence word rest)) inferInstance
    (Equiv.cast (reassembledPoint_first_eq word rest combined retainedPolygon))
    (reassembledFirstCast_isHomeomorph word rest combined retainedPolygon)

/-- Helper for Proposition 76.2: the canonical cast from a retained reassembled
component to its lifted retained polygon is a homeomorphism. -/
private theorem reassembledRestCast_isHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest) : @IsHomeomorph
      (reassembledPoint word rest combined retainedPolygon
        (mergedRestOccurrence word rest region))
      (ULift.{v, 0} (retainedPolygon region).region)
      (reassembledTopology word rest combined retainedPolygon
        (mergedRestOccurrence word rest region)) inferInstance
      (Equiv.cast
        (reassembledPoint_rest_eq word rest combined retainedPolygon region)) := by
  have hbranch := consOccurrenceEquiv_mergedRest word rest region
  rw [reassembledTopology_eq_of_eq_some word rest combined retainedPolygon
    (mergedRestOccurrence word rest region) region hbranch]
  exact isHomeomorph_equivCast
    (reassembledPoint_eq_of_eq_some word rest combined retainedPolygon
      (mergedRestOccurrence word rest region) region hbranch) inferInstance

/-- Helper for Proposition 76.2: normalize a retained component point type of a
reassembled family. -/
private noncomputable def reassembledRestHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest) :
    @Homeomorph
      (reassembledPoint word rest combined retainedPolygon
        (mergedRestOccurrence word rest region))
      (ULift.{v, 0} (retainedPolygon region).region)
      (reassembledTopology word rest combined retainedPolygon
        (mergedRestOccurrence word rest region)) inferInstance :=
  @IsHomeomorph.homeomorph _ _
    (reassembledTopology word rest combined retainedPolygon
      (mergedRestOccurrence word rest region)) inferInstance
    (Equiv.cast
      (reassembledPoint_rest_eq word rest combined retainedPolygon region))
    (reassembledRestCast_isHomeomorph word rest combined retainedPolygon region)

/-- Helper for Proposition 76.2: the distinguished normalization is the
canonical cast on points. -/
private theorem reassembledFirstHomeomorph_apply {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length)
    (x : reassembledPoint word rest combined retainedPolygon
      (mergedFirstOccurrence word rest)) :
    reassembledFirstHomeomorph word rest combined retainedPolygon x =
      Equiv.cast (reassembledPoint_first_eq word rest combined retainedPolygon) x := by
  rfl

/-- Helper for Proposition 76.2: each retained normalization is the canonical
cast on points. -/
private theorem reassembledRestHomeomorph_apply {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest)
    (x : reassembledPoint word rest combined retainedPolygon
      (mergedRestOccurrence word rest region)) :
    reassembledRestHomeomorph word rest combined retainedPolygon region x =
      Equiv.cast
        (reassembledPoint_rest_eq word rest combined retainedPolygon region) x := by
  rfl

/-- Helper for Proposition 76.2: normalizing a distinguished boundary point
recovers the corresponding lifted boundary point of the combined polygon. -/
private theorem reassembledFirstHomeomorph_edge {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length)
    (index : Fin (mergedFirstOccurrence word rest).1.1.length)
    (t : unitInterval) :
    reassembledFirstHomeomorph word rest combined retainedPolygon
        ((reassembledRegions word rest combined retainedPolygon).edge
          (mergedFirstOccurrence word rest) index t) =
      ULift.up.{v, 0} (combined.boundaryToRegion
        (combined.edgePoint
          (Fin.cast (congrArg (fun polygonWord : PolygonWord α ↦
            polygonWord.1.length) (mergedFirstOccurrence_fst word rest)) index) t)) := by
  have hbranch := consOccurrenceEquiv_mergedFirst word rest
  rw [reassembledFirstHomeomorph_apply]
  simp only [reassembledRegions]
  unfold reassembledEdge
  split
  · rename_i heq
    have hpointProof : reassembledPoint_first_eq.{u, v} word rest combined retainedPolygon =
        reassembledPoint_eq_of_eq_none.{u, v} word rest combined retainedPolygon
          (mergedFirstOccurrence word rest) heq := Subsingleton.elim _ _
    have hindexProof :
        congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
            (occurrenceWord_eq_of_consOccurrenceEquiv_eq_none word rest
              (mergedFirstOccurrence word rest) heq) =
          congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
            (mergedFirstOccurrence_fst word rest) := Subsingleton.elim _ _
    cases hpointProof
    cases hindexProof
    exact equivCast_symm_transport _ _
  · rename_i retained hsome
    have himpossible : none = some retained := hbranch.symm.trans hsome
    cases himpossible

/-- Helper for Proposition 76.2: normalizing a retained boundary point recovers
the corresponding lifted boundary point of its retained polygon. -/
private theorem reassembledRestHomeomorph_edge {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest)
    (index : Fin (mergedRestOccurrence word rest region).1.1.length)
    (t : unitInterval) :
    reassembledRestHomeomorph word rest combined retainedPolygon region
        ((reassembledRegions word rest combined retainedPolygon).edge
          (mergedRestOccurrence word rest region) index t) =
      ULift.up.{v, 0} ((retainedPolygon region).boundaryToRegion
        ((retainedPolygon region).edgePoint
          (Fin.cast (congrArg (fun polygonWord : PolygonWord α ↦
            polygonWord.1.length) (mergedRestOccurrence_fst word rest region)) index) t)) := by
  have hbranch := consOccurrenceEquiv_mergedRest word rest region
  rw [reassembledRestHomeomorph_apply]
  simp only [reassembledRegions]
  unfold reassembledEdge
  split
  · rename_i hnone
    have himpossible : some region = none := hbranch.symm.trans hnone
    cases himpossible
  · rename_i retained hsome
    have hretained : retained = region := Option.some.inj (hsome.symm.trans hbranch)
    subst retained
    have hpointProof :
        reassembledPoint_rest_eq.{u, v} word rest combined retainedPolygon region =
          reassembledPoint_eq_of_eq_some.{u, v} word rest combined retainedPolygon
            (mergedRestOccurrence word rest region) region hsome := Subsingleton.elim _ _
    have hindexProof :
        congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
            (occurrenceWord_eq_of_consOccurrenceEquiv_eq_some word rest
              (mergedRestOccurrence word rest region) region hsome) =
          congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
            (mergedRestOccurrence_fst word rest region) := Subsingleton.elim _ _
    cases hpointProof
    cases hindexProof
    exact equivCast_symm_transport _ _

/-- Helper for Proposition 76.2: the combined polygon transported to the exact
vertex count of the distinguished merged occurrence. -/
private noncomputable def reassembledFirstPolygon {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length) :
    CyclicPolygon (mergedFirstOccurrence word rest).1.1.length :=
  CyclicPolygon.castVertexCount
    (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
      (mergedFirstOccurrence_fst word rest)).symm combined

/-- Helper for Proposition 76.2: the distinguished merged component is
homeomorphic to its transported combined polygon. -/
private noncomputable def reassembledFirstRegionHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) :
    RegionHomeomorph (reassembledRegions word rest combined retainedPolygon)
      (mergedFirstOccurrence word rest) (reassembledFirstPolygon word rest combined).region :=
  @Homeomorph.trans _ _ _
    (reassembledTopology word rest combined retainedPolygon
      (mergedFirstOccurrence word rest)) inferInstance inferInstance
    (reassembledFirstHomeomorph word rest combined retainedPolygon)
    (@Homeomorph.trans _ _ _ inferInstance inferInstance inferInstance
      Homeomorph.ulift
      (Homeomorph.setCongr
        (CyclicPolygon.castVertexCount_region
          (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
            (mergedFirstOccurrence_fst word rest)).symm combined)).symm)

/-- Helper for Proposition 76.2: forgetting the transported polygon membership
in the distinguished comparison leaves the normalized combined-region point. -/
private theorem reassembledFirstRegionHomeomorph_coe {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length)
    (x : reassembledPoint word rest combined retainedPolygon
      (mergedFirstOccurrence word rest)) :
    ((reassembledFirstRegionHomeomorph word rest combined retainedPolygon x :
        (reassembledFirstPolygon word rest combined).region) :
      EuclideanSpace ℝ (Fin 2)) =
      ((reassembledFirstHomeomorph word rest combined retainedPolygon x).down :
        EuclideanSpace ℝ (Fin 2)) := by
  rfl

/-- Helper for Proposition 76.2: the distinguished reassembled homeomorphism
preserves every canonical affine edge parameter. -/
private theorem reassembledFirstEdgeCompatibility {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length)
    (index : Fin (mergedFirstOccurrence word rest).1.1.length)
    (t : unitInterval) :
    ((reassembledFirstRegionHomeomorph word rest combined retainedPolygon
        ((reassembledRegions word rest combined retainedPolygon).edge
          (mergedFirstOccurrence word rest) index t) :
          (reassembledFirstPolygon word rest combined).region) :
        EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap
        ((reassembledFirstPolygon word rest combined).toPolygon.vertices index)
        ((reassembledFirstPolygon word rest combined).toPolygon.vertices
          (finRotate (mergedFirstOccurrence word rest).1.1.length index)) (t : ℝ) := by
  let hcount := congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
    (mergedFirstOccurrence_fst word rest)
  let originalIndex : Fin word.1.length := Fin.cast hcount index
  have hedge := reassembledFirstHomeomorph_edge word rest combined retainedPolygon index t
  have hedgeValue := congrArg (fun point ↦ (point.down : EuclideanSpace ℝ (Fin 2))) hedge
  calc
    ((reassembledFirstRegionHomeomorph word rest combined retainedPolygon
        ((reassembledRegions word rest combined retainedPolygon).edge
          (mergedFirstOccurrence word rest) index t) :
          (reassembledFirstPolygon word rest combined).region) :
        EuclideanSpace ℝ (Fin 2)) =
        (combined.edgePoint originalIndex t : EuclideanSpace ℝ (Fin 2)) := by
      rw [reassembledFirstRegionHomeomorph_coe]
      simpa only [CyclicPolygon.boundaryToRegion_coe, originalIndex, hcount]
        using hedgeValue
    _ = ((reassembledFirstPolygon word rest combined).edgePoint index t :
        EuclideanSpace ℝ (Fin 2)) := by
      symm
      have hcast := CyclicPolygon.castVertexCount_edgePoint_coe hcount.symm combined
        originalIndex t
      simpa only [reassembledFirstPolygon, originalIndex, Fin.cast_cast,
        Fin.cast_eq_self] using hcast
    _ = _ := (reassembledFirstPolygon word rest combined).edgePoint_coe_eq_lineMap index t

/-- Helper for Proposition 76.2: the distinguished component of the reassembled
family has its canonical cyclic-polygon presentation. -/
private noncomputable def reassembledFirstCyclicRegion {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) :
    CyclicRegion (reassembledRegions word rest combined retainedPolygon)
      (mergedFirstOccurrence word rest) :=
  ⟨reassembledFirstPolygon word rest combined,
    reassembledFirstRegionHomeomorph word rest combined retainedPolygon,
    reassembledFirstEdgeCompatibility word rest combined retainedPolygon⟩

/-- Helper for Proposition 76.2: a retained polygon transported to the exact
vertex count of its merged occurrence. -/
private noncomputable def reassembledRestPolygon {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest) :
    CyclicPolygon (mergedRestOccurrence word rest region).1.1.length :=
  CyclicPolygon.castVertexCount
    (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
      (mergedRestOccurrence_fst word rest region)).symm (retainedPolygon region)

/-- Helper for Proposition 76.2: a retained merged component is homeomorphic to
its transported retained polygon. -/
private noncomputable def reassembledRestRegionHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest) :
    RegionHomeomorph (reassembledRegions word rest combined retainedPolygon)
      (mergedRestOccurrence word rest region)
      (reassembledRestPolygon word rest retainedPolygon region).region :=
  @Homeomorph.trans _ _ _
    (reassembledTopology word rest combined retainedPolygon
      (mergedRestOccurrence word rest region)) inferInstance inferInstance
    (reassembledRestHomeomorph word rest combined retainedPolygon region)
    (@Homeomorph.trans _ _ _ inferInstance inferInstance inferInstance
      Homeomorph.ulift
      (Homeomorph.setCongr
        (CyclicPolygon.castVertexCount_region
          (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
            (mergedRestOccurrence_fst word rest region)).symm
          (retainedPolygon region))).symm)

/-- Helper for Proposition 76.2: forgetting transported polygon membership in a
retained comparison leaves the normalized retained-region point. -/
private theorem reassembledRestRegionHomeomorph_coe {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest)
    (x : reassembledPoint word rest combined retainedPolygon
      (mergedRestOccurrence word rest region)) :
    ((reassembledRestRegionHomeomorph word rest combined retainedPolygon region x :
        (reassembledRestPolygon word rest retainedPolygon region).region) :
      EuclideanSpace ℝ (Fin 2)) =
      ((reassembledRestHomeomorph word rest combined retainedPolygon region x).down :
        EuclideanSpace ℝ (Fin 2)) := by
  rfl

/-- Helper for Proposition 76.2: each retained reassembled homeomorphism
preserves every canonical affine edge parameter. -/
private theorem reassembledRestEdgeCompatibility {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest)
    (index : Fin (mergedRestOccurrence word rest region).1.1.length)
    (t : unitInterval) :
    ((reassembledRestRegionHomeomorph word rest combined retainedPolygon region
        ((reassembledRegions word rest combined retainedPolygon).edge
          (mergedRestOccurrence word rest region) index t) :
          (reassembledRestPolygon word rest retainedPolygon region).region) :
        EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap
        ((reassembledRestPolygon word rest retainedPolygon region).toPolygon.vertices index)
        ((reassembledRestPolygon word rest retainedPolygon region).toPolygon.vertices
          (finRotate (mergedRestOccurrence word rest region).1.1.length index)) (t : ℝ) := by
  let hcount := congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
    (mergedRestOccurrence_fst word rest region)
  let originalIndex : Fin region.1.1.length := Fin.cast hcount index
  have hedge := reassembledRestHomeomorph_edge word rest combined retainedPolygon
    region index t
  have hedgeValue := congrArg (fun point ↦ (point.down : EuclideanSpace ℝ (Fin 2))) hedge
  calc
    ((reassembledRestRegionHomeomorph word rest combined retainedPolygon region
        ((reassembledRegions word rest combined retainedPolygon).edge
          (mergedRestOccurrence word rest region) index t) :
          (reassembledRestPolygon word rest retainedPolygon region).region) :
        EuclideanSpace ℝ (Fin 2)) =
        ((retainedPolygon region).edgePoint originalIndex t :
          EuclideanSpace ℝ (Fin 2)) := by
      rw [reassembledRestRegionHomeomorph_coe]
      simpa only [CyclicPolygon.boundaryToRegion_coe, originalIndex, hcount]
        using hedgeValue
    _ = ((reassembledRestPolygon word rest retainedPolygon region).edgePoint index t :
        EuclideanSpace ℝ (Fin 2)) := by
      symm
      have hcast := CyclicPolygon.castVertexCount_edgePoint_coe hcount.symm
        (retainedPolygon region) originalIndex t
      simpa only [reassembledRestPolygon, originalIndex, Fin.cast_cast,
        Fin.cast_eq_self] using hcast
    _ = _ :=
      (reassembledRestPolygon word rest retainedPolygon region).edgePoint_coe_eq_lineMap index t

/-- Helper for Proposition 76.2: every retained component of the reassembled
family has its canonical cyclic-polygon presentation. -/
private noncomputable def reassembledRestCyclicRegion {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest) :
    CyclicRegion (reassembledRegions word rest combined retainedPolygon)
      (mergedRestOccurrence word rest region) :=
  ⟨reassembledRestPolygon word rest retainedPolygon region,
    reassembledRestRegionHomeomorph word rest combined retainedPolygon region,
    reassembledRestEdgeCompatibility word rest combined retainedPolygon region⟩

/-- Helper for Proposition 76.2: the original retained component is
homeomorphic to its corresponding reassembled component. -/
private noncomputable def reassembledRetainedComparison {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion regions (splitRestOccurrence word₁ word₂ rest region))
    (word : PolygonWord α) (combined : CyclicPolygon word.1.length)
    (region : Occurrence rest) :
    RegionHomeomorph.Between regions (splitRestOccurrence word₁ word₂ rest region)
      (reassembledRegions word rest combined (fun retained ↦ (retainedRegion retained).polygon))
      (mergedRestOccurrence word rest region) :=
  @Homeomorph.trans _ _ _
    (regions.topology (splitRestOccurrence word₁ word₂ rest region)) inferInstance
    ((reassembledRegions word rest combined
      (fun retained ↦ (retainedRegion retained).polygon)).topology
      (mergedRestOccurrence word rest region))
    (retainedRegion region).homeomorph
    (@Homeomorph.trans _ _ _ inferInstance inferInstance
      ((reassembledRegions word rest combined
        (fun retained ↦ (retainedRegion retained).polygon)).topology
        (mergedRestOccurrence word rest region))
      Homeomorph.ulift.symm
      (@Homeomorph.symm _ _
        (reassembledTopology word rest combined
          (fun retained ↦ (retainedRegion retained).polygon)
          (mergedRestOccurrence word rest region)) inferInstance
        (reassembledRestHomeomorph word rest combined
          (fun retained ↦ (retainedRegion retained).polygon) region)))

/-- Helper for Proposition 76.2: the canonical retained branch in the finite
source enumeration is the corresponding embedded retained occurrence. -/
private theorem splitOccurrenceEquiv_symm_retained {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (index : Fin (retainedOccurrenceCount rest)) :
    (splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index)) =
      splitRestOccurrence word₁ word₂ rest
        ((retainedOccurrenceEquiv rest).symm index) := by
  apply (splitOccurrenceEquiv word₁ word₂ rest).injective
  simp only [splitOccurrenceEquiv, splitRestOccurrence, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.optionCongr_apply, Option.map_some]

/-- Helper for Proposition 76.2: enumerating a retained occurrence and then
embedding that finite index recovers the original retained occurrence. -/
private theorem splitOccurrenceEquiv_symm_retained_apply {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (region : Occurrence rest) :
    (splitOccurrenceEquiv word₁ word₂ rest).symm
        (some (some (retainedOccurrenceEquiv rest region))) =
      splitRestOccurrence word₁ word₂ rest region := by
  apply (splitOccurrenceEquiv word₁ word₂ rest).injective
  rw [Equiv.apply_symm_apply, splitOccurrenceEquiv_retained]

/-- Helper for Proposition 76.2: transport between equal component indices as a
homeomorphism for the stored component topologies. -/
private noncomputable def regionCastHomeomorph {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    {left right : Occurrence scheme} (h : left = right) :
    @Homeomorph (regions.Point left) (regions.Point right)
      (regions.topology left) (regions.topology right) :=
  match h with
  | rfl => @Homeomorph.refl _ (regions.topology left)

/-- Helper for Proposition 76.2: a finitely enumerated retained source fibre is
homeomorphic to the lifted polygon presenting its retained occurrence. -/
private noncomputable def retainedFiberHomeomorph {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion regions (splitRestOccurrence word₁ word₂ rest region))
    (index : Fin (retainedOccurrenceCount rest)) :
    @Homeomorph
      (regions.Point
        ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))))
      (ULift.{v, 0}
        (retainedRegion ((retainedOccurrenceEquiv rest).symm index)).polygon.region)
      (regions.topology
        ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))))
      inferInstance :=
  @Homeomorph.trans _ _ _
    (regions.topology
      ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))))
    (regions.topology (splitRestOccurrence word₁ word₂ rest
      ((retainedOccurrenceEquiv rest).symm index))) inferInstance
    (regionCastHomeomorph regions
      (splitOccurrenceEquiv_symm_retained word₁ word₂ rest index))
    (@Homeomorph.trans _ _ _
      (regions.topology (splitRestOccurrence word₁ word₂ rest
        ((retainedOccurrenceEquiv rest).symm index))) inferInstance inferInstance
      (retainedRegion ((retainedOccurrenceEquiv rest).symm index)).homeomorph
      Homeomorph.ulift.symm)

/-- Helper for Proposition 76.2: a retained finite-fibre normalization applies
the component-index transport followed by its cyclic-region homeomorphism. -/
private theorem retainedFiberHomeomorph_apply {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion regions (splitRestOccurrence word₁ word₂ rest region))
    (index : Fin (retainedOccurrenceCount rest))
    (x : regions.Point
      ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index)))) :
    retainedFiberHomeomorph word₁ word₂ rest regions retainedRegion index x =
      ULift.up.{v, 0}
        ((retainedRegion ((retainedOccurrenceEquiv rest).symm index)).homeomorph
          (regionCastEquiv regions
            (splitOccurrenceEquiv_symm_retained word₁ word₂ rest index) x)) := by
  rfl

/-- Helper for Proposition 76.2: the retained summand of the selected-edge
decomposition is homeomorphic to the sigma of lifted retained polygons. -/
private noncomputable def retainedSourceHomeomorph {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion regions (splitRestOccurrence word₁ word₂ rest region)) :
    selectedEdgeRetainedSource word₁ word₂ rest regions ≃ₜ
      ((region : Occurrence rest) × ULift.{v, 0} (retainedRegion region).polygon.region) :=
  @IsHomeomorph.homeomorph _ _
    (selectedEdgeRetainedSource word₁ word₂ rest regions).str
    (⨆ region, TopologicalSpace.coinduced (Sigma.mk region) inferInstance)
    (Sigma.map (retainedOccurrenceEquiv rest).symm
      (fun index ↦ retainedFiberHomeomorph word₁ word₂ rest regions retainedRegion index))
    (@IsHomeomorph.sigmaMap
    (Fin (retainedOccurrenceCount rest)) (Occurrence rest)
    (fun index ↦ regions.Point
      ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))))
    (fun region ↦ ULift.{v, 0} (retainedRegion region).polygon.region)
    (fun index ↦ regions.topology
      ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))))
    (fun _ ↦ inferInstance)
    (retainedOccurrenceEquiv rest).symm
    (retainedOccurrenceEquiv rest).symm.bijective
    (fun index ↦ retainedFiberHomeomorph word₁ word₂ rest regions retainedRegion index)
    (fun index ↦
      @Homeomorph.isHomeomorph _ _
        (regions.topology
          ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))))
        inferInstance
        (retainedFiberHomeomorph word₁ word₂ rest regions retainedRegion index)))

/-- Helper for Proposition 76.2: the retained-source normalization evaluates by
mapping the finite occurrence index and its corresponding fibre homeomorphism. -/
private theorem retainedSourceHomeomorph_apply {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion regions (splitRestOccurrence word₁ word₂ rest region))
    (point : selectedEdgeRetainedSource word₁ word₂ rest regions) :
    retainedSourceHomeomorph word₁ word₂ rest regions retainedRegion point =
      Sigma.map (retainedOccurrenceEquiv rest).symm
        (fun index ↦ retainedFiberHomeomorph word₁ word₂ rest regions
          retainedRegion index) point := by
  rfl

/-- Helper for Proposition 76.2: the inverse selected-edge source decomposition
places a retained finite fibre back in its canonical embedded occurrence. -/
private theorem selectedEdgeSourceHomeomorph_symm_retained {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (index : Fin (retainedOccurrenceCount rest))
    (x : regions.Point
      ((splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index)))) :
    (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
      rightRegion).symm (Sum.inr ⟨index, x⟩) =
      ⟨(splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index)), x⟩ := by
  apply Sigma.ext
  · rfl
  · exact HEq.rfl

/-- Helper for Proposition 76.2: the selected-edge source decomposition sends a
retained component point to its canonical finite retained fibre. -/
private theorem selectedEdgeSourceHomeomorph_retained {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (region : Occurrence rest)
    (x : regions.Point (splitRestOccurrence word₁ word₂ rest region)) :
    selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion
        ⟨splitRestOccurrence word₁ word₂ rest region, x⟩ =
      Sum.inr ⟨retainedOccurrenceEquiv rest region,
        (regionCastEquiv regions
          (splitOccurrenceEquiv_symm_retained_apply word₁ word₂ rest region)).symm x⟩ := by
  apply (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion
    rightRegion).symm.injective
  rw [Homeomorph.symm_apply_apply, selectedEdgeSourceHomeomorph_symm_retained]
  exact sigmaMk_regionCastEquiv_symm regions
    (splitOccurrenceEquiv_symm_retained_apply word₁ word₂ rest region) x

/-- Helper for Proposition 76.2: after normalizing the retained source summand,
a retained component point is indexed by its original occurrence and presented
by its lifted cyclic-region homeomorphism. -/
private theorem retainedSourceHomeomorph_selectedEdgeSource {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α)
    (regions : PolygonalRegions.{u, v} (word₁ ::ₘ word₂ ::ₘ rest))
    (leftRegion : CyclicRegion regions (firstOccurrence word₁ word₂ rest))
    (rightRegion : CyclicRegion regions (secondOccurrence word₁ word₂ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion regions (splitRestOccurrence word₁ word₂ rest region))
    (region : Occurrence rest)
    (x : regions.Point (splitRestOccurrence word₁ word₂ rest region)) :
    (Homeomorph.sumCongr (Homeomorph.refl _)
      (retainedSourceHomeomorph word₁ word₂ rest regions retainedRegion))
      (selectedEdgeSourceHomeomorph word₁ word₂ rest regions leftRegion rightRegion
          ⟨splitRestOccurrence word₁ word₂ rest region, x⟩) =
      Sum.inr ⟨region, ULift.up.{v, 0} ((retainedRegion region).homeomorph x)⟩ := by
  rw [selectedEdgeSourceHomeomorph_retained]
  change Sum.inr
      (retainedSourceHomeomorph word₁ word₂ rest regions retainedRegion
        ⟨retainedOccurrenceEquiv rest region,
          (regionCastEquiv regions
            (splitOccurrenceEquiv_symm_retained_apply word₁ word₂ rest region)).symm x⟩) = _
  apply congrArg Sum.inr
  rw [retainedSourceHomeomorph_apply]
  let index := retainedOccurrenceEquiv rest region
  let canonicalOccurrence :=
    (splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index))
  let hcanonical : canonicalOccurrence =
      splitRestOccurrence word₁ word₂ rest region :=
    splitOccurrenceEquiv_symm_retained_apply word₁ word₂ rest region
  let canonicalPoint : regions.Point canonicalOccurrence :=
    (regionCastEquiv regions hcanonical).symm x
  let retained := (retainedOccurrenceEquiv rest).symm index
  let hretainedOccurrence :
      (splitOccurrenceEquiv word₁ word₂ rest).symm (some (some index)) =
        splitRestOccurrence word₁ word₂ rest retained :=
    splitOccurrenceEquiv_symm_retained word₁ word₂ rest index
  let retainedPoint : regions.Point
      (splitRestOccurrence word₁ word₂ rest retained) :=
    regionCastEquiv regions hretainedOccurrence canonicalPoint
  have hleftSource :
      (⟨splitRestOccurrence word₁ word₂ rest retained, retainedPoint⟩ :
        regions.Source) =
      ⟨canonicalOccurrence, canonicalPoint⟩ := by
    calc
      (⟨splitRestOccurrence word₁ word₂ rest retained, retainedPoint⟩ :
          regions.Source) =
          ⟨canonicalOccurrence,
            (regionCastEquiv regions hretainedOccurrence).symm retainedPoint⟩ :=
        sigmaMk_regionCastEquiv_symm regions hretainedOccurrence retainedPoint
      _ = ⟨canonicalOccurrence, canonicalPoint⟩ := by
        exact congrArg (Sigma.mk canonicalOccurrence)
          ((regionCastEquiv regions hretainedOccurrence).symm_apply_apply
            canonicalPoint)
  have hrightSource :
      (⟨splitRestOccurrence word₁ word₂ rest region, x⟩ :
        regions.Source) =
      ⟨canonicalOccurrence, canonicalPoint⟩ := by
    exact sigmaMk_regionCastEquiv_symm regions hcanonical x
  have hretainedSource :
      (⟨retained, retainedPoint⟩ :
        (retained : Occurrence rest) ×
          regions.Point (splitRestOccurrence word₁ word₂ rest retained)) =
      ⟨region, x⟩ := by
    apply Sigma.ext
    · exact (retainedOccurrenceEquiv rest).symm_apply_apply region
    · exact (Sigma.ext_iff.mp (hleftSource.trans hrightSource.symm)).2
  let normalizeRetained :
      ((retained : Occurrence rest) ×
        regions.Point (splitRestOccurrence word₁ word₂ rest retained)) →
      ((retained : Occurrence rest) ×
        ULift.{v, 0} (retainedRegion retained).polygon.region) :=
    fun point ↦ ⟨point.1, ULift.up.{v, 0} ((retainedRegion point.1).homeomorph point.2)⟩
  calc
    Sigma.map (retainedOccurrenceEquiv rest).symm
        (fun finiteIndex ↦ retainedFiberHomeomorph word₁ word₂ rest regions
          retainedRegion finiteIndex) ⟨index, canonicalPoint⟩ =
        normalizeRetained ⟨retained, retainedPoint⟩ := by
      exact congrArg (Sigma.mk retained)
        (retainedFiberHomeomorph_apply word₁ word₂ rest regions retainedRegion
          index canonicalPoint)
    _ = normalizeRetained ⟨region, x⟩ := by
      exact congrArg normalizeRetained hretainedSource
    _ = ⟨region, ULift.up.{v, 0} ((retainedRegion region).homeomorph x)⟩ := rfl

/-- Helper for Proposition 76.2: normalize the sigma of retained reassembled
components to the sigma of their lifted polygon regions. -/
private noncomputable def reassembledRetainedSourceHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) :
    @Homeomorph ((region : Occurrence rest) ×
        (reassembledRegions word rest combined retainedPolygon).Point
          ((consOccurrenceEquiv word rest).symm (some region)))
      ((region : Occurrence rest) × ULift.{v, 0} (retainedPolygon region).region)
      (⨆ region, TopologicalSpace.coinduced (Sigma.mk region)
        ((reassembledRegions word rest combined retainedPolygon).topology
          ((consOccurrenceEquiv word rest).symm (some region))))
      (⨆ region, TopologicalSpace.coinduced (Sigma.mk region) inferInstance) :=
  @IsHomeomorph.homeomorph _ _
    (⨆ region, TopologicalSpace.coinduced (Sigma.mk region)
      ((reassembledRegions word rest combined retainedPolygon).topology
        ((consOccurrenceEquiv word rest).symm (some region))))
    (⨆ region, TopologicalSpace.coinduced (Sigma.mk region) inferInstance)
    (Sigma.map (Equiv.refl _) (fun region ↦
      ⇑(reassembledRestHomeomorph word rest combined retainedPolygon region)))
    (@IsHomeomorph.sigmaMap
      (Occurrence rest) (Occurrence rest)
      (fun region ↦ (reassembledRegions word rest combined retainedPolygon).Point
        ((consOccurrenceEquiv word rest).symm (some region)))
      (fun region ↦ ULift.{v, 0} (retainedPolygon region).region)
      (fun region ↦ (reassembledRegions word rest combined retainedPolygon).topology
        ((consOccurrenceEquiv word rest).symm (some region)))
      (fun _ ↦ inferInstance) (Equiv.refl _) (Equiv.refl _).bijective
      (fun region ↦
        reassembledRestHomeomorph word rest combined retainedPolygon region)
      (fun region ↦ @Homeomorph.isHomeomorph _ _
        ((reassembledRegions word rest combined retainedPolygon).topology
          ((consOccurrenceEquiv word rest).symm (some region))) inferInstance
        (reassembledRestHomeomorph word rest combined retainedPolygon region)))

/-- Helper for Proposition 76.2: split the reassembled source into its lifted
combined component and the sigma of lifted retained polygon regions. -/
private noncomputable def reassembledSourceSplittingHomeomorph {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) :
    (reassembledRegions word rest combined retainedPolygon).Source ≃ₜ
      (ULift.{v, 0} combined.region ⊕
        ((region : Occurrence rest) × ULift.{v, 0} (retainedPolygon region).region)) :=
  -- Local instance justification (dependent component topology): the reassembled
  -- family stores these topologies as data, so no global instance can infer them.
  letI _componentTopology : ∀ i : Option (Occurrence rest),
      TopologicalSpace
        ((reassembledRegions word rest combined retainedPolygon).Point
          ((consOccurrenceEquiv word rest).symm i)) :=
    fun i ↦ (reassembledRegions word rest combined retainedPolygon).topology
      ((consOccurrenceEquiv word rest).symm i)
  (canonicalSourceReindexingHomeomorph
      (reassembledRegions word rest combined retainedPolygon)
      (consOccurrenceEquiv word rest)).trans
    (sigmaOptionHomeomorph
      (fun i : Option (Occurrence rest) ↦
        (reassembledRegions word rest combined retainedPolygon).Point
          ((consOccurrenceEquiv word rest).symm i))) |>.trans
    (Homeomorph.sumCongr
      (reassembledFirstHomeomorph word rest combined retainedPolygon)
      (reassembledRetainedSourceHomeomorph word rest combined retainedPolygon))

/-- Helper for Proposition 76.2: the inverse reassembled source splitting sends
the normalized combined summand back to the distinguished component. -/
private theorem reassembledSourceSplittingHomeomorph_symm_first {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (x : ULift.{v, 0} combined.region) :
    (reassembledSourceSplittingHomeomorph word rest combined retainedPolygon).symm
        (Sum.inl x) =
      ⟨mergedFirstOccurrence word rest,
        (@Homeomorph.toEquiv _ _
          (reassembledTopology word rest combined retainedPolygon
            (mergedFirstOccurrence word rest)) inferInstance
          (reassembledFirstHomeomorph word rest combined retainedPolygon)).symm x⟩ := by
  apply Sigma.ext
  · rfl
  · exact HEq.rfl

/-- Helper for Proposition 76.2: the source splitting sends a distinguished
component point to the left summand through its normalization. -/
private theorem reassembledSourceSplittingHomeomorph_first {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length)
    (x : (reassembledRegions word rest combined retainedPolygon).Point
      (mergedFirstOccurrence word rest)) :
    reassembledSourceSplittingHomeomorph word rest combined retainedPolygon
        ⟨mergedFirstOccurrence word rest, x⟩ =
      Sum.inl (reassembledFirstHomeomorph word rest combined retainedPolygon x) := by
  apply (reassembledSourceSplittingHomeomorph word rest combined
    retainedPolygon).symm.injective
  rw [Homeomorph.symm_apply_apply,
    reassembledSourceSplittingHomeomorph_symm_first]
  exact congrArg (Sigma.mk (mergedFirstOccurrence word rest))
    ((@Homeomorph.toEquiv _ _
      (reassembledTopology word rest combined retainedPolygon
        (mergedFirstOccurrence word rest)) inferInstance
      (reassembledFirstHomeomorph word rest combined retainedPolygon)).symm_apply_apply x).symm

/-- Helper for Proposition 76.2: the source splitting sends a retained component
point to its indexed right-summand fibre through its normalization. -/
private theorem reassembledSourceSplittingHomeomorph_rest {α : Type u}
    (word : PolygonWord α) (rest : LabellingScheme α)
    (combined : CyclicPolygon word.1.length)
    (retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length) (region : Occurrence rest)
    (x : (reassembledRegions word rest combined retainedPolygon).Point
      (mergedRestOccurrence word rest region)) :
    reassembledSourceSplittingHomeomorph word rest combined retainedPolygon
        ⟨mergedRestOccurrence word rest region, x⟩ =
      Sum.inr ⟨region,
        reassembledRestHomeomorph word rest combined retainedPolygon region x⟩ := by
  -- Local instance justification (dependent component topology): this is the
  -- stored topology used by the source splitting on each occurrence branch.
  letI _componentTopology : ∀ i : Option (Occurrence rest),
      TopologicalSpace
        ((reassembledRegions word rest combined retainedPolygon).Point
          ((consOccurrenceEquiv word rest).symm i)) :=
    fun i ↦ (reassembledRegions word rest combined retainedPolygon).topology
      ((consOccurrenceEquiv word rest).symm i)
  let base :=
    (canonicalSourceReindexingHomeomorph
      (reassembledRegions word rest combined retainedPolygon)
      (consOccurrenceEquiv word rest)).trans
        (sigmaOptionHomeomorph
          (fun i : Option (Occurrence rest) ↦
            (reassembledRegions word rest combined retainedPolygon).Point
              ((consOccurrenceEquiv word rest).symm i)))
  have hbase : base ⟨mergedRestOccurrence word rest region, x⟩ =
      Sum.inr ⟨region, x⟩ := by
    apply base.symm.injective
    rw [Homeomorph.symm_apply_apply]
    apply Sigma.ext
    · rfl
    · exact HEq.rfl
  -- Local instance justification (dependent spelling bridge): the named first
  -- occurrence is definitionally the `none` fibre, but instance search does not unfold it here.
  letI _firstTopology : TopologicalSpace
      (reassembledPoint word rest combined retainedPolygon
        (mergedFirstOccurrence word rest)) :=
    reassembledTopology word rest combined retainedPolygon
      (mergedFirstOccurrence word rest)
  change (Homeomorph.sumCongr
      (reassembledFirstHomeomorph word rest combined retainedPolygon)
      (reassembledRetainedSourceHomeomorph word rest combined retainedPolygon))
      (base ⟨mergedRestOccurrence word rest region, x⟩) = _
  rw [hbase]
  rfl

/-- Helper for Proposition 76.2: the two occurrences introduced at the front of
a labelling scheme are distinct. -/
private theorem firstOccurrence_ne_secondOccurrence {α : Type u}
    (word₁ word₂ : PolygonWord α) (rest : LabellingScheme α) :
    firstOccurrence word₁ word₂ rest ≠ secondOccurrence word₁ word₂ rest := by
  intro hequal
  have hbranches := congrArg (consOccurrenceEquiv word₁ (word₂ ::ₘ rest)) hequal
  simp only [firstOccurrence, secondOccurrence, Equiv.apply_symm_apply] at hbranches
  cases hbranches

/-- Helper for Proposition 76.2: two-way label- and parameter-preserving
boundary correspondences transport the remaining direct relation. -/
private theorem remainingRelated_iff_edgeRelated_of_boundaryCorrespondence {α : Type u}
    {splitScheme mergedScheme : LabellingScheme α}
    (splitRegions : PolygonalRegions.{u, v} splitScheme) (c : α)
    {Y : Type v} [TopologicalSpace Y] (firstPaste : splitRegions.Source → Y)
    (mergedRegions : PolygonalRegions.{u, v} mergedScheme)
    (sourceHomeomorph : Y ≃ₜ mergedRegions.Source)
    (forwardBoundary : ∀ (region : Occurrence splitScheme)
      (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 ≠ c →
        ∃ (mergedRegion : Occurrence mergedScheme)
          (mergedEdge : Fin mergedRegion.1.1.length),
          region.1.1.get edge = mergedRegion.1.1.get mergedEdge ∧
            ∀ t, sourceHomeomorph
                (firstPaste ⟨region, splitRegions.edge region edge t⟩) =
              ⟨mergedRegion, mergedRegions.edge mergedRegion mergedEdge t⟩)
    (backwardBoundary : ∀ (mergedRegion : Occurrence mergedScheme)
      (mergedEdge : Fin mergedRegion.1.1.length),
        ∃ (region : Occurrence splitScheme) (edge : Fin region.1.1.length),
          (region.1.1.get edge).1 ≠ c ∧
            region.1.1.get edge = mergedRegion.1.1.get mergedEdge ∧
            ∀ t, sourceHomeomorph
                (firstPaste ⟨region, splitRegions.edge region edge t⟩) =
              ⟨mergedRegion, mergedRegions.edge mergedRegion mergedEdge t⟩)
    (x y : Y) :
    splitRegions.RemainingRelated c firstPaste x y ↔
      mergedRegions.EdgeRelated (sourceHomeomorph x) (sourceHomeomorph y) := by
  constructor
  · rw [splitRegions.remainingRelated_iff]
    rintro ⟨x', y', hx', hy', hrelated⟩
    rw [splitRegions.edgeRelatedAwayFrom_iff] at hrelated
    rcases hrelated with ⟨region₁, region₂, edge₁, edge₂, t,
      hlabels, hc, rfl, rfl⟩
    have hc₂ : (region₂.1.1.get edge₂).1 ≠ c :=
      fun heq ↦ hc (hlabels.trans heq)
    obtain ⟨mergedRegion₁, mergedEdge₁, hletter₁, hedge₁⟩ :=
      forwardBoundary region₁ edge₁ hc
    obtain ⟨mergedRegion₂, mergedEdge₂, hletter₂, hedge₂⟩ :=
      forwardBoundary region₂ edge₂ hc₂
    rw [mergedRegions.edgeRelated_iff]
    refine ⟨mergedRegion₁, mergedRegion₂, mergedEdge₁, mergedEdge₂,
      t, ?_, ?_, ?_⟩
    · exact (congrArg Prod.fst hletter₁).symm.trans
        (hlabels.trans (congrArg Prod.fst hletter₂))
    · rw [← hx']
      exact hedge₁ t
    · rw [← hy']
      have hsigns :
          (mergedRegion₁.1.1.get mergedEdge₁).2 =
              (mergedRegion₂.1.1.get mergedEdge₂).2 ↔
            (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 := by
        rw [← hletter₁, ← hletter₂]
      rw [if_congr hsigns rfl rfl]
      exact hedge₂
        (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
          else unitInterval.symm t)
  · rw [mergedRegions.edgeRelated_iff]
    rintro ⟨mergedRegion₁, mergedRegion₂, mergedEdge₁, mergedEdge₂,
      t, hlabels, hx, hy⟩
    obtain ⟨region₁, edge₁, hc₁, hletter₁, hedge₁⟩ :=
      backwardBoundary mergedRegion₁ mergedEdge₁
    obtain ⟨region₂, edge₂, hc₂, hletter₂, hedge₂⟩ :=
      backwardBoundary mergedRegion₂ mergedEdge₂
    let x' : splitRegions.Source :=
      ⟨region₁, splitRegions.edge region₁ edge₁ t⟩
    let oldParameter :=
      if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
      else unitInterval.symm t
    let y' : splitRegions.Source :=
      ⟨region₂, splitRegions.edge region₂ edge₂ oldParameter⟩
    have hsigns :
        (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 ↔
          (mergedRegion₁.1.1.get mergedEdge₁).2 =
            (mergedRegion₂.1.1.get mergedEdge₂).2 := by
      rw [hletter₁, hletter₂]
    have hx' : firstPaste x' = x := by
      apply sourceHomeomorph.injective
      rw [hedge₁ t]
      exact hx.symm
    have hy' : firstPaste y' = y := by
      apply sourceHomeomorph.injective
      rw [hedge₂ oldParameter]
      simp only [oldParameter]
      rw [if_congr hsigns rfl rfl]
      exact hy.symm
    rw [splitRegions.remainingRelated_iff]
    refine ⟨x', y', hx', hy', ?_⟩
    rw [splitRegions.edgeRelatedAwayFrom_iff]
    refine ⟨region₁, region₂, edge₁, edge₂, t, ?_, hc₁, rfl, ?_⟩
    · exact (congrArg Prod.fst hletter₁).trans
        (hlabels.trans (congrArg Prod.fst hletter₂).symm)
    · rfl

/-- Helper for Proposition 76.2: the stored remaining-identification setoid is
the equivalence closure of the remaining direct edge relation. -/
private theorem remainingIdentified_iff_eqvGen {α : Type u}
    {scheme : LabellingScheme α} (regions : PolygonalRegions.{u, v} scheme)
    (c : α) {Y : Type v} (firstPaste : regions.Source → Y) (x y : Y) :
    (regions.RemainingIdentified c firstPaste).r x y ↔
      Relation.EqvGen (regions.RemainingRelated c firstPaste) x y := by
  rfl

/-- Helper for Proposition 76.2: the stored full-identification setoid is the
equivalence closure of the direct labelled-edge relation. -/
private theorem identified_iff_eqvGen {α : Type u} {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme) (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  rfl

/-- Concrete reassembly of the two distinguished cyclic regions produces explicit
edge-paste data and homeomorphically retains every region in the remainder. -/
theorem existsOfEdgeGluing {α : Type u} [DecidableEq α]
    (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool) (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c)
    (splitRegions : PolygonalRegions.{u, v}
      (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest))
    (leftRegion : CyclicRegion splitRegions
      (firstOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest))
    (rightRegion : CyclicRegion splitRegions
      (secondOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest))
    (retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion splitRegions
        (splitRestOccurrence
          ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
          ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest region))
    (gluing : CyclicPolygon.EdgeGluing leftRegion.polygon rightRegion.polygon)
    (h_leftEdge :
      (firstOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
        rest).1.1.get gluing.leftEdge.index = (c, !b))
    (h_rightEdge :
      (secondOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
        rest).1.1.get gluing.rightEdge.index = (c, b))
    (h_oppositeOrientation :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward) :
    ∃ result : PasteResult splitRegions c
        (mergedFirstOccurrence
          ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ rest)
        (fun region ↦ splitRestOccurrence
          ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
          ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest region)
        (fun region ↦ mergedRestOccurrence
          ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ rest region),
      AgreesWithEdgeGluing result leftRegion rightRegion gluing := by
  classical
  let leftWord : PolygonWord α :=
    ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
  let rightWord : PolygonWord α :=
    ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩
  have hleftIndex : gluing.leftEdge.index.val =
      (firstOccurrence leftWord rightWord rest).1.1.length - 1 := by
    have hclassification := cEdgeOccurrence_eq_firstOrSecond y₀ y₁ c b rest
      hy₀Length hy₁Length hy₀ hy₁ hrest _ gluing.leftEdge.index
      (congrArg Prod.fst h_leftEdge)
    rcases hclassification with hleft | hright
    · have hlength :
          (firstOccurrence leftWord rightWord rest).1.1.length - 1 = y₀.length := by
        rw [firstOccurrence_fst]
        simp only [leftWord, List.length_append, List.length_singleton]
        omega
      exact hleft.2.trans hlength.symm
    · have hwrong : firstOccurrence leftWord rightWord rest =
          secondOccurrence leftWord rightWord rest := by
        simpa only [leftWord, rightWord] using hright.1
      exact False.elim (firstOccurrence_ne_secondOccurrence leftWord rightWord rest hwrong)
  have hrightIndex : gluing.rightEdge.index.val = 0 := by
    have hclassification := cEdgeOccurrence_eq_firstOrSecond y₀ y₁ c b rest
      hy₀Length hy₁Length hy₀ hy₁ hrest _ gluing.rightEdge.index
      (congrArg Prod.fst h_rightEdge)
    rcases hclassification with hleft | hright
    · have hwrong : firstOccurrence leftWord rightWord rest =
          secondOccurrence leftWord rightWord rest := by
        simpa only [leftWord, rightWord] using hleft.1.symm
      exact False.elim (firstOccurrence_ne_secondOccurrence leftWord rightWord rest hwrong)
    · exact hright.2
  obtain ⟨replacement, combined, leftHomeomorph, realizationHomeomorph,
      hvertices, hparameters, hattaching, hunion, hrealLeft, hrealRight,
      hleftBoundary, hrightBoundary⟩ :=
    gluing.existsLastFirstReassembly hleftIndex hrightIndex h_oppositeOrientation
  let mergedWord : PolygonWord α :=
    ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩
  have hcombinedCount :
      (firstOccurrence leftWord rightWord rest).1.1.length +
          (secondOccurrence leftWord rightWord rest).1.1.length - 2 =
        mergedWord.1.length := by
    have hleftLength : (firstOccurrence leftWord rightWord rest).1.1.length =
        y₀.length + 1 := by
      rw [firstOccurrence_fst]
      simp only [leftWord, List.length_append, List.length_singleton]
    have hrightLength : (secondOccurrence leftWord rightWord rest).1.1.length =
        y₁.length + 1 := by
      rw [secondOccurrence_fst]
      simp only [rightWord, List.length_cons]
    rw [hleftLength, hrightLength]
    simp only [mergedWord, List.length_append]
    omega
  let mergedPolygon := CyclicPolygon.castVertexCount hcombinedCount combined
  let retainedPolygon : ∀ region : Occurrence rest,
      CyclicPolygon region.1.1.length :=
    fun region ↦ (retainedRegion region).polygon
  let mergedRegions : PolygonalRegions.{u, v} (mergedWord ::ₘ rest) :=
    reassembledRegions mergedWord rest mergedPolygon retainedPolygon
  let firstPaste :=
    selectedEdgeFirstPaste leftWord rightWord rest splitRegions leftRegion rightRegion gluing
  have hleftLabel :
      ((firstOccurrence leftWord rightWord rest).1.1.get gluing.leftEdge.index).1 = c := by
    simpa only [leftWord, rightWord] using congrArg Prod.fst h_leftEdge
  have hrightLabel :
      ((secondOccurrence leftWord rightWord rest).1.1.get gluing.rightEdge.index).1 = c := by
    simpa only [leftWord, rightWord] using congrArg Prod.fst h_rightEdge
  have hleftFull : (firstOccurrence leftWord rightWord rest).1.1.get
      gluing.leftEdge.index = (c, !b) := by
    simpa only [leftWord, rightWord] using h_leftEdge
  have hrightFull : (secondOccurrence leftWord rightWord rest).1.1.get
      gluing.rightEdge.index = (c, b) := by
    simpa only [leftWord, rightWord] using h_rightEdge
  have hoppositeSigns :
      ((firstOccurrence leftWord rightWord rest).1.1.get gluing.leftEdge.index).2 ≠
        ((secondOccurrence leftWord rightWord rest).1.1.get gluing.rightEdge.index).2 := by
    rw [hleftFull, hrightFull]
    exact Bool.not_ne_self b
  have hleftIndexValue : gluing.leftEdge.index.val = y₀.length := by
    have hlength :
        (firstOccurrence leftWord rightWord rest).1.1.length - 1 = y₀.length := by
      rw [firstOccurrence_fst]
      simp only [leftWord, List.length_append, List.length_singleton]
      omega
    exact hleftIndex.trans hlength
  have hclassify : ∀ (region : Occurrence (leftWord ::ₘ rightWord ::ₘ rest))
      (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 = c →
        (region = firstOccurrence leftWord rightWord rest ∧
          edge.val = gluing.leftEdge.index.val) ∨
        (region = secondOccurrence leftWord rightWord rest ∧
          edge.val = gluing.rightEdge.index.val) := by
    intro region edge hlabel
    have hlabelExplicit : (region.1.1.get edge).1 = c := by
      simpa only [leftWord, rightWord] using hlabel
    rcases cEdgeOccurrence_eq_firstOrSecond y₀ y₁ c b rest hy₀Length hy₁Length
      hy₀ hy₁ hrest region edge hlabelExplicit with
      hleft | hright
    · have hregion : region = firstOccurrence leftWord rightWord rest := by
        simpa only [leftWord, rightWord] using hleft.1
      exact Or.inl ⟨hregion, hleft.2.trans hleftIndexValue.symm⟩
    · have hregion : region = secondOccurrence leftWord rightWord rest := by
        simpa only [leftWord, rightWord] using hright.1
      exact Or.inr ⟨hregion, hright.2.trans hrightIndex.symm⟩
  have hleftQuotient : ∀ z : splitRegions.Point
      (firstOccurrence leftWord rightWord rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inl (leftRegion.homeomorph z)) =
        gluing.includeLeft (leftRegion.homeomorph z) := by
    intro z
    rw [gluing.includeLeft_eq_includeX]
    exact AdjunctionSpace.quotientMap_inl gluing.attachingSubset gluing.attachingMap _
  have hrightQuotient : ∀ z : splitRegions.Point
      (secondOccurrence leftWord rightWord rest),
      AdjunctionSpace.quotientMap gluing.attachingSubset gluing.attachingMap
          (Sum.inr (rightRegion.homeomorph z)) =
        gluing.includeRight (rightRegion.homeomorph z) := by
    intro z
    rw [gluing.includeRight_eq_includeY]
    exact AdjunctionSpace.quotientMap_inr gluing.attachingSubset gluing.attachingMap _
  have hpastesLabel : splitRegions.PastesLabel c firstPaste := by
    exact selectedEdgeFirstPaste_pastesLabel leftWord rightWord rest splitRegions c
      leftRegion rightRegion gluing hleftLabel hrightLabel hoppositeSigns
      h_oppositeOrientation hclassify hleftQuotient hrightQuotient
  let comparison : gluing.Realization ≃ₜ ULift.{v, 0} mergedPolygon.region :=
    realizationHomeomorph.trans
      ((Homeomorph.setCongr
        (CyclicPolygon.castVertexCount_region hcombinedCount combined)).symm.trans
          Homeomorph.ulift.symm)
  let normalizedPairHomeomorph :
      (gluing.Realization ⊕ selectedEdgeRetainedSource leftWord rightWord rest splitRegions) ≃ₜ
        (ULift.{v, 0} mergedPolygon.region ⊕
          ((region : Occurrence rest) ×
            ULift.{v, 0} (retainedPolygon region).region)) :=
    Homeomorph.sumCongr comparison
      (retainedSourceHomeomorph leftWord rightWord rest splitRegions retainedRegion)
  let sourceSplitting :=
    reassembledSourceSplittingHomeomorph mergedWord rest mergedPolygon retainedPolygon
  let sourceHomeomorph :
      (gluing.Realization ⊕ selectedEdgeRetainedSource leftWord rightWord rest splitRegions) ≃ₜ
        mergedRegions.Source :=
    normalizedPairHomeomorph.trans sourceSplitting.symm
  have hsourceFirstNormalized : ∀ x : splitRegions.Point
      (firstOccurrence leftWord rightWord rest),
      sourceSplitting (sourceHomeomorph
        (firstPaste ⟨firstOccurrence leftWord rightWord rest, x⟩)) =
        Sum.inl (comparison (gluing.includeLeft (leftRegion.homeomorph x))) := by
    intro x
    simp only [sourceHomeomorph, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply]
    change normalizedPairHomeomorph
      (firstPaste ⟨firstOccurrence leftWord rightWord rest, x⟩) = _
    simp only [firstPaste]
    rw [selectedEdgeFirstPaste_first, hleftQuotient]
    rfl
  have hsourceSecondNormalized : ∀ x : splitRegions.Point
      (secondOccurrence leftWord rightWord rest),
      sourceSplitting (sourceHomeomorph
        (firstPaste ⟨secondOccurrence leftWord rightWord rest, x⟩)) =
        Sum.inl (comparison (gluing.includeRight (rightRegion.homeomorph x))) := by
    intro x
    simp only [sourceHomeomorph, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply]
    change normalizedPairHomeomorph
      (firstPaste ⟨secondOccurrence leftWord rightWord rest, x⟩) = _
    simp only [firstPaste]
    rw [selectedEdgeFirstPaste_second, hrightQuotient]
    rfl
  have hsourceRestNormalized : ∀ (region : Occurrence rest)
      (x : splitRegions.Point (splitRestOccurrence leftWord rightWord rest region)),
      sourceSplitting (sourceHomeomorph
        (firstPaste ⟨splitRestOccurrence leftWord rightWord rest region, x⟩)) =
        Sum.inr ⟨region,
          ULift.up.{v, 0} ((retainedRegion region).homeomorph x)⟩ := by
    intro region x
    simp only [sourceHomeomorph, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply]
    change normalizedPairHomeomorph
      (firstPaste ⟨splitRestOccurrence leftWord rightWord rest region, x⟩) = _
    simp only [normalizedPairHomeomorph, firstPaste, selectedEdgeFirstPaste]
    rw [selectedEdgeSourceHomeomorph_retained]
    have hretained :=
      retainedSourceHomeomorph_selectedEdgeSource leftWord rightWord rest splitRegions
        leftRegion rightRegion retainedRegion region x
    rw [selectedEdgeSourceHomeomorph_retained] at hretained
    have hretainedInner := Sum.inr.inj hretained
    change Sum.inr
      (retainedSourceHomeomorph leftWord rightWord rest splitRegions retainedRegion
        ⟨retainedOccurrenceEquiv rest region,
          (regionCastEquiv splitRegions
            (splitOccurrenceEquiv_symm_retained_apply leftWord rightWord rest region)).symm x⟩) = _
    exact congrArg Sum.inr hretainedInner
  have hleftSourceCorrespondence : ∀
      (edge : Fin (firstOccurrence leftWord rightWord rest).1.1.length)
      (mergedEdge : Fin (mergedFirstOccurrence mergedWord rest).1.1.length),
      edge.val = mergedEdge.val → edge.val < y₀.length → ∀ t,
        sourceHomeomorph
            (firstPaste ⟨firstOccurrence leftWord rightWord rest,
              splitRegions.edge (firstOccurrence leftWord rightWord rest) edge t⟩) =
          ⟨mergedFirstOccurrence mergedWord rest,
            mergedRegions.edge (mergedFirstOccurrence mergedWord rest) mergedEdge t⟩ := by
    intro edge mergedEdge hedgeValue hedgeLt t
    apply sourceSplitting.injective
    rw [hsourceFirstNormalized,
      reassembledSourceSplittingHomeomorph_first]
    apply congrArg Sum.inl
    rw [leftRegion.homeomorph_edge_eq_boundaryToRegion,
      reassembledFirstHomeomorph_edge]
    simp only [comparison, Homeomorph.trans_apply]
    apply ULift.ext
    apply Subtype.ext
    have hleftPredLength :
        (firstOccurrence leftWord rightWord rest).1.1.length - 1 = y₀.length := by
      rw [firstOccurrence_fst]
      simp only [leftWord, List.length_append, List.length_singleton]
      omega
    -- Record the prefix bound before packaging the old boundary index.
    have holdIndexBound :
        edge.val < (firstOccurrence leftWord rightWord rest).1.1.length - 1 := by
      simpa only [hleftPredLength] using hedgeLt
    let oldIndex : Fin ((firstOccurrence leftWord rightWord rest).1.1.length - 1) :=
      ⟨edge.val, holdIndexBound⟩
    let combinedIndex : Fin
        ((firstOccurrence leftWord rightWord rest).1.1.length +
          (secondOccurrence leftWord rightWord rest).1.1.length - 2) :=
      Fin.cast (CyclicPolygon.EdgeGluing.concatenatedBoundaryCount
        leftRegion.polygon.three_le rightRegion.polygon.three_le)
        (Fin.castAdd ((secondOccurrence leftWord rightWord rest).1.1.length - 1)
          oldIndex)
    let targetIndex : Fin mergedWord.1.length :=
      Fin.cast (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
        (mergedFirstOccurrence_fst mergedWord rest)) mergedEdge
    have holdIndex : Fin.cast
        (CyclicPolygon.EdgeGluing.predAddOne_eq leftRegion.polygon.three_le)
          oldIndex.castSucc =
      edge := by
      apply Fin.ext
      rfl
    have htargetIndex : Fin.cast hcombinedCount combinedIndex = targetIndex := by
      apply Fin.ext
      exact hedgeValue
    have hboundaryValue := hleftBoundary oldIndex t
    rw [holdIndex] at hboundaryValue
    calc
      _ = (realizationHomeomorph
          (gluing.includeLeft (leftRegion.polygon.boundaryToRegion
            (leftRegion.polygon.edgePoint edge t))) :
            EuclideanSpace ℝ (Fin 2)) := rfl
      _ = (combined.boundaryToRegion (combined.edgePoint combinedIndex t) :
          EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hboundaryValue
      _ = (combined.edgePoint combinedIndex t : EuclideanSpace ℝ (Fin 2)) := by
        rw [combined.boundaryToRegion_coe]
      _ = (mergedPolygon.edgePoint targetIndex t : EuclideanSpace ℝ (Fin 2)) := by
        rw [← htargetIndex]
        exact (CyclicPolygon.castVertexCount_edgePoint_coe hcombinedCount combined
          combinedIndex t).symm
      _ = _ := by
        rw [mergedPolygon.boundaryToRegion_coe]
  have hrightSourceCorrespondence : ∀
      (edge : Fin (secondOccurrence leftWord rightWord rest).1.1.length)
      (mergedEdge : Fin (mergedFirstOccurrence mergedWord rest).1.1.length),
      mergedEdge.val = y₀.length + edge.val - 1 → 0 < edge.val → ∀ t,
        sourceHomeomorph
            (firstPaste ⟨secondOccurrence leftWord rightWord rest,
              splitRegions.edge (secondOccurrence leftWord rightWord rest) edge t⟩) =
          ⟨mergedFirstOccurrence mergedWord rest,
            mergedRegions.edge (mergedFirstOccurrence mergedWord rest) mergedEdge t⟩ := by
    intro edge mergedEdge hedgeValue hedgePositive t
    apply sourceSplitting.injective
    rw [hsourceSecondNormalized,
      reassembledSourceSplittingHomeomorph_first]
    apply congrArg Sum.inl
    rw [rightRegion.homeomorph_edge_eq_boundaryToRegion,
      reassembledFirstHomeomorph_edge]
    simp only [comparison, Homeomorph.trans_apply]
    apply ULift.ext
    apply Subtype.ext
    have hleftPredLength :
        (firstOccurrence leftWord rightWord rest).1.1.length - 1 = y₀.length := by
      rw [firstOccurrence_fst]
      simp only [leftWord, List.length_append, List.length_singleton]
      omega
    have hrightPredLength :
        (secondOccurrence leftWord rightWord rest).1.1.length - 1 = y₁.length := by
      rw [secondOccurrence_fst]
      simp only [rightWord, List.length_cons]
      omega
    -- Positivity moves the selected right edge into the retained suffix.
    have holdIndexBound :
        edge.val - 1 <
          (secondOccurrence leftWord rightWord rest).1.1.length - 1 := by
      have hedgeBound := edge.isLt
      omega
    let oldIndex : Fin ((secondOccurrence leftWord rightWord rest).1.1.length - 1) :=
      ⟨edge.val - 1, holdIndexBound⟩
    let combinedIndex : Fin
        ((firstOccurrence leftWord rightWord rest).1.1.length +
          (secondOccurrence leftWord rightWord rest).1.1.length - 2) :=
      Fin.cast (CyclicPolygon.EdgeGluing.concatenatedBoundaryCount
        leftRegion.polygon.three_le rightRegion.polygon.three_le)
        (Fin.natAdd ((firstOccurrence leftWord rightWord rest).1.1.length - 1)
          oldIndex)
    let targetIndex : Fin mergedWord.1.length :=
      Fin.cast (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
        (mergedFirstOccurrence_fst mergedWord rest)) mergedEdge
    have holdIndex : Fin.cast
        (CyclicPolygon.EdgeGluing.predAddOne_eq rightRegion.polygon.three_le)
          oldIndex.succ = edge := by
      apply Fin.ext
      simp only [oldIndex, Fin.val_cast, Fin.val_succ]
      omega
    have htargetIndex : Fin.cast hcombinedCount combinedIndex = targetIndex := by
      apply Fin.ext
      simp only [combinedIndex, targetIndex, Fin.val_cast, Fin.val_natAdd, oldIndex]
      rw [hleftPredLength, hedgeValue]
      omega
    have hboundaryValue := hrightBoundary oldIndex t
    rw [holdIndex] at hboundaryValue
    calc
      _ = (realizationHomeomorph
          (gluing.includeRight (rightRegion.polygon.boundaryToRegion
            (rightRegion.polygon.edgePoint edge t))) :
            EuclideanSpace ℝ (Fin 2)) := rfl
      _ = (combined.boundaryToRegion (combined.edgePoint combinedIndex t) :
          EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hboundaryValue
      _ = (combined.edgePoint combinedIndex t : EuclideanSpace ℝ (Fin 2)) := by
        rw [combined.boundaryToRegion_coe]
      _ = (mergedPolygon.edgePoint targetIndex t : EuclideanSpace ℝ (Fin 2)) := by
        rw [← htargetIndex]
        exact (CyclicPolygon.castVertexCount_edgePoint_coe hcombinedCount combined
          combinedIndex t).symm
      _ = _ := by
        rw [mergedPolygon.boundaryToRegion_coe]
  have hforwardBoundary : ∀
      (region : Occurrence (leftWord ::ₘ rightWord ::ₘ rest))
      (edge : Fin region.1.1.length),
      (region.1.1.get edge).1 ≠ c →
        ∃ (mergedRegion : Occurrence (mergedWord ::ₘ rest))
          (mergedEdge : Fin mergedRegion.1.1.length),
          region.1.1.get edge = mergedRegion.1.1.get mergedEdge ∧
            ∀ t, sourceHomeomorph
                (firstPaste ⟨region, splitRegions.edge region edge t⟩) =
              ⟨mergedRegion, mergedRegions.edge mergedRegion mergedEdge t⟩ := by
    intro region edge hc
    cases hposition : splitOccurrenceEquiv leftWord rightWord rest region with
    | none =>
        have hregion : region = firstOccurrence leftWord rightWord rest := by
          apply (splitOccurrenceEquiv leftWord rightWord rest).injective
          rw [hposition, splitOccurrenceEquiv_first]
        subst region
        have hedgeLt : edge.val < y₀.length := by
          by_contra hnot
          have hedgeBound := edge.isLt
          have hleftLength :
              (firstOccurrence leftWord rightWord rest).1.1.length = y₀.length + 1 := by
            rw [firstOccurrence_fst]
            simp only [leftWord, List.length_append, List.length_singleton]
          have hedgeValue : edge.val = y₀.length := by omega
          have hedgeSelected : edge = gluing.leftEdge.index := by
            apply Fin.ext
            exact hedgeValue.trans hleftIndexValue.symm
          subst edge
          exact hc hleftLabel
        have hmergedLength :
            (mergedFirstOccurrence mergedWord rest).1.1.length =
              y₀.length + y₁.length := by
          rw [mergedFirstOccurrence_fst]
          simp only [mergedWord, List.length_append]
        have hmergedEdgeBound :
            edge.val < (mergedFirstOccurrence mergedWord rest).1.1.length := by
          rw [hmergedLength]
          omega
        let mergedEdge : Fin (mergedFirstOccurrence mergedWord rest).1.1.length :=
          ⟨edge.val, hmergedEdgeBound⟩
        have hleftWord := firstOccurrence_fst leftWord rightWord rest
        have hmergedWord := mergedFirstOccurrence_fst mergedWord rest
        let oldIndex : Fin leftWord.1.length :=
          Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hleftWord) edge
        let newIndex : Fin mergedWord.1.length :=
          Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hmergedWord)
            mergedEdge
        have holdIndex : Fin.cast
            (congrArg (fun word : PolygonWord α ↦ word.1.length) hleftWord).symm
              oldIndex = edge := by
          apply Fin.ext
          rfl
        have hnewIndex : Fin.cast
            (congrArg (fun word : PolygonWord α ↦ word.1.length) hmergedWord).symm
              newIndex = mergedEdge := by
          apply Fin.ext
          rfl
        have hletter :
            (firstOccurrence leftWord rightWord rest).1.1.get edge =
              (mergedFirstOccurrence mergedWord rest).1.1.get mergedEdge := by
          calc
            _ = leftWord.1.get oldIndex := by
              rw [← holdIndex]
              exact get_cast_fst_eq hleftWord oldIndex
            _ = mergedWord.1.get newIndex := by
              simp only [leftWord, mergedWord, oldIndex, newIndex,
                List.get_eq_getElem, Fin.val_cast]
              rw [List.getElem_append_left hedgeLt,
                List.getElem_append_left hedgeLt]
            _ = _ := by
              rw [← hnewIndex]
              exact (get_cast_fst_eq hmergedWord newIndex).symm
        exact ⟨mergedFirstOccurrence mergedWord rest, mergedEdge, hletter,
          hleftSourceCorrespondence edge mergedEdge rfl hedgeLt⟩
    | some remaining =>
        cases remaining with
        | none =>
            have hregion : region = secondOccurrence leftWord rightWord rest := by
              apply (splitOccurrenceEquiv leftWord rightWord rest).injective
              rw [hposition, splitOccurrenceEquiv_second]
            subst region
            have hedgePositive : 0 < edge.val := by
              by_contra hnot
              have hedgeValue : edge.val = 0 := by omega
              have hedgeSelected : edge = gluing.rightEdge.index := by
                apply Fin.ext
                exact hedgeValue.trans hrightIndex.symm
              subst edge
              exact hc hrightLabel
            have hmergedLength :
                (mergedFirstOccurrence mergedWord rest).1.1.length =
                  y₀.length + y₁.length := by
              rw [mergedFirstOccurrence_fst]
              simp only [mergedWord, List.length_append]
            have hedgeBound := edge.isLt
            have hrightLength :
                (secondOccurrence leftWord rightWord rest).1.1.length =
                  y₁.length + 1 := by
              rw [secondOccurrence_fst]
              simp only [rightWord, List.length_cons]
            have hmergedEdgeBound :
                y₀.length + edge.val - 1 <
                  (mergedFirstOccurrence mergedWord rest).1.1.length := by
              rw [hmergedLength]
              omega
            have htailBound : edge.val - 1 < y₁.length := by
              omega
            let mergedEdge : Fin
                (mergedFirstOccurrence mergedWord rest).1.1.length :=
              ⟨y₀.length + edge.val - 1, hmergedEdgeBound⟩
            let tailIndex : Fin y₁.length :=
              ⟨edge.val - 1, htailBound⟩
            have hrightWord := secondOccurrence_fst leftWord rightWord rest
            have hmergedWord := mergedFirstOccurrence_fst mergedWord rest
            let oldIndex : Fin rightWord.1.length :=
              Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
                hrightWord) edge
            let newIndex : Fin mergedWord.1.length :=
              Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
                hmergedWord) mergedEdge
            have holdIndex : Fin.cast
                (congrArg (fun word : PolygonWord α ↦ word.1.length)
                  hrightWord).symm oldIndex = edge := by
              apply Fin.ext
              rfl
            have hnewIndex : Fin.cast
                (congrArg (fun word : PolygonWord α ↦ word.1.length)
                  hmergedWord).symm newIndex = mergedEdge := by
              apply Fin.ext
              rfl
            have holdTail : oldIndex = tailIndex.succ := by
              apply Fin.ext
              simp only [oldIndex, tailIndex, Fin.val_cast, Fin.val_succ]
              omega
            have hnewValue : newIndex.val = y₀.length + tailIndex.val := by
              simp only [newIndex, mergedEdge, tailIndex, Fin.val_cast]
              omega
            have happendRight : y₀.length ≤ newIndex.val := by
              rw [hnewValue]
              omega
            have hletter :
                (secondOccurrence leftWord rightWord rest).1.1.get edge =
                  (mergedFirstOccurrence mergedWord rest).1.1.get mergedEdge := by
              calc
                _ = rightWord.1.get oldIndex := by
                  rw [← holdIndex]
                  exact get_cast_fst_eq hrightWord oldIndex
                _ = mergedWord.1.get newIndex := by
                  rw [holdTail]
                  simp only [rightWord, mergedWord, List.get_eq_getElem]
                  change y₁[tailIndex.val] = (y₀ ++ y₁)[newIndex.val]
                  rw [List.getElem_append_right happendRight]
                  congr 1
                  rw [hnewValue]
                  omega
                _ = _ := by
                  rw [← hnewIndex]
                  exact (get_cast_fst_eq hmergedWord newIndex).symm
            exact ⟨mergedFirstOccurrence mergedWord rest, mergedEdge, hletter,
              hrightSourceCorrespondence edge mergedEdge rfl hedgePositive⟩
        | some index =>
            let retained := (retainedOccurrenceEquiv rest).symm index
            have hregion :
                region = splitRestOccurrence leftWord rightWord rest retained := by
              apply (splitOccurrenceEquiv leftWord rightWord rest).injective
              rw [hposition, splitOccurrenceEquiv_retained]
              simp only [retained, Equiv.apply_symm_apply]
            subst region
            have holdWord := splitRestOccurrence_fst leftWord rightWord rest retained
            have hmergedWord := mergedRestOccurrence_fst mergedWord rest retained
            let nativeEdge : Fin retained.1.1.length :=
              Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) holdWord)
                edge
            let mergedEdge : Fin
                (mergedRestOccurrence mergedWord rest retained).1.1.length :=
              Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
                hmergedWord).symm nativeEdge
            have holdIndex : Fin.cast
                (congrArg (fun word : PolygonWord α ↦ word.1.length) holdWord).symm
                  nativeEdge = edge := by
              apply Fin.ext
              rfl
            have hletter :
                (splitRestOccurrence leftWord rightWord rest retained).1.1.get edge =
                  (mergedRestOccurrence mergedWord rest retained).1.1.get mergedEdge := by
              calc
                _ = retained.1.1.get nativeEdge := by
                  rw [← holdIndex]
                  exact get_cast_fst_eq holdWord nativeEdge
                _ = _ := by
                  exact (get_cast_fst_eq hmergedWord nativeEdge).symm
            refine ⟨mergedRestOccurrence mergedWord rest retained, mergedEdge,
              hletter, ?_⟩
            intro t
            apply sourceSplitting.injective
            rw [hsourceRestNormalized,
              reassembledSourceSplittingHomeomorph_rest]
            apply congrArg Sum.inr
            apply congrArg (Sigma.mk retained)
            rw [(retainedRegion retained).homeomorph_edge_eq_boundaryToRegion,
              reassembledRestHomeomorph_edge]
            have hmergedIndex : Fin.cast
                (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
                  hmergedWord) mergedEdge = nativeEdge := by
              apply Fin.ext
              rfl
            rw [hmergedIndex, ← holdIndex]
            simp only [retainedPolygon]
            rfl
  have hbackwardBoundary : ∀
      (mergedRegion : Occurrence (mergedWord ::ₘ rest))
      (mergedEdge : Fin mergedRegion.1.1.length),
        ∃ (region : Occurrence (leftWord ::ₘ rightWord ::ₘ rest))
          (edge : Fin region.1.1.length),
          (region.1.1.get edge).1 ≠ c ∧
            region.1.1.get edge = mergedRegion.1.1.get mergedEdge ∧
            ∀ t, sourceHomeomorph
                (firstPaste ⟨region, splitRegions.edge region edge t⟩) =
              ⟨mergedRegion, mergedRegions.edge mergedRegion mergedEdge t⟩ := by
    intro mergedRegion mergedEdge
    cases hposition : consOccurrenceEquiv mergedWord rest mergedRegion with
    | none =>
        have hregion : mergedRegion = mergedFirstOccurrence mergedWord rest := by
          apply (consOccurrenceEquiv mergedWord rest).injective
          rw [hposition, consOccurrenceEquiv_mergedFirst]
        subst mergedRegion
        by_cases hleft : mergedEdge.val < y₀.length
        · have hleftWord := firstOccurrence_fst leftWord rightWord rest
          have hmergedWord := mergedFirstOccurrence_fst mergedWord rest
          have hleftLength : leftWord.1.length = y₀.length + 1 := by
            simp only [leftWord, List.length_append, List.length_singleton]
          have hsourceIndexBound : mergedEdge.val < leftWord.1.length := by
            rw [hleftLength]
            omega
          let sourceIndex : Fin leftWord.1.length :=
            ⟨mergedEdge.val, hsourceIndexBound⟩
          let originalEdge : Fin
              (firstOccurrence leftWord rightWord rest).1.1.length :=
            Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
              hleftWord).symm sourceIndex
          let mergedIndex : Fin mergedWord.1.length :=
            Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
              hmergedWord) mergedEdge
          let prefixIndex : Fin y₀.length := ⟨mergedEdge.val, hleft⟩
          have hsourceLetter : leftWord.1.get sourceIndex = y₀.get prefixIndex := by
            simp only [leftWord, sourceIndex, prefixIndex, List.get_eq_getElem,
              List.getElem_append_left hleft]
          have hletters :
              (firstOccurrence leftWord rightWord rest).1.1.get originalEdge =
                (mergedFirstOccurrence mergedWord rest).1.1.get mergedEdge := by
            calc
              _ = leftWord.1.get sourceIndex := get_cast_fst_eq hleftWord sourceIndex
              _ = mergedWord.1.get mergedIndex := by
                simp only [leftWord, mergedWord, sourceIndex, mergedIndex,
                  List.get_eq_getElem, Fin.val_cast]
                rw [List.getElem_append_left hleft,
                  List.getElem_append_left hleft]
              _ = _ := (get_cast_fst_eq hmergedWord mergedIndex).symm
          have hcOriginal :
              ((firstOccurrence leftWord rightWord rest).1.1.get originalEdge).1 ≠ c := by
            rw [get_cast_fst_eq hleftWord sourceIndex, hsourceLetter]
            exact hy₀ _ (List.get_mem y₀ prefixIndex)
          refine ⟨firstOccurrence leftWord rightWord rest, originalEdge,
            hcOriginal, hletters, ?_⟩
          exact hleftSourceCorrespondence originalEdge mergedEdge rfl hleft
        · have hrightWord := secondOccurrence_fst leftWord rightWord rest
          have hmergedWord := mergedFirstOccurrence_fst mergedWord rest
          have hmergedLength :
              (mergedFirstOccurrence mergedWord rest).1.1.length =
                y₀.length + y₁.length := by
            rw [mergedFirstOccurrence_fst]
            simp only [mergedWord, List.length_append]
          have hmergedBound := mergedEdge.isLt
          have hrightLength : rightWord.1.length = y₁.length + 1 := by
            simp only [rightWord, List.length_cons]
          have hsuffixIndexBound : mergedEdge.val - y₀.length < y₁.length := by
            omega
          let suffixIndex : Fin y₁.length :=
            ⟨mergedEdge.val - y₀.length, hsuffixIndexBound⟩
          have hsourceIndexBound : suffixIndex.val + 1 < rightWord.1.length := by
            rw [hrightLength]
            omega
          let sourceIndex : Fin rightWord.1.length :=
            ⟨suffixIndex.val + 1, hsourceIndexBound⟩
          let originalEdge : Fin
              (secondOccurrence leftWord rightWord rest).1.1.length :=
            Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
              hrightWord).symm sourceIndex
          let mergedIndex : Fin mergedWord.1.length :=
            Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
              hmergedWord) mergedEdge
          have hsourceLetter : rightWord.1.get sourceIndex = y₁.get suffixIndex := by
            simp only [rightWord, sourceIndex, List.get_eq_getElem]
            rfl
          have hmergedIndexValue :
              mergedIndex.val = y₀.length + suffixIndex.val := by
            simp only [mergedIndex, suffixIndex, Fin.val_cast]
            omega
          have happendRight : y₀.length ≤ mergedIndex.val := by
            rw [hmergedIndexValue]
            omega
          have hletters :
              (secondOccurrence leftWord rightWord rest).1.1.get originalEdge =
                (mergedFirstOccurrence mergedWord rest).1.1.get mergedEdge := by
            calc
              _ = rightWord.1.get sourceIndex := get_cast_fst_eq hrightWord sourceIndex
              _ = mergedWord.1.get mergedIndex := by
                rw [hsourceLetter]
                simp only [mergedWord, List.get_eq_getElem]
                rw [List.getElem_append_right happendRight]
                congr 1
              _ = _ := (get_cast_fst_eq hmergedWord mergedIndex).symm
          have hcOriginal :
              ((secondOccurrence leftWord rightWord rest).1.1.get originalEdge).1 ≠ c := by
            rw [get_cast_fst_eq hrightWord sourceIndex, hsourceLetter]
            exact hy₁ _ (List.get_mem y₁ suffixIndex)
          have hsourceValue : originalEdge.val = suffixIndex.val + 1 := by
            rfl
          have hmergedValue :
              mergedEdge.val = y₀.length + originalEdge.val - 1 := by
            simp only [hsourceValue, suffixIndex]
            omega
          have hsourcePositive : 0 < originalEdge.val := by
            rw [hsourceValue]
            omega
          refine ⟨secondOccurrence leftWord rightWord rest, originalEdge,
            hcOriginal, hletters, ?_⟩
          exact hrightSourceCorrespondence originalEdge mergedEdge hmergedValue hsourcePositive
    | some retained =>
        have hregion : mergedRegion = mergedRestOccurrence mergedWord rest retained := by
          apply (consOccurrenceEquiv mergedWord rest).injective
          rw [hposition, consOccurrenceEquiv_mergedRest]
        subst mergedRegion
        have holdWord := splitRestOccurrence_fst leftWord rightWord rest retained
        have hmergedWord := mergedRestOccurrence_fst mergedWord rest retained
        let nativeEdge : Fin retained.1.1.length :=
          Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
            hmergedWord) mergedEdge
        let originalEdge : Fin
            (splitRestOccurrence leftWord rightWord rest retained).1.1.length :=
          Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length)
            holdWord).symm nativeEdge
        have hletters :
            (splitRestOccurrence leftWord rightWord rest retained).1.1.get originalEdge =
              (mergedRestOccurrence mergedWord rest retained).1.1.get mergedEdge := by
          calc
            _ = retained.1.1.get nativeEdge := get_cast_fst_eq holdWord nativeEdge
            _ = _ := (get_cast_fst_eq hmergedWord nativeEdge).symm
        have hcNative : (retained.1.1.get nativeEdge).1 ≠ c :=
          (LabellingScheme.avoidsLabel_iff.mp hrest) retained.1
            (@Multiset.coe_mem (PolygonWord α) (Classical.decEq _) rest retained)
            (retained.1.1.get nativeEdge) (List.get_mem _ _)
        have hcOriginal :
            ((splitRestOccurrence leftWord rightWord rest retained).1.1.get
              originalEdge).1 ≠ c := by
          rw [get_cast_fst_eq holdWord nativeEdge]
          exact hcNative
        refine ⟨splitRestOccurrence leftWord rightWord rest retained, originalEdge,
          hcOriginal, hletters, ?_⟩
        intro t
        apply sourceSplitting.injective
        rw [hsourceRestNormalized,
          reassembledSourceSplittingHomeomorph_rest]
        apply congrArg Sum.inr
        apply congrArg (Sigma.mk retained)
        rw [(retainedRegion retained).homeomorph_edge_eq_boundaryToRegion,
          reassembledRestHomeomorph_edge]
        have hmergedIndex : Fin.cast
            (congrArg (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
              hmergedWord) mergedEdge = nativeEdge := by
          apply Fin.ext
          rfl
        rw [hmergedIndex]
        simp only [retainedPolygon, originalEdge]
        rfl
  have hboundary : ∀ x y,
      (splitRegions.RemainingIdentified c firstPaste).r x y ↔
        mergedRegions.Identified.r (sourceHomeomorph x) (sourceHomeomorph y) := by
    intro x y
    rw [remainingIdentified_iff_eqvGen, identified_iff_eqvGen]
    exact Relation.eqvGen_iff_map_equiv sourceHomeomorph.toEquiv
      (remainingRelated_iff_edgeRelated_of_boundaryCorrespondence splitRegions c
        firstPaste mergedRegions sourceHomeomorph hforwardBoundary hbackwardBoundary)
      x y
  let pasting : Pasting (mergedWord ::ₘ rest) splitRegions c firstPaste :=
    ⟨mergedRegions, hpastesLabel, sourceHomeomorph, hboundary⟩
  let result : PasteResult splitRegions c (mergedFirstOccurrence mergedWord rest)
      (splitRestOccurrence leftWord rightWord rest)
      (mergedRestOccurrence mergedWord rest) :=
    ⟨TopCat.of
      (gluing.Realization ⊕ selectedEdgeRetainedSource leftWord rightWord rest splitRegions),
      firstPaste, pasting,
      reassembledFirstCyclicRegion mergedWord rest mergedPolygon retainedPolygon,
      reassembledRetainedComparison leftWord rightWord rest splitRegions retainedRegion
        mergedWord mergedPolygon,
      reassembledRestCyclicRegion mergedWord rest mergedPolygon retainedPolygon⟩
  refine ⟨result, ?_⟩
  apply (agreesWithEdgeGluing_iff result leftRegion rightRegion gluing).mpr
  let presentationCount := congrArg
    (fun polygonWord : PolygonWord α ↦ polygonWord.1.length)
    (mergedFirstOccurrence_fst mergedWord rest)
  let presentationTransport : ULift.{v, 0} mergedPolygon.region ≃ₜ
      (reassembledFirstPolygon mergedWord rest mergedPolygon).region :=
    Homeomorph.ulift.trans
      (Homeomorph.setCongr
        (CyclicPolygon.castVertexCount_region presentationCount.symm mergedPolygon)).symm
  let rawResultComparison : gluing.Realization ≃ₜ
      (reassembledFirstPolygon mergedWord rest mergedPolygon).region :=
    comparison.trans presentationTransport
  let resultComparison : gluing.Realization ≃ₜ
      (reassembledFirstPolygon mergedWord rest mergedPolygon).region :=
    rawResultComparison
  refine ⟨resultComparison, ?_, ?_, ?_⟩
  · intro x
    apply sourceSplitting.injective
    rw [hsourceFirstNormalized,
      reassembledSourceSplittingHomeomorph_first]
    apply congrArg Sum.inl
    simp only [result, resultComparison, rawResultComparison,
      reassembledFirstCyclicRegion, CyclicRegion.equiv]
    apply presentationTransport.injective
    exact ((@Homeomorph.toEquiv _ _
      (reassembledTopology mergedWord rest mergedPolygon retainedPolygon
        (mergedFirstOccurrence mergedWord rest)) inferInstance
      (reassembledFirstRegionHomeomorph mergedWord rest mergedPolygon
        retainedPolygon)).apply_symm_apply
          (resultComparison (gluing.includeLeft (leftRegion.homeomorph x)))).symm
  · intro y
    apply sourceSplitting.injective
    rw [hsourceSecondNormalized,
      reassembledSourceSplittingHomeomorph_first]
    apply congrArg Sum.inl
    simp only [result, resultComparison, rawResultComparison,
      reassembledFirstCyclicRegion, CyclicRegion.equiv]
    apply presentationTransport.injective
    exact ((@Homeomorph.toEquiv _ _
      (reassembledTopology mergedWord rest mergedPolygon retainedPolygon
        (mergedFirstOccurrence mergedWord rest)) inferInstance
      (reassembledFirstRegionHomeomorph mergedWord rest mergedPolygon
        retainedPolygon)).apply_symm_apply
          (resultComparison (gluing.includeRight (rightRegion.homeomorph y)))).symm
  · intro region x
    apply sourceSplitting.injective
    rw [hsourceRestNormalized,
      reassembledSourceSplittingHomeomorph_rest]
    apply congrArg Sum.inr
    apply congrArg (Sigma.mk region)
    simp only [result, reassembledRetainedComparison, retainedPolygon,
      Homeomorph.trans_apply]
    exact ((@Homeomorph.toEquiv _ _
      (reassembledTopology mergedWord rest mergedPolygon
        (fun retained ↦ (retainedRegion retained).polygon)
        (mergedRestOccurrence mergedWord rest region)) inferInstance
      (reassembledRestHomeomorph mergedWord rest mergedPolygon
        (fun retained ↦ (retainedRegion retained).polygon) region)).apply_symm_apply
          (Homeomorph.ulift.symm ((retainedRegion region).homeomorph x))).symm

end LabellingScheme.PolygonalRegions.Pasting

/-- Proposition 76.2. If a family of polygonal regions realizing `X` has uniquely paired
edges labelled `c⁻¹` and `c` on its first two regions, those edges can be pasted to form
a polygonal merged first region while retaining polygonal presentations of every remaining
region and realizing the same space `X`. -/
theorem pasteRealizesSameSpace {α : Type u} [DecidableEq α]
    (y₀ y₁ : List (α × Bool)) (c : α) (b : Bool) (rest : LabellingScheme α)
    (hy₀Length : 2 ≤ y₀.length) (hy₁Length : 2 ≤ y₁.length)
    (hy₀ : ∀ letter ∈ y₀, letter.1 ≠ c) (hy₁ : ∀ letter ∈ y₁, letter.1 ≠ c)
    (hrest : rest.AvoidsLabel c)
    (splitRegions : PolygonalRegions.{u, v}
      (⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest))
    (hsplitPolygonal : splitRegions.IsPolygonal)
    {X : Type w} [TopologicalSpace X] (q : splitRegions.Source → X)
    (hsplit : splitRegions.Realizes q) :
    ∃ result : PolygonalRegions.PasteResult splitRegions c
        (mergedFirstOccurrence
          ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ rest)
        (fun region ↦ splitRestOccurrence
          ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
          ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest region)
        (fun region ↦ mergedRestOccurrence
          ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ rest region),
      IsPolygonal result.pasting.mergedRegions ∧
        ∃ mergedQuotient : Source result.pasting.mergedRegions → X,
          Realizes result.pasting.mergedRegions mergedQuotient := by
  classical
  -- First choose concrete cyclic presentations of the two regions carrying the `c`-edges.
  obtain ⟨leftRegion⟩ := (isPolygonal_iff splitRegions).mp hsplitPolygonal
    (firstOccurrence
      ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
      ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest)
  obtain ⟨rightRegion⟩ := (isPolygonal_iff splitRegions).mp hsplitPolygonal
    (secondOccurrence
      ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
      ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest)
  -- Route correction: the strengthened producer now owns compatible retained cyclic
  -- presentations, so choose those presentations directly from split polygonality.
  let retainedRegion : ∀ region : Occurrence rest,
      CyclicRegion splitRegions
        (splitRestOccurrence
          ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
          ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest region) :=
    fun region ↦ Classical.choice ((isPolygonal_iff splitRegions).mp hsplitPolygonal
      (splitRestOccurrence
        ⟨y₀ ++ [(c, !b)], PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩
        ⟨(c, b) :: y₁, PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ rest region))
  -- Glue the distinguished labelled edges after translating the left presentation.
  obtain ⟨offset, gluing, hleftEdge, hrightEdge, hopposite⟩ :=
    leftRegion.existsDistinguishedLabelledEdgeGluing y₀ y₁ c b rest hy₀Length
      hy₁Length splitRegions rightRegion
  -- Route correction: the producer now uses the owner-level adjunction automorphism;
  -- its remaining frontier is explicit boundary concatenation and relation reassembly.
  obtain ⟨result, _⟩ := existsOfEdgeGluing y₀ y₁ c b rest hy₀Length hy₁Length
    hy₀ hy₁ hrest splitRegions (leftRegion.translate offset) rightRegion retainedRegion
    gluing hleftEdge hrightEdge hopposite
  refine ⟨result, ?_⟩
  -- The producer's cyclic presentations prove polygonality, and quotient transport
  -- carries the original realization to the merged family.
  exact result.existsPolygonalRealization
    (result.isPolygonal_cons
      ⟨y₀ ++ y₁, PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ rest)
    q hsplit
