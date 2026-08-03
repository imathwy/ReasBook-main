module

public import Topology_Munkres_2000.Book.Definition_76_6.Relabel
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
public import Mathlib.Topology.Constructions
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Definition_76_6.Relabel

public section

universe u v w

namespace LabellingScheme.PolygonalRegions

variable {α : Type u} {β : Type v} {scheme : LabellingScheme α}

/-- The canonical equivalence between region occurrences before and after relabelling. -/
@[expose]
noncomputable def relabelRegionEquiv (e : α ≃ β) (scheme : LabellingScheme α) :
    Occurrence scheme ≃ Occurrence (scheme.relabel e) :=
  @Multiset.mapEquiv (PolygonWord α) (PolygonWord β) (Classical.decEq _)
    (Classical.decEq _) scheme (PolygonWord.relabel e)

/-- The word underlying a transported region occurrence is the relabelled original word. -/
theorem relabelRegionEquiv_val (e : α ≃ β) (scheme : LabellingScheme α)
    (region : Occurrence scheme) :
    (relabelRegionEquiv e scheme region).1 = region.1.relabel e := by
  -- The chosen multiset occurrence equivalence computes to the mapped polygon word.
  exact @Multiset.mapEquiv_apply (PolygonWord α) (PolygonWord β) (Classical.decEq _)
    (Classical.decEq _) scheme (PolygonWord.relabel e) region

/-- Helper for Definition 76.6: a transported relabelled occurrence has the same boundary
length as its original occurrence. -/
theorem relabelRegionEquiv_length (e : α ≃ β) (scheme : LabellingScheme α)
    (region : Occurrence scheme) :
    (relabelRegionEquiv e scheme region).1.1.length = region.1.1.length := by
  -- Reduce the transported word to a list map, which preserves length.
  rw [relabelRegionEquiv_val]
  simp [PolygonWord.relabel]

/-- Relabelling preserves the number of boundary edges in each transported region. -/
theorem relabelRegion_length (e : α ≃ β) (scheme : LabellingScheme α)
    (region : Occurrence (scheme.relabel e)) :
    region.1.1.length = ((relabelRegionEquiv e scheme).symm region).1.1.length := by
  let original := (relabelRegionEquiv e scheme).symm region
  have hregion : (relabelRegionEquiv e scheme) original = region :=
    (relabelRegionEquiv e scheme).apply_symm_apply region
  calc
    region.1.1.length = ((relabelRegionEquiv e scheme) original).1.1.length := by rw [hregion]
    _ = (original.1.relabel e).1.length := by
      exact congrArg (fun word : PolygonWord β ↦ word.1.length)
        (@Multiset.mapEquiv_apply (PolygonWord α) (PolygonWord β) (Classical.decEq _)
          (Classical.decEq _) scheme (PolygonWord.relabel e) original)
    _ = original.1.1.length := by simp [PolygonWord.relabel]

/-- Transport polygonal regions along a label equivalence, retaining their points and edges. -/
@[expose]
noncomputable def relabel (regions : PolygonalRegions scheme) (e : α ≃ β) :
    PolygonalRegions (scheme.relabel e) where
  Point region := regions.Point ((relabelRegionEquiv e scheme).symm region)
  topology region := regions.topology ((relabelRegionEquiv e scheme).symm region)
  edge region edge t :=
    regions.edge ((relabelRegionEquiv e scheme).symm region)
      (Fin.cast (relabelRegion_length e scheme region) edge) t

/-- The canonical equivalence of disjoint-union sources induced by relabelling. -/
@[expose]
noncomputable def relabelSourceEquiv (regions : PolygonalRegions scheme) (e : α ≃ β) :
    regions.Source ≃ (regions.relabel e).Source :=
  Equiv.sigmaCongr (relabelRegionEquiv e scheme) fun region ↦
    Equiv.cast (congrArg regions.Point ((relabelRegionEquiv e scheme).symm_apply_apply region).symm)

/-- Helper for Definition 76.6: transport between equal region fibers is continuous for
the stored component topologies. -/
theorem continuous_regionPointCast (regions : PolygonalRegions scheme)
    {region₁ region₂ : Occurrence scheme} (hregion : region₂ = region₁) :
    @Continuous (regions.Point region₁) (regions.Point region₂)
      (regions.topology region₁) (regions.topology region₂)
      (Equiv.cast (congrArg regions.Point hregion.symm)) := by
  -- Eliminating the occurrence equality reduces the transport to the identity map.
  subst region₂
  exact @continuous_id _ (regions.topology region₁)

/-- Helper for Definition 76.6: the relabelling source equivalence is continuous. -/
theorem continuous_relabelSourceEquiv (regions : PolygonalRegions scheme) (e : α ≃ β) :
    Continuous (relabelSourceEquiv regions e) := by
  -- Check continuity on each summand of the source topology.
  change @Continuous _ _ regions.sourceTopology (regions.relabel e).sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let target := relabelRegionEquiv e scheme region
  have hregion := (relabelRegionEquiv e scheme).symm_apply_apply region
  have hcast := continuous_regionPointCast regions hregion
  have hinclusion :
      @Continuous ((regions.relabel e).Point target) (regions.relabel e).Source
        ((regions.relabel e).topology target) (regions.relabel e).sourceTopology
        (Sigma.mk target) :=
    continuous_iSup_rng (i := target) (f := Sigma.mk target)
      (continuous_coinduced_rng (f := Sigma.mk target))
  dsimp [relabelSourceEquiv, Equiv.sigmaCongr]
  exact @Continuous.comp
    (regions.Point region) ((regions.relabel e).Point target) (regions.relabel e).Source
    (regions.topology region) ((regions.relabel e).topology target)
    (regions.relabel e).sourceTopology _ _ hinclusion hcast

/-- Helper for Definition 76.6: the inverse relabelling source equivalence is continuous. -/
theorem continuous_relabelSourceEquiv_symm
    (regions : PolygonalRegions scheme) (e : α ≃ β) :
    Continuous (relabelSourceEquiv regions e).symm := by
  -- On each relabelled summand the inverse is the canonical inclusion of its preimage.
  change @Continuous _ _ (regions.relabel e).sourceTopology regions.sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let original := (relabelRegionEquiv e scheme).symm region
  letI : TopologicalSpace (regions.Point original) := regions.topology original
  have hinclusion : Continuous
      (Sigma.mk original : regions.Point original → regions.Source) :=
    continuous_iSup_rng (i := original) (f := Sigma.mk original)
      (continuous_coinduced_rng (f := Sigma.mk original))
  have hinverse :
      (relabelSourceEquiv regions e).symm ∘ Sigma.mk region =
        (Sigma.mk original : regions.Point original → regions.Source) := by
    funext point
    dsimp only [Function.comp_apply]
    dsimp [relabel, original] at point
    apply (relabelSourceEquiv regions e).injective
    rw [(relabelSourceEquiv regions e).apply_symm_apply]
    apply Sigma.ext
    · exact (relabelRegionEquiv e scheme).apply_symm_apply region |>.symm
    · exact (cast_heq _ _).symm
  rw [hinverse]
  exact hinclusion

/-- Helper for Definition 76.6: relabelling preserves the source topology. -/
theorem relabelSourceEquiv_isOpen_iff (regions : PolygonalRegions scheme) (e : α ≃ β)
    (s : Set (regions.relabel e).Source) :
    IsOpen (relabelSourceEquiv regions e ⁻¹' s) ↔ IsOpen s := by
  constructor
  · intro hopen
    -- Pull the open preimage back along the continuous inverse and cancel the equivalence.
    have hpreimage :
        (relabelSourceEquiv regions e).symm ⁻¹'
            (relabelSourceEquiv regions e ⁻¹' s) = s := by
      ext point
      simp only [Set.mem_preimage, Equiv.apply_symm_apply]
    rw [← hpreimage]
    exact (continuous_relabelSourceEquiv_symm regions e).isOpen_preimage _ hopen
  · intro hopen
    exact (continuous_relabelSourceEquiv regions e).isOpen_preimage _ hopen

/-- Helper for Definition 76.6: relabelling gives a homeomorphism of polygonal-region
sources. -/
@[expose]
noncomputable def relabelSourceHomeomorph (regions : PolygonalRegions scheme) (e : α ≃ β) :
    regions.Source ≃ₜ (regions.relabel e).Source :=
  (relabelSourceEquiv regions e).toHomeomorph (relabelSourceEquiv_isOpen_iff regions e)

/-- Helper for Definition 76.6: the relabelling source homeomorphism has the canonical
source equivalence as its forward function. -/
theorem relabelSourceHomeomorph_apply (regions : PolygonalRegions scheme) (e : α ≃ β)
    (x : regions.Source) :
    relabelSourceHomeomorph regions e x = relabelSourceEquiv regions e x := by
  -- Bundling the equivalence as a homeomorphism does not alter its function.
  rfl

/-- Helper for Definition 76.6: the inverse relabelling source homeomorphism has the
canonical inverse source equivalence as its function. -/
theorem relabelSourceHomeomorph_symm_apply
    (regions : PolygonalRegions scheme) (e : α ≃ β) (x : (regions.relabel e).Source) :
    (relabelSourceHomeomorph regions e).symm x = (relabelSourceEquiv regions e).symm x := by
  -- Bundling the equivalence as a homeomorphism does not alter its inverse.
  rfl

/-- Helper for Definition 76.6: the relabelling source equivalence carries each original
boundary point to the corresponding boundary point of the transported occurrence. -/
theorem relabelSourceEquiv_edge (regions : PolygonalRegions scheme) (e : α ≃ β)
    (region : Occurrence scheme) (edge : Fin region.1.1.length) (t : unitInterval) :
    relabelSourceEquiv regions e ⟨region, regions.edge region edge t⟩ =
      ⟨relabelRegionEquiv e scheme region,
        (regions.relabel e).edge (relabelRegionEquiv e scheme region)
          (Fin.cast (relabelRegionEquiv_length e scheme region).symm edge) t⟩ := by
  -- Compare the sigma components, then normalize the two proof-only casts.
  apply Sigma.ext
  · rfl
  · have hregion := (relabelRegionEquiv e scheme).symm_apply_apply region
    have hindex :
        (⟨(relabelRegionEquiv e scheme).symm (relabelRegionEquiv e scheme region),
            Fin.cast (relabelRegion_length e scheme (relabelRegionEquiv e scheme region))
              (Fin.cast (relabelRegionEquiv_length e scheme region).symm edge)⟩ :
          (r : Occurrence scheme) × Fin r.1.1.length) = ⟨region, edge⟩ := by
      apply Sigma.ext hregion
      rw [Fin.heq_ext_iff (congrArg (fun r : Occurrence scheme ↦ r.1.1.length) hregion)]
      rfl
    have hedge := congr_arg_heq
      (fun p : (r : Occurrence scheme) × Fin r.1.1.length ↦
        regions.edge p.1 p.2 t) hindex
    dsimp [relabelSourceEquiv, Equiv.sigmaCongr, relabel]
    exact (cast_heq _ _).trans hedge.symm

/-- Helper for Definition 76.6: pulling a transported boundary point back through the source
equivalence recovers its original boundary edge and parameter. -/
theorem relabelSourceEquiv_symm_edge (regions : PolygonalRegions scheme) (e : α ≃ β)
    (region : Occurrence (scheme.relabel e)) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    (relabelSourceEquiv regions e).symm
        ⟨region, (regions.relabel e).edge region edge t⟩ =
      ⟨(relabelRegionEquiv e scheme).symm region,
        regions.edge ((relabelRegionEquiv e scheme).symm region)
          (Fin.cast (relabelRegion_length e scheme region) edge) t⟩ := by
  -- Apply the forward equivalence and use its edge computation at the inverse occurrence.
  apply (relabelSourceEquiv regions e).injective
  rw [(relabelSourceEquiv regions e).apply_symm_apply, relabelSourceEquiv_edge]
  let original := (relabelRegionEquiv e scheme).symm region
  let originalEdge := Fin.cast (relabelRegion_length e scheme region) edge
  have hregion : relabelRegionEquiv e scheme original = region :=
    (relabelRegionEquiv e scheme).apply_symm_apply region
  have hboundary :
      (⟨relabelRegionEquiv e scheme original,
          Fin.cast (relabelRegionEquiv_length e scheme original).symm originalEdge⟩ :
        (r : Occurrence (scheme.relabel e)) × Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    rw [Fin.heq_ext_iff
      (congrArg (fun r : Occurrence (scheme.relabel e) ↦ r.1.1.length) hregion)]
    rfl
  have hedge := congr_arg_heq
    (fun p : (r : Occurrence (scheme.relabel e)) × Fin r.1.1.length ↦
      (regions.relabel e).edge p.1 p.2 t) hboundary
  exact Sigma.ext hregion.symm hedge.symm

/-- Helper for Definition 76.6: a relabelled boundary edge has the transformed label and the
same orientation as its corresponding original edge. -/
theorem relabelLetter_eq (e : α ≃ β) (scheme : LabellingScheme α)
    (region : Occurrence (scheme.relabel e)) (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      (e (((relabelRegionEquiv e scheme).symm region).1.1.get
        (Fin.cast (relabelRegion_length e scheme region) edge)).1,
       (((relabelRegionEquiv e scheme).symm region).1.1.get
        (Fin.cast (relabelRegion_length e scheme region) edge)).2) := by
  -- Compare boundary positions in one dependent pair, then compute lookup in the mapped list.
  let original := (relabelRegionEquiv e scheme).symm region
  have hword : region.1 = original.1.relabel e := by
    calc
      region.1 = (relabelRegionEquiv e scheme original).1 :=
        congrArg (fun r : Occurrence (scheme.relabel e) ↦ r.1)
          ((relabelRegionEquiv e scheme).apply_symm_apply region).symm
      _ = original.1.relabel e := relabelRegionEquiv_val e scheme original
  have hboundary :
      (⟨region.1, edge⟩ : (word : PolygonWord β) × Fin word.1.length) =
        ⟨original.1.relabel e,
          Fin.cast (congrArg (fun word : PolygonWord β ↦ word.1.length) hword) edge⟩ := by
    apply Sigma.ext hword
    rw [Fin.heq_ext_iff
      (congrArg (fun word : PolygonWord β ↦ word.1.length) hword)]
    rfl
  have hget := congrArg
    (fun p : (word : PolygonWord β) × Fin word.1.length ↦ p.1.1.get p.2) hboundary
  simpa [original, PolygonWord.relabel] using hget

/-- Helper for Definition 76.6: pulling a relabelled occurrence and transported edge
index back recovers the original boundary letter. -/
theorem relabelOriginalLetter_eq (e : α ≃ β) (scheme : LabellingScheme α)
    (region : Occurrence scheme) (edge : Fin region.1.1.length) :
    ((relabelRegionEquiv e scheme).symm (relabelRegionEquiv e scheme region)).1.1.get
        (Fin.cast (relabelRegion_length e scheme (relabelRegionEquiv e scheme region))
          (Fin.cast (relabelRegionEquiv_length e scheme region).symm edge)) =
      region.1.1.get edge := by
  -- Compare the dependent occurrence-index pairs before applying list lookup.
  have hregion := (relabelRegionEquiv e scheme).symm_apply_apply region
  have hboundary :
      (⟨(relabelRegionEquiv e scheme).symm (relabelRegionEquiv e scheme region),
          Fin.cast (relabelRegion_length e scheme (relabelRegionEquiv e scheme region))
            (Fin.cast (relabelRegionEquiv_length e scheme region).symm edge)⟩ :
        (r : Occurrence scheme) × Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    rw [Fin.heq_ext_iff
      (congrArg (fun r : Occurrence scheme ↦ r.1.1.length) hregion)]
    rfl
  exact congrArg
    (fun p : (r : Occurrence scheme) × Fin r.1.1.length ↦ p.1.1.1.get p.2)
    hboundary

/-- Helper for Definition 76.6: relabelling preserves and reflects equality of the
unsigned labels at corresponding boundary positions. -/
theorem relabel_fst_eq_iff (e : α ≃ β) (scheme : LabellingScheme α)
    (region₁ region₂ : Occurrence (scheme.relabel e))
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length) :
    (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ↔
      (((relabelRegionEquiv e scheme).symm region₁).1.1.get
          (Fin.cast (relabelRegion_length e scheme region₁) edge₁)).1 =
        (((relabelRegionEquiv e scheme).symm region₂).1.1.get
          (Fin.cast (relabelRegion_length e scheme region₂) edge₂)).1 := by
  -- Normalize both relabelled letters and reflect equality through the label equivalence.
  rw [relabelLetter_eq, relabelLetter_eq]
  exact e.injective.eq_iff

/-- Helper for Definition 76.6: relabelling leaves each boundary orientation unchanged. -/
theorem relabel_snd_eq (e : α ≃ β) (scheme : LabellingScheme α)
    (region : Occurrence (scheme.relabel e)) (edge : Fin region.1.1.length) :
    (region.1.1.get edge).2 =
      (((relabelRegionEquiv e scheme).symm region).1.1.get
        (Fin.cast (relabelRegion_length e scheme region) edge)).2 := by
  -- Project the orientation component from the relabelled-letter computation.
  exact congrArg Prod.snd (relabelLetter_eq e scheme region edge)

/-- Helper for Definition 76.6: direct edge relatedness is characterized by its boundary
occurrences, indices, and affine parameter. -/
theorem edgeRelated_iff_exists_boundaryData (regions : PolygonalRegions scheme)
    (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
          (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
          x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
          y = ⟨region₂, regions.edge region₂ edge₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t)⟩ := by
  -- Expose the owner definition once for all subsequent transport arguments.
  unfold EdgeRelated
  rfl

/-- Helper for Definition 76.6: the labelled-edge setoid is the equivalence closure of
direct edge relatedness. -/
theorem identified_iff_generatedEdgeRelated (regions : PolygonalRegions scheme)
    (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- Expose the generated setoid once for all transport arguments.
  unfold Identified
  rfl

/-- Helper for Definition 76.6: an equivalence preserving a relation also preserves the
equivalence relation it generates. -/
theorem eqvGen_equiv_iff {A B : Type*} (equiv : A ≃ B)
    {r : A → A → Prop} {s : B → B → Prop}
    (hrel : ∀ x y, s (equiv x) (equiv y) ↔ r x y) (x y : A) :
    Relation.EqvGen s (equiv x) (equiv y) ↔ Relation.EqvGen r x y := by
  constructor
  · intro hxy
    -- Pull an arbitrary generated chain back one relation edge at a time.
    have hpull : ∀ {a b}, Relation.EqvGen s a b →
        Relation.EqvGen r (equiv.symm a) (equiv.symm b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
          exact Relation.EqvGen.rel _ _
            ((hrel (equiv.symm a) (equiv.symm b)).mp (by simpa using hab))
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c _ _ hab hbc => exact Relation.EqvGen.trans _ _ _ hab hbc
    simpa using hpull hxy
  · intro hxy
    -- Push an arbitrary generated chain forward in the same structural fashion.
    have hpush : ∀ {a b}, Relation.EqvGen r a b →
        Relation.EqvGen s (equiv a) (equiv b) := by
      intro a b hab
      induction hab with
      | rel a b hab => exact Relation.EqvGen.rel _ _ ((hrel a b).mpr hab)
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c _ _ hab hbc => exact Relation.EqvGen.trans _ _ _ hab hbc
    exact hpush hxy

/-- Relabelling preserves the direct labelled-edge relation under the source equivalence. -/
theorem edgeRelated_relabel_iff (regions : PolygonalRegions scheme) (e : α ≃ β)
    (x y : regions.Source) :
    (regions.relabel e).EdgeRelated (relabelSourceEquiv regions e x)
        (relabelSourceEquiv regions e y) ↔
      regions.EdgeRelated x y := by
  rw [edgeRelated_iff_exists_boundaryData, edgeRelated_iff_exists_boundaryData]
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let original₁ := (relabelRegionEquiv e scheme).symm region₁
    let original₂ := (relabelRegionEquiv e scheme).symm region₂
    let originalEdge₁ := Fin.cast (relabelRegion_length e scheme region₁) edge₁
    let originalEdge₂ := Fin.cast (relabelRegion_length e scheme region₂) edge₂
    refine ⟨original₁, original₂, originalEdge₁, originalEdge₂, t,
      (relabel_fst_eq_iff e scheme region₁ region₂ edge₁ edge₂).mp hlabel, ?_, ?_⟩
    · -- Pull the first transported boundary point back to its original occurrence.
      have hx' := congrArg (relabelSourceEquiv regions e).symm hx
      simpa only [Equiv.symm_apply_apply, relabelSourceEquiv_symm_edge] using hx'
    · -- Pull back the second point and normalize the unchanged orientation signs.
      have hy' := congrArg (relabelSourceEquiv regions e).symm hy
      simpa only [Equiv.symm_apply_apply, relabelSourceEquiv_symm_edge,
        relabel_snd_eq] using hy'
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let mapped₁ := relabelRegionEquiv e scheme region₁
    let mapped₂ := relabelRegionEquiv e scheme region₂
    let mappedEdge₁ := Fin.cast (relabelRegionEquiv_length e scheme region₁).symm edge₁
    let mappedEdge₂ := Fin.cast (relabelRegionEquiv_length e scheme region₂).symm edge₂
    refine ⟨mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, t, ?_, ?_, ?_⟩
    · -- Apply the label equivalence to the original label equality.
      apply (relabel_fst_eq_iff e scheme mapped₁ mapped₂ mappedEdge₁ mappedEdge₂).mpr
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simpa only [relabelOriginalLetter_eq] using hlabel
    · -- The forward source equivalence computes on the first boundary point.
      rw [hx, relabelSourceEquiv_edge]
    · -- The same computation applies to the second point and preserves its sign test.
      rw [hy, relabelSourceEquiv_edge]
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simp only [relabel_snd_eq, relabelOriginalLetter_eq]

/-- Relabelling preserves realization by precomposition with the inverse source equivalence. -/
theorem realizes_relabel_iff (regions : PolygonalRegions scheme) (e : α ≃ β)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X) :
    regions.Realizes q ↔
      (regions.relabel e).Realizes (q ∘ (relabelSourceEquiv regions e).symm) := by
  constructor
  · intro hrealizes
    constructor
    · -- Precomposition with the inverse source homeomorphism preserves quotientness.
      have hinverse :
          q ∘ (relabelSourceHomeomorph regions e).symm =
            q ∘ (relabelSourceEquiv regions e).symm := by
        funext point
        rw [Function.comp_apply, Function.comp_apply,
          relabelSourceHomeomorph_symm_apply]
      rw [← hinverse]
      exact hrealizes.isQuotientMap.comp
        (relabelSourceHomeomorph regions e).symm.isQuotientMap
    · intro x y
      simp only [Function.comp_apply]
      rw [hrealizes.fibers, identified_iff_generatedEdgeRelated,
        identified_iff_generatedEdgeRelated]
      simpa only [Equiv.apply_symm_apply] using
        (eqvGen_equiv_iff (relabelSourceEquiv regions e)
        (edgeRelated_relabel_iff regions e)
        ((relabelSourceEquiv regions e).symm x)
        ((relabelSourceEquiv regions e).symm y)).symm
  · intro hrealizes
    constructor
    · -- Compose back with the forward source homeomorphism and cancel its inverse.
      simpa only [Function.comp_def, relabelSourceHomeomorph_apply,
        Equiv.symm_apply_apply] using
        hrealizes.isQuotientMap.comp (relabelSourceHomeomorph regions e).isQuotientMap
    · intro x y
      have hfibers := hrealizes.fibers
        (relabelSourceEquiv regions e x) (relabelSourceEquiv regions e y)
      have hmapped :
          q x = q y ↔
            (regions.relabel e).Identified.r
              (relabelSourceEquiv regions e x) (relabelSourceEquiv regions e y) := by
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hfibers
      rw [identified_iff_generatedEdgeRelated] at hmapped
      rw [identified_iff_generatedEdgeRelated]
      exact hmapped.trans (eqvGen_equiv_iff (relabelSourceEquiv regions e)
        (edgeRelated_relabel_iff regions e) x y)

/-- Transport polygonal regions across replacement of one label by another. -/
@[expose]
noncomputable def renameLabel (regions : PolygonalRegions scheme) (a c : α) :
    PolygonalRegions (scheme.renameLabel a c) :=
  regions.relabel (PolygonWord.swapLabels a c)

/-- The source equivalence induced by replacing one label by another. -/
@[expose]
noncomputable def renameLabelSourceEquiv (regions : PolygonalRegions scheme) (a c : α) :
    regions.Source ≃ (regions.renameLabel a c).Source :=
  relabelSourceEquiv regions (PolygonWord.swapLabels a c)

/-- Helper for Definition 76.6: the geometric rename construction is the relabelling
construction at the label transposition. -/
theorem renameLabel_eq_relabel (regions : PolygonalRegions scheme) (a c : α) :
    regions.renameLabel a c = regions.relabel (PolygonWord.swapLabels a c) := by
  -- Both constructions have exactly the same defining data.
  rfl

/-- Helper for Definition 76.6: the rename source equivalence is the relabelling source
equivalence at the label transposition. -/
theorem renameLabelSourceEquiv_eq_relabelSourceEquiv
    (regions : PolygonalRegions scheme) (a c : α) :
    renameLabelSourceEquiv regions a c =
      relabelSourceEquiv regions (PolygonWord.swapLabels a c) := by
  -- This is the defining source equivalence for geometric renaming.
  rfl

/-- Replacing one label by another preserves realization and hence the pasting map. -/
theorem realizes_renameLabel_iff (regions : PolygonalRegions scheme) (a c : α)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X) :
    regions.Realizes q ↔
      (regions.renameLabel a c).Realizes
        (q ∘ (renameLabelSourceEquiv regions a c).symm) := by
  -- Renaming is the relabelling theorem specialized to the transposition of `a` and `c`.
  exact realizes_relabel_iff regions (PolygonWord.swapLabels a c) q

/-- The canonical equivalence between region occurrences before and after reversing one label. -/
@[expose]
noncomputable def reverseLabelRegionEquiv (scheme : LabellingScheme α) (a : α) :
    Occurrence scheme ≃ Occurrence (scheme.reverseLabel a) :=
  @Multiset.mapEquiv (PolygonWord α) (PolygonWord α) (Classical.decEq _)
    (Classical.decEq _) scheme (PolygonWord.reverseLabel a)

/-- Helper for Definition 76.6: a transported occurrence carries the word obtained by
reversing the selected label's signs. -/
theorem reverseLabelRegionEquiv_val (scheme : LabellingScheme α) (a : α)
    (region : Occurrence scheme) :
    (reverseLabelRegionEquiv scheme a region).1 = region.1.reverseLabel a := by
  -- Compute the mapped multiset occurrence.
  exact @Multiset.mapEquiv_apply (PolygonWord α) (PolygonWord α) (Classical.decEq _)
    (Classical.decEq _) scheme (PolygonWord.reverseLabel a) region

/-- Helper for Definition 76.6: corresponding occurrences before and after sign reversal
have equal boundary lengths. -/
theorem reverseLabelRegionEquiv_length (scheme : LabellingScheme α) (a : α)
    (region : Occurrence scheme) :
    (reverseLabelRegionEquiv scheme a region).1.1.length = region.1.1.length := by
  -- Sign reversal maps letters pointwise and therefore preserves list length.
  rw [reverseLabelRegionEquiv_val]
  simp [PolygonWord.reverseLabel]

/-- Sign reversal preserves the number of boundary edges in each transported region. -/
theorem reverseLabelRegion_length (scheme : LabellingScheme α) (a : α)
    (region : Occurrence (scheme.reverseLabel a)) :
    region.1.1.length = ((reverseLabelRegionEquiv scheme a).symm region).1.1.length := by
  let original := (reverseLabelRegionEquiv scheme a).symm region
  have hregion : (reverseLabelRegionEquiv scheme a) original = region :=
    (reverseLabelRegionEquiv scheme a).apply_symm_apply region
  calc
    region.1.1.length = ((reverseLabelRegionEquiv scheme a) original).1.1.length := by rw [hregion]
    _ = (original.1.reverseLabel a).1.length := by
      exact congrArg (fun word : PolygonWord α ↦ word.1.length)
        (@Multiset.mapEquiv_apply (PolygonWord α) (PolygonWord α) (Classical.decEq _)
          (Classical.decEq _) scheme (PolygonWord.reverseLabel a) original)
    _ = original.1.1.length := by simp [PolygonWord.reverseLabel]

/-- Transport polygonal regions while reversing every occurrence of one label. -/
noncomputable def reverseLabel (regions : PolygonalRegions scheme) (a : α) :
    PolygonalRegions (scheme.reverseLabel a) where
  Point region := regions.Point ((reverseLabelRegionEquiv scheme a).symm region)
  topology region := regions.topology ((reverseLabelRegionEquiv scheme a).symm region)
  edge region edge t :=
    regions.edge ((reverseLabelRegionEquiv scheme a).symm region)
      (Fin.cast (reverseLabelRegion_length scheme a region) edge) t

/-- The canonical equivalence of disjoint-union sources induced by sign reversal. -/
noncomputable def reverseLabelSourceEquiv (regions : PolygonalRegions scheme) (a : α) :
    regions.Source ≃ (regions.reverseLabel a).Source :=
  Equiv.sigmaCongr (reverseLabelRegionEquiv scheme a) fun region ↦
    Equiv.cast
      (congrArg regions.Point ((reverseLabelRegionEquiv scheme a).symm_apply_apply region).symm)

/-- Helper for Definition 76.6: the sign-reversal source equivalence carries an original
boundary point to the corresponding transported boundary point. -/
theorem reverseLabelSourceEquiv_edge (regions : PolygonalRegions scheme) (a : α)
    (region : Occurrence scheme) (edge : Fin region.1.1.length) (t : unitInterval) :
    reverseLabelSourceEquiv regions a ⟨region, regions.edge region edge t⟩ =
      ⟨reverseLabelRegionEquiv scheme a region,
        (regions.reverseLabel a).edge (reverseLabelRegionEquiv scheme a region)
          (Fin.cast (reverseLabelRegionEquiv_length scheme a region).symm edge) t⟩ := by
  -- Compare the sigma components and normalize the inverse occurrence and index casts.
  apply Sigma.ext
  · rfl
  · have hregion := (reverseLabelRegionEquiv scheme a).symm_apply_apply region
    have hindex :
        (⟨(reverseLabelRegionEquiv scheme a).symm
              (reverseLabelRegionEquiv scheme a region),
            Fin.cast
              (reverseLabelRegion_length scheme a (reverseLabelRegionEquiv scheme a region))
              (Fin.cast (reverseLabelRegionEquiv_length scheme a region).symm edge)⟩ :
          (r : Occurrence scheme) × Fin r.1.1.length) = ⟨region, edge⟩ := by
      apply Sigma.ext hregion
      rw [Fin.heq_ext_iff
        (congrArg (fun r : Occurrence scheme ↦ r.1.1.length) hregion)]
      rfl
    have hedge := congr_arg_heq
      (fun p : (r : Occurrence scheme) × Fin r.1.1.length ↦
        regions.edge p.1 p.2 t) hindex
    dsimp [reverseLabelSourceEquiv, Equiv.sigmaCongr, reverseLabel]
    exact (cast_heq _ _).trans hedge.symm

/-- Helper for Definition 76.6: pulling a sign-reversed boundary point back through the
source equivalence recovers its original boundary point. -/
theorem reverseLabelSourceEquiv_symm_edge (regions : PolygonalRegions scheme) (a : α)
    (region : Occurrence (scheme.reverseLabel a)) (edge : Fin region.1.1.length)
    (t : unitInterval) :
    (reverseLabelSourceEquiv regions a).symm
        ⟨region, (regions.reverseLabel a).edge region edge t⟩ =
      ⟨(reverseLabelRegionEquiv scheme a).symm region,
        regions.edge ((reverseLabelRegionEquiv scheme a).symm region)
          (Fin.cast (reverseLabelRegion_length scheme a region) edge) t⟩ := by
  -- Apply the forward equivalence and cancel its occurrence and finite-index transports.
  apply (reverseLabelSourceEquiv regions a).injective
  rw [(reverseLabelSourceEquiv regions a).apply_symm_apply, reverseLabelSourceEquiv_edge]
  let original := (reverseLabelRegionEquiv scheme a).symm region
  let originalEdge := Fin.cast (reverseLabelRegion_length scheme a region) edge
  have hregion : reverseLabelRegionEquiv scheme a original = region :=
    (reverseLabelRegionEquiv scheme a).apply_symm_apply region
  have hboundary :
      (⟨reverseLabelRegionEquiv scheme a original,
          Fin.cast (reverseLabelRegionEquiv_length scheme a original).symm originalEdge⟩ :
        (r : Occurrence (scheme.reverseLabel a)) × Fin r.1.1.length) =
        ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    rw [Fin.heq_ext_iff
      (congrArg (fun r : Occurrence (scheme.reverseLabel a) ↦ r.1.1.length) hregion)]
    rfl
  have hedge := congr_arg_heq
    (fun p : (r : Occurrence (scheme.reverseLabel a)) × Fin r.1.1.length ↦
      (regions.reverseLabel a).edge p.1 p.2 t) hboundary
  exact Sigma.ext hregion.symm hedge.symm

/-- Helper for Definition 76.6: a sign-reversed boundary letter is obtained by applying
`PolygonWord.reverseSignAt` to the corresponding original letter. -/
theorem reverseLabelLetter_eq (scheme : LabellingScheme α) (a : α)
    (region : Occurrence (scheme.reverseLabel a)) (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      PolygonWord.reverseSignAt a
        (((reverseLabelRegionEquiv scheme a).symm region).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region) edge)) := by
  -- Package the word with its dependent edge index, then compute lookup in the mapped list.
  let original := (reverseLabelRegionEquiv scheme a).symm region
  have hword : region.1 = original.1.reverseLabel a := by
    calc
      region.1 = (reverseLabelRegionEquiv scheme a original).1 :=
        congrArg (fun r : Occurrence (scheme.reverseLabel a) ↦ r.1)
          ((reverseLabelRegionEquiv scheme a).apply_symm_apply region).symm
      _ = original.1.reverseLabel a := reverseLabelRegionEquiv_val scheme a original
  have hboundary :
      (⟨region.1, edge⟩ : (word : PolygonWord α) × Fin word.1.length) =
        ⟨original.1.reverseLabel a,
          Fin.cast (congrArg (fun word : PolygonWord α ↦ word.1.length) hword) edge⟩ := by
    apply Sigma.ext hword
    rw [Fin.heq_ext_iff
      (congrArg (fun word : PolygonWord α ↦ word.1.length) hword)]
    rfl
  have hget := congrArg
    (fun p : (word : PolygonWord α) × Fin word.1.length ↦ p.1.1.get p.2) hboundary
  simpa [original, PolygonWord.reverseLabel] using hget

/-- Helper for Definition 76.6: pulling a transported sign-reversed edge back recovers
the original boundary letter. -/
theorem reverseLabelOriginalLetter_eq (scheme : LabellingScheme α) (a : α)
    (region : Occurrence scheme) (edge : Fin region.1.1.length) :
    ((reverseLabelRegionEquiv scheme a).symm
        (reverseLabelRegionEquiv scheme a region)).1.1.get
        (Fin.cast
          (reverseLabelRegion_length scheme a (reverseLabelRegionEquiv scheme a region))
          (Fin.cast (reverseLabelRegionEquiv_length scheme a region).symm edge)) =
      region.1.1.get edge := by
  -- Compare the dependent occurrence-index pairs before applying boundary lookup.
  have hregion := (reverseLabelRegionEquiv scheme a).symm_apply_apply region
  have hboundary :
      (⟨(reverseLabelRegionEquiv scheme a).symm
            (reverseLabelRegionEquiv scheme a region),
          Fin.cast
            (reverseLabelRegion_length scheme a (reverseLabelRegionEquiv scheme a region))
            (Fin.cast (reverseLabelRegionEquiv_length scheme a region).symm edge)⟩ :
        (r : Occurrence scheme) × Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregion
    rw [Fin.heq_ext_iff
      (congrArg (fun r : Occurrence scheme ↦ r.1.1.length) hregion)]
    rfl
  exact congrArg
    (fun p : (r : Occurrence scheme) × Fin r.1.1.length ↦ p.1.1.1.get p.2)
    hboundary

/-- Helper for Definition 76.6: sign reversal leaves the unsigned boundary label
unchanged. -/
theorem reverseLabel_fst_eq (scheme : LabellingScheme α) (a : α)
    (region : Occurrence (scheme.reverseLabel a)) (edge : Fin region.1.1.length) :
    (region.1.1.get edge).1 =
      (((reverseLabelRegionEquiv scheme a).symm region).1.1.get
        (Fin.cast (reverseLabelRegion_length scheme a region) edge)).1 := by
  classical
  -- Project the first component and reduce the conditional sign reversal.
  rw [reverseLabelLetter_eq]
  unfold PolygonWord.reverseSignAt
  split
  · rfl
  · rfl

/-- Helper for Definition 76.6: sign reversal preserves and reflects equality of unsigned
labels at corresponding boundary positions. -/
theorem reverseLabel_fst_eq_iff (scheme : LabellingScheme α) (a : α)
    (region₁ region₂ : Occurrence (scheme.reverseLabel a))
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length) :
    (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ↔
      (((reverseLabelRegionEquiv scheme a).symm region₁).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁)).1 =
        (((reverseLabelRegionEquiv scheme a).symm region₂).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂)).1 := by
  -- Rewrite both unsigned labels to their original boundary positions.
  rw [reverseLabel_fst_eq, reverseLabel_fst_eq]

/-- Helper for Definition 76.6: simultaneously reversing two equal labels preserves and
reflects equality of their orientation bits. -/
theorem reverseLabel_snd_eq_iff_of_fst_eq (scheme : LabellingScheme α) (a : α)
    (region₁ region₂ : Occurrence (scheme.reverseLabel a))
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (hlabels :
      (((reverseLabelRegionEquiv scheme a).symm region₁).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁)).1 =
        (((reverseLabelRegionEquiv scheme a).symm region₂).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂)).1) :
    (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 ↔
      (((reverseLabelRegionEquiv scheme a).symm region₁).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁)).2 =
        (((reverseLabelRegionEquiv scheme a).symm region₂).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂)).2 := by
  classical
  -- Equal labels select the same branch of `reverseSignAt`; Boolean negation is injective.
  rw [reverseLabelLetter_eq, reverseLabelLetter_eq]
  unfold PolygonWord.reverseSignAt
  split
  · rename_i hfirst
    split
    · dsimp only [Prod.snd]
      constructor
      · exact Bool.not_inj
      · intro hsign
        exact congrArg (fun sign : Bool ↦ !sign) hsign
    · rename_i hsecond
      exact (hsecond (hlabels.symm.trans hfirst)).elim
  · rename_i hfirst
    split
    · rename_i hsecond
      exact (hfirst (hlabels.trans hsecond)).elim
    · rfl

/-- Helper for Definition 76.6: the affine parameter chosen by the edge relation is
unchanged when the signs of two equal labels are reversed simultaneously. -/
theorem reverseLabel_edgeParameter_eq (scheme : LabellingScheme α) (a : α)
    (region₁ region₂ : Occurrence (scheme.reverseLabel a))
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (hlabels :
      (((reverseLabelRegionEquiv scheme a).symm region₁).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁)).1 =
        (((reverseLabelRegionEquiv scheme a).symm region₂).1.1.get
          (Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂)).1)
    (t : unitInterval) :
    (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
      else unitInterval.symm t) =
      (if
        (((reverseLabelRegionEquiv scheme a).symm region₁).1.1.get
            (Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁)).2 =
          (((reverseLabelRegionEquiv scheme a).symm region₂).1.1.get
            (Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂)).2
        then t else unitInterval.symm t) := by
  -- Select the same branch on both sides using the verified sign equivalence.
  have hsigns :=
    reverseLabel_snd_eq_iff_of_fst_eq scheme a region₁ region₂ edge₁ edge₂ hlabels
  by_cases htarget : (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2
  · have horiginal := hsigns.mp htarget
    rw [if_pos htarget, if_pos horiginal]
  · have horiginal : ¬
        (((reverseLabelRegionEquiv scheme a).symm region₁).1.1.get
            (Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁)).2 =
          (((reverseLabelRegionEquiv scheme a).symm region₂).1.1.get
            (Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂)).2 := by
      intro horiginal
      exact htarget (hsigns.mpr horiginal)
    rw [if_neg htarget, if_neg horiginal]

/-- Helper for Definition 76.6: the sign-reversal source equivalence is continuous. -/
theorem continuous_reverseLabelSourceEquiv (regions : PolygonalRegions scheme) (a : α) :
    Continuous (reverseLabelSourceEquiv regions a) := by
  -- Check continuity independently on every original region summand.
  change @Continuous _ _ regions.sourceTopology
    (regions.reverseLabel a).sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let target := reverseLabelRegionEquiv scheme a region
  have hregion := (reverseLabelRegionEquiv scheme a).symm_apply_apply region
  have hcast := continuous_regionPointCast regions hregion
  have hinclusion :
      @Continuous ((regions.reverseLabel a).Point target) (regions.reverseLabel a).Source
        ((regions.reverseLabel a).topology target) (regions.reverseLabel a).sourceTopology
        (Sigma.mk target) :=
    continuous_iSup_rng (i := target) (f := Sigma.mk target)
      (continuous_coinduced_rng (f := Sigma.mk target))
  dsimp [reverseLabelSourceEquiv, Equiv.sigmaCongr]
  exact @Continuous.comp
    (regions.Point region) ((regions.reverseLabel a).Point target)
    (regions.reverseLabel a).Source (regions.topology region)
    ((regions.reverseLabel a).topology target) (regions.reverseLabel a).sourceTopology
    _ _ hinclusion hcast

/-- Helper for Definition 76.6: the inverse sign-reversal source equivalence is continuous. -/
theorem continuous_reverseLabelSourceEquiv_symm
    (regions : PolygonalRegions scheme) (a : α) :
    Continuous (reverseLabelSourceEquiv regions a).symm := by
  -- Each inverse component is the canonical inclusion of the original summand.
  change @Continuous _ _ (regions.reverseLabel a).sourceTopology regions.sourceTopology _
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  let original := (reverseLabelRegionEquiv scheme a).symm region
  letI : TopologicalSpace (regions.Point original) := regions.topology original
  have hinclusion : Continuous
      (Sigma.mk original : regions.Point original → regions.Source) :=
    continuous_iSup_rng (i := original) (f := Sigma.mk original)
      (continuous_coinduced_rng (f := Sigma.mk original))
  have hinverse :
      (reverseLabelSourceEquiv regions a).symm ∘ Sigma.mk region =
        (Sigma.mk original : regions.Point original → regions.Source) := by
    funext point
    dsimp only [Function.comp_apply]
    dsimp [reverseLabel, original] at point
    apply (reverseLabelSourceEquiv regions a).injective
    rw [(reverseLabelSourceEquiv regions a).apply_symm_apply]
    apply Sigma.ext
    · exact (reverseLabelRegionEquiv scheme a).apply_symm_apply region |>.symm
    · exact (cast_heq _ _).symm
  rw [hinverse]
  exact hinclusion

/-- Helper for Definition 76.6: sign reversal preserves the disjoint-union source topology. -/
theorem reverseLabelSourceEquiv_isOpen_iff (regions : PolygonalRegions scheme) (a : α)
    (s : Set (regions.reverseLabel a).Source) :
    IsOpen (reverseLabelSourceEquiv regions a ⁻¹' s) ↔ IsOpen s := by
  constructor
  · intro hopen
    have hpreimage :
        (reverseLabelSourceEquiv regions a).symm ⁻¹'
            (reverseLabelSourceEquiv regions a ⁻¹' s) = s := by
      ext point
      simp only [Set.mem_preimage, Equiv.apply_symm_apply]
    rw [← hpreimage]
    exact (continuous_reverseLabelSourceEquiv_symm regions a).isOpen_preimage _ hopen
  · intro hopen
    exact (continuous_reverseLabelSourceEquiv regions a).isOpen_preimage _ hopen

/-- Helper for Definition 76.6: sign reversal gives a homeomorphism of source spaces. -/
@[expose]
noncomputable def reverseLabelSourceHomeomorph
    (regions : PolygonalRegions scheme) (a : α) :
    regions.Source ≃ₜ (regions.reverseLabel a).Source :=
  (reverseLabelSourceEquiv regions a).toHomeomorph
    (reverseLabelSourceEquiv_isOpen_iff regions a)

/-- Helper for Definition 76.6: the sign-reversal source homeomorphism has the canonical
source equivalence as its forward map. -/
theorem reverseLabelSourceHomeomorph_apply
    (regions : PolygonalRegions scheme) (a : α) (x : regions.Source) :
    reverseLabelSourceHomeomorph regions a x = reverseLabelSourceEquiv regions a x := by
  -- The homeomorphism bundles the existing equivalence without changing its map.
  rfl

/-- Helper for Definition 76.6: the inverse sign-reversal source homeomorphism has the
canonical inverse source equivalence as its map. -/
theorem reverseLabelSourceHomeomorph_symm_apply
    (regions : PolygonalRegions scheme) (a : α) (x : (regions.reverseLabel a).Source) :
    (reverseLabelSourceHomeomorph regions a).symm x =
      (reverseLabelSourceEquiv regions a).symm x := by
  -- The homeomorphism bundles the existing equivalence without changing its inverse.
  rfl

/-- Reversing one label's signs preserves the direct labelled-edge relation. -/
theorem edgeRelated_reverseLabel_iff (regions : PolygonalRegions scheme) (a : α)
    (x y : regions.Source) :
    (regions.reverseLabel a).EdgeRelated (reverseLabelSourceEquiv regions a x)
        (reverseLabelSourceEquiv regions a y) ↔
      regions.EdgeRelated x y := by
  rw [edgeRelated_iff_exists_boundaryData, edgeRelated_iff_exists_boundaryData]
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let original₁ := (reverseLabelRegionEquiv scheme a).symm region₁
    let original₂ := (reverseLabelRegionEquiv scheme a).symm region₂
    let originalEdge₁ := Fin.cast (reverseLabelRegion_length scheme a region₁) edge₁
    let originalEdge₂ := Fin.cast (reverseLabelRegion_length scheme a region₂) edge₂
    have horiginalLabel :=
      (reverseLabel_fst_eq_iff scheme a region₁ region₂ edge₁ edge₂).mp hlabel
    have hparameter :=
      reverseLabel_edgeParameter_eq scheme a region₁ region₂ edge₁ edge₂ horiginalLabel t
    refine ⟨original₁, original₂, originalEdge₁, originalEdge₂, t,
      horiginalLabel, ?_, ?_⟩
    · -- Pull the first transported boundary point back to the original source.
      have hx' := congrArg (reverseLabelSourceEquiv regions a).symm hx
      simpa only [Equiv.symm_apply_apply, reverseLabelSourceEquiv_symm_edge] using hx'
    · -- Pull back the second point and rewrite the sign-dependent parameter.
      have hy' := congrArg (reverseLabelSourceEquiv regions a).symm hy
      simpa only [Equiv.symm_apply_apply, reverseLabelSourceEquiv_symm_edge,
        hparameter] using hy'
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabel, hx, hy⟩
    let mapped₁ := reverseLabelRegionEquiv scheme a region₁
    let mapped₂ := reverseLabelRegionEquiv scheme a region₂
    let mappedEdge₁ :=
      Fin.cast (reverseLabelRegionEquiv_length scheme a region₁).symm edge₁
    let mappedEdge₂ :=
      Fin.cast (reverseLabelRegionEquiv_length scheme a region₂).symm edge₂
    have hpreimageLabels :
        (((reverseLabelRegionEquiv scheme a).symm mapped₁).1.1.get
            (Fin.cast (reverseLabelRegion_length scheme a mapped₁) mappedEdge₁)).1 =
          (((reverseLabelRegionEquiv scheme a).symm mapped₂).1.1.get
            (Fin.cast (reverseLabelRegion_length scheme a mapped₂) mappedEdge₂)).1 := by
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simpa only [reverseLabelOriginalLetter_eq] using hlabel
    have hmappedLabel :=
      (reverseLabel_fst_eq_iff scheme a mapped₁ mapped₂ mappedEdge₁ mappedEdge₂).mpr
        hpreimageLabels
    have hparameter := reverseLabel_edgeParameter_eq scheme a mapped₁ mapped₂
      mappedEdge₁ mappedEdge₂ hpreimageLabels t
    refine ⟨mapped₁, mapped₂, mappedEdge₁, mappedEdge₂, t, hmappedLabel, ?_, ?_⟩
    · -- The forward source equivalence computes on the first boundary point.
      rw [hx, reverseLabelSourceEquiv_edge]
    · -- The second boundary computation uses the preserved sign-dependent parameter.
      rw [hy, reverseLabelSourceEquiv_edge]
      rw [hparameter]
      dsimp only [mapped₁, mapped₂, mappedEdge₁, mappedEdge₂]
      simp only [reverseLabelOriginalLetter_eq]

/-- Reversing one label's signs preserves realization and hence the pasting map. -/
theorem realizes_reverseLabel_iff (regions : PolygonalRegions scheme) (a : α)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X) :
    regions.Realizes q ↔
      (regions.reverseLabel a).Realizes
        (q ∘ (reverseLabelSourceEquiv regions a).symm) := by
  constructor
  · intro hrealizes
    constructor
    · -- Precompose with the inverse source homeomorphism.
      have hinverse :
          q ∘ (reverseLabelSourceHomeomorph regions a).symm =
            q ∘ (reverseLabelSourceEquiv regions a).symm := by
        funext point
        rw [Function.comp_apply, Function.comp_apply,
          reverseLabelSourceHomeomorph_symm_apply]
      rw [← hinverse]
      exact hrealizes.isQuotientMap.comp
        (reverseLabelSourceHomeomorph regions a).symm.isQuotientMap
    · intro x y
      simp only [Function.comp_apply]
      rw [hrealizes.fibers, identified_iff_generatedEdgeRelated,
        identified_iff_generatedEdgeRelated]
      simpa only [Equiv.apply_symm_apply] using
        (eqvGen_equiv_iff (reverseLabelSourceEquiv regions a)
          (edgeRelated_reverseLabel_iff regions a)
          ((reverseLabelSourceEquiv regions a).symm x)
          ((reverseLabelSourceEquiv regions a).symm y)).symm
  · intro hrealizes
    constructor
    · -- Compose back with the forward homeomorphism and cancel its inverse.
      simpa only [Function.comp_def, reverseLabelSourceHomeomorph_apply,
        Equiv.symm_apply_apply] using
        hrealizes.isQuotientMap.comp (reverseLabelSourceHomeomorph regions a).isQuotientMap
    · intro x y
      have hfibers := hrealizes.fibers
        (reverseLabelSourceEquiv regions a x) (reverseLabelSourceEquiv regions a y)
      have hmapped :
          q x = q y ↔
            (regions.reverseLabel a).Identified.r
              (reverseLabelSourceEquiv regions a x)
              (reverseLabelSourceEquiv regions a y) := by
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hfibers
      rw [identified_iff_generatedEdgeRelated] at hmapped
      rw [identified_iff_generatedEdgeRelated]
      exact hmapped.trans (eqvGen_equiv_iff (reverseLabelSourceEquiv regions a)
        (edgeRelated_reverseLabel_iff regions a) x y)


end LabellingScheme.PolygonalRegions
