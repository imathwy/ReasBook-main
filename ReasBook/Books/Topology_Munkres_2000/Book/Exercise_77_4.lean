module

public import Topology_Munkres_2000.Book.Exercise_77_4.BoundaryWord
public import Topology_Munkres_2000.Book.Exercise_77_4.BoundedWordNormalization
public import Topology_Munkres_2000.Book.Theorem_75_5.Classification
public import Topology_Munkres_2000.Book.Theorem_77_1.BoundaryPresentation
import Topology_Munkres_2000.Book.Algorithm_76_3.Cancel
import Topology_Munkres_2000.Book.Definition_76_6.Permutation
import Topology_Munkres_2000.Book.Theorem_77_1.SourceComparison
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
import Mathlib.Data.List.Cycle

public section

universe u v w z

namespace LabellingScheme.PolygonalRegions

/-- Helper for Exercise 77.4: a source homeomorphism preserving and reflecting
direct edge pairings also preserves the generated identification relation. -/
private theorem identified_transportSourceHomeomorph_iff {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} leftScheme)
    (right : PolygonalRegions.{u, w} rightScheme)
    (e : left.Source ≃ₜ right.Source)
    (hrel : ∀ x y, right.EdgeRelated (e x) (e y) ↔ left.EdgeRelated x y)
    (x y : left.Source) :
    right.Identified.r (e x) (e y) ↔ left.Identified.r x y := by
  -- Lift the direct relation comparison through the equivalence closure once.
  rw [identified_iff_eqvGen, identified_iff_eqvGen]
  exact eqvGen_equiv_iff e.toEquiv hrel x y

/-- Helper for Exercise 77.4: realization by a quotient map transports in
both directions across a source homeomorphism that compares edge pairings. -/
private theorem Realizes.transportSourceHomeomorph_iff {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, v} leftScheme)
    (right : PolygonalRegions.{u, w} rightScheme)
    (e : left.Source ≃ₜ right.Source)
    (hrel : ∀ x y, right.EdgeRelated (e x) (e y) ↔ left.EdgeRelated x y)
    {X : Type z} [TopologicalSpace X] (q : left.Source → X) :
    left.Realizes q ↔ right.Realizes (q ∘ e.symm) := by
  constructor
  · intro hrealizes
    refine ⟨hrealizes.isQuotientMap.comp e.symm.isQuotientMap, ?_⟩
    intro x y
    -- Pull target points back, then rewrite their fibers by the generated relation.
    simp only [Function.comp_apply]
    rw [hrealizes.fibers]
    simpa only [Homeomorph.apply_symm_apply] using
      (identified_transportSourceHomeomorph_iff left right e hrel
        (e.symm x) (e.symm y)).symm
  · intro hrealizes
    constructor
    · -- Composing back with the forward homeomorphism cancels its inverse.
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
        hrealizes.isQuotientMap.comp e.isQuotientMap
    · intro x y
      -- Compare the fibers at the forward images and reflect identification.
      simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using
        (hrealizes.fibers (e x) (e y)).trans
          (identified_transportSourceHomeomorph_iff left right e hrel x y)

end LabellingScheme.PolygonalRegions

namespace LabellingScheme.Presents

/-- Helper for Exercise 77.4: fixed polygonal models related by an
edge-compatible source homeomorphism transport every presented target. -/
private theorem ofSourceHomeomorph {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, z} leftScheme)
    (right : PolygonalRegions.{u, z} rightScheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (e : left.Source ≃ₜ right.Source)
    (hrel : ∀ x y, right.EdgeRelated (e x) (e y) ↔ left.EdgeRelated x y)
    {X : Type z} [TopologicalSpace X]
    (hpresents : leftScheme.Presents X) : rightScheme.Presents X := by
  rw [LabellingScheme.presents_iff] at hpresents ⊢
  obtain ⟨original, horiginal, q, hrealizes⟩ := hpresents
  let qleft := q ∘
    (PolygonalRegions.presentationSourceHomeomorph
      original left horiginal hleft).symm
  have hleftRealizes : left.Realizes qleft := by
    -- First move the arbitrary presentation to the fixed left polygonal model.
    exact PolygonalRegions.realizesOfPresentationComparison
      original left horiginal hleft q hrealizes
  refine ⟨right, hright, qleft ∘ e.symm, ?_⟩
  -- Then cross the concrete source homeomorphism without reopening quotient details.
  exact (PolygonalRegions.Realizes.transportSourceHomeomorph_iff
    left right e hrel qleft).mp hleftRealizes

/-- Helper for Exercise 77.4: an edge-compatible homeomorphism between fixed
polygonal models preserves and reflects the spaces presented by their schemes. -/
private theorem transportSourceHomeomorph_iff {α : Type u}
    {leftScheme rightScheme : LabellingScheme α}
    (left : PolygonalRegions.{u, z} leftScheme)
    (right : PolygonalRegions.{u, z} rightScheme)
    (hleft : left.IsPolygonal) (hright : right.IsPolygonal)
    (e : left.Source ≃ₜ right.Source)
    (hrel : ∀ x y, right.EdgeRelated (e x) (e y) ↔ left.EdgeRelated x y)
    {X : Type z} [TopologicalSpace X] :
    leftScheme.Presents X ↔ rightScheme.Presents X := by
  constructor
  · -- The forward direction uses the supplied relation comparison directly.
    exact fun hpresents ↦
      ofSourceHomeomorph left right hleft hright e hrel hpresents
  · intro hpresents
    have hinverseRel : ∀ x y,
        left.EdgeRelated (e.symm x) (e.symm y) ↔ right.EdgeRelated x y := by
      intro x y
      -- Apply the original comparison to inverse images and cancel both maps.
      simpa only [Homeomorph.apply_symm_apply] using
        (hrel (e.symm x) (e.symm y)).symm
    exact ofSourceHomeomorph right left hright hleft e.symm hinverseRel hpresents

end LabellingScheme.Presents

namespace CyclicPolygon.EdgePasting

/-- Helper for Exercise 77.4: a transparent copy of the canonical boundary
polygon word used by the presentation bridge. -/
private def presentationBoundaryPolygonWord {n : ℕ} {S : Type u}
    {poly : CyclicPolygon n} (pasting : poly.EdgePasting S) :
    PolygonWord pasting.UsedLabel :=
  ⟨pasting.boundaryWord, pasting.boundaryWord_length.symm ▸ poly.three_le⟩

/-- Helper for Exercise 77.4: the transparent presentation word agrees with
the statement-facing canonical boundary word. -/
private theorem presentationBoundaryPolygonWord_eq_toPolygonWord
    {n : ℕ} {S : Type u} {poly : CyclicPolygon n}
    (pasting : poly.EdgePasting S) :
    presentationBoundaryPolygonWord pasting = pasting.toPolygonWord := by
  -- Both polygon words expose exactly the same signed boundary list.
  apply Subtype.ext
  rw [pasting.toPolygonWord_val]
  rfl

/-- Helper for Exercise 77.4: the transparent boundary polygon word has one
letter for each polygon edge. -/
private theorem presentationBoundaryPolygonWord_length {n : ℕ} {S : Type u}
    {poly : CyclicPolygon n} (pasting : poly.EdgePasting S) :
    (presentationBoundaryPolygonWord pasting).val.length = n := by
  -- Reduce to the edge pasting's boundary-word length formula.
  exact pasting.boundaryWord_length

/-- Helper for Exercise 77.4: each canonical boundary-word letter records the
label and orientation of its corresponding polygon edge. -/
private theorem presentationBoundaryPolygonWord_get {n : ℕ} {S : Type u}
    {poly : CyclicPolygon n} (pasting : poly.EdgePasting S) (i : Fin n) :
    (presentationBoundaryPolygonWord pasting).val.get
        (Fin.cast pasting.presentationBoundaryPolygonWord_length.symm i) =
      (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i) := by
  -- Unfold the local word and use the canonical boundary lookup formula.
  exact pasting.boundaryWord_get i

/-- Helper for Exercise 77.4: the canonical boundary polygon word presents the
edge-pasting realization. -/
private theorem presentationBoundaryPolygonWord_presents {n : ℕ} {S : Type u}
    {poly : CyclicPolygon n} (pasting : poly.EdgePasting S) :
    ({presentationBoundaryPolygonWord pasting} : LabellingScheme pasting.UsedLabel).Presents
        pasting.Realization := by
  -- Feed the length and lookup formulas to the generic singleton presentation bridge.
  exact pasting.singletonBoundaryWord_presents
    (presentationBoundaryPolygonWord pasting)
    pasting.presentationBoundaryPolygonWord_length
    pasting.presentationBoundaryPolygonWord_get

/-- Helper for Exercise 77.4: injectively mapping the labels of one polygon word
maps its unsigned-label multiset by the same embedding. -/
private theorem singletonMapLabels_labels {α β : Type*} (f : α ↪ β)
    (word : PolygonWord α) :
    ({word.mapLabels f} : LabellingScheme β).labels =
      (({word} : LabellingScheme α).labels.map f) := by
  -- Expand the singleton bind once; both sides then apply the same label map
  -- pointwise to the underlying boundary list.
  simp only [LabellingScheme.labels, Multiset.singleton_bind,
    PolygonWord.mapLabels_val, Multiset.map_coe, List.map_map,
    Function.comp_def]

/-- Helper for Exercise 77.4: coercing a mapped polygon-word boundary to a
multiset agrees with mapping the coerced original boundary. -/
private theorem mapLabels_coe {α β : Type*} (f : α ↪ β)
    (word : PolygonWord α) :
    ((word.mapLabels f).val : Multiset (β × Bool)) =
      (word.val : Multiset (α × Bool)).map
        (fun letter ↦ (f letter.1, letter.2)) := by
  -- The list coercion and multiset map share the same quotient representative.
  rw [PolygonWord.mapLabels_val]
  rfl

/-- Helper for Exercise 77.4: injectively mapping the labels of a singleton
polygon scheme preserves and reflects properness. -/
private theorem proper_mapLabels_singleton_iff {α β : Type*} (f : α ↪ β)
    (word : PolygonWord α) :
    ({word.mapLabels f} : LabellingScheme β).Proper ↔
      ({word} : LabellingScheme α).Proper := by
  classical
  rw [LabellingScheme.proper_iff, LabellingScheme.proper_iff]
  constructor
  · intro hmapped label hlabel
    -- Test the mapped properness equation at the image of the chosen source label.
    have hmappedLabel : f label ∈ ({word.mapLabels f} : LabellingScheme β).labels := by
      rw [singletonMapLabels_labels]
      exact Multiset.mem_map_of_mem f hlabel
    have hcount := hmapped (f label) hmappedLabel
    rw [singletonMapLabels_labels,
      Multiset.count_map_eq_count' f _ f.injective label] at hcount
    exact hcount
  · intro horiginal label hlabel
    -- Every mapped label has a unique source label; its multiplicity is unchanged.
    rw [singletonMapLabels_labels] at hlabel ⊢
    obtain ⟨sourceLabel, hsourceLabel, rfl⟩ := Multiset.mem_map.mp hlabel
    rw [Multiset.count_map_eq_count' f _ f.injective sourceLabel]
    exact horiginal sourceLabel hsourceLabel

/-- Helper for Exercise 77.4: injectively mapping polygon-word labels preserves
and reflects torus type. -/
private theorem torusType_mapLabels_iff {α β : Type*} (f : α ↪ β)
    (word : PolygonWord α) :
    (word.mapLabels f).TorusType ↔ word.TorusType := by
  classical
  have hletterInjective :
      Function.Injective (fun letter : α × Bool ↦ (f letter.1, letter.2)) := by
    rintro ⟨leftLabel, leftSign⟩ ⟨rightLabel, rightSign⟩ heq
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨f.injective heq.1, heq.2⟩
  rw [PolygonWord.torusType_iff_count, PolygonWord.torusType_iff_count]
  constructor
  · intro hmapped label hlabel sign
    -- Read the mapped signed count at `f label` and reflect it through injectivity.
    have hmappedLabel : f label ∈ ({word.mapLabels f} : LabellingScheme β).labels := by
      rw [singletonMapLabels_labels]
      exact Multiset.mem_map_of_mem f hlabel
    have hcount := hmapped (f label) hmappedLabel sign
    rw [mapLabels_coe,
      Multiset.count_map_eq_count'
        (fun letter : α × Bool ↦ (f letter.1, letter.2)) _ hletterInjective
        (label, sign)] at hcount
    exact hcount
  · intro horiginal label hlabel sign
    -- Choose the source of the mapped label and transport its signed count forward.
    rw [singletonMapLabels_labels] at hlabel
    obtain ⟨sourceLabel, hsourceLabel, rfl⟩ := Multiset.mem_map.mp hlabel
    have hcount := horiginal sourceLabel hsourceLabel sign
    rw [mapLabels_coe,
      Multiset.count_map_eq_count'
        (fun letter : α × Bool ↦ (f letter.1, letter.2)) _ hletterInjective
        (sourceLabel, sign)]
    exact hcount

/-- Helper for Exercise 77.4: injectively mapping polygon-word labels preserves
and reflects projective type. -/
private theorem projectiveType_mapLabels_iff {α β : Type*} (f : α ↪ β)
    (word : PolygonWord α) :
    (word.mapLabels f).ProjectiveType ↔ word.ProjectiveType := by
  -- Projective type is properness together with failure of torus type, and both
  -- constituents have already been transported through the embedding.
  rw [PolygonWord.projectiveType_iff, PolygonWord.projectiveType_iff,
    proper_mapLabels_singleton_iff, torusType_mapLabels_iff]

/-- Helper for Exercise 77.4: injectively extending the labels of the canonical
boundary word preserves its presentation of the edge-pasting realization. -/
private theorem presentationBoundaryPolygonWord_mapLabels_presents
    {n : ℕ} {S : Type u}
    {poly : CyclicPolygon n} (pasting : poly.EdgePasting S) {β : Type*}
    (f : pasting.UsedLabel ↪ β) :
    ({(presentationBoundaryPolygonWord pasting).mapLabels f} : LabellingScheme β).Presents
      pasting.Realization := by
  -- Map the known singleton presentation, then identify its mapped scheme with
  -- the singleton containing the mapped boundary word.
  have hmapped := LabellingScheme.Presents.mapLabels f
    (pasting.presentationBoundaryPolygonWord_presents)
  have hscheme :
      LabellingScheme.mapLabels f
          ({presentationBoundaryPolygonWord pasting} :
            LabellingScheme pasting.UsedLabel) =
        ({(presentationBoundaryPolygonWord pasting).mapLabels f} :
          LabellingScheme β) := by
    rw [LabellingScheme.mapLabels_singleton]
  rwa [hscheme] at hmapped


/-- Helper for Exercise 77.4: a proper presented polygon word with at most ten
letters has the bounded standard form determined by its orientation type. -/
private theorem presentedClassificationOfLengthAtMostTen
    {α : Type*} [Infinite α] {X : Type u} [TopologicalSpace X]
    (word : PolygonWord α)
    (hpresents : ({word} : LabellingScheme α).Presents X)
    (hproper : ({word} : LabellingScheme α).Proper)
    (hlength : word.val.length ≤ 10) :
    (word.TorusType ∧
        (Nonempty (X ≃ₜ StandardSphere 2) ∨
          ∃ (g : ℕ) (hg : 0 < g), g ≤ 2 ∧
            Nonempty (X ≃ₜ
              OrientableSurfacePresentation.nFoldTorus g hg))) ∨
      (word.ProjectiveType ∧
        (Nonempty (X ≃ₜ RealProjectivePlane) ∨
          ∃ (m : ℕ) (hm : 1 < m), m ≤ 5 ∧
            Nonempty (X ≃ₜ
              NonorientableSurfacePresentation.mFoldProjectivePlane m hm))) := by
  -- Route correction: the shared classifier owns the decreasing-rank
  -- normalization, avoiding the former cycle through its orientation adapters.
  have hfrontier := boundedCancellationFrontier word hproper hlength
  -- TODO: transport `hpresents` through the verified cancellation branch and
  -- through the Lemmas 77.1/77.4/77.5 equivalences in the adjacency branch.
  -- The missing prerequisite is a dependency-closed `Equivalent.presents_iff`;
  -- the earlier modules expose quotient homeomorphisms for elementary steps but
  -- do not yet expose polygonality preservation for `Flip` and `Permute`.
  sorry

/-- Helper for Exercise 77.4: the projective branch is the corresponding
projection of the shared bounded presented-word classifier. -/
private theorem presentedProjectiveClassificationOfLengthAtMostTen
    {α : Type*} [Infinite α] {X : Type u} [TopologicalSpace X]
    (word : PolygonWord α)
    (hpresents : ({word} : LabellingScheme α).Presents X)
    (h_type : word.ProjectiveType) (hlength : word.val.length ≤ 10) :
    Nonempty (X ≃ₜ RealProjectivePlane) ∨
      ∃ (m : ℕ) (hm : 1 < m), m ≤ 5 ∧
        Nonempty
          (X ≃ₜ NonorientableSurfacePresentation.mFoldProjectivePlane m hm) := by
  -- The projective hypothesis rules out the torus half of the shared result.
  have hproper := (PolygonWord.projectiveType_iff.mp h_type).1
  rcases presentedClassificationOfLengthAtMostTen
      word hpresents hproper hlength with
    ⟨htorus, _hclassification⟩ | ⟨_hprojective, hclassification⟩
  · exact ((PolygonWord.projectiveType_iff.mp h_type).2 htorus).elim
  · exact hclassification

/-- Helper for Exercise 77.4: the torus branch is the corresponding projection
of the shared bounded presented-word classifier. -/
private theorem presentedTorusClassificationOfLengthAtMostTen
    {α : Type*} [Infinite α] {X : Type u} [TopologicalSpace X]
    (word : PolygonWord α)
    (hpresents : ({word} : LabellingScheme α).Presents X)
    (h_type : word.TorusType) (hlength : word.val.length ≤ 10) :
    Nonempty (X ≃ₜ StandardSphere 2) ∨
      ∃ (g : ℕ) (hg : 0 < g), g ≤ 2 ∧
        Nonempty (X ≃ₜ OrientableSurfacePresentation.nFoldTorus g hg) := by
  -- The torus hypothesis rules out the projective half of the shared result.
  rcases presentedClassificationOfLengthAtMostTen
      word hpresents h_type.proper hlength with
    ⟨_htorus, hclassification⟩ | ⟨hprojective, _hclassification⟩
  · exact hclassification
  · exact ((PolygonWord.projectiveType_iff.mp hprojective).2 h_type).elim

/-- Exercise 77.4 (1). A projective-type proper labelling scheme on a ten-sided
polygon represents the projective plane or an `m`-fold projective plane with
`2 ≤ m ≤ 5`. -/
theorem projectiveTypeTenGonClassification {S : Type u}
    (poly : CyclicPolygon 10) (pasting : poly.EdgePasting S)
    (h_type : pasting.toPolygonWord.ProjectiveType) :
    Nonempty (pasting.Realization ≃ₜ RealProjectivePlane) ∨
      ∃ (m : ℕ) (hm : 1 < m), m ≤ 5 ∧
        Nonempty
          (pasting.Realization ≃ₜ
            NonorientableSurfacePresentation.mFoldProjectivePlane m hm) := by
  -- Extend the finite boundary-label type once, preserving the presentation,
  -- orientation tag, and its exact ten-letter rank.
  let labelEmbedding : pasting.UsedLabel ↪ pasting.UsedLabel ⊕ ℕ :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hworkingType :
      ((presentationBoundaryPolygonWord pasting).mapLabels
        labelEmbedding).ProjectiveType := by
    rw [projectiveType_mapLabels_iff,
      presentationBoundaryPolygonWord_eq_toPolygonWord]
    exact h_type
  have hworkingLength :
      ((presentationBoundaryPolygonWord pasting).mapLabels
        labelEmbedding).val.length ≤ 10 := by
    rw [PolygonWord.mapLabels_length,
      presentationBoundaryPolygonWord_length]
  have hworkingPresents :
      ({(presentationBoundaryPolygonWord pasting).mapLabels labelEmbedding} :
          LabellingScheme (pasting.UsedLabel ⊕ ℕ)).Presents pasting.Realization :=
    presentationBoundaryPolygonWord_mapLabels_presents pasting labelEmbedding
  -- The projective adapter selects the compatible half of the bounded classifier.
  exact presentedProjectiveClassificationOfLengthAtMostTen
    ((presentationBoundaryPolygonWord pasting).mapLabels labelEmbedding)
    hworkingPresents hworkingType hworkingLength

/-- Exercise 77.4 (2). A torus-type proper labelling scheme on a ten-sided
polygon represents the sphere or a `g`-fold torus with `1 ≤ g ≤ 2`. -/
theorem torusTypeTenGonClassification {S : Type u}
    (poly : CyclicPolygon 10) (pasting : poly.EdgePasting S)
    (h_type : pasting.toPolygonWord.TorusType) :
    Nonempty (pasting.Realization ≃ₜ StandardSphere 2) ∨
      ∃ (g : ℕ) (hg : 0 < g), g ≤ 2 ∧
        Nonempty
          (pasting.Realization ≃ₜ
            OrientableSurfacePresentation.nFoldTorus g hg) := by
  -- Extend the finite boundary-label type once, preserving the presentation,
  -- orientation tag, and its exact ten-letter rank.
  let labelEmbedding : pasting.UsedLabel ↪ pasting.UsedLabel ⊕ ℕ :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hworkingType :
      ((presentationBoundaryPolygonWord pasting).mapLabels labelEmbedding).TorusType := by
    rw [torusType_mapLabels_iff,
      presentationBoundaryPolygonWord_eq_toPolygonWord]
    exact h_type
  have hworkingLength :
      ((presentationBoundaryPolygonWord pasting).mapLabels
        labelEmbedding).val.length ≤ 10 := by
    rw [PolygonWord.mapLabels_length,
      presentationBoundaryPolygonWord_length]
  have hworkingPresents :
      ({(presentationBoundaryPolygonWord pasting).mapLabels labelEmbedding} :
          LabellingScheme (pasting.UsedLabel ⊕ ℕ)).Presents pasting.Realization :=
    presentationBoundaryPolygonWord_mapLabels_presents pasting labelEmbedding
  -- The torus adapter selects the compatible half of the bounded classifier.
  exact presentedTorusClassificationOfLengthAtMostTen
    ((presentationBoundaryPolygonWord pasting).mapLabels labelEmbedding)
    hworkingPresents hworkingType hworkingLength

end CyclicPolygon.EdgePasting
