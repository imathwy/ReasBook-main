module

public import Topology_Munkres_2000.Book.Definition_77_1.Proper
public import Topology_Munkres_2000.Book.Theorem_77_1.BoundaryPresentation

import all Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Definition_74_3
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

universe u v w

namespace LabellingScheme

/-- Helper for Theorem 78.2: enumerating the positions of one polygon word
recovers its multiset of unsigned labels. -/
theorem enumerateWordLabels (word : PolygonWord α) :
    (Finset.univ : Finset (Fin word.1.length)).val.map
        (fun edge ↦ (word.1.get edge).1) = word.1.map Prod.fst := by
  -- Rewrite finite-index enumeration as `List.ofFn`, then recover the original list.
  have hlist : List.ofFn (fun edge ↦ (word.1.get edge).1) =
      word.1.map Prod.fst := by
    calc
      _ = (List.ofFn word.1.get).map Prod.fst :=
        List.ofFn_comp' word.1.get Prod.fst
      _ = word.1.map Prod.fst := congrArg (List.map Prod.fst)
        (List.ofFn_get word.1)
  rw [Finset.val_univ_fin, Multiset.map_coe]
  exact congrArg (fun labels : List α ↦ (labels : Multiset α))
    (List.ofFn_eq_map.symm.trans hlist)

/-- Helper for Theorem 78.2: multiplicity two in a finite label enumeration
supplies a unique distinct equal-label mate for every position. -/
theorem uniqueDistinctMate_of_count_eq_two {P : Type*} [Fintype P]
    {A : Type*} [DecidableEq A] (label : P → A)
    (hcount : ∀ c ∈ (Finset.univ : Finset P).val.map label,
      Multiset.count c ((Finset.univ : Finset P).val.map label) = 2) :
    ∀ position, ∃! mate, mate ≠ position ∧ label mate = label position := by
  classical
  intro position
  have hmem : label position ∈ (Finset.univ : Finset P).val.map label :=
    Multiset.mem_map.mpr ⟨position, by simp, rfl⟩
  have hcard : (Finset.univ.filter fun candidate ↦
      label position = label candidate).card = 2 := by
    have hcountValue := hcount (label position) hmem
    rw [Multiset.count_map] at hcountValue
    exact hcountValue
  obtain ⟨first, second, hne, hfiber⟩ := Finset.card_eq_two.mp hcard
  have hposition : position = first ∨ position = second := by
    have : position ∈ Finset.univ.filter fun candidate ↦
        label position = label candidate := by simp
    rw [hfiber] at this
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hposition with rfl | rfl
  · refine ⟨second, ⟨hne.symm, ?_⟩, ?_⟩
    · have hsecond : second ∈ Finset.univ.filter fun candidate ↦
          label position = label candidate := by
        rw [hfiber]
        simp
      exact (Finset.mem_filter.mp hsecond).2.symm
    · intro candidate hcandidate
      have hcandidateMem : candidate ∈
          Finset.univ.filter fun other ↦ label position = label other := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          hcandidate.2.symm
      rw [hfiber] at hcandidateMem
      rcases Finset.mem_insert.mp hcandidateMem with heq | heq
      · exact (hcandidate.1 heq).elim
      · exact Finset.mem_singleton.mp heq
  · refine ⟨first, ⟨hne, ?_⟩, ?_⟩
    · have hfirst : first ∈ Finset.univ.filter fun candidate ↦
          label position = label candidate := by
        rw [hfiber]
        simp
      exact (Finset.mem_filter.mp hfirst).2.symm
    · intro candidate hcandidate
      have hcandidateMem : candidate ∈
          Finset.univ.filter fun other ↦ label position = label other := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          hcandidate.2.symm
      rw [hfiber] at hcandidateMem
      rcases Finset.mem_insert.mp hcandidateMem with heq | heq
      · exact heq
      · exact (hcandidate.1 (Finset.mem_singleton.mp heq)).elim

/-- Helper for Theorem 78.2: properness of a singleton scheme supplies the
unique distinct equal-label mate of every boundary position. -/
theorem uniqueBoundaryMate_of_properSingleton (word : PolygonWord α)
    (hproper : ({word} : LabellingScheme α).Proper) :
    ∀ edge : Fin word.1.length, ∃! mate : Fin word.1.length,
      mate ≠ edge ∧ (word.1.get mate).1 = (word.1.get edge).1 := by
  classical
  rw [proper_iff] at hproper
  apply uniqueDistinctMate_of_count_eq_two
    (fun edge : Fin word.1.length ↦ (word.1.get edge).1)
  intro c hc
  rw [enumerateWordLabels] at hc ⊢
  have hlabels : ({word} : LabellingScheme α).labels =
      word.1.map Prod.fst := by
    simp only [labels, Multiset.singleton_bind]
  rw [← hlabels]
  exact hproper c (hlabels.symm ▸ hc)

/-- Helper for Theorem 78.2: a signed polygon word gives the corresponding
labelled and oriented edge pasting on any cyclic polygon of the same length. -/
noncomputable def edgePastingOfWord (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) : poly.EdgePasting α :=
  CyclicPolygon.EdgePasting.ofSigns poly
    (fun edge ↦ (word.1.get edge).1) (fun edge ↦ (word.1.get edge).2)

/-- Helper for Theorem 78.2: the edge-pasting label constructed from a word
is its unsigned letter at that position. -/
theorem edgePastingOfWord_label (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) (edge : Fin word.1.length) :
    (edgePastingOfWord word poly).label edge = (word.1.get edge).1 := by
  -- `EdgePasting.ofSigns` stores the supplied label function unchanged.
  rfl

/-- Helper for Theorem 78.2: the edge-pasting sign constructed from a word
is its stored orientation sign at that position. -/
theorem edgePastingOfWord_sign (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) (edge : Fin word.1.length) :
    (edgePastingOfWord word poly).sign edge = (word.1.get edge).2 := by
  -- `EdgePasting.ofSigns` stores the supplied sign function unchanged.
  rfl

/-- Helper for Theorem 78.2: a proper singleton word constructs an edge
pasting whose edges are paired. -/
theorem edgePastingOfWord_pairsEdges (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length)
    (hproper : ({word} : LabellingScheme α).Proper) :
    (edgePastingOfWord word poly).PairsEdges := by
  rw [CyclicPolygon.EdgePasting.pairsEdges_iff]
  intro edge
  -- The edge labels are exactly the unsigned word letters used by properness.
  simpa only [edgePastingOfWord_label] using
    uniqueBoundaryMate_of_properSingleton word hproper edge

namespace PolygonalRegions

/-- Helper for Theorem 78.2: project the source of a singleton polygonal
family onto the fiber over its distinguished occurrence. -/
noncomputable def singletonSourceProjection (word : PolygonWord α)
    (regions : PolygonalRegions.{u, v} ({word} : LabellingScheme α)) :
    regions.Source →
      regions.Point (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word) :=
  fun point ↦ cast
    (congrArg regions.Point
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_eq word point.1))
    point.2

/-- Helper for Theorem 78.2: singleton-source projection fixes the
distinguished component pointwise. -/
theorem singletonSourceProjection_selected (word : PolygonWord α)
    (regions : PolygonalRegions.{u, v} ({word} : LabellingScheme α))
    (point : regions.Point
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word)) :
    regions.singletonSourceProjection word
        ⟨CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word, point⟩ =
      point := by
  -- Proof irrelevance reduces the self-transport in the selected fiber to `rfl`.
  unfold singletonSourceProjection
  change cast
    (congrArg regions.Point
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_eq word
        (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word))) point = point
  exact eq_of_heq ((cast_heq_iff_heq _ _ _).mpr HEq.rfl)

/-- Helper for Theorem 78.2: projection from a singleton indexed source to
its distinguished fiber is a homeomorphism. -/
theorem singletonSourceProjection_isHomeomorph (word : PolygonWord α)
    (regions : PolygonalRegions.{u, v} ({word} : LabellingScheme α)) :
    @IsHomeomorph regions.Source
      (regions.Point (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word))
      regions.sourceTopology
      (regions.topology (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word))
      (regions.singletonSourceProjection word) := by
  let selected := CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word
  letI : TopologicalSpace (regions.Point selected) := regions.topology selected
  apply (@isHomeomorph_iff_exists_inverse regions.Source
    (regions.Point selected) regions.sourceTopology (regions.topology selected)
    (regions.singletonSourceProjection word)).mpr
  constructor
  · -- Continuity is checked separately on every summand of the source topology.
    change @Continuous regions.Source (regions.Point selected)
      (⨆ region, TopologicalSpace.coinduced (Sigma.mk region)
        (regions.topology region)) (regions.topology selected)
      (regions.singletonSourceProjection word)
    rw [continuous_iSup_dom]
    intro region
    rw [continuous_coinduced_dom]
    have hregion :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_eq word region
    subst region
    have hprojection : regions.singletonSourceProjection word ∘ Sigma.mk selected =
        id := by
      funext point
      exact regions.singletonSourceProjection_selected word point
    rw [hprojection]
    exact @continuous_id (regions.Point selected) (regions.topology selected)
  · -- Insert a point into the distinguished summand and verify both inverses.
    have hinclusion :
        @Continuous (regions.Point selected) regions.Source
          (regions.topology selected) regions.sourceTopology
          (Sigma.mk selected) := by
      change @Continuous (regions.Point selected) regions.Source
        (regions.topology selected)
        (⨆ region, TopologicalSpace.coinduced (Sigma.mk region)
          (regions.topology region)) (Sigma.mk selected)
      exact continuous_iSup_rng (i := selected) (f := Sigma.mk selected)
        (continuous_coinduced_rng (f := Sigma.mk selected))
    refine ⟨Sigma.mk selected, ?_, ?_, hinclusion⟩
    · rintro ⟨region, point⟩
      have hregion :=
        CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_eq word region
      subst region
      rw [regions.singletonSourceProjection_selected word]
    · exact regions.singletonSourceProjection_selected word

/-- Helper for Theorem 78.2: a cyclic presentation of the sole region
identifies the whole singleton source with its filled cyclic polygon, preserving
each affine boundary parameter. -/
theorem exists_singletonSourceHomeomorph (word : PolygonWord α)
    (regions : PolygonalRegions.{u, v} ({word} : LabellingScheme α))
    (presentation : CyclicRegion regions
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word)) :
    ∃ H : regions.Source ≃ₜ presentation.polygon.region,
      ∀ (edge : Fin
          (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word).1.1.length)
        (t : unitInterval),
        H ⟨CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word,
            regions.edge
              (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word) edge t⟩ =
          presentation.polygon.boundaryToRegion
            (presentation.polygon.edgePoint edge t) := by
  let selected := CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word
  letI : TopologicalSpace (regions.Point selected) := regions.topology selected
  let projectionHomeomorph :
      @Homeomorph regions.Source (regions.Point selected)
        regions.sourceTopology (regions.topology selected) :=
    IsHomeomorph.homeomorph (regions.singletonSourceProjection word)
      (regions.singletonSourceProjection_isHomeomorph word)
  let H := projectionHomeomorph.trans presentation.homeomorph
  refine ⟨H, ?_⟩
  intro edge t
  -- Project to the unique component, then use its cyclic edge compatibility.
  simp only [H, Homeomorph.trans_apply, projectionHomeomorph,
    IsHomeomorph.homeomorph_apply]
  rw [regions.singletonSourceProjection_selected word]
  apply Subtype.ext
  exact (presentation.edgeCompatibility edge t).trans
    ((presentation.polygon.edgePoint_coe_eq_lineMap edge t).symm.trans
      (presentation.polygon.boundaryToRegion_coe
        (presentation.polygon.edgePoint edge t)).symm)

/-- Helper for Theorem 78.2: transporting the selected cyclic polygon to the
original word length preserves the singleton source and every boundary parameter. -/
theorem exists_singletonSourceHomeomorph_transportSides (word : PolygonWord α)
    (regions : PolygonalRegions.{u, v} ({word} : LabellingScheme α))
    (presentation : CyclicRegion regions
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word))
    (hlength :
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word).1.1.length =
        word.1.length) :
    ∃ H : regions.Source ≃ₜ
        (CyclicPolygon.transportSides hlength presentation.polygon).region,
      ∀ (edge : Fin
          (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word).1.1.length)
        (t : unitInterval),
        H ⟨CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word,
            regions.edge
              (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word) edge t⟩ =
          (CyclicPolygon.transportSides hlength presentation.polygon).boundaryToRegion
            ((CyclicPolygon.transportSides hlength presentation.polygon).edgePoint
              (Fin.cast hlength edge) t) := by
  obtain ⟨sourceHomeomorph, hsource⟩ :=
    regions.exists_singletonSourceHomeomorph word presentation
  obtain ⟨polygonHomeomorph, hpolygon⟩ :=
    CyclicPolygon.existsRegionHomeomorphPreservingEdgeParameters_of_eq
      hlength presentation.polygon
        (CyclicPolygon.transportSides hlength presentation.polygon)
  refine ⟨sourceHomeomorph.trans polygonHomeomorph, ?_⟩
  intro edge t
  -- First enter the selected polygon, then transport the common edge index.
  rw [Homeomorph.trans_apply, hsource edge t]
  have htransport := hpolygon (Fin.cast hlength edge) t
  have hedge : Fin.cast hlength.symm (Fin.cast hlength edge) = edge :=
    Fin.leftInverse_cast hlength edge
  rw [hedge] at htransport
  exact htransport

/-- Helper for Theorem 78.2: the singleton scheme's direct edge relation is
exactly the direct relation of the edge pasting read from its polygon word. -/
theorem edgeRelated_iff_edgePastingOfWord (word : PolygonWord α)
    (regions : PolygonalRegions.{u, v} ({word} : LabellingScheme α))
    (presentation : CyclicRegion regions
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word))
    (hlength :
      (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word).1.1.length =
        word.1.length)
    (H : regions.Source ≃ₜ
      (CyclicPolygon.transportSides hlength presentation.polygon).region)
    (hH : ∀ (edge : Fin
          (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word).1.1.length)
        (t : unitInterval),
      H ⟨CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word,
          regions.edge
            (CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word) edge t⟩ =
        (CyclicPolygon.transportSides hlength presentation.polygon).boundaryToRegion
          ((CyclicPolygon.transportSides hlength presentation.polygon).edgePoint
            (Fin.cast hlength edge) t))
    (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      (edgePastingOfWord word
        (CyclicPolygon.transportSides hlength presentation.polygon)).Related
          (H x) (H y) := by
  classical
  let selected := CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word
  let poly := CyclicPolygon.transportSides hlength presentation.polygon
  let pasting := edgePastingOfWord word poly
  rw [edgeRelated_iff_witness, pasting.related_iff_orientedPoints]
  constructor
  · rintro ⟨firstRegion, secondRegion, firstEdge, secondEdge, t,
      hlabels, hx, hy⟩
    have hfirstRegion :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_eq word firstRegion
    have hsecondRegion :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_eq word secondRegion
    subst firstRegion
    subst secondRegion
    let first := Fin.cast hlength firstEdge
    let second := Fin.cast hlength secondEdge
    have hselectedWord :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_word word selected
    have hlist : selected.1.1 = word.1 := congrArg Subtype.val hselectedWord
    have hfirstLetter : selected.1.1.get firstEdge = word.1.get first := by
      exact Renumbering.get_eq_of_list_eq_of_val_eq firstEdge first hlist rfl
    have hsecondLetter : selected.1.1.get secondEdge = word.1.get second := by
      exact Renumbering.get_eq_of_list_eq_of_val_eq secondEdge second hlist rfl
    have hlabel : pasting.label first = pasting.label second := by
      calc
        pasting.label first = (word.1.get first).1 :=
          edgePastingOfWord_label word poly first
        _ = (selected.1.1.get firstEdge).1 :=
          (congrArg Prod.fst hfirstLetter).symm
        _ = (selected.1.1.get secondEdge).1 := hlabels
        _ = (word.1.get second).1 := congrArg Prod.fst hsecondLetter
        _ = pasting.label second :=
          (edgePastingOfWord_label word poly second).symm
    refine ⟨first, second,
      CyclicPolygon.EdgePasting.correctedBoundaryParameter (pasting.sign first) t,
      hlabel, ?_, ?_⟩
    · -- The first scheme edge becomes the first positively oriented pasting edge.
      calc
        H x = H ⟨selected, regions.edge selected firstEdge t⟩ :=
          congrArg H hx
        _ = poly.boundaryToRegion (poly.edgePoint first t) := hH firstEdge t
        _ = pasting.orientedPoint first
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter
              (pasting.sign first) t) :=
          (pasting.orientedPoint_corrected first t).symm
    · -- The scheme's sign comparison gives the same positive parameter on edge two.
      let parameter :=
        if (selected.1.1.get firstEdge).2 = (selected.1.1.get secondEdge).2 then t
        else unitInterval.symm t
      have hparameter : parameter =
          if pasting.sign first = pasting.sign second then t
          else unitInterval.symm t := by
        dsimp only [parameter]
        rw [hfirstLetter, hsecondLetter,
          ← edgePastingOfWord_sign word poly first,
          ← edgePastingOfWord_sign word poly second]
      calc
        H y = H ⟨selected, regions.edge selected secondEdge parameter⟩ := by
          rw [hy]
        _ = poly.boundaryToRegion (poly.edgePoint second parameter) :=
          hH secondEdge parameter
        _ = pasting.orientedPoint second
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter
              (pasting.sign second) parameter) :=
          (pasting.orientedPoint_corrected second parameter).symm
        _ = pasting.orientedPoint second
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter
              (pasting.sign first) t) := by
          rw [hparameter]
          exact congrArg (pasting.orientedPoint second)
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter_pair
              (pasting.sign first) (pasting.sign second) t)
  · intro hrelated
    obtain ⟨first, second, t, hlabel, hx, hy⟩ := hrelated
    let firstEdge := Fin.cast hlength.symm first
    let secondEdge := Fin.cast hlength.symm second
    have hfirstIndex : Fin.cast hlength firstEdge = first :=
      Fin.rightInverse_cast hlength first
    have hsecondIndex : Fin.cast hlength secondEdge = second :=
      Fin.rightInverse_cast hlength second
    have hselectedWord :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_word word selected
    have hlist : selected.1.1 = word.1 := congrArg Subtype.val hselectedWord
    have hfirstLetter : selected.1.1.get firstEdge = word.1.get first := by
      have hlookup := Renumbering.get_eq_of_list_eq_of_val_eq
        firstEdge first hlist (by rfl)
      exact hlookup
    have hsecondLetter : selected.1.1.get secondEdge = word.1.get second := by
      have hlookup := Renumbering.get_eq_of_list_eq_of_val_eq
        secondEdge second hlist (by rfl)
      exact hlookup
    let firstParameter :=
      CyclicPolygon.EdgePasting.correctedBoundaryParameter (pasting.sign first) t
    refine ⟨selected, selected, firstEdge, secondEdge, firstParameter, ?_, ?_, ?_⟩
    · -- Equality of pasting labels is equality of the two scheme labels.
      calc
        (selected.1.1.get firstEdge).1 = (word.1.get first).1 :=
          congrArg Prod.fst hfirstLetter
        _ = pasting.label first :=
          (edgePastingOfWord_label word poly first).symm
        _ = pasting.label second := hlabel
        _ = (word.1.get second).1 := edgePastingOfWord_label word poly second
        _ = (selected.1.1.get secondEdge).1 :=
          (congrArg Prod.fst hsecondLetter).symm
    · -- Injectivity of `H` pulls the first oriented point back to the scheme edge.
      apply H.injective
      calc
        H x = pasting.orientedPoint first t := hx
        _ = pasting.orientedPoint first
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter
              (pasting.sign first) firstParameter) :=
          congrArg (pasting.orientedPoint first)
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter_involutive
              (pasting.sign first) t).symm
        _ = poly.boundaryToRegion (poly.edgePoint first firstParameter) :=
          pasting.orientedPoint_corrected first firstParameter
        _ = poly.boundaryToRegion
            (poly.edgePoint (Fin.cast hlength firstEdge) firstParameter) := by
          rw [hfirstIndex]
        _ = H ⟨selected, regions.edge selected firstEdge firstParameter⟩ :=
          (hH firstEdge firstParameter).symm
    · -- The paired-sign formula supplies the scheme parameter on the second edge.
      let secondParameter :=
        if (selected.1.1.get firstEdge).2 = (selected.1.1.get secondEdge).2 then
          firstParameter else unitInterval.symm firstParameter
      apply H.injective
      have hparameter : secondParameter =
          CyclicPolygon.EdgePasting.correctedBoundaryParameter
            (pasting.sign second) t := by
        dsimp only [secondParameter, firstParameter]
        rw [hfirstLetter, hsecondLetter,
          ← edgePastingOfWord_sign word poly first,
          ← edgePastingOfWord_sign word poly second]
        exact CyclicPolygon.EdgePasting.pairedCyclicParameter_eq
          (pasting.sign first) (pasting.sign second) t
      calc
        H y = pasting.orientedPoint second t := hy
        _ = pasting.orientedPoint second
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter
              (pasting.sign second)
              (CyclicPolygon.EdgePasting.correctedBoundaryParameter
                (pasting.sign second) t)) :=
          congrArg (pasting.orientedPoint second)
            (CyclicPolygon.EdgePasting.correctedBoundaryParameter_involutive
              (pasting.sign second) t).symm
        _ = poly.boundaryToRegion
            (poly.edgePoint second
              (CyclicPolygon.EdgePasting.correctedBoundaryParameter
                (pasting.sign second) t)) :=
          pasting.orientedPoint_corrected second _
        _ = poly.boundaryToRegion (poly.edgePoint second secondParameter) :=
          congrArg (fun parameter ↦
            poly.boundaryToRegion (poly.edgePoint second parameter)) hparameter.symm
        _ = poly.boundaryToRegion
            (poly.edgePoint (Fin.cast hlength secondEdge) secondParameter) := by
          rw [hsecondIndex]
        _ = H ⟨selected, regions.edge selected secondEdge secondParameter⟩ :=
          (hH secondEdge secondParameter).symm

/-- Helper for Theorem 78.2: a map realizing a labelled-edge quotient
identifies the canonical realization homeomorphically with its target. -/
theorem quotientHomeomorphOfRealizes {scheme : LabellingScheme α}
    (regions : PolygonalRegions.{u, v} scheme)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X)
    (hq : regions.Realizes q) : Nonempty (regions.Realization ≃ₜ X) := by
  -- Compare the defining setoid with the kernel setoid of the quotient map.
  let qContinuous : C(regions.Source, X) :=
    ⟨q, hq.isQuotientMap.continuous⟩
  let relationEquiv : regions.Realization ≃ₜ Quotient (Setoid.ker q) :=
    Homeomorph.Quotient.congrRight (r := regions.Identified)
      (r' := Setoid.ker q) (fun x y ↦ (hq.fibers x y).symm)
  -- The quotient-kernel theorem closes the comparison with the target.
  exact ⟨relationEquiv.trans
    (Topology.IsQuotientMap.homeomorph (f := qContinuous) hq.isQuotientMap)⟩

end PolygonalRegions

end LabellingScheme
