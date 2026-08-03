module

public import Topology_Munkres_2000.Book.Definition_74_3.EdgePairing
public import Topology_Munkres_2000.Book.Definition_76_6.Realization
public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Definition_78_1.Triangulation
public import Topology_Munkres_2000.Book.Proposition_74_1
public import Topology_Munkres_2000.Book.Theorem_76_1
public import Topology_Munkres_2000.Book.Theorem_78_1
public import Topology_Munkres_2000.Book.Definition_77_1.Proper
public import Topology_Munkres_2000.Book.Theorem_78_2.BoundaryNormalization
public import Topology_Munkres_2000.Book.Theorem_78_2.CutProperPair
public import Topology_Munkres_2000.Book.Theorem_78_2.SingletonPresentation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

import all Topology_Munkres_2000.Book.Definition_74_3
import all Topology_Munkres_2000.Book.Definition_77_1.Proper
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Theorem_74_1

public section

universe u

namespace Fintype

universe v

/-- Helper for Theorem 78.2: a finite index type is equivalent to the occurrences
in the multiset obtained by mapping its universe, with the expected underlying value. -/
theorem exists_equivOccurrence_mapUniv {ι : Type u} [Fintype ι]
    {β : Type v} (f : ι → β) :
    ∃ e : ι ≃ @Multiset.ToType β (Classical.decEq β)
        ((Finset.univ : Finset ι).val.map f),
      ∀ i, (e i).1 = f i := by
  classical
  -- First identify each index with its unique occurrence in `Finset.univ.val`.
  let indexOccurrence : ι ≃ Multiset.ToType (Finset.univ : Finset ι).val := by
    refine
      { toFun := fun i ↦ ⟨i, ⟨0, by simp⟩⟩
        invFun := fun occurrence ↦ occurrence.1
        left_inv := fun _ ↦ rfl
        right_inv := ?_ }
    rintro ⟨i, occurrence⟩
    -- Every element occurs exactly once in the universe multiset.
    have hcount : Multiset.count i (Finset.univ : Finset ι).val = 1 := by simp
    have hzero : occurrence.1 = 0 := by
      have hlt : occurrence.1 < 1 := by simpa [hcount] using occurrence.2
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
    cases occurrence
    simp only at hzero
    subst hzero
    rfl
  -- Then transport occurrences through `Multiset.map`, retaining its computation rule.
  let occurrenceEquiv := indexOccurrence.trans
    (@Multiset.mapEquiv ι β (Classical.decEq ι) (Classical.decEq β)
      (Finset.univ : Finset ι).val f)
  refine ⟨occurrenceEquiv, ?_⟩
  intro i
  exact @Multiset.mapEquiv_apply ι β (Classical.decEq ι) (Classical.decEq β)
    (Finset.univ : Finset ι).val f (indexOccurrence i)

/-- Helper for Theorem 78.2: enumerating a finite dependent sum is the
concatenation of the enumerations of its fibers. -/
theorem map_univ_sigma {ι : Type u} {κ : ι → Type v} [Fintype ι]
    [∀ i, Fintype (κ i)] {β : Type*} (f : (i : ι) → κ i → β) :
    (Finset.univ : Finset ((i : ι) × κ i)).val.map
        (fun position ↦ f position.1 position.2) =
      (Finset.univ : Finset ι).val.bind fun i ↦
        (Finset.univ : Finset (κ i)).val.map (f i) := by
  -- Replace the universe of the sigma type by the sigma of the fiber universes.
  rw [← Finset.univ_sigma_univ]
  simp only [Finset.sigma, Multiset.sigma, Multiset.map_bind, Multiset.map_map,
    Function.comp_apply]

/-- Helper for Theorem 78.2: enumerating the indices of a list and retaining
the first coordinate gives the multiset underlying its mapped list. -/
theorem map_univ_fin_get_fst {A B : Type*} (word : List (A × B)) :
    (Finset.univ : Finset (Fin word.length)).val.map
        (fun edge ↦ (word.get edge).1) = word.map Prod.fst := by
  have hlist : List.ofFn (fun edge ↦ (word.get edge).1) =
      word.map Prod.fst := by
    calc
      _ = (List.ofFn word.get).map Prod.fst :=
        List.ofFn_comp' word.get Prod.fst
      _ = word.map Prod.fst := congrArg (List.map Prod.fst)
        (List.ofFn_get word)
  rw [Finset.val_univ_fin, Multiset.map_coe]
  exact congrArg (fun letters : List A ↦ (letters : Multiset A))
    (List.ofFn_eq_map.symm.trans hlist)

end Fintype

namespace List

/-- Helper for Theorem 78.2: splitting a list at a valid index isolates the
selected entry between its prefix and suffix. -/
theorem take_append_get_append_drop_succ {A : Type*} (word : List A)
    (edge : Fin word.length) :
    word.take edge.1 ++ [word.get edge] ++ word.drop (edge.1 + 1) = word := by
  -- Recombine the prefix through the selected entry, then append the suffix.
  rw [List.get_eq_getElem, List.take_append_getElem edge.2,
    List.take_append_drop]

/-- Helper for Theorem 78.2: after selecting one entry of a list of length at
least three, the cyclically adjacent remainder still has length at least two. -/
theorem two_le_length_drop_succ_append_take {A : Type*} (word : List A)
    (edge : Fin word.length) (hlength : 3 ≤ word.length) :
    2 ≤ (word.drop (edge.1 + 1) ++ word.take edge.1).length := by
  -- The two fragments contain every entry except the selected one.
  simp only [List.length_append, List.length_drop, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt edge.2)]
  omega

end List

namespace LabellingScheme

/-- Helper for Theorem 78.2: polygon words use the same classical equality
decision as the occurrence type that retains multiset multiplicities. -/
@[reducible] noncomputable local instance polygonWordDecidableEq :
    DecidableEq (PolygonWord α) :=
  Classical.decEq _

/-- Helper for Theorem 78.2: occurrences of a finite labelling scheme form a
finite type, with multiplicities retained. -/
@[reducible] noncomputable local instance occurrenceFintype
    (scheme : LabellingScheme α) :
    Fintype (Occurrence scheme) :=
  @Multiset.fintypeCoe _ (Classical.decEq _) scheme

/-- Helper for Theorem 78.2: enumerating the occurrences of a scheme recovers
the scheme with all word multiplicities. -/
theorem map_univ_occurrence (scheme : LabellingScheme α) :
    (Finset.univ : Finset (Occurrence scheme)).val.map
        (fun occurrence ↦ occurrence.1) = scheme := by
  -- This is the multiset-occurrence enumeration theorem in the local spelling.
  exact @Multiset.map_univ_coe _ (Classical.decEq _) scheme

/-- Helper for Theorem 78.2: binding a construction over every word occurrence
is the same as binding it over the scheme multiset. -/
theorem bind_univ_occurrence {β : Type*} (scheme : LabellingScheme α)
    (f : PolygonWord α → Multiset β) :
    (Finset.univ : Finset (Occurrence scheme)).val.bind
        (fun occurrence ↦ f occurrence.1) = scheme.bind f := by
  -- Move the occurrence projection into a map, then use its enumeration law.
  calc
    _ = ((Finset.univ : Finset (Occurrence scheme)).val.map
        (fun occurrence ↦ occurrence.1)).bind f :=
      (Multiset.bind_map _ _ _).symm
    _ = scheme.bind f := congrArg (fun words ↦ words.bind f)
      (map_univ_occurrence scheme)

/-- Helper for Theorem 78.2: a finite labeling has a unique distinct mate at
every position exactly when every occurring label has multiplicity two. -/
theorem uniqueDistinctMate_iff_count_eq_two {P : Type*} [Fintype P]
    {A : Type*} [DecidableEq A] (label : P → A) :
    (∀ position, ∃! mate, mate ≠ position ∧ label mate = label position) ↔
      ∀ c ∈ (Finset.univ : Finset P).val.map label,
        Multiset.count c ((Finset.univ : Finset P).val.map label) = 2 := by
  classical
  constructor
  · intro hmates c hc
    obtain ⟨position, _, hposition⟩ := Multiset.mem_map.mp hc
    obtain ⟨mate, hmate, hunique⟩ := hmates position
    have hfiber : (Finset.univ.filter fun candidate ↦ c = label candidate) =
        {position, mate} := by
      ext candidate
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hcandidate
        by_cases heq : candidate = position
        · exact Or.inl heq
        · right
          apply hunique candidate
          exact ⟨heq, hcandidate.symm.trans hposition.symm⟩
      · rintro (rfl | rfl)
        · exact hposition.symm
        · exact hposition.symm.trans hmate.2.symm
    rw [Multiset.count_map, ← Finset.filter_val, hfiber]
    exact Finset.card_pair hmate.1.symm
  · intro hcount position
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
        rcases (Finset.mem_insert.mp hcandidateMem) with heq | heq
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
        rcases (Finset.mem_insert.mp hcandidateMem) with heq | heq
        · exact heq
        · exact (hcandidate.1 (Finset.mem_singleton.mp heq)).elim

/-- Helper for Theorem 78.2: enumerating all dependent letter positions of a
scheme gives exactly its multiset of unsigned labels. -/
theorem map_univ_letterLabels_eq_labels (scheme : LabellingScheme α) :
    (Finset.univ : Finset
      ((region : Occurrence scheme) × Fin region.1.1.length)).val.map
        (fun position ↦ (position.1.1.1.get position.2).1) = scheme.labels := by
  classical
  -- First enumerate the dependent sum fiberwise, keeping `Occurrence` opaque.
  calc
    _ = (Finset.univ : Finset (Occurrence scheme)).val.bind (fun region ↦
        (Finset.univ : Finset (Fin region.1.1.length)).val.map
          (fun edge ↦ (region.1.1.get edge).1)) :=
      Fintype.map_univ_sigma
        (fun (region : Occurrence scheme)
          (edge : Fin region.1.1.length) ↦ (region.1.1.get edge).1)
    _ = scheme.labels := by
      -- Normalize each finite edge enumeration to its boundary list.
      calc
        _ = (Finset.univ : Finset (Occurrence scheme)).val.bind
            (fun region ↦ region.1.1.map Prod.fst) := by
          apply Multiset.bind_congr
          intro region _
          exact Fintype.map_univ_fin_get_fst region.1.1
        _ = scheme.bind (fun word ↦ word.1.map Prod.fst) :=
          bind_univ_occurrence scheme
            (fun word : PolygonWord α ↦ (word.1.map Prod.fst : Multiset α))
        _ = scheme.labels := by
          unfold LabellingScheme.labels
          rfl

/-- Helper for Theorem 78.2: every signed letter occurrence has a unique distinct
occurrence carrying the same underlying label. -/
def PairsLetters (scheme : LabellingScheme α) : Prop :=
  ∀ region edge,
    ∃! mate : (other : Occurrence scheme) × Fin other.1.1.length,
      mate ≠ ⟨region, edge⟩ ∧
        (mate.1.1.1.get mate.2).1 = (region.1.1.get edge).1

/-- Helper for Theorem 78.2: paired letters are characterized by their unique
distinct equal-label mates. -/
theorem pairsLetters_iff (scheme : LabellingScheme α) :
    scheme.PairsLetters ↔
      ∀ region edge,
        ∃! mate : (other : Occurrence scheme) × Fin other.1.1.length,
          mate ≠ ⟨region, edge⟩ ∧
            (mate.1.1.1.get mate.2).1 = (region.1.1.get edge).1 := by
  -- The quantified mate property is exactly the definition of `PairsLetters`.
  rfl

/-- Helper for Theorem 78.2: a paired letter has a distinct occurrence with the
same underlying label. -/
theorem exists_distinctMate_of_pairsLetters {scheme : LabellingScheme α}
    (hpairs : scheme.PairsLetters) (region : Occurrence scheme)
    (edge : Fin region.1.1.length) :
    ∃ mate : (other : Occurrence scheme) × Fin other.1.1.length,
      mate ≠ ⟨region, edge⟩ ∧
        (mate.1.1.1.get mate.2).1 = (region.1.1.get edge).1 := by
  -- Forget uniqueness from the mate supplied by the pairing invariant.
  obtain ⟨mate, hmate, _⟩ := hpairs region edge
  exact ⟨mate, hmate⟩

/-- Helper for Theorem 78.2: two distinct equal-label mates of the same letter
occurrence coincide. -/
theorem mate_eq_of_pairsLetters {scheme : LabellingScheme α}
    (hpairs : scheme.PairsLetters) (region : Occurrence scheme)
    (edge : Fin region.1.1.length)
    {first second : (other : Occurrence scheme) × Fin other.1.1.length}
    (hfirst : first ≠ ⟨region, edge⟩ ∧
      (first.1.1.1.get first.2).1 = (region.1.1.get edge).1)
    (hsecond : second ≠ ⟨region, edge⟩ ∧
      (second.1.1.1.get second.2).1 = (region.1.1.get edge).1) :
    first = second := by
  -- Compare both candidates with the unique mate supplied by `PairsLetters`.
  obtain ⟨mate, _, hunique⟩ := hpairs region edge
  exact (hunique first hfirst).trans (hunique second hsecond).symm

/-- Helper for Theorem 78.2: occurrence-wise pairing is equivalent to the
count-based properness invariant. -/
theorem pairsLetters_iff_proper (scheme : LabellingScheme α) :
    scheme.PairsLetters ↔ scheme.Proper := by
  classical
  rw [LabellingScheme.proper_iff,
    ← scheme.map_univ_letterLabels_eq_labels]
  -- Curry the generic finite-position characterization to region and edge indices.
  let label : ((region : Occurrence scheme) × Fin region.1.1.length) → α :=
    fun position ↦ (position.1.1.1.get position.2).1
  constructor
  · intro hpairs
    apply (uniqueDistinctMate_iff_count_eq_two label).mp
    intro position
    exact hpairs position.1 position.2
  · intro hcount region edge
    have hmates := (uniqueDistinctMate_iff_count_eq_two label).mpr hcount
    exact hmates ⟨region, edge⟩

/-- Helper for Theorem 78.2: the canonical edge pasting whose labels are equality
classes of boundary positions carrying the same unsigned word label. -/
noncomputable def edgePastingOfWordLabelClasses (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) :
    poly.EdgePasting
      (Quotient (Setoid.ker (fun edge : Fin word.1.length ↦
        (word.1.get edge).1))) :=
  CyclicPolygon.EdgePasting.ofSigns poly
    (fun edge ↦ Quotient.mk'' edge) (fun edge ↦ (word.1.get edge).2)

/-- Helper for Theorem 78.2: the canonical boundary-position pasting stores
the quotient class of each edge as its label. -/
theorem edgePastingOfWordLabelClasses_label (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) (edge : Fin word.1.length) :
    (edgePastingOfWordLabelClasses word poly).label edge = Quotient.mk'' edge := by
  -- `EdgePasting.ofSigns` stores the supplied quotient-label function unchanged.
  rfl

/-- Helper for Theorem 78.2: the canonical boundary-position pasting retains
the orientation sign stored in the polygon word. -/
theorem edgePastingOfWordLabelClasses_sign (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) (edge : Fin word.1.length) :
    (edgePastingOfWordLabelClasses word poly).sign edge = (word.1.get edge).2 := by
  -- `EdgePasting.ofSigns` stores the supplied sign function unchanged.
  rfl

/-- Helper for Theorem 78.2: two canonical boundary-position classes agree
exactly when the corresponding unsigned word labels agree. -/
theorem edgePastingOfWordLabelClasses_label_eq_iff (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) (i j : Fin word.1.length) :
    (edgePastingOfWordLabelClasses word poly).label i =
        (edgePastingOfWordLabelClasses word poly).label j ↔
      (word.1.get i).1 = (word.1.get j).1 := by
  -- Normalize both stored labels before applying the quotient kernel law.
  rw [edgePastingOfWordLabelClasses_label,
    edgePastingOfWordLabelClasses_label, Quotient.eq'']
  rfl

/-- Helper for Theorem 78.2: unique distinct equal-label mates in a polygon word
pair all edges of its canonical boundary-position pasting. -/
theorem edgePastingOfWordLabelClasses_pairsEdges_of_uniqueMates
    (word : PolygonWord α) (poly : CyclicPolygon word.1.length)
    (hmates : ∀ edge : Fin word.1.length, ∃! mate : Fin word.1.length,
      mate ≠ edge ∧ (word.1.get mate).1 = (word.1.get edge).1) :
    (edgePastingOfWordLabelClasses word poly).PairsEdges := by
  rw [CyclicPolygon.EdgePasting.pairsEdges_iff]
  intro edge
  -- The quotient-label equality law converts the word mate directly to an edge mate.
  simpa only [edgePastingOfWordLabelClasses_label_eq_iff] using hmates edge

/-- Helper for Theorem 78.2: properness of a singleton polygon word pairs every
edge of its canonical boundary-position pasting. -/
theorem edgePastingOfWordLabelClasses_pairsEdges (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length)
    (hproper : ({word} : LabellingScheme α).Proper) :
    (edgePastingOfWordLabelClasses word poly).PairsEdges := by
  apply edgePastingOfWordLabelClasses_pairsEdges_of_uniqueMates
  classical
  rw [proper_iff] at hproper
  apply (uniqueDistinctMate_iff_count_eq_two
    (fun edge : Fin word.1.length ↦ (word.1.get edge).1)).mpr
  intro label hlabel
  -- Enumerate the finite boundary positions and identify the singleton scheme labels.
  rw [Fintype.map_univ_fin_get_fst] at hlabel ⊢
  have hlabels : ({word} : LabellingScheme α).labels =
      word.1.map Prod.fst := by
    simp only [labels, Multiset.singleton_bind]
  rw [← hlabels]
  exact hproper label (hlabels.symm ▸ hlabel)

/-- Helper for Theorem 78.2: edge pastings on the same polygon with the same
sign at an edge have the same oriented point there. -/
theorem CyclicPolygon.EdgePasting.orientedPoint_eq_of_sign_eq
    {poly : CyclicPolygon n} {A B : Type*}
    (first : poly.EdgePasting A) (second : poly.EdgePasting B)
    (edge : Fin n) (t : unitInterval)
    (hsign : first.sign edge = second.sign edge) :
    first.orientedPoint edge t = second.orientedPoint edge t := by
  have horientation : first.orientation edge = second.orientation edge := by
    calc
      first.orientation edge = poly.signedOrientation edge (first.sign edge) :=
        first.orientation_eq edge
      _ = poly.signedOrientation edge (second.sign edge) :=
        congrArg (poly.signedOrientation edge) hsign
      _ = second.orientation edge := (second.orientation_eq edge).symm
  -- Forget the carrier-membership proofs and compare the common affine point.
  apply Subtype.ext
  rw [first.orientedPoint_apply, second.orientedPoint_apply,
    first.includePoint_coe, second.includePoint_coe,
    OrientedSegment.point_coe, OrientedSegment.point_coe, horientation]

/-- Helper for Theorem 78.2: replacing raw word labels by their equality
classes does not change the direct edge-pasting relation. -/
theorem edgePastingOfWordLabelClasses_related_iff (word : PolygonWord α)
    (poly : CyclicPolygon word.1.length) (x y : poly.region) :
    (edgePastingOfWordLabelClasses word poly).Related x y ↔
      (edgePastingOfWord word poly).Related x y := by
  -- Both pastings use the same oriented edges, and quotient equality records
  -- exactly equality of the underlying unsigned labels.
  rw [(edgePastingOfWordLabelClasses word poly).related_iff_orientedPoints,
    (edgePastingOfWord word poly).related_iff_orientedPoints]
  constructor
  · rintro ⟨first, second, t, hlabel, hx, hy⟩
    have hrawLabel :
        (edgePastingOfWord word poly).label first =
          (edgePastingOfWord word poly).label second := by
      simpa only [edgePastingOfWord_label] using
        (edgePastingOfWordLabelClasses_label_eq_iff word poly first second).mp
          hlabel
    have hfirstPoint := CyclicPolygon.EdgePasting.orientedPoint_eq_of_sign_eq
      (edgePastingOfWordLabelClasses word poly) (edgePastingOfWord word poly)
      first t
      ((edgePastingOfWordLabelClasses_sign word poly first).trans
        (edgePastingOfWord_sign word poly first).symm)
    have hsecondPoint := CyclicPolygon.EdgePasting.orientedPoint_eq_of_sign_eq
      (edgePastingOfWordLabelClasses word poly) (edgePastingOfWord word poly)
      second t
      ((edgePastingOfWordLabelClasses_sign word poly second).trans
        (edgePastingOfWord_sign word poly second).symm)
    exact ⟨first, second, t, hrawLabel, hx.trans hfirstPoint,
      hy.trans hsecondPoint⟩
  · rintro ⟨first, second, t, hlabel, hx, hy⟩
    have hwordLabel : (word.1.get first).1 = (word.1.get second).1 := by
      simpa only [edgePastingOfWord_label] using hlabel
    have hfirstPoint := CyclicPolygon.EdgePasting.orientedPoint_eq_of_sign_eq
      (edgePastingOfWordLabelClasses word poly) (edgePastingOfWord word poly)
      first t
      ((edgePastingOfWordLabelClasses_sign word poly first).trans
        (edgePastingOfWord_sign word poly first).symm)
    have hsecondPoint := CyclicPolygon.EdgePasting.orientedPoint_eq_of_sign_eq
      (edgePastingOfWordLabelClasses word poly) (edgePastingOfWord word poly)
      second t
      ((edgePastingOfWordLabelClasses_sign word poly second).trans
        (edgePastingOfWord_sign word poly second).symm)
    exact ⟨first, second, t,
      (edgePastingOfWordLabelClasses_label_eq_iff word poly first second).mpr
        hwordLabel, hx.trans hfirstPoint.symm, hy.trans hsecondPoint.symm⟩

/-- Helper for Theorem 78.2: every polygonal component has a point. -/
theorem PolygonalRegions.nonemptyPoint_of_isPolygonal
    {scheme : LabellingScheme α} (regions : PolygonalRegions scheme)
    (hpolygonal : regions.IsPolygonal) (region : Occurrence scheme) :
    Nonempty (regions.Point region) := by
  obtain ⟨cyclicRegion⟩ :=
    (PolygonalRegions.isPolygonal_iff regions).mp hpolygonal region
  letI : TopologicalSpace (regions.Point region) := regions.topology region
  have hpositive : 0 < region.1.1.length := lt_of_lt_of_le (by omega) region.1.2
  let firstVertex : Fin region.1.1.length := ⟨0, hpositive⟩
  -- Pull a vertex of the model polygon back to the presented component.
  exact ⟨cyclicRegion.homeomorph.symm
    (cyclicRegion.polygon.vertexPoint firstVertex)⟩

/-- Helper for Theorem 78.2: if a connected space has a presentation with at
least two regions, some equal label occurs in two distinct regions. -/
theorem exists_equalLabel_in_distinctRegions_of_connectedPresentation
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (scheme : LabellingScheme α) (hpresents : scheme.Presents X)
    (hcard : 1 < scheme.card) :
    ∃ (first second : Occurrence scheme), first ≠ second ∧
      ∃ (firstEdge : Fin first.1.1.length)
        (secondEdge : Fin second.1.1.length),
        (first.1.1.get firstEdge).1 = (second.1.1.get secondEdge).1 := by
  classical
  rw [LabellingScheme.presents_iff] at hpresents
  obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
  letI : ∀ region, TopologicalSpace (regions.Point region) :=
    fun region ↦ regions.topology region
  by_contra hcross
  have hsameRegion {first second : Occurrence scheme}
      {firstEdge : Fin first.1.1.length} {secondEdge : Fin second.1.1.length}
      (hlabel : (first.1.1.get firstEdge).1 =
        (second.1.1.get secondEdge).1) : first = second := by
    by_contra hne
    exact hcross ⟨first, second, hne, firstEdge, secondEdge, hlabel⟩
  have hidentifiedRegion {x y : regions.Source}
      (hxy : regions.Identified.r x y) : x.1 = y.1 := by
    induction hxy with
    | rel x y hxy =>
        unfold PolygonalRegions.EdgeRelated at hxy
        obtain ⟨first, second, firstEdge, secondEdge, t, hlabel, hx, hy⟩ := hxy
        subst x
        subst y
        exact hsameRegion hlabel
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ hxy hyz => exact hxy.trans hyz
  let sourceSection : X → regions.Source :=
    Function.surjInv hrealizes.isQuotientMap.surjective
  let component : X → Occurrence scheme := fun x ↦ (sourceSection x).1
  have hcomponentComp : component ∘ q = fun x : regions.Source ↦ x.1 := by
    funext x
    apply hidentifiedRegion
    apply (hrealizes.fibers (sourceSection (q x)) x).mp
    exact Function.surjInv_eq hrealizes.isQuotientMap.surjective (q x)
  letI : TopologicalSpace (Occurrence scheme) := ⊥
  letI : DiscreteTopology (Occurrence scheme) := ⟨rfl⟩
  have hsourceComponent : Continuous (fun x : regions.Source ↦ x.1) := by
    rw [continuous_sigma_iff]
    intro region
    exact continuous_const
  have hcomponentContinuous : Continuous component := by
    rw [hrealizes.isQuotientMap.continuous_iff]
    rw [hcomponentComp]
    exact hsourceComponent
  have hoccurrenceCard : 1 < Fintype.card (Occurrence scheme) := by
    simpa only [Occurrence, Multiset.card_coe] using hcard
  obtain ⟨first, second, hne⟩ :=
    Fintype.exists_pair_of_one_lt_card hoccurrenceCard
  let firstPoint : regions.Source :=
    ⟨first, Classical.choice (regions.nonemptyPoint_of_isPolygonal hpolygonal first)⟩
  let secondPoint : regions.Source :=
    ⟨second, Classical.choice (regions.nonemptyPoint_of_isPolygonal hpolygonal second)⟩
  have hconstant := TotallyDisconnectedSpace.eq_of_continuous component
    hcomponentContinuous (q firstPoint) (q secondPoint)
  apply hne
  calc
    first = (fun x : regions.Source ↦ x.1) firstPoint := rfl
    _ = component (q firstPoint) := congrFun hcomponentComp firstPoint |>.symm
    _ = component (q secondPoint) := hconstant
    _ = (fun x : regions.Source ↦ x.1) secondPoint :=
      congrFun hcomponentComp secondPoint
    _ = second := rfl

/-- Helper for Theorem 78.2: a presentation of a nonempty space contains at
least one polygon word. -/
theorem one_le_card_of_presents {X : Type*} [TopologicalSpace X] [Nonempty X]
    (scheme : LabellingScheme α) (hpresents : scheme.Presents X) :
    1 ≤ scheme.card := by
  classical
  rw [LabellingScheme.presents_iff] at hpresents
  obtain ⟨regions, _, q, hrealizes⟩ := hpresents
  obtain ⟨source, _⟩ := hrealizes.isQuotientMap.surjective (Classical.choice inferInstance)
  have hwordMem : source.1.1 ∈ scheme :=
    Multiset.count_pos.mp source.1.2.pos
  exact Nat.succ_le_iff.mpr
    (Multiset.card_pos_iff_exists_mem.mpr ⟨source.1.1, hwordMem⟩)

/-- Helper for Theorem 78.2: two distinct multiset occurrences can be removed
in order even when they carry equal polygon-word values. -/
theorem exists_twoOccurrenceDecomposition (scheme : LabellingScheme α)
    {first second : Occurrence scheme} (hne : first ≠ second) :
    ∃ rest : LabellingScheme α,
      scheme = first.1 ::ₘ second.1 ::ₘ rest := by
  classical
  have hsecondMem : second.1 ∈ scheme.erase first.1 := by
    by_cases hvalue : second.1 = first.1
    · have hindex : second.2.1 ≠ first.2.1 := by
        intro hindex
        apply hne
        apply Sigma.ext hvalue.symm
        exact Fin.heq_ext_iff
          (congrArg (fun word : PolygonWord α ↦ scheme.count word) hvalue.symm) |>.mpr
            hindex.symm
      have hcount : 2 ≤ scheme.count first.1 := by
        have hfirstLt := first.2.2
        have hcountEq : scheme.count second.1 = scheme.count first.1 :=
          congrArg (fun word : PolygonWord α ↦ scheme.count word) hvalue
        have hsecondLt : second.2.1 < scheme.count first.1 :=
          lt_of_lt_of_eq second.2.2 hcountEq
        omega
      rw [hvalue, ← Multiset.count_pos, Multiset.count_erase_self]
      omega
    · exact (Multiset.mem_erase_of_ne hvalue).mpr
        (Multiset.coe_mem (x := second))
  refine ⟨(scheme.erase first.1).erase second.1, ?_⟩
  -- Remove the two occurrence slots successively; multiplicity is retained by `erase`.
  calc
    scheme = first.1 ::ₘ scheme.erase first.1 :=
      (Multiset.cons_erase (Multiset.coe_mem (x := first))).symm
    _ = first.1 ::ₘ second.1 ::ₘ (scheme.erase first.1).erase second.1 :=
      congrArg (Multiset.cons first.1) (Multiset.cons_erase hsecondMem).symm

/-- Helper for Theorem 78.2: cyclically moving an initial boundary fragment
to the end does not change the multiset of unsigned labels. -/
theorem labels_appendSwap (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length) :
    labels (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest) =
      labels (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest) := by
  classical
  -- Count each unsigned label; the two boundary fragments merely exchange order.
  ext a
  unfold labels
  simp only [Multiset.cons_bind, Multiset.count_add, List.map_append,
    Multiset.coe_count, List.count_append]
  omega

/-- Helper for Theorem 78.2: formally inverting one polygon word preserves all
unsigned-label multiplicities in the surrounding scheme. -/
theorem labels_formalInverseCons (word : PolygonWord α)
    (rest : LabellingScheme α) :
    labels (word.formalInverse ::ₘ rest) = labels (word ::ₘ rest) := by
  classical
  -- Reversal and sign negation leave the first projection of every letter unchanged.
  ext a
  unfold labels
  simp only [Multiset.cons_bind, Multiset.count_add]
  rw [PolygonWord.formalInverse_val]
  simp only [List.map_map, List.map_reverse, Multiset.coe_count,
    List.count_reverse]
  rfl

/-- Helper for Theorem 78.2: properness depends only on the multiset of
unsigned labels. -/
theorem proper_congr_labels {first second : LabellingScheme α}
    (hlabels : first.labels = second.labels) :
    first.Proper ↔ second.Proper := by
  -- Rewrite the defining multiplicity condition through the supplied label equality.
  unfold Proper
  rw [hlabels]

/-- Helper for Theorem 78.2: cyclically moving a boundary fragment preserves
properness of the surrounding labelling scheme. -/
theorem proper_appendSwap_iff (y₀ y₁ : List (α × Bool))
    (rest : LabellingScheme α) (hLength : 3 ≤ (y₀ ++ y₁).length) :
    Proper
        (⟨y₁ ++ y₀, PolygonWord.appendSwap_length y₀ y₁ hLength⟩ ::ₘ rest) ↔
      Proper (⟨y₀ ++ y₁, hLength⟩ ::ₘ rest) := by
  -- Properness only records unsigned-label multiplicities, which append-swap preserves.
  exact proper_congr_labels (labels_appendSwap y₀ y₁ rest hLength)

/-- Helper for Theorem 78.2: formally inverting one boundary word preserves
properness of the surrounding labelling scheme. -/
theorem proper_formalInverseCons_iff (word : PolygonWord α)
    (rest : LabellingScheme α) :
    Proper (word.formalInverse ::ₘ rest) ↔ Proper (word ::ₘ rest) := by
  -- Reversal and sign negation do not change any unsigned-label multiplicity.
  exact proper_congr_labels (labels_formalInverseCons word rest)

/-- Helper for Theorem 78.2: a chosen letter can be moved to the front of its
polygon word while preserving properness and the presented space. -/
theorem exists_presentationWithSelectedLetterFirst
    {X : Type*} [TopologicalSpace X] (word : PolygonWord α)
    (edge : Fin word.1.length) (rest : LabellingScheme α)
    (hproper : Proper (word ::ₘ rest))
    (hpresents : Presents (word ::ₘ rest) X) :
    ∃ (tail : List (α × Bool)) (htail : 2 ≤ tail.length),
      Proper
          (⟨word.1.get edge :: tail,
            PolygonWord.consLetter_length (word.1.get edge) tail htail⟩ ::ₘ rest) ∧
        Presents
          (⟨word.1.get edge :: tail,
            PolygonWord.consLetter_length (word.1.get edge) tail htail⟩ ::ₘ rest) X := by
  let initial := word.1.take edge.1
  let suffix := word.1.drop (edge.1 + 1)
  let tail := suffix ++ initial
  have htail : 2 ≤ tail.length := by
    exact List.two_le_length_drop_succ_append_take word.1 edge word.2
  have hsplit : initial ++ [word.1.get edge] ++ suffix = word.1 := by
    exact List.take_append_get_append_drop_succ word.1 edge
  have hsourceLength :
      3 ≤ (initial ++ ([word.1.get edge] ++ suffix)).length := by
    rw [← List.append_assoc, hsplit]
    exact word.2
  let sourceWord : PolygonWord α :=
    ⟨initial ++ ([word.1.get edge] ++ suffix), hsourceLength⟩
  have hsourceWord : sourceWord = word := by
    apply Subtype.ext
    exact List.append_assoc initial [word.1.get edge] suffix |>.symm.trans hsplit
  have hsourceProper : Proper (sourceWord ::ₘ rest) := by
    rw [hsourceWord]
    exact hproper
  have hsourcePresents : Presents (sourceWord ::ₘ rest) X := by
    rw [hsourceWord]
    exact hpresents
  let rotatedWord : PolygonWord α :=
    ⟨([word.1.get edge] ++ suffix) ++ initial,
      PolygonWord.appendSwap_length initial
        ([word.1.get edge] ++ suffix) hsourceLength⟩
  have hrotatedProper : Proper (rotatedWord ::ₘ rest) := by
    exact (proper_appendSwap_iff initial ([word.1.get edge] ++ suffix)
      rest hsourceLength).mpr hsourceProper
  have hrotatedPresents : Presents (rotatedWord ::ₘ rest) X := by
    exact Presents.appendSwap initial ([word.1.get edge] ++ suffix)
      rest hsourceLength hsourcePresents
  have hrotatedWord : rotatedWord =
      ⟨word.1.get edge :: tail,
        PolygonWord.consLetter_length (word.1.get edge) tail htail⟩ := by
    apply Subtype.ext
    simp only [rotatedWord, tail, List.cons_append, List.nil_append]
  -- The append-swap is precisely the desired front-selected normal form.
  refine ⟨tail, htail, ?_, ?_⟩
  · rw [← hrotatedWord]
    exact hrotatedProper
  · rw [← hrotatedWord]
    exact hrotatedPresents

namespace Cut

/-- Helper for Theorem 78.2: a cut increases the number of polygon words by
exactly one. -/
theorem card_before_add_one {before after : LabellingScheme α}
    (hcut : Cut before after) : before.card + 1 = after.card := by
  rcases hcut with
    ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
  -- The joined scheme has one head word, while the split scheme has two.
  simp only [Multiset.card_cons]

/-- Helper for Theorem 78.2: removing the fresh oppositely signed label pair
inserted by a cut preserves properness of the remaining labelling scheme. -/
theorem proper_before {before after : LabellingScheme α}
    (hcut : Cut before after) (hproper : after.Proper) : before.Proper := by
  classical
  rcases hcut with
    ⟨y₀, y₁, c, b, rest, hy₀Length, hy₁Length, hy₀, hy₁, hrest⟩
  rw [proper_iff] at hproper ⊢
  intro a ha
  -- A cut adds exactly two unsigned occurrences of its fresh label.
  have hcount :
      Multiset.count a (labels
        (⟨y₀ ++ [(c, !b)],
            PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
          ⟨(c, b) :: y₁,
            PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest)) =
        Multiset.count a (labels
          (⟨y₀ ++ y₁,
            PolygonWord.append_length y₀ y₁ hy₀Length hy₁Length⟩ ::ₘ rest)) +
          (if a = c then 2 else 0) := by
    unfold labels
    simp only [Multiset.cons_bind, Multiset.count_add, List.map_append,
      List.map_cons, List.map_nil, Multiset.coe_count, List.count_append,
      List.count_cons, List.count_nil]
    by_cases hac : a = c
    · subst a
      simp
      omega
    · have hca : (c == a) = false := by
        simp only [beq_eq_false_iff_ne]
        exact Ne.symm hac
      rw [hca, if_neg hac]
      simp only [Bool.false_eq_true, if_false]
      omega
  -- Every old label still occurs after the cut, so properness computes its count.
  have hafterMem : a ∈ labels
      (⟨y₀ ++ [(c, !b)],
          PolygonWord.appendLetter_length y₀ (c, !b) hy₀Length⟩ ::ₘ
        ⟨(c, b) :: y₁,
          PolygonWord.consLetter_length (c, b) y₁ hy₁Length⟩ ::ₘ rest) := by
    rw [← Multiset.count_pos, hcount]
    exact Nat.add_pos_left (Multiset.count_pos.mpr ha) _
  have hafterCount := hproper a hafterMem
  rw [hcount] at hafterCount
  by_cases hac : a = c
  · rw [if_pos hac] at hafterCount
    have hbeforePos := Multiset.count_pos.mpr ha
    omega
  · rw [if_neg hac, Nat.add_zero] at hafterCount
    exact hafterCount

/-- Helper for Theorem 78.2: pasting a proper cut presentation preserves the
space and properness while decreasing the polygon-word count by one. -/
theorem pasteProperPresentation {before after : LabellingScheme α}
    (hcut : Cut before after) {X : Type*} [TopologicalSpace X]
    (hproper : after.Proper) (hpresents : after.Presents X) :
    before.card + 1 = after.card ∧ before.Proper ∧ before.Presents X := by
  -- Combine the cut's rank equation with its combinatorial and geometric invariants.
  exact ⟨hcut.card_before_add_one, hcut.proper_before hproper,
    LabellingScheme.Presents.paste hcut hpresents⟩

end Cut

end LabellingScheme

namespace PolygonalPasting

universe v w

variable {ι : Type u} [Fintype ι] {S : Type v}

/-- Helper for Theorem 78.2: a relation equivalence transported by an equivalence
also transports the generated equivalence closures. -/
theorem eqvGen_iff_of_equiv {A : Type v} {B : Type w} (e : A ≃ B)
    {r : A → A → Prop} {s : B → B → Prop}
    (hrelated : ∀ x y, r x y ↔ s (e x) (e y)) (x y : A) :
    Relation.EqvGen r x y ↔ Relation.EqvGen s (e x) (e y) := by
  -- Push each generating, reflexive, symmetric, and transitive step through `e`.
  have hforward : ∀ {a b}, Relation.EqvGen r a b →
      Relation.EqvGen s (e a) (e b) := by
    intro a b hab
    induction hab with
    | rel a b hab => exact Relation.EqvGen.rel _ _ ((hrelated a b).mp hab)
    | refl a => exact Relation.EqvGen.refl (e a)
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
  have hinverse : ∀ a b, s a b ↔ r (e.symm a) (e.symm b) := by
    intro a b
    simpa only [Equiv.apply_symm_apply] using
      (hrelated (e.symm a) (e.symm b)).symm
  have hbackward : ∀ {a b}, Relation.EqvGen s a b →
      Relation.EqvGen r (e.symm a) (e.symm b) := by
    intro a b hab
    induction hab with
    | rel a b hab => exact Relation.EqvGen.rel _ _ ((hinverse a b).mp hab)
    | refl a => exact Relation.EqvGen.refl (e.symm a)
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
  constructor
  · exact hforward
  · intro hxy
    simpa only [Equiv.symm_apply_apply] using hbackward hxy

/-- Helper for Theorem 78.2: the labels and orientation signs around one polygon
form a polygon word. -/
theorem boundaryWord_three_le (presentation : PolygonalPasting ι S) (i : ι) :
    3 ≤ (List.ofFn fun edge : Fin (presentation.sides i) ↦
      ((presentation.pasting i).label edge, (presentation.pasting i).sign edge)).length := by
  -- The boundary list has exactly the number of sides of the cyclic polygon.
  simpa only [List.length_ofFn] using (presentation.polygon i).three_le

/-- Helper for Theorem 78.2: the signed boundary word of one indexed polygon. -/
def boundaryWord (presentation : PolygonalPasting ι S) (i : ι) : PolygonWord S :=
  ⟨List.ofFn fun edge : Fin (presentation.sides i) ↦
      ((presentation.pasting i).label edge, (presentation.pasting i).sign edge),
    presentation.boundaryWord_three_le i⟩

/-- Helper for Theorem 78.2: a polygon boundary word has exactly the polygon's
number of edges. -/
theorem boundaryWord_length (presentation : PolygonalPasting ι S) (i : ι) :
    (presentation.boundaryWord i).1.length = presentation.sides i := by
  -- Compute the length of the list generated from the edge-indexing function.
  exact List.length_ofFn

/-- Helper for Theorem 78.2: polygon edges and positions in the corresponding
boundary word have the same canonical finite indexing. -/
def boundaryEdgeEquiv (presentation : PolygonalPasting ι S) (i : ι) :
    Fin (presentation.sides i) ≃ Fin (presentation.boundaryWord i).1.length :=
  finCongr (presentation.boundaryWord_length i).symm

/-- Helper for Theorem 78.2: reading a boundary word at the position corresponding
to an edge returns that edge's label and orientation sign. -/
theorem boundaryWord_get_boundaryEdgeEquiv (presentation : PolygonalPasting ι S)
    (i : ι) (edge : Fin (presentation.sides i)) :
    (presentation.boundaryWord i).1.get (presentation.boundaryEdgeEquiv i edge) =
      ((presentation.pasting i).label edge, (presentation.pasting i).sign edge) := by
  -- `List.get_ofFn` computes the entry, and both finite casts preserve its value.
  unfold boundaryWord
  rw [List.get_ofFn]
  congr 2

/-- Helper for Theorem 78.2: the labelling scheme consisting of all indexed
polygon boundary words, retaining repeated equal words as separate occurrences. -/
def boundaryScheme (presentation : PolygonalPasting ι S) : LabellingScheme S :=
  (Finset.univ : Finset ι).val.map presentation.boundaryWord

/-- Helper for Theorem 78.2: each polygon index corresponds to its boundary-word
occurrence in the associated labelling scheme. -/
theorem exists_boundaryOccurrenceEquiv (presentation : PolygonalPasting ι S) :
    ∃ e : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme,
      ∀ i, (e i).1 = presentation.boundaryWord i := by
  -- Apply the generic mapped-universe occurrence equivalence to boundary words.
  exact Fintype.exists_equivOccurrence_mapUniv presentation.boundaryWord

/-- Helper for Theorem 78.2: the chosen boundary occurrence has the same number
of letter positions as the indexed polygon has edges. -/
theorem boundaryOccurrence_length (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) (i : ι) :
    (presentation.boundaryWord i).1.length = (regionEquiv i).1.1.length := by
  -- Transport the list length along the equation identifying the chosen occurrence.
  exact congrArg (fun word : PolygonWord S ↦ word.1.length) (hregion i).symm

/-- Helper for Theorem 78.2: transporting a word position with `finCongr` does
not change the letter read at that position. -/
theorem polygonWord_get_finCongr {first second : PolygonWord S}
    (hword : first = second) (edge : Fin second.1.length) :
    first.1.get
      (finCongr (congrArg (fun word : PolygonWord S ↦ word.1.length) hword.symm) edge) =
        second.1.get edge := by
  -- Once the two words are identified, the finite transport is the identity.
  subst hword
  rfl

/-- Helper for Theorem 78.2: all indexed polygon edges are canonically equivalent
to all letter positions in the associated boundary labelling scheme. -/
def boundaryLetterEquiv (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    ((i : ι) × Fin (presentation.sides i)) ≃
      ((region : LabellingScheme.Occurrence presentation.boundaryScheme) ×
        Fin region.1.1.length) :=
  Equiv.sigmaCongr regionEquiv fun i ↦
    (presentation.boundaryEdgeEquiv i).trans
      (finCongr (presentation.boundaryOccurrence_length regionEquiv hregion i))

/-- Helper for Theorem 78.2: the bundled boundary-letter equivalence sends an
indexed edge to the chosen occurrence of its polygon. -/
theorem boundaryLetterEquiv_fst (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (edge : (i : ι) × Fin (presentation.sides i)) :
    (presentation.boundaryLetterEquiv regionEquiv hregion edge).1 =
      regionEquiv edge.1 := by
  -- The base component of `Equiv.sigmaCongr` is the supplied region equivalence.
  rfl

/-- Helper for Theorem 78.2: pulling a scheme letter back through the bundled
boundary equivalence selects the inverse image of its region occurrence. -/
theorem boundaryLetterEquiv_symm_fst (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (edge : (region : LabellingScheme.Occurrence presentation.boundaryScheme) ×
      Fin region.1.1.length) :
    ((presentation.boundaryLetterEquiv regionEquiv hregion).symm edge).1 =
      regionEquiv.symm edge.1 := by
  -- Apply the region equivalence and compare first components of `apply_symm_apply`.
  apply regionEquiv.injective
  have himage := (presentation.boundaryLetterEquiv regionEquiv hregion).apply_symm_apply edge
  have hfirst := congrArg Sigma.fst himage
  rw [presentation.boundaryLetterEquiv_fst regionEquiv hregion] at hfirst
  calc
    regionEquiv ((presentation.boundaryLetterEquiv regionEquiv hregion).symm edge).1 =
        edge.1 := hfirst
    _ = regionEquiv (regionEquiv.symm edge.1) :=
      (regionEquiv.apply_symm_apply edge.1).symm

/-- Helper for Theorem 78.2: reading the scheme letter selected by the bundled
edge equivalence recovers the original edge label and orientation sign. -/
theorem boundaryLetterEquiv_letter (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (edge : (i : ι) × Fin (presentation.sides i)) :
    ((presentation.boundaryLetterEquiv regionEquiv hregion edge).1.1.1.get
      (presentation.boundaryLetterEquiv regionEquiv hregion edge).2) =
        ((presentation.pasting edge.1).label edge.2,
          (presentation.pasting edge.1).sign edge.2) := by
  -- Normalize the bundled equivalence, then compute the original boundary word.
  unfold boundaryLetterEquiv
  simp only [Equiv.sigmaCongr, Equiv.trans_apply]
  exact (polygonWord_get_finCongr (hregion edge.1)
    (presentation.boundaryEdgeEquiv edge.1 edge.2)).trans
      (presentation.boundaryWord_get_boundaryEdgeEquiv edge.1 edge.2)

/-- Helper for Theorem 78.2: the polygon belonging to a boundary occurrence has
the same number of sides as the word carried by that occurrence. -/
theorem boundaryRegion_length (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme) :
    presentation.sides (regionEquiv.symm region) = region.1.1.length := by
  -- Pass from polygon sides to its boundary word, then to the selected occurrence.
  calc
    presentation.sides (regionEquiv.symm region) =
        (presentation.boundaryWord (regionEquiv.symm region)).1.length :=
      (presentation.boundaryWord_length (regionEquiv.symm region)).symm
    _ = (regionEquiv (regionEquiv.symm region)).1.1.length :=
      presentation.boundaryOccurrence_length regionEquiv hregion
        (regionEquiv.symm region)
    _ = region.1.1.length := congrArg (fun occurrence ↦ occurrence.1.1.length)
      (regionEquiv.apply_symm_apply region)

/-- Helper for Theorem 78.2: a cyclic polygon can be transported across an
equality of its numbers of sides. -/
def castCyclicPolygon {first second : ℕ} (h : first = second)
    (poly : CyclicPolygon first) : CyclicPolygon second :=
  h ▸ poly

/-- Helper for Theorem 78.2: transporting a cyclic polygon's number of sides
induces the identity homeomorphism on its filled region. -/
noncomputable def castCyclicPolygonRegionHomeomorph {first second : ℕ}
    (h : first = second) (poly : CyclicPolygon first) :
    poly.region ≃ₜ (castCyclicPolygon h poly).region :=
  match h with
  | rfl => Homeomorph.refl poly.region

/-- Helper for Theorem 78.2: transporting a polygon's side count does not change
the underlying Euclidean point of its region. -/
theorem castCyclicPolygonRegionHomeomorph_coe {first second : ℕ}
    (h : first = second) (poly : CyclicPolygon first) (x : poly.region) :
    (castCyclicPolygonRegionHomeomorph h poly x : EuclideanSpace ℝ (Fin 2)) = x := by
  -- Equality elimination reduces the transport homeomorphism to the identity.
  cases h
  rfl

/-- Helper for Theorem 78.2: the original polygon attached to a scheme occurrence,
transported to the boundary length of that occurrence. -/
def boundaryRegionPolygon (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme) :
    CyclicPolygon region.1.1.length :=
  castCyclicPolygon (presentation.boundaryRegion_length regionEquiv hregion region)
    (presentation.polygon (regionEquiv.symm region))

/-- Helper for Theorem 78.2: a scheme edge position determines the corresponding
edge of its original indexed polygon. -/
def boundaryRegionEdge (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme)
    (edge : Fin region.1.1.length) :
    Fin (presentation.sides (regionEquiv.symm region)) :=
  Fin.cast (presentation.boundaryRegion_length regionEquiv hregion region).symm edge

/-- Helper for Theorem 78.2: scheme lookup at a boundary occurrence recovers the
label and sign of the corresponding original polygon edge. -/
theorem boundaryRegionEdge_letter (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme)
    (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      ((presentation.pasting (regionEquiv.symm region)).label
          (presentation.boundaryRegionEdge regionEquiv hregion region edge),
        (presentation.pasting (regionEquiv.symm region)).sign
          (presentation.boundaryRegionEdge regionEquiv hregion region edge)) := by
  -- Compare the occurrence list with its indexed boundary word at equal numerical positions.
  let i := regionEquiv.symm region
  let originalEdge := presentation.boundaryRegionEdge regionEquiv hregion region edge
  have hlist : region.1.1 = (presentation.boundaryWord i).1 := by
    calc
      region.1.1 = (regionEquiv i).1.1 := congrArg (fun occurrence ↦ occurrence.1.1)
        (regionEquiv.apply_symm_apply region).symm
      _ = (presentation.boundaryWord i).1 := congrArg Subtype.val (hregion i)
  have hvalue : edge.1 = (presentation.boundaryEdgeEquiv i originalEdge).1 := by
    rfl
  calc
    region.1.1.get edge =
        (presentation.boundaryWord i).1.get
          (presentation.boundaryEdgeEquiv i originalEdge) :=
      LabellingScheme.PolygonalRegions.Renumbering.get_eq_of_list_eq_of_val_eq
        edge (presentation.boundaryEdgeEquiv i originalEdge) hlist hvalue
    _ = ((presentation.pasting i).label originalEdge,
        (presentation.pasting i).sign originalEdge) :=
      presentation.boundaryWord_get_boundaryEdgeEquiv i originalEdge

/-- Helper for Theorem 78.2: correcting by the stored orientation sign converts
the positive oriented-edge parameter to the cyclic boundary parameter. -/
def correctedBoundaryParameter (presentation : PolygonalPasting ι S)
    (i : ι) (edge : Fin (presentation.sides i)) (t : unitInterval) : unitInterval :=
  if (presentation.pasting i).sign edge then t else unitInterval.symm t

/-- Helper for Theorem 78.2: correcting a boundary parameter twice by the same
orientation sign restores the original parameter. -/
theorem correctedBoundaryParameter_involutive (presentation : PolygonalPasting ι S)
    (i : ι) (edge : Fin (presentation.sides i)) (t : unitInterval) :
    presentation.correctedBoundaryParameter i edge
        (presentation.correctedBoundaryParameter i edge t) = t := by
  -- The positive case is immediate and the negative case uses interval reflection twice.
  unfold correctedBoundaryParameter
  cases hsign : (presentation.pasting i).sign edge
  · simp only [Bool.false_eq_true, if_false, unitInterval.symm_symm]
  · simp only [if_true]

/-- Helper for Theorem 78.2: the labelled-edge sign rule carries the corrected
parameter on one edge to the corrected parameter on the other edge. -/
theorem correctedBoundaryParameter_relates (presentation : PolygonalPasting ι S)
    (first second : ι) (firstEdge : Fin (presentation.sides first))
    (secondEdge : Fin (presentation.sides second)) (t : unitInterval) :
    (if (presentation.pasting first).sign firstEdge =
        (presentation.pasting second).sign secondEdge then
      presentation.correctedBoundaryParameter first firstEdge t
    else unitInterval.symm
      (presentation.correctedBoundaryParameter first firstEdge t)) =
        presentation.correctedBoundaryParameter second secondEdge t := by
  -- Each of the four sign combinations is the same choice of zero or one reflection.
  cases hfirst : (presentation.pasting first).sign firstEdge
  · cases hsecond : (presentation.pasting second).sign secondEdge
    · simp [correctedBoundaryParameter, hfirst, hsecond]
    · simp [correctedBoundaryParameter, hfirst, hsecond]
  · cases hsecond : (presentation.pasting second).sign secondEdge
    · simp [correctedBoundaryParameter, hfirst, hsecond]
    · simp [correctedBoundaryParameter, hfirst, hsecond]

/-- Helper for Theorem 78.2: an indexed edge transports to the same numerical
position in its chosen boundary-word occurrence. -/
theorem boundaryForward_length (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) (i : ι) :
    presentation.sides i = (regionEquiv i).1.1.length := by
  -- Compare polygon sides with the boundary word and then with its chosen occurrence.
  calc
    presentation.sides i = (presentation.boundaryWord i).1.length :=
      (presentation.boundaryWord_length i).symm
    _ = (regionEquiv i).1.1.length :=
      presentation.boundaryOccurrence_length regionEquiv hregion i

/-- Helper for Theorem 78.2: the forward image of an indexed edge in its
boundary-word occurrence. -/
def boundaryForwardEdge (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (i : ι) (edge : Fin (presentation.sides i)) :
    Fin (regionEquiv i).1.1.length :=
  Fin.cast (presentation.boundaryForward_length regionEquiv hregion i) edge

/-- Helper for Theorem 78.2: reading the forward boundary position recovers the
label and sign of the original indexed edge. -/
theorem boundaryForwardEdge_letter (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (i : ι) (edge : Fin (presentation.sides i)) :
    (regionEquiv i).1.1.get
        (presentation.boundaryForwardEdge regionEquiv hregion i edge) =
      ((presentation.pasting i).label edge, (presentation.pasting i).sign edge) := by
  -- Compare the chosen occurrence with the boundary word at the common numerical index.
  have hlist : (regionEquiv i).1.1 = (presentation.boundaryWord i).1 :=
    congrArg Subtype.val (hregion i)
  calc
    (regionEquiv i).1.1.get
        (presentation.boundaryForwardEdge regionEquiv hregion i edge) =
      (presentation.boundaryWord i).1.get
        (presentation.boundaryEdgeEquiv i edge) :=
      LabellingScheme.PolygonalRegions.Renumbering.get_eq_of_list_eq_of_val_eq
        (presentation.boundaryForwardEdge regionEquiv hregion i edge)
        (presentation.boundaryEdgeEquiv i edge) hlist rfl
    _ = ((presentation.pasting i).label edge, (presentation.pasting i).sign edge) :=
      presentation.boundaryWord_get_boundaryEdgeEquiv i edge

/-- Helper for Theorem 78.2: the scheme's sign-comparison parameter, followed by
the second edge's correction, recovers the first edge's positive parameter. -/
theorem correctedBoundaryParameter_pair (presentation : PolygonalPasting ι S)
    (first second : ι) (firstEdge : Fin (presentation.sides first))
    (secondEdge : Fin (presentation.sides second)) (t : unitInterval) :
    presentation.correctedBoundaryParameter second secondEdge
        (if (presentation.pasting first).sign firstEdge =
            (presentation.pasting second).sign secondEdge then
          presentation.correctedBoundaryParameter first firstEdge t
        else unitInterval.symm
          (presentation.correctedBoundaryParameter first firstEdge t)) = t := by
  -- The four Boolean sign combinations reduce to one or two interval reflections.
  cases hfirst : (presentation.pasting first).sign firstEdge
  · cases hsecond : (presentation.pasting second).sign secondEdge
    · simp [correctedBoundaryParameter, hfirst, hsecond]
    · simp [correctedBoundaryParameter, hfirst, hsecond]
  · cases hsecond : (presentation.pasting second).sign secondEdge
    · simp [correctedBoundaryParameter, hfirst, hsecond]
    · simp [correctedBoundaryParameter, hfirst, hsecond]

/-- Helper for Theorem 78.2: pulling a scheme pairing back to the two indexed
edges gives one common positive oriented-edge parameter. -/
theorem correctedBoundaryParameter_common (presentation : PolygonalPasting ι S)
    (first second : ι) (firstEdge : Fin (presentation.sides first))
    (secondEdge : Fin (presentation.sides second)) (t : unitInterval) :
    presentation.correctedBoundaryParameter second secondEdge
        (if (presentation.pasting first).sign firstEdge =
            (presentation.pasting second).sign secondEdge then t
        else unitInterval.symm t) =
      presentation.correctedBoundaryParameter first firstEdge t := by
  -- The scheme reverses precisely the parameter whose two edge signs differ.
  cases hfirst : (presentation.pasting first).sign firstEdge
  · cases hsecond : (presentation.pasting second).sign secondEdge
    · simp [correctedBoundaryParameter, hfirst, hsecond]
    · simp [correctedBoundaryParameter, hfirst, hsecond]
  · cases hsecond : (presentation.pasting second).sign secondEdge
    · simp [correctedBoundaryParameter, hfirst, hsecond]
    · simp [correctedBoundaryParameter, hfirst, hsecond]

/-- Helper for Theorem 78.2: the indexed polygons regarded as polygonal regions
whose cyclic boundary words form `boundaryScheme`. -/
@[expose]
noncomputable def boundaryRegions (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    LabellingScheme.PolygonalRegions presentation.boundaryScheme where
  Point region := (presentation.polygon (regionEquiv.symm region)).region
  topology _ := inferInstance
  edge region edge t :=
    (presentation.pasting (regionEquiv.symm region)).orientedPoint
      (presentation.boundaryRegionEdge regionEquiv hregion region edge)
      (presentation.correctedBoundaryParameter (regionEquiv.symm region)
        (presentation.boundaryRegionEdge regionEquiv hregion region edge) t)

/-- Helper for Theorem 78.2: after transporting a polygon's side count, correcting
an oriented-edge parameter by its sign gives the transported cyclic edge point. -/
theorem castCyclicPolygon_orientedPoint_corrected {first second : ℕ}
    (h : first = second) (poly : CyclicPolygon first)
    (pasting : poly.EdgePasting S) (edge : Fin second) (t : unitInterval) :
    ((castCyclicPolygonRegionHomeomorph h poly)
      (pasting.orientedPoint (Fin.cast h.symm edge)
        (if pasting.sign (Fin.cast h.symm edge) then t else unitInterval.symm t)) :
        EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap
        ((castCyclicPolygon h poly).toPolygon.vertices edge)
        ((castCyclicPolygon h poly).toPolygon.vertices (finRotate second edge))
        (t : ℝ) := by
  -- With a variable target length, equality elimination removes every finite cast at once.
  rw [castCyclicPolygonRegionHomeomorph_coe]
  cases h
  simp only [castCyclicPolygon, Fin.cast_eq_self]
  split
  · rename_i hsign
    rw [pasting.orientedPoint_apply, pasting.includePoint_coe,
      pasting.orientation_eq, hsign]
    simp only [CyclicPolygon.signedOrientation, if_true, OrientedSegment.point_coe]
    rfl
  · rename_i hsign
    rw [pasting.orientedPoint_apply, pasting.includePoint_coe,
      pasting.orientation_eq, Bool.eq_false_of_not_eq_true hsign]
    simp only [CyclicPolygon.signedOrientation, OrientedSegment.point_coe,
      unitInterval.coe_symm_eq]
    rw [AffineMap.lineMap_apply_one_sub]
    simp only [Bool.false_eq_true, if_false, OrientedSegment.reverse_final,
      OrientedSegment.reverse_initial, CyclicPolygon.cyclicOrientation]

/-- Helper for Theorem 78.2: the sign-corrected oriented point is the usual
cyclic affine point on the corresponding transported polygon edge. -/
theorem boundaryRegions_edgeCompatibility (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    ((castCyclicPolygonRegionHomeomorph
        (presentation.boundaryRegion_length regionEquiv hregion region)
        (presentation.polygon (regionEquiv.symm region)))
      ((presentation.boundaryRegions regionEquiv hregion).edge region edge t) :
        EuclideanSpace ℝ (Fin 2)) =
      AffineMap.lineMap
        ((presentation.boundaryRegionPolygon regionEquiv hregion region).toPolygon.vertices
          edge)
        ((presentation.boundaryRegionPolygon regionEquiv hregion region).toPolygon.vertices
          (finRotate region.1.1.length edge)) (t : ℝ) := by
  -- Apply the generic transport lemma to the occurrence's side-count equality.
  unfold boundaryRegions boundaryRegionPolygon boundaryRegionEdge correctedBoundaryParameter
  exact castCyclicPolygon_orientedPoint_corrected
    (presentation.boundaryRegion_length regionEquiv hregion region)
    (presentation.polygon (regionEquiv.symm region))
    (presentation.pasting (regionEquiv.symm region)) edge t

/-- Helper for Theorem 78.2: the canonical boundary-scheme regions are genuine
polygonal regions. -/
theorem boundaryRegions_isPolygonal (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    (presentation.boundaryRegions regionEquiv hregion).IsPolygonal := by
  rw [LabellingScheme.PolygonalRegions.isPolygonal_iff]
  intro region
  -- Use the transported original polygon; the preceding computation supplies edge compatibility.
  refine ⟨LabellingScheme.PolygonalRegions.CyclicRegion.ofHomeomorph
    (presentation.boundaryRegionPolygon regionEquiv hregion region)
    (castCyclicPolygonRegionHomeomorph
      (presentation.boundaryRegion_length regionEquiv hregion region)
      (presentation.polygon (regionEquiv.symm region))) ?_⟩
  exact presentation.boundaryRegions_edgeCompatibility regionEquiv hregion region

/-- Helper for Theorem 78.2: equality of indices gives the canonical
homeomorphism between the corresponding members of a topological family. -/
noncomputable def indexCastHomeomorph {A : Type*} {family : A → Type*}
    [∀ a, TopologicalSpace (family a)] {first second : A} (h : first = second) :
    family first ≃ₜ family second :=
  match h with
  | rfl => Homeomorph.refl (family first)

/-- Helper for Theorem 78.2: the canonical family-index homeomorphism is
heterogeneously equal to the original point. -/
theorem indexCastHomeomorph_heq {A : Type*} {family : A → Type*}
    [∀ a, TopologicalSpace (family a)] {first second : A} (h : first = second)
    (x : family first) : HEq (indexCastHomeomorph h x) x := by
  -- Equality elimination reduces the family transport to the identity map.
  cases h
  rfl

/-- Helper for Theorem 78.2: the polygon fiber over an index is canonically
homeomorphic to the fiber over its image boundary occurrence. -/
noncomputable def boundarySourceFiberHomeomorph
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (i : ι) :
    (presentation.polygon i).region ≃ₜ
      (presentation.polygon (regionEquiv.symm (regionEquiv i))).region :=
  indexCastHomeomorph
    (family := fun j : ι ↦ (presentation.polygon j).region)
    (regionEquiv.symm_apply_apply i).symm

/-- Helper for Theorem 78.2: reindexing the disjoint union of indexed polygons by
boundary-word occurrences is a homeomorphism of sources. -/
noncomputable def boundarySourceHomeomorph
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    presentation.Source ≃ₜ
      (presentation.boundaryRegions regionEquiv hregion).Source :=
  let regions := presentation.boundaryRegions regionEquiv hregion
  letI : ∀ region, TopologicalSpace (regions.Point region) :=
    fun region ↦ regions.topology region
  IsHomeomorph.homeomorph
    (Sigma.map regionEquiv fun i ↦ presentation.boundarySourceFiberHomeomorph regionEquiv i)
    (IsHomeomorph.sigmaMap regionEquiv.bijective fun i ↦
      (presentation.boundarySourceFiberHomeomorph regionEquiv i).isHomeomorph)

/-- Helper for Theorem 78.2: the boundary-source homeomorphism sends an indexed
polygon to its chosen boundary-word occurrence. -/
theorem boundarySourceHomeomorph_fst
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (point : presentation.Source) :
    (presentation.boundarySourceHomeomorph regionEquiv hregion point).1 =
      regionEquiv point.1 := by
  -- The source map is the dependent sigma map over `regionEquiv`.
  simp only [boundarySourceHomeomorph, IsHomeomorph.homeomorph_apply]
  rfl

/-- Helper for Theorem 78.2: the source homeomorphism carries an oriented edge
point to the sign-corrected cyclic edge point in the chosen boundary occurrence. -/
theorem boundarySourceHomeomorph_orientedPoint
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (i : ι) (edge : Fin (presentation.sides i)) (t : unitInterval) :
    presentation.boundarySourceHomeomorph regionEquiv hregion
        ⟨i, (presentation.pasting i).orientedPoint edge t⟩ =
      ⟨regionEquiv i,
        (presentation.boundaryRegions regionEquiv hregion).edge (regionEquiv i)
          (presentation.boundaryForwardEdge regionEquiv hregion i edge)
          (presentation.correctedBoundaryParameter
            (regionEquiv.symm (regionEquiv i))
            (presentation.boundaryRegionEdge regionEquiv hregion (regionEquiv i)
              (presentation.boundaryForwardEdge regionEquiv hregion i edge)) t)⟩ := by
  -- Normalize the source map, then compare the dependent original-edge indices.
  simp only [boundarySourceHomeomorph, IsHomeomorph.homeomorph_apply]
  apply Sigma.ext
  · rfl
  · simp only [boundaryRegions]
    have hparameter :
        presentation.correctedBoundaryParameter
          (regionEquiv.symm (regionEquiv i))
          (presentation.boundaryRegionEdge regionEquiv hregion (regionEquiv i)
            (presentation.boundaryForwardEdge regionEquiv hregion i edge))
          (presentation.correctedBoundaryParameter
            (regionEquiv.symm (regionEquiv i))
            (presentation.boundaryRegionEdge regionEquiv hregion (regionEquiv i)
              (presentation.boundaryForwardEdge regionEquiv hregion i edge)) t) = t :=
      presentation.correctedBoundaryParameter_involutive
        (regionEquiv.symm (regionEquiv i))
        (presentation.boundaryRegionEdge regionEquiv hregion (regionEquiv i)
          (presentation.boundaryForwardEdge regionEquiv hregion i edge)) t
    rw [hparameter]
    have hindex := regionEquiv.symm_apply_apply i
    have hedgeIndex :
        (⟨regionEquiv.symm (regionEquiv i),
            presentation.boundaryRegionEdge regionEquiv hregion (regionEquiv i)
              (presentation.boundaryForwardEdge regionEquiv hregion i edge)⟩ :
          (j : ι) × Fin (presentation.sides j)) = ⟨i, edge⟩ := by
      apply Sigma.ext hindex
      rw [Fin.heq_ext_iff (congrArg presentation.sides hindex)]
      rfl
    have hedge := congr_arg_heq
      (fun p : (j : ι) × Fin (presentation.sides j) ↦
        (presentation.pasting p.1).orientedPoint p.2 t) hedgeIndex
    have hcast := indexCastHomeomorph_heq
      (family := fun j : ι ↦ (presentation.polygon j).region)
      (regionEquiv.symm_apply_apply i).symm
      ((presentation.pasting i).orientedPoint edge t)
    exact hcast.trans hedge.symm

/-- Helper for Theorem 78.2: in the canonical forward edge indexing, the source
homeomorphism is computed using the original edge's sign correction. -/
theorem boundarySourceHomeomorph_forwardEdge
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (i : ι) (edge : Fin (presentation.sides i)) (t : unitInterval) :
    presentation.boundarySourceHomeomorph regionEquiv hregion
        ⟨i, (presentation.pasting i).orientedPoint edge t⟩ =
      ⟨regionEquiv i,
        (presentation.boundaryRegions regionEquiv hregion).edge (regionEquiv i)
          (presentation.boundaryForwardEdge regionEquiv hregion i edge)
          (presentation.correctedBoundaryParameter i edge t)⟩ := by
  -- Collapse the round trip from an indexed edge to a boundary edge and back.
  rw [presentation.boundarySourceHomeomorph_orientedPoint regionEquiv hregion]
  let forwardEdge := presentation.boundaryForwardEdge regionEquiv hregion i edge
  have hbase : regionEquiv.symm (regionEquiv i) = i := regionEquiv.symm_apply_apply i
  have hroundEdge :
      (⟨regionEquiv.symm (regionEquiv i),
          presentation.boundaryRegionEdge regionEquiv hregion (regionEquiv i)
            forwardEdge⟩ : (j : ι) × Fin (presentation.sides j)) = ⟨i, edge⟩ := by
    apply Sigma.ext hbase
    rw [Fin.heq_ext_iff (congrArg presentation.sides hbase)]
    rfl
  have hparameter := congrArg
    (fun p : (j : ι) × Fin (presentation.sides j) ↦
      presentation.correctedBoundaryParameter p.1 p.2 t) hroundEdge
  exact congrArg (fun parameter : unitInterval ↦
    (⟨regionEquiv i,
      (presentation.boundaryRegions regionEquiv hregion).edge (regionEquiv i)
        forwardEdge parameter⟩ :
      (presentation.boundaryRegions regionEquiv hregion).Source)) hparameter

/-- Helper for Theorem 78.2: every boundary-scheme edge point is the image of
the corresponding sign-corrected point on the original indexed polygon. -/
theorem boundarySourceHomeomorph_inverseEdge
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    presentation.boundarySourceHomeomorph regionEquiv hregion
        ⟨regionEquiv.symm region,
          (presentation.pasting (regionEquiv.symm region)).orientedPoint
            (presentation.boundaryRegionEdge regionEquiv hregion region edge)
            (presentation.correctedBoundaryParameter (regionEquiv.symm region)
              (presentation.boundaryRegionEdge regionEquiv hregion region edge) t)⟩ =
      ⟨region, (presentation.boundaryRegions regionEquiv hregion).edge region edge t⟩ := by
  -- The forward computation corrects the parameter a second time, so it returns `t`.
  rw [presentation.boundarySourceHomeomorph_orientedPoint regionEquiv hregion]
  have hregionIndex := regionEquiv.apply_symm_apply region
  let originalEdge := presentation.boundaryRegionEdge regionEquiv hregion region edge
  let forwardRegion := regionEquiv (regionEquiv.symm region)
  let forwardEdge := presentation.boundaryForwardEdge regionEquiv hregion
    (regionEquiv.symm region) originalEdge
  have hroundEdge :
      (⟨regionEquiv.symm forwardRegion,
          presentation.boundaryRegionEdge regionEquiv hregion forwardRegion forwardEdge⟩ :
        (i : ι) × Fin (presentation.sides i)) =
        ⟨regionEquiv.symm region, originalEdge⟩ := by
    have hbase : regionEquiv.symm forwardRegion = regionEquiv.symm region :=
      congrArg regionEquiv.symm hregionIndex
    apply Sigma.ext hbase
    rw [Fin.heq_ext_iff (congrArg presentation.sides hbase)]
    rfl
  have hparameterTransport := congrArg
    (fun p : (i : ι) × Fin (presentation.sides i) ↦
      presentation.correctedBoundaryParameter p.1 p.2
        (presentation.correctedBoundaryParameter (regionEquiv.symm region)
          originalEdge t)) hroundEdge
  have hparameter :
      presentation.correctedBoundaryParameter (regionEquiv.symm forwardRegion)
          (presentation.boundaryRegionEdge regionEquiv hregion forwardRegion forwardEdge)
          (presentation.correctedBoundaryParameter (regionEquiv.symm region)
            originalEdge t) = t := by
    calc
      presentation.correctedBoundaryParameter (regionEquiv.symm forwardRegion)
          (presentation.boundaryRegionEdge regionEquiv hregion forwardRegion forwardEdge)
          (presentation.correctedBoundaryParameter (regionEquiv.symm region)
            originalEdge t) =
        presentation.correctedBoundaryParameter (regionEquiv.symm region) originalEdge
          (presentation.correctedBoundaryParameter (regionEquiv.symm region)
            originalEdge t) := hparameterTransport
      _ = t := presentation.correctedBoundaryParameter_involutive
        (regionEquiv.symm region) originalEdge t
  rw [hparameter]
  have hedgeIndex :
      (⟨regionEquiv (regionEquiv.symm region),
          presentation.boundaryForwardEdge regionEquiv hregion
            (regionEquiv.symm region)
            (presentation.boundaryRegionEdge regionEquiv hregion region edge)⟩ :
        (r : LabellingScheme.Occurrence presentation.boundaryScheme) ×
          Fin r.1.1.length) = ⟨region, edge⟩ := by
    apply Sigma.ext hregionIndex
    rw [Fin.heq_ext_iff
      (congrArg (fun r : LabellingScheme.Occurrence presentation.boundaryScheme ↦
        r.1.1.length) hregionIndex)]
    rfl
  have hedge := congr_arg_heq
    (fun p : (r : LabellingScheme.Occurrence presentation.boundaryScheme) ×
        Fin r.1.1.length ↦
      (presentation.boundaryRegions regionEquiv hregion).edge p.1 p.2 t) hedgeIndex
  exact Sigma.ext hregionIndex hedge

/-- Helper for Theorem 78.2: the boundary-source homeomorphism sends every
direct indexed edge pairing to the corresponding labelling-scheme pairing. -/
theorem edgeRelated_boundarySourceHomeomorph_of_related
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (x y : presentation.Source) (hxy : presentation.Related x y) :
    (presentation.boundaryRegions regionEquiv hregion).EdgeRelated
      (presentation.boundarySourceHomeomorph regionEquiv hregion x)
      (presentation.boundarySourceHomeomorph regionEquiv hregion y) := by
  unfold PolygonalPasting.Related at hxy
  obtain ⟨first, second, firstEdge, secondEdge, t, hlabel, hx, hy⟩ := hxy
  let firstBoundaryEdge :=
    presentation.boundaryForwardEdge regionEquiv hregion first firstEdge
  let secondBoundaryEdge :=
    presentation.boundaryForwardEdge regionEquiv hregion second secondEdge
  have hfirstLetter :=
    presentation.boundaryForwardEdge_letter regionEquiv hregion first firstEdge
  have hsecondLetter :=
    presentation.boundaryForwardEdge_letter regionEquiv hregion second secondEdge
  -- Use the corrected first parameter as the scheme parameter for the paired edges.
  refine ⟨regionEquiv first, regionEquiv second, firstBoundaryEdge,
    secondBoundaryEdge,
    presentation.correctedBoundaryParameter first firstEdge t, ?_, ?_, ?_⟩
  · calc
      ((regionEquiv first).1.1.get firstBoundaryEdge).1 =
          (presentation.pasting first).label firstEdge := congrArg Prod.fst hfirstLetter
      _ = (presentation.pasting second).label secondEdge := hlabel
      _ = ((regionEquiv second).1.1.get secondBoundaryEdge).1 :=
        (congrArg Prod.fst hsecondLetter).symm
  · calc
      presentation.boundarySourceHomeomorph regionEquiv hregion x =
          presentation.boundarySourceHomeomorph regionEquiv hregion
            ⟨first, (presentation.pasting first).orientedPoint firstEdge t⟩ :=
        congrArg (presentation.boundarySourceHomeomorph regionEquiv hregion) hx
      _ = ⟨regionEquiv first,
          (presentation.boundaryRegions regionEquiv hregion).edge
            (regionEquiv first) firstBoundaryEdge
            (presentation.correctedBoundaryParameter first firstEdge t)⟩ :=
        presentation.boundarySourceHomeomorph_forwardEdge
          regionEquiv hregion first firstEdge t
  · rw [hfirstLetter, hsecondLetter]
    have hparameter := presentation.correctedBoundaryParameter_relates
      first second firstEdge secondEdge t
    calc
      presentation.boundarySourceHomeomorph regionEquiv hregion y =
          presentation.boundarySourceHomeomorph regionEquiv hregion
            ⟨second, (presentation.pasting second).orientedPoint secondEdge t⟩ :=
        congrArg (presentation.boundarySourceHomeomorph regionEquiv hregion) hy
      _ = ⟨regionEquiv second,
          (presentation.boundaryRegions regionEquiv hregion).edge
            (regionEquiv second) secondBoundaryEdge
            (presentation.correctedBoundaryParameter second secondEdge t)⟩ :=
        presentation.boundarySourceHomeomorph_forwardEdge
          regionEquiv hregion second secondEdge t
      _ = ⟨regionEquiv second,
          (presentation.boundaryRegions regionEquiv hregion).edge
            (regionEquiv second) secondBoundaryEdge
            (if (presentation.pasting first).sign firstEdge =
                (presentation.pasting second).sign secondEdge then
              presentation.correctedBoundaryParameter first firstEdge t
            else unitInterval.symm
              (presentation.correctedBoundaryParameter first firstEdge t))⟩ :=
        congrArg (fun parameter : unitInterval ↦
          (⟨regionEquiv second,
            (presentation.boundaryRegions regionEquiv hregion).edge
              (regionEquiv second) secondBoundaryEdge parameter⟩ :
            (presentation.boundaryRegions regionEquiv hregion).Source)) hparameter.symm

/-- Helper for Theorem 78.2: every direct boundary-scheme edge pairing pulls
back through the source homeomorphism to an indexed edge pairing. -/
theorem related_of_edgeRelated_boundarySourceHomeomorph
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (x y : presentation.Source)
    (hxy : (presentation.boundaryRegions regionEquiv hregion).EdgeRelated
      (presentation.boundarySourceHomeomorph regionEquiv hregion x)
      (presentation.boundarySourceHomeomorph regionEquiv hregion y)) :
    presentation.Related x y := by
  unfold LabellingScheme.PolygonalRegions.EdgeRelated at hxy
  obtain ⟨firstRegion, secondRegion, firstBoundaryEdge, secondBoundaryEdge,
    t, hlabel, hx, hy⟩ := hxy
  let first := regionEquiv.symm firstRegion
  let second := regionEquiv.symm secondRegion
  let firstEdge := presentation.boundaryRegionEdge regionEquiv hregion
    firstRegion firstBoundaryEdge
  let secondEdge := presentation.boundaryRegionEdge regionEquiv hregion
    secondRegion secondBoundaryEdge
  have hfirstLetter := presentation.boundaryRegionEdge_letter regionEquiv hregion
    firstRegion firstBoundaryEdge
  have hsecondLetter := presentation.boundaryRegionEdge_letter regionEquiv hregion
    secondRegion secondBoundaryEdge
  unfold PolygonalPasting.Related
  -- The first sign correction is the common original oriented-edge parameter.
  refine ⟨first, second, firstEdge, secondEdge,
    presentation.correctedBoundaryParameter first firstEdge t, ?_, ?_, ?_⟩
  · calc
      (presentation.pasting first).label firstEdge =
          (firstRegion.1.1.get firstBoundaryEdge).1 :=
        (congrArg Prod.fst hfirstLetter).symm
      _ = (secondRegion.1.1.get secondBoundaryEdge).1 := hlabel
      _ = (presentation.pasting second).label secondEdge :=
        congrArg Prod.fst hsecondLetter
  · apply (presentation.boundarySourceHomeomorph regionEquiv hregion).injective
    calc
      presentation.boundarySourceHomeomorph regionEquiv hregion x =
          ⟨firstRegion,
            (presentation.boundaryRegions regionEquiv hregion).edge
              firstRegion firstBoundaryEdge t⟩ := hx
      _ = presentation.boundarySourceHomeomorph regionEquiv hregion
          ⟨first, (presentation.pasting first).orientedPoint firstEdge
            (presentation.correctedBoundaryParameter first firstEdge t)⟩ :=
        (presentation.boundarySourceHomeomorph_inverseEdge regionEquiv hregion
          firstRegion firstBoundaryEdge t).symm
  · let secondParameter :=
      if (firstRegion.1.1.get firstBoundaryEdge).2 =
          (secondRegion.1.1.get secondBoundaryEdge).2 then t
      else unitInterval.symm t
    have hcommon :
        presentation.correctedBoundaryParameter second secondEdge secondParameter =
          presentation.correctedBoundaryParameter first firstEdge t := by
      dsimp only [secondParameter]
      rw [hfirstLetter, hsecondLetter]
      exact presentation.correctedBoundaryParameter_common
        first second firstEdge secondEdge t
    apply (presentation.boundarySourceHomeomorph regionEquiv hregion).injective
    calc
      presentation.boundarySourceHomeomorph regionEquiv hregion y =
          ⟨secondRegion,
            (presentation.boundaryRegions regionEquiv hregion).edge
              secondRegion secondBoundaryEdge secondParameter⟩ := by
        exact hy
      _ = presentation.boundarySourceHomeomorph regionEquiv hregion
          ⟨second, (presentation.pasting second).orientedPoint secondEdge
            (presentation.correctedBoundaryParameter second secondEdge
              secondParameter)⟩ :=
        (presentation.boundarySourceHomeomorph_inverseEdge regionEquiv hregion
          secondRegion secondBoundaryEdge secondParameter).symm
      _ = presentation.boundarySourceHomeomorph regionEquiv hregion
          ⟨second, (presentation.pasting second).orientedPoint secondEdge
            (presentation.correctedBoundaryParameter first firstEdge t)⟩ :=
        congrArg (presentation.boundarySourceHomeomorph regionEquiv hregion)
          (congrArg (fun parameter : unitInterval ↦
            (⟨second, (presentation.pasting second).orientedPoint secondEdge parameter⟩ :
              presentation.Source)) hcommon)

/-- Helper for Theorem 78.2: the source homeomorphism preserves and reflects
the direct edge relations of the indexed and boundary-scheme presentations. -/
theorem related_iff_edgeRelated_boundarySourceHomeomorph
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (x y : presentation.Source) :
    presentation.Related x y ↔
      (presentation.boundaryRegions regionEquiv hregion).EdgeRelated
        (presentation.boundarySourceHomeomorph regionEquiv hregion x)
        (presentation.boundarySourceHomeomorph regionEquiv hregion y) := by
  -- The two implications are the forward and inverse edge computations above.
  constructor
  · exact presentation.edgeRelated_boundarySourceHomeomorph_of_related
      regionEquiv hregion x y
  · exact presentation.related_of_edgeRelated_boundarySourceHomeomorph
      regionEquiv hregion x y

/-- Helper for Theorem 78.2: the source homeomorphism preserves and reflects
the equivalence relations generated by all paired edges. -/
theorem identified_iff_boundarySourceHomeomorph
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (x y : presentation.Source) :
    presentation.Identified.r x y ↔
      (presentation.boundaryRegions regionEquiv hregion).Identified.r
        (presentation.boundarySourceHomeomorph regionEquiv hregion x)
        (presentation.boundarySourceHomeomorph regionEquiv hregion y) := by
  -- Transport the generated equivalence closure through the direct-relation equivalence.
  exact eqvGen_iff_of_equiv
    (presentation.boundarySourceHomeomorph regionEquiv hregion).toEquiv
    (presentation.related_iff_edgeRelated_boundarySourceHomeomorph regionEquiv hregion)
    x y

/-- Helper for Theorem 78.2: the canonical boundary regions lifted to the
universe of a prospective presented space. -/
@[expose]
noncomputable def liftedBoundaryRegions
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    LabellingScheme.PolygonalRegions.{v, w} presentation.boundaryScheme where
  Point region := ULift.{w}
    ((presentation.boundaryRegions regionEquiv hregion).Point region)
  topology region := TopologicalSpace.induced ULift.down
    ((presentation.boundaryRegions regionEquiv hregion).topology region)
  edge region edge t :=
    ULift.up ((presentation.boundaryRegions regionEquiv hregion).edge region edge t)

/-- Helper for Theorem 78.2: lifting every component gives a homeomorphism of
the disjoint unions of the original and universe-lifted boundary regions. -/
noncomputable def boundaryLiftSourceHomeomorph
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    (presentation.boundaryRegions regionEquiv hregion).Source ≃ₜ
      (presentation.liftedBoundaryRegions regionEquiv hregion).Source :=
  let original := presentation.boundaryRegions regionEquiv hregion
  let lifted := presentation.liftedBoundaryRegions regionEquiv hregion
  letI : ∀ region, TopologicalSpace (original.Point region) :=
    fun region ↦ original.topology region
  letI : ∀ region, TopologicalSpace (lifted.Point region) :=
    fun region ↦ lifted.topology region
  IsHomeomorph.homeomorph
    (Sigma.map (Equiv.refl _) fun _ ↦ Homeomorph.ulift.symm)
    (IsHomeomorph.sigmaMap (Equiv.refl _).bijective fun _ ↦
      Homeomorph.ulift.symm.isHomeomorph)

/-- Helper for Theorem 78.2: the componentwise lift sends every original
boundary edge point to the corresponding lifted edge point. -/
theorem boundaryLiftSourceHomeomorph_edge
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (region : LabellingScheme.Occurrence presentation.boundaryScheme)
    (edge : Fin region.1.1.length) (t : unitInterval) :
    presentation.boundaryLiftSourceHomeomorph regionEquiv hregion
        ⟨region, (presentation.boundaryRegions regionEquiv hregion).edge region edge t⟩ =
      ⟨region, (presentation.liftedBoundaryRegions regionEquiv hregion).edge
        region edge t⟩ := by
  -- Both the sigma map and the fiber homeomorphism compute by `ULift.up`.
  simp only [boundaryLiftSourceHomeomorph, IsHomeomorph.homeomorph_apply]
  rfl

/-- Helper for Theorem 78.2: universe lifting preserves and reflects direct
labelled-edge relations under the componentwise source homeomorphism. -/
theorem edgeRelated_liftedBoundary_iff
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (x y : (presentation.boundaryRegions regionEquiv hregion).Source) :
    (presentation.boundaryRegions regionEquiv hregion).EdgeRelated x y ↔
      (presentation.liftedBoundaryRegions regionEquiv hregion).EdgeRelated
        (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion x)
        (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion y) := by
  constructor
  · intro hxy
    unfold LabellingScheme.PolygonalRegions.EdgeRelated at hxy ⊢
    obtain ⟨first, second, firstEdge, secondEdge, t, hlabel, hx, hy⟩ := hxy
    refine ⟨first, second, firstEdge, secondEdge, t, hlabel, ?_, ?_⟩
    · calc
        presentation.boundaryLiftSourceHomeomorph regionEquiv hregion x =
            presentation.boundaryLiftSourceHomeomorph regionEquiv hregion
              ⟨first, (presentation.boundaryRegions regionEquiv hregion).edge
                first firstEdge t⟩ :=
          congrArg (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion) hx
        _ = ⟨first, (presentation.liftedBoundaryRegions regionEquiv hregion).edge
              first firstEdge t⟩ :=
          presentation.boundaryLiftSourceHomeomorph_edge
            regionEquiv hregion first firstEdge t
    · let parameter :=
        if (first.1.1.get firstEdge).2 = (second.1.1.get secondEdge).2 then t
        else unitInterval.symm t
      calc
        presentation.boundaryLiftSourceHomeomorph regionEquiv hregion y =
            presentation.boundaryLiftSourceHomeomorph regionEquiv hregion
              ⟨second, (presentation.boundaryRegions regionEquiv hregion).edge
                second secondEdge parameter⟩ :=
          congrArg (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion) hy
        _ = ⟨second, (presentation.liftedBoundaryRegions regionEquiv hregion).edge
              second secondEdge parameter⟩ :=
          presentation.boundaryLiftSourceHomeomorph_edge
            regionEquiv hregion second secondEdge parameter
  · intro hxy
    unfold LabellingScheme.PolygonalRegions.EdgeRelated at hxy ⊢
    obtain ⟨first, second, firstEdge, secondEdge, t, hlabel, hx, hy⟩ := hxy
    refine ⟨first, second, firstEdge, secondEdge, t, hlabel, ?_, ?_⟩
    · apply (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion).injective
      calc
        presentation.boundaryLiftSourceHomeomorph regionEquiv hregion x =
            ⟨first, (presentation.liftedBoundaryRegions regionEquiv hregion).edge
              first firstEdge t⟩ := hx
        _ = presentation.boundaryLiftSourceHomeomorph regionEquiv hregion
            ⟨first, (presentation.boundaryRegions regionEquiv hregion).edge
              first firstEdge t⟩ :=
          (presentation.boundaryLiftSourceHomeomorph_edge
            regionEquiv hregion first firstEdge t).symm
    · let parameter :=
        if (first.1.1.get firstEdge).2 = (second.1.1.get secondEdge).2 then t
        else unitInterval.symm t
      apply (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion).injective
      calc
        presentation.boundaryLiftSourceHomeomorph regionEquiv hregion y =
            ⟨second, (presentation.liftedBoundaryRegions regionEquiv hregion).edge
              second secondEdge parameter⟩ := hy
        _ = presentation.boundaryLiftSourceHomeomorph regionEquiv hregion
            ⟨second, (presentation.boundaryRegions regionEquiv hregion).edge
              second secondEdge parameter⟩ :=
          (presentation.boundaryLiftSourceHomeomorph_edge
            regionEquiv hregion second secondEdge parameter).symm

/-- Helper for Theorem 78.2: universe lifting preserves the generated boundary
identification relation. -/
theorem identified_liftedBoundary_iff
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i)
    (x y : (presentation.boundaryRegions regionEquiv hregion).Source) :
    (presentation.boundaryRegions regionEquiv hregion).Identified.r x y ↔
      (presentation.liftedBoundaryRegions regionEquiv hregion).Identified.r
        (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion x)
        (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion y) := by
  -- Apply generated-relation transport to the direct-relation lift equivalence.
  exact eqvGen_iff_of_equiv
    (presentation.boundaryLiftSourceHomeomorph regionEquiv hregion).toEquiv
    (presentation.edgeRelated_liftedBoundary_iff regionEquiv hregion) x y

/-- Helper for Theorem 78.2: universe lifting retains the cyclic-polygon
presentation of every canonical boundary region. -/
theorem liftedBoundaryRegions_isPolygonal
    (presentation : PolygonalPasting ι S)
    (regionEquiv : ι ≃ LabellingScheme.Occurrence presentation.boundaryScheme)
    (hregion : ∀ i, (regionEquiv i).1 = presentation.boundaryWord i) :
    (liftedBoundaryRegions.{u, v, w} presentation regionEquiv hregion).IsPolygonal := by
  let originalRegions := presentation.boundaryRegions regionEquiv hregion
  let liftedRegions : LabellingScheme.PolygonalRegions.{v, w}
      presentation.boundaryScheme :=
    liftedBoundaryRegions.{u, v, w} presentation regionEquiv hregion
  apply (LabellingScheme.PolygonalRegions.isPolygonal_iff liftedRegions).mpr
  intro region
  have horiginal : originalRegions.IsPolygonal :=
    presentation.boundaryRegions_isPolygonal regionEquiv hregion
  rw [LabellingScheme.PolygonalRegions.isPolygonal_iff] at horiginal
  obtain ⟨cyclicRegion⟩ := horiginal region
  letI : TopologicalSpace (originalRegions.Point region) :=
    originalRegions.topology region
  letI : TopologicalSpace (liftedRegions.Point region) :=
    liftedRegions.topology region
  let liftedHomeomorph :
      LabellingScheme.PolygonalRegions.RegionHomeomorph liftedRegions region
        cyclicRegion.polygon.region :=
    (Homeomorph.ulift : ULift.{w} (originalRegions.Point region) ≃ₜ
      originalRegions.Point region).trans cyclicRegion.homeomorph
  refine ⟨LabellingScheme.PolygonalRegions.CyclicRegion.ofHomeomorph
    cyclicRegion.polygon liftedHomeomorph ?_⟩
  intro edge t
  -- `Homeomorph.ulift` removes the `ULift.up` inserted in the lifted edge.
  exact cyclicRegion.edgeCompatibility edge t

/-- Helper for Theorem 78.2: the canonical boundary labelling scheme presents
every space homeomorphic to the original indexed polygonal realization. -/
theorem boundaryScheme_presents {X : Type w} [TopologicalSpace X]
    (presentation : PolygonalPasting ι S)
    (hrealization : Nonempty (presentation.Realization ≃ₜ X)) :
    presentation.boundaryScheme.Presents X := by
  classical
  obtain ⟨regionEquiv, hregion⟩ := presentation.exists_boundaryOccurrenceEquiv
  let originalRegions := presentation.boundaryRegions regionEquiv hregion
  let regions := presentation.liftedBoundaryRegions regionEquiv hregion
  let originalSourceHomeomorph :=
    presentation.boundarySourceHomeomorph regionEquiv hregion
  let liftSourceHomeomorph :=
    presentation.boundaryLiftSourceHomeomorph regionEquiv hregion
  let originalRealizationHomeomorph : presentation.Realization ≃ₜ
      originalRegions.Realization :=
    Homeomorph.Quotient.congr originalSourceHomeomorph
      (presentation.identified_iff_boundarySourceHomeomorph regionEquiv hregion)
  let liftRealizationHomeomorph : originalRegions.Realization ≃ₜ regions.Realization :=
    Homeomorph.Quotient.congr liftSourceHomeomorph
      (presentation.identified_liftedBoundary_iff regionEquiv hregion)
  let targetHomeomorph : regions.Realization ≃ₜ X :=
    liftRealizationHomeomorph.symm.trans
      (originalRealizationHomeomorph.symm.trans (Classical.choice hrealization))
  let q : regions.Source → X := targetHomeomorph ∘ regions.quotientMap
  rw [LabellingScheme.presents_iff]
  refine ⟨regions, presentation.liftedBoundaryRegions_isPolygonal regionEquiv hregion, q, ?_⟩
  constructor
  · -- A homeomorphism after the canonical quotient remains a quotient map.
    exact targetHomeomorph.isQuotientMap.comp regions.quotientMap_realizes.isQuotientMap
  · intro x y
    -- Injectivity of the target homeomorphism leaves precisely the canonical quotient fibers.
    simp only [q, Function.comp_apply, targetHomeomorph.injective.eq_iff]
    exact regions.quotientMap_realizes.fibers x y

/-- Helper for Theorem 78.2: edge pairing in an indexed polygonal pasting
induces letter pairing in its canonical boundary labelling scheme. -/
theorem pairsLetters_boundaryScheme (presentation : PolygonalPasting ι S)
    (hpairs : presentation.PairsEdges) :
    presentation.boundaryScheme.PairsLetters := by
  classical
  -- Choose the bundled edge-to-letter equivalence once for the whole proof.
  obtain ⟨regionEquiv, hregion⟩ := presentation.exists_boundaryOccurrenceEquiv
  let letterEquiv := presentation.boundaryLetterEquiv regionEquiv hregion
  rw [LabellingScheme.pairsLetters_iff]
  intro region edge
  let source := letterEquiv.symm ⟨region, edge⟩
  have hsourceImage : letterEquiv source = ⟨region, edge⟩ := by
    simp only [source, Equiv.apply_symm_apply]
  -- Map the unique indexed mate forward to obtain the scheme mate.
  obtain ⟨mate, hmate, hunique⟩ :=
    (presentation.pairsEdges_iff.mp hpairs) source.1 source.2
  refine ⟨letterEquiv mate, ?_, ?_⟩
  · constructor
    · -- Distinct indexed edges remain distinct after applying the equivalence.
      intro heq
      apply hmate.1
      apply letterEquiv.injective
      calc
        letterEquiv mate = ⟨region, edge⟩ := heq
        _ = letterEquiv source := hsourceImage.symm
    · -- The lookup computation transports the equal-label equation.
      calc
        ((letterEquiv mate).1.1.1.get (letterEquiv mate).2).1 =
            (presentation.pasting mate.1).label mate.2 :=
          congrArg Prod.fst
            (presentation.boundaryLetterEquiv_letter regionEquiv hregion mate)
        _ = (presentation.pasting source.1).label source.2 := hmate.2
        _ = ((letterEquiv source).1.1.1.get (letterEquiv source).2).1 :=
          (congrArg Prod.fst
            (presentation.boundaryLetterEquiv_letter regionEquiv hregion source)).symm
        _ = (region.1.1.get edge).1 := by
          rw [hsourceImage]
  · intro candidate hcandidate
    let sourceCandidate := letterEquiv.symm candidate
    have hcandidateImage : letterEquiv sourceCandidate = candidate := by
      simp only [sourceCandidate, Equiv.apply_symm_apply]
    -- Pull an arbitrary scheme candidate back and invoke indexed uniqueness.
    have hsourceCandidate :
        sourceCandidate ≠ source ∧
          (presentation.pasting sourceCandidate.1).label sourceCandidate.2 =
            (presentation.pasting source.1).label source.2 := by
      constructor
      · intro heq
        apply hcandidate.1
        calc
          candidate = letterEquiv sourceCandidate := hcandidateImage.symm
          _ = letterEquiv source := congrArg letterEquiv heq
          _ = ⟨region, edge⟩ := hsourceImage
      · calc
          (presentation.pasting sourceCandidate.1).label sourceCandidate.2 =
              ((letterEquiv sourceCandidate).1.1.1.get
                (letterEquiv sourceCandidate).2).1 :=
            (congrArg Prod.fst
              (presentation.boundaryLetterEquiv_letter regionEquiv hregion
                sourceCandidate)).symm
          _ = (candidate.1.1.1.get candidate.2).1 := by
            rw [hcandidateImage]
          _ = (region.1.1.get edge).1 := hcandidate.2
          _ = ((letterEquiv source).1.1.1.get (letterEquiv source).2).1 := by
            rw [hsourceImage]
          _ = (presentation.pasting source.1).label source.2 :=
            congrArg Prod.fst
              (presentation.boundaryLetterEquiv_letter regionEquiv hregion source)
    have hsourceEq : sourceCandidate = mate := hunique sourceCandidate hsourceCandidate
    calc
      candidate = letterEquiv sourceCandidate := hcandidateImage.symm
      _ = letterEquiv mate := congrArg letterEquiv hsourceEq

/-- Helper for Theorem 78.2: two regions are adjacent when they contain edges with the
same label. -/
def regionAdjacent (presentation : PolygonalPasting ι S) (i j : ι) : Prop :=
  ∃ edgeᵢ edgeⱼ,
    (presentation.pasting i).label edgeᵢ = (presentation.pasting j).label edgeⱼ

/-- Helper for Theorem 78.2: region adjacency is symmetric. -/
theorem regionAdjacent_symm (presentation : PolygonalPasting ι S) {i j : ι}
    (hij : presentation.regionAdjacent i j) :
    presentation.regionAdjacent j i := by
  -- Reverse the two witnessing edges and the label equality.
  obtain ⟨edgeᵢ, edgeⱼ, hlabel⟩ := hij
  exact ⟨edgeⱼ, edgeᵢ, hlabel.symm⟩

/-- Helper for Theorem 78.2: in a paired presentation, every edge has an adjacent
region containing its uniquely labelled mate. -/
theorem exists_regionAdjacent_of_pairsEdges (presentation : PolygonalPasting ι S)
    (hpairs : presentation.PairsEdges) (i : ι) (edge : Fin (presentation.sides i)) :
    ∃ j, presentation.regionAdjacent i j := by
  -- Use the region component of the unique distinct mate supplied by edge pairing.
  obtain ⟨mate, hmate, _⟩ := (presentation.pairsEdges_iff.mp hpairs) i edge
  exact ⟨mate.1, edge, mate.2, hmate.2.symm⟩

/-- Helper for Theorem 78.2: two front-normalized words beginning with the same
unsigned label can be pasted while preserving a proper presentation. -/
theorem exists_pastedPresentation_of_frontPair
    {X : Type w} [TopologicalSpace X] (c : S)
    (firstSign secondSign : Bool) (firstTail secondTail : List (S × Bool))
    (rest : LabellingScheme S) (hfirstLength : 2 ≤ firstTail.length)
    (hsecondLength : 2 ≤ secondTail.length)
    (hproper : LabellingScheme.Proper
      (⟨(c, firstSign) :: firstTail,
          PolygonWord.consLetter_length (c, firstSign) firstTail hfirstLength⟩ ::ₘ
        ⟨(c, secondSign) :: secondTail,
          PolygonWord.consLetter_length (c, secondSign) secondTail hsecondLength⟩ ::ₘ
        rest))
    (hpresents : LabellingScheme.Presents
      (⟨(c, firstSign) :: firstTail,
          PolygonWord.consLetter_length (c, firstSign) firstTail hfirstLength⟩ ::ₘ
        ⟨(c, secondSign) :: secondTail,
          PolygonWord.consLetter_length (c, secondSign) secondTail hsecondLength⟩ ::ₘ
        rest) X) :
    ∃ reduced : LabellingScheme S,
      reduced.card + 1 =
          (⟨(c, firstSign) :: firstTail,
              PolygonWord.consLetter_length (c, firstSign) firstTail hfirstLength⟩ ::ₘ
            ⟨(c, secondSign) :: secondTail,
              PolygonWord.consLetter_length (c, secondSign) secondTail hsecondLength⟩ ::ₘ
            rest).card ∧
        reduced.Proper ∧ reduced.Presents X := by
  classical
  let firstWord : PolygonWord S :=
    ⟨(c, firstSign) :: firstTail,
      PolygonWord.consLetter_length (c, firstSign) firstTail hfirstLength⟩
  let secondWord : PolygonWord S :=
    ⟨(c, secondSign) :: secondTail,
      PolygonWord.consLetter_length (c, secondSign) secondTail hsecondLength⟩
  have hproperWords :
      LabellingScheme.Proper (firstWord ::ₘ secondWord ::ₘ rest) := hproper
  have hpresentsWords :
      LabellingScheme.Presents (firstWord ::ₘ secondWord ::ₘ rest) X := hpresents
  by_cases hsign : firstSign = secondSign
  · subst secondSign
    let invertedTail :=
      firstTail.reverse.map (fun letter ↦ (letter.1, !letter.2))
    have hinvertedLength : 2 ≤ invertedTail.length := by
      simpa only [invertedTail, List.length_map, List.length_reverse]
        using hfirstLength
    let invertedWord : PolygonWord S :=
      ⟨invertedTail ++ [(c, !firstSign)],
        PolygonWord.appendLetter_length invertedTail (c, !firstSign)
          hinvertedLength⟩
    have hinverseWord : firstWord.formalInverse = invertedWord := by
      apply Subtype.ext
      simp only [firstWord, invertedWord, invertedTail,
        PolygonWord.formalInverse_val, List.reverse_cons, List.map_append,
        List.map_reverse, List.map_singleton]
    have hproperInverse :
        LabellingScheme.Proper (invertedWord ::ₘ secondWord ::ₘ rest) := by
      rw [← hinverseWord]
      exact (LabellingScheme.proper_formalInverseCons_iff firstWord
        (secondWord ::ₘ rest)).mpr hproperWords
    have hpresentsInverse :
        LabellingScheme.Presents (invertedWord ::ₘ secondWord ::ₘ rest) X := by
      rw [← hinverseWord]
      exact LabellingScheme.Presents.formalInverseCons hpresentsWords
    let cut := LabellingScheme.Cut.ofProperPair invertedTail secondTail c
      firstSign rest hinvertedLength hsecondLength hproperInverse
    obtain ⟨hcard, hreducedProper, hreducedPresents⟩ :=
      cut.pasteProperPresentation hproperInverse hpresentsInverse
    -- Formal inversion corrects equal signs; the cut then removes the displayed pair.
    refine ⟨_, ?_, hreducedProper, hreducedPresents⟩
    simp only [Multiset.card_cons] at hcard ⊢
  · have hopposite : firstSign = !secondSign := by
      exact Bool.eq_not_iff.mpr hsign
    subst firstSign
    have hsourceLength : 3 ≤ ([(c, !secondSign)] ++ firstTail).length := by
      simp only [List.singleton_append, List.length_cons]
      omega
    let rotatedWord : PolygonWord S :=
      ⟨firstTail ++ [(c, !secondSign)],
        PolygonWord.appendLetter_length firstTail (c, !secondSign)
          hfirstLength⟩
    have hrotatedWord :
        (⟨firstTail ++ [(c, !secondSign)],
            PolygonWord.appendSwap_length [(c, !secondSign)] firstTail
              hsourceLength⟩ : PolygonWord S) = rotatedWord := by
      apply Subtype.ext
      rfl
    have hproperRotated :
        LabellingScheme.Proper (rotatedWord ::ₘ secondWord ::ₘ rest) := by
      rw [← hrotatedWord]
      exact (LabellingScheme.proper_appendSwap_iff [(c, !secondSign)]
        firstTail (secondWord ::ₘ rest) hsourceLength).mpr hproperWords
    have hpresentsRotated :
        LabellingScheme.Presents (rotatedWord ::ₘ secondWord ::ₘ rest) X := by
      rw [← hrotatedWord]
      exact LabellingScheme.Presents.appendSwap [(c, !secondSign)] firstTail
        (secondWord ::ₘ rest) hsourceLength hpresentsWords
    let cut := LabellingScheme.Cut.ofProperPair firstTail secondTail c
      secondSign rest hfirstLength hsecondLength hproperRotated
    obtain ⟨hcard, hreducedProper, hreducedPresents⟩ :=
      cut.pasteProperPresentation hproperRotated hpresentsRotated
    -- Opposite signs already have cut form after rotating the first letter to the end.
    refine ⟨_, ?_, hreducedProper, hreducedPresents⟩
    simp only [Multiset.card_cons] at hcard ⊢

/-- Helper for Theorem 78.2: two regions sharing a label in a connected proper
presentation can be normalized and pasted to reduce the region count by one. -/
theorem exists_smallerProperPresentation
    {X : Type w} [TopologicalSpace X] [ConnectedSpace X]
    (scheme : LabellingScheme S) (hproper : scheme.Proper)
    (hpresents : scheme.Presents X) (hcard : 1 < scheme.card) :
    ∃ reduced : LabellingScheme S,
      reduced.card + 1 = scheme.card ∧ reduced.Proper ∧ reduced.Presents X := by
  classical
  obtain ⟨first, second, hne, firstEdge, secondEdge, hlabel⟩ :=
    LabellingScheme.exists_equalLabel_in_distinctRegions_of_connectedPresentation
      scheme hpresents hcard
  obtain ⟨rest, hscheme⟩ :=
    LabellingScheme.exists_twoOccurrenceDecomposition scheme hne
  have hproperSplit :
      LabellingScheme.Proper (first.1 ::ₘ second.1 ::ₘ rest) := by
    rw [← hscheme]
    exact hproper
  have hpresentsSplit :
      LabellingScheme.Presents (first.1 ::ₘ second.1 ::ₘ rest) X := by
    rw [← hscheme]
    exact hpresents
  -- Rotate the chosen occurrence in each polygon word to the first position.
  obtain ⟨firstTail, hfirstLength, hproperFirst, hpresentsFirst⟩ :=
    LabellingScheme.exists_presentationWithSelectedLetterFirst first.1
      firstEdge (second.1 ::ₘ rest) hproperSplit hpresentsSplit
  let firstWord : PolygonWord S :=
    ⟨first.1.1.get firstEdge :: firstTail,
      PolygonWord.consLetter_length (first.1.1.get firstEdge) firstTail
        hfirstLength⟩
  have hproperSecondInput :
      LabellingScheme.Proper (second.1 ::ₘ firstWord ::ₘ rest) := by
    rw [Multiset.cons_swap]
    exact hproperFirst
  have hpresentsSecondInput :
      LabellingScheme.Presents (second.1 ::ₘ firstWord ::ₘ rest) X := by
    rw [Multiset.cons_swap]
    exact hpresentsFirst
  obtain ⟨secondTail, hsecondLength, hproperSecond, hpresentsSecond⟩ :=
    LabellingScheme.exists_presentationWithSelectedLetterFirst second.1
      secondEdge (firstWord ::ₘ rest) hproperSecondInput hpresentsSecondInput
  let secondWord : PolygonWord S :=
    ⟨second.1.1.get secondEdge :: secondTail,
      PolygonWord.consLetter_length (second.1.1.get secondEdge) secondTail
        hsecondLength⟩
  have hproperPair :
      LabellingScheme.Proper (firstWord ::ₘ secondWord ::ₘ rest) := by
    rw [Multiset.cons_swap]
    exact hproperSecond
  have hpresentsPair :
      LabellingScheme.Presents (firstWord ::ₘ secondWord ::ₘ rest) X := by
    rw [Multiset.cons_swap]
    exact hpresentsSecond
  let c := (first.1.1.get firstEdge).1
  let firstSign := (first.1.1.get firstEdge).2
  let secondSign := (second.1.1.get secondEdge).2
  have hfirstLetter : first.1.1.get firstEdge = (c, firstSign) := by
    exact Prod.ext rfl rfl
  have hsecondLetter : second.1.1.get secondEdge = (c, secondSign) := by
    exact Prod.ext hlabel.symm rfl
  simp only [firstWord, secondWord, hfirstLetter, hsecondLetter]
    at hproperPair hpresentsPair
  obtain ⟨reduced, hreducedCard, hreducedProper, hreducedPresents⟩ :=
    exists_pastedPresentation_of_frontPair c firstSign secondSign
      firstTail secondTail rest hfirstLength hsecondLength hproperPair hpresentsPair
  -- The two rotations and the paste change no card except for removing one word.
  refine ⟨reduced, ?_, hreducedProper, hreducedPresents⟩
  calc
    reduced.card + 1 =
        (⟨(c, firstSign) :: firstTail,
            PolygonWord.consLetter_length (c, firstSign) firstTail hfirstLength⟩ ::ₘ
          ⟨(c, secondSign) :: secondTail,
            PolygonWord.consLetter_length (c, secondSign) secondTail hsecondLength⟩ ::ₘ
          rest).card := hreducedCard
    _ = scheme.card := by
      rw [hscheme]
      simp only [Multiset.card_cons]

/-- Helper for Theorem 78.2: a proper singleton presentation is the realization
of one cyclic polygon whose edges are paired. -/
theorem exists_edgePasting_of_singletonProperPresentation
    {X : Type w} [TopologicalSpace X] (word : PolygonWord S)
    (hproper : ({word} : LabellingScheme S).Proper)
    (hpresents : ({word} : LabellingScheme S).Presents X) :
    ∃ (n : ℕ) (T : Type) (poly : CyclicPolygon n) (pasting : poly.EdgePasting T),
      pasting.PairsEdges ∧ Nonempty (X ≃ₜ pasting.Realization) := by
    classical
    -- Extract the sole polygonal region and the quotient map realizing `X`.
    rw [LabellingScheme.presents_iff] at hpresents
    obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
    let selected :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence word
    obtain ⟨presentation⟩ :=
      (LabellingScheme.PolygonalRegions.isPolygonal_iff regions).mp
        hpolygonal selected
    have hlength : selected.1.1.length = word.1.length :=
      CyclicPolygon.EdgePasting.singletonBoundaryOccurrence_length
        word rfl selected
    -- Replace the selected region by a cyclic polygon with exactly the word's sides.
    obtain ⟨sourceHomeomorph, hsourceHomeomorph⟩ :=
      regions.exists_singletonSourceHomeomorph_transportSides
        word presentation hlength
    let poly := CyclicPolygon.transportSides hlength presentation.polygon
    let pasting := LabellingScheme.edgePastingOfWordLabelClasses word poly
    have hpairs : pasting.PairsEdges :=
      LabellingScheme.edgePastingOfWordLabelClasses_pairsEdges
        word poly hproper
    -- The source homeomorphism carries the direct labelled-edge relation to
    -- the quotient-label pasting relation.
    have hrelated : ∀ x y, regions.EdgeRelated x y ↔
        pasting.Related (sourceHomeomorph x) (sourceHomeomorph y) := by
      intro x y
      calc
        regions.EdgeRelated x y ↔
            (LabellingScheme.edgePastingOfWord word poly).Related
              (sourceHomeomorph x) (sourceHomeomorph y) :=
          regions.edgeRelated_iff_edgePastingOfWord word presentation hlength
            sourceHomeomorph hsourceHomeomorph x y
        _ ↔ pasting.Related (sourceHomeomorph x) (sourceHomeomorph y) :=
          (LabellingScheme.edgePastingOfWordLabelClasses_related_iff
            word poly (sourceHomeomorph x) (sourceHomeomorph y)).symm
    -- Transport the generated equivalence relation, then descend to quotients.
    have hidentified : ∀ x y, regions.Identified.r x y ↔
        pasting.Identified.r (sourceHomeomorph x) (sourceHomeomorph y) := by
      intro x y
      exact eqvGen_iff_of_equiv sourceHomeomorph.toEquiv hrelated x y
    let realizationHomeomorph : regions.Realization ≃ₜ pasting.Realization :=
      Homeomorph.Quotient.congr sourceHomeomorph hidentified
    obtain ⟨regionsToX⟩ := regions.quotientHomeomorphOfRealizes q hrealizes
    -- Compose the inverse realizing homeomorphism with the quotient transport.
    refine ⟨word.1.length,
      Quotient (Setoid.ker (fun edge : Fin word.1.length ↦
        (word.1.get edge).1)), poly, pasting, hpairs, ?_⟩
    exact ⟨regionsToX.symm.trans realizationHomeomorph⟩

/-- Helper for Theorem 78.2: a connected space with a paired polygonal-word
presentation admits a presentation by one paired polygonal region. -/
theorem exists_edgePasting_of_connectedPairedPresentation
    {X : Type w} [TopologicalSpace X] [ConnectedSpace X]
    (scheme : LabellingScheme S) (hpairs : scheme.PairsLetters)
    (hpresents : scheme.Presents X) :
    ∃ (n : ℕ) (T : Type) (poly : CyclicPolygon n) (pasting : poly.EdgePasting T),
      pasting.PairsEdges ∧ Nonempty (X ≃ₜ pasting.Realization) := by
    classical
    have hproper : scheme.Proper :=
      (LabellingScheme.pairsLetters_iff_proper scheme).mp hpairs
    -- Strong induction uses the number of polygon words as the decreasing rank.
    induction hschemeCard : scheme.card using Nat.strong_induction_on generalizing scheme with
    | h regionCount inductionHypothesis =>
        have hone : 1 ≤ regionCount := by
          rw [← hschemeCard]
          exact LabellingScheme.one_le_card_of_presents scheme hpresents
        rcases regionCount with _ | remainingCount
        · omega
        · rcases remainingCount with _ | remainingCount
          · obtain ⟨word, hword⟩ := Multiset.card_eq_one.mp hschemeCard
            subst scheme
            exact exists_edgePasting_of_singletonProperPresentation
              word hproper hpresents
          · have hmoreThanOne : 1 < scheme.card := by omega
            obtain ⟨reduced, hreducedCard, hreducedProper, hreducedPresents⟩ :=
              exists_smallerProperPresentation scheme hproper hpresents hmoreThanOne
            apply inductionHypothesis reduced.card
            · omega
            · exact (LabellingScheme.pairsLetters_iff_proper reduced).mpr hreducedProper
            · exact hreducedPresents
            · exact hreducedProper
            · rfl

/-- Helper for Theorem 78.2: a connected finite paired polygonal presentation can be
consolidated into one polygonal region without changing its realized space. -/
theorem exists_singlePolygon_of_connectedRealization
    {X : Type w} [TopologicalSpace X] [ConnectedSpace X]
    (presentation : PolygonalPasting ι S) (hpairs : presentation.PairsEdges)
    (hrealization : Nonempty (presentation.Realization ≃ₜ X)) :
    ∃ (n : ℕ) (T : Type) (poly : CyclicPolygon n) (pasting : poly.EdgePasting T),
      pasting.PairsEdges ∧ Nonempty (X ≃ₜ pasting.Realization) := by
  -- Route correction: avoid rebuilding geometric polygon merges; convert once to a
  -- `LabellingScheme.Presents` witness and use the Section 76 paste-preservation API.
  have hpresents := presentation.boundaryScheme_presents hrealization
  have hletters := presentation.pairsLetters_boundaryScheme hpairs
  -- The remaining abstract reduction theorem now consumes the checked boundary interface.
  exact exists_edgePasting_of_connectedPairedPresentation
    presentation.boundaryScheme hletters hpresents

end PolygonalPasting

/-- Theorem 78.2. A compact connected triangulable surface is homeomorphic to
the realization of one planar polygonal region whose edges are pasted in pairs. -/
theorem compactConnectedTriangulableSurface_homeomorphic_polygonalPasting
    (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    [CompactSpace X] [ConnectedSpace X]
    (h_triangulable : Triangulable X) :
    ∃ (n : ℕ) (S : Type) (poly : CyclicPolygon n) (pasting : poly.EdgePasting S),
      pasting.PairsEdges ∧ Nonempty (X ≃ₜ pasting.Realization) := by
  -- First use Theorem 78.1 to present `X` by finitely many paired triangles.
  obtain ⟨m, S, presentation, _, hpairs, hrealization⟩ :=
    compactTriangulableSurface_homeomorphicRealization X h_triangulable
  -- Consolidate the connected finite presentation into a single polygon.
  exact presentation.exists_singlePolygon_of_connectedRealization hpairs hrealization
