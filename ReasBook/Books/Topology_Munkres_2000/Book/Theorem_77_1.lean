module

public import Topology_Munkres_2000.Book.Definition_74_3.EdgePairing
public import Topology_Munkres_2000.Book.Theorem_74_2.Presentation
public import Topology_Munkres_2000.Book.Theorem_75_5.Classification
public import Topology_Munkres_2000.Book.Theorem_77_1.BoundaryPresentation
public import Topology_Munkres_2000.Book.Theorem_77_1.CancelCompression
public import Topology_Munkres_2000.Book.Theorem_77_1.PairedWordCombinatorics
public import Topology_Munkres_2000.Book.Theorem_77_1.SourceComparison

public section

universe u v

namespace CyclicPolygon.EdgeCompression

/-- Helper for Theorem 77.1: a unit-interval parameter lies in the range of
`lowerHalfParameter` exactly when it is at most the midpoint. -/
theorem exists_lowerHalfParameter_iff (t : unitInterval) :
    (∃ s : unitInterval, lowerHalfParameter s = t) ↔ (t : ℝ) ≤ 1 / 2 := by
  constructor
  · rintro ⟨s, rfl⟩
    -- The contracted coordinate is `s / 2`, and `s` is at most one.
    rw [lowerHalfParameter_coe]
    linarith [s.property.2]
  · intro ht
    have hsourceMem : 2 * (t : ℝ) ∈ unitInterval := by
      -- Doubling a point in the lower half stays between zero and one.
      constructor
      · nlinarith [t.property.1]
      · linarith
    let source : unitInterval := ⟨2 * (t : ℝ), hsourceMem⟩
    refine ⟨source, ?_⟩
    -- The explicit rescaling is a right inverse to lower-half contraction.
    apply Subtype.ext
    rw [lowerHalfParameter_coe]
    dsimp only [source]
    ring

/-- Helper for Theorem 77.1: a unit-interval parameter lies in the range of
`upperHalfParameter` exactly when it is at least the midpoint. -/
theorem exists_upperHalfParameter_iff (t : unitInterval) :
    (∃ s : unitInterval, upperHalfParameter s = t) ↔ 1 / 2 ≤ (t : ℝ) := by
  constructor
  · rintro ⟨s, rfl⟩
    -- The contracted coordinate is `(1 + s) / 2`, and `s` is nonnegative.
    rw [upperHalfParameter_coe]
    linarith [s.property.1]
  · intro ht
    have hsourceMem : 2 * (t : ℝ) - 1 ∈ unitInterval := by
      -- Translating and doubling a point in the upper half stays in the interval.
      constructor
      · linarith
      · linarith [t.property.2]
    let source : unitInterval := ⟨2 * (t : ℝ) - 1, hsourceMem⟩
    refine ⟨source, ?_⟩
    -- The explicit affine rescaling is a right inverse to upper-half contraction.
    apply Subtype.ext
    rw [upperHalfParameter_coe]
    dsimp only [source]
    ring

/-- Helper for Theorem 77.1: every target edge parameter comes from either
the lower-half or the upper-half parametrization. -/
theorem existsLowerOrUpperHalfParameter (t : unitInterval) :
    (∃ s : unitInterval, lowerHalfParameter s = t) ∨
      ∃ s : unitInterval, upperHalfParameter s = t := by
  -- Compare the target coordinate with the midpoint and use the matching range theorem.
  rcases le_total (t : ℝ) (1 / 2) with ht | ht
  · exact Or.inl ((exists_lowerHalfParameter_iff t).mpr ht)
  · exact Or.inr ((exists_upperHalfParameter_iff t).mpr ht)

end CyclicPolygon.EdgeCompression

namespace CyclicPolygon.EdgePasting

variable {n : ℕ} {S : Type u} {poly : CyclicPolygon n}

/-- Helper for Theorem 77.1: the signed boundary list of an edge pasting has
the minimum length required of a polygon word. -/
theorem boundaryWord_three_le (pasting : poly.EdgePasting S) :
    3 ≤ pasting.boundaryWord.length := by
  -- Transfer the polygon's edge-count bound across the boundary-word length formula.
  rw [pasting.boundaryWord_length]
  exact poly.three_le

/-- Helper for Theorem 77.1: the signed boundary of an edge pasting, bundled as
a polygon word. -/
def boundaryPolygonWord (pasting : poly.EdgePasting S) : PolygonWord pasting.UsedLabel :=
  ⟨pasting.boundaryWord, boundaryWord_three_le pasting⟩

/-- Helper for Theorem 77.1: the underlying list of `boundaryPolygonWord` is
the signed boundary list of the pasting. -/
theorem boundaryPolygonWord_val (pasting : poly.EdgePasting S) :
    pasting.boundaryPolygonWord.val = pasting.boundaryWord := by
  -- Unpack only the stable list projection of the bundled boundary word.
  rfl

/-- Helper for Theorem 77.1: the bundled boundary polygon word has one letter
for each edge of the original polygon. -/
theorem boundaryPolygonWord_length (pasting : poly.EdgePasting S) :
    pasting.boundaryPolygonWord.val.length = n := by
  -- Pass through the stable list projection and use the boundary-word length formula.
  rw [pasting.boundaryPolygonWord_val, pasting.boundaryWord_length]

/-- Helper for Theorem 77.1: a letter of the bundled boundary polygon word is
the label and orientation of the corresponding polygon edge. -/
theorem boundaryPolygonWord_get (pasting : poly.EdgePasting S) (i : Fin n) :
    pasting.boundaryPolygonWord.val.get
        (Fin.cast pasting.boundaryPolygonWord_length.symm i) =
      (⟨pasting.label i, Set.mem_range_self i⟩, pasting.sign i) := by
  -- The bundled and unbundled words have the same list; proof irrelevance aligns the casts.
  unfold boundaryPolygonWord
  exact pasting.boundaryWord_get i

/-- Helper for Theorem 77.1: paired edges give every boundary occurrence a
unique distinct occurrence with the same unsigned used label. -/
theorem PairsEdges.boundaryWordLabelsPaired (pasting : poly.EdgePasting S)
    (h_pairs : pasting.PairsEdges) :
    ∀ i : Fin n, ∃! j : Fin n, j ≠ i ∧
      (pasting.boundaryWord.get (Fin.cast pasting.boundaryWord_length.symm j)).1 =
        (pasting.boundaryWord.get (Fin.cast pasting.boundaryWord_length.symm i)).1 := by
  intro i
  obtain ⟨j, hj, hj_unique⟩ := (pasting.pairsEdges_iff.mp h_pairs) i
  refine ⟨j, ⟨hj.1, ?_⟩, ?_⟩
  · -- Rewrite both boundary entries to their originating edge labels.
    rw [pasting.boundaryWord_get, pasting.boundaryWord_get]
    exact Subtype.ext hj.2
  · intro k hk
    -- Forget the used-label membership proofs and reuse uniqueness from `PairsEdges`.
    apply hj_unique k
    have hklabel : pasting.label k = pasting.label i := by
      have hkvalue := congrArg Subtype.val hk.2
      rw [pasting.boundaryWord_get, pasting.boundaryWord_get] at hkvalue
      exact hkvalue
    exact ⟨hk.1, hklabel⟩

/-- Helper for Theorem 77.1: after using the polygon word's own length as the
index type, every boundary letter still has a unique distinct mate with the
same unsigned label. -/
theorem PairsEdges.boundaryPolygonWordLabelsPaired (pasting : poly.EdgePasting S)
    (h_pairs : pasting.PairsEdges) :
    ∀ i : Fin pasting.boundaryPolygonWord.val.length,
      ∃! j : Fin pasting.boundaryPolygonWord.val.length,
        j ≠ i ∧
          (pasting.boundaryPolygonWord.val.get j).1 =
            (pasting.boundaryPolygonWord.val.get i).1 := by
  intro i
  let iEdge := Fin.cast pasting.boundaryPolygonWord_length i
  obtain ⟨jEdge, hj, hj_unique⟩ := (pasting.pairsEdges_iff.mp h_pairs) iEdge
  let j := Fin.cast pasting.boundaryPolygonWord_length.symm jEdge
  have hiLetter :
      pasting.boundaryPolygonWord.val.get i =
        (⟨pasting.label iEdge, Set.mem_range_self iEdge⟩, pasting.sign iEdge) := by
    have hletter := pasting.boundaryPolygonWord_get iEdge
    rw [Fin.leftInverse_cast pasting.boundaryPolygonWord_length i] at hletter
    exact hletter
  have hjLetter :
      pasting.boundaryPolygonWord.val.get j =
        (⟨pasting.label jEdge, Set.mem_range_self jEdge⟩, pasting.sign jEdge) := by
    exact pasting.boundaryPolygonWord_get jEdge
  refine ⟨j, ⟨?_, ?_⟩, ?_⟩
  · -- A coincidence of word positions would give a coincidence of their edge indices.
    intro hji
    apply hj.1
    apply Fin.cast_injective pasting.boundaryPolygonWord_length.symm
    calc
      Fin.cast pasting.boundaryPolygonWord_length.symm jEdge = j := rfl
      _ = i := hji
      _ = Fin.cast pasting.boundaryPolygonWord_length.symm iEdge :=
        (Fin.leftInverse_cast pasting.boundaryPolygonWord_length i).symm
  · -- Compute both letters at their corresponding edge indices.
    rw [hjLetter, hiLetter]
    exact Subtype.ext hj.2
  · intro k hk
    -- Transport uniqueness back to edge indices, then return through the inverse cast.
    let kEdge := Fin.cast pasting.boundaryPolygonWord_length k
    have hkLetter :
        pasting.boundaryPolygonWord.val.get k =
          (⟨pasting.label kEdge, Set.mem_range_self kEdge⟩, pasting.sign kEdge) := by
      have hletter := pasting.boundaryPolygonWord_get kEdge
      rw [Fin.leftInverse_cast pasting.boundaryPolygonWord_length k] at hletter
      exact hletter
    have hkLabel : pasting.label kEdge = pasting.label iEdge := by
      have hkUsed :
          (⟨pasting.label kEdge, Set.mem_range_self kEdge⟩ : pasting.UsedLabel) =
            ⟨pasting.label iEdge, Set.mem_range_self iEdge⟩ := by
        calc
          _ = (pasting.boundaryPolygonWord.val.get k).1 :=
            (congrArg Prod.fst hkLetter).symm
          _ = (pasting.boundaryPolygonWord.val.get i).1 := hk.2
          _ = _ := congrArg Prod.fst hiLetter
      exact congrArg Subtype.val hkUsed
    have hkEdge : kEdge = jEdge := by
      apply hj_unique
      constructor
      · intro hki
        apply hk.1
        apply Fin.cast_injective pasting.boundaryPolygonWord_length
        exact hki
      · exact hkLabel
    apply Fin.cast_injective pasting.boundaryPolygonWord_length
    calc
      Fin.cast pasting.boundaryPolygonWord_length k = jEdge := hkEdge
      _ = Fin.cast pasting.boundaryPolygonWord_length j :=
        (Fin.rightInverse_cast pasting.boundaryPolygonWord_length jEdge).symm

/-- Helper for Theorem 77.1: a polygon whose edges are pasted in pairs has at
least four edges. -/
theorem PairsEdges.four_le (pasting : poly.EdgePasting S)
    (h_pairs : pasting.PairsEdges) : 4 ≤ n := by
  -- The polygon already has three edges; exclude the sole remaining case by pairing its edges.
  by_contra hfour
  have hthree : 3 ≤ n := poly.three_le
  have hn : n = 3 := by
    omega
  subst n
  obtain ⟨j, hj, hj_unique⟩ :=
    (pasting.pairsEdges_iff.mp h_pairs) (0 : Fin 3)
  fin_cases j
  · exact hj.1 rfl
  · obtain ⟨k, hk, _⟩ :=
      (pasting.pairsEdges_iff.mp h_pairs) (2 : Fin 3)
    fin_cases k
    · have htwo_ne_zero : (2 : Fin 3) ≠ 0 := by
        decide
      have hmate : (2 : Fin 3) = 1 :=
        hj_unique 2 ⟨htwo_ne_zero, hk.2.symm⟩
      omega
    · have hlabel : pasting.label (2 : Fin 3) = pasting.label 0 :=
        hk.2.symm.trans hj.2
      have htwo_ne_zero : (2 : Fin 3) ≠ 0 := by
        decide
      have hmate : (2 : Fin 3) = 1 :=
        hj_unique 2 ⟨htwo_ne_zero, hlabel⟩
      omega
    · exact hk.1 rfl
  · obtain ⟨k, hk, _⟩ :=
      (pasting.pairsEdges_iff.mp h_pairs) (1 : Fin 3)
    fin_cases k
    · have hone_ne_zero : (1 : Fin 3) ≠ 0 := by
        decide
      have hmate : (1 : Fin 3) = 2 :=
        hj_unique 1 ⟨hone_ne_zero, hk.2.symm⟩
      omega
    · exact hk.1 rfl
    · have hlabel : pasting.label (1 : Fin 3) = pasting.label 0 :=
        hk.2.symm.trans hj.2
      have hone_ne_zero : (1 : Fin 3) ≠ 0 := by
        decide
      have hmate : (1 : Fin 3) = 2 :=
        hj_unique 1 ⟨hone_ne_zero, hlabel⟩
      omega

/-- Helper for Theorem 77.1: the singleton scheme formed from an edge pasting's
signed boundary word presents its canonical quotient realization. -/
theorem boundaryPolygonWord_presents (pasting : poly.EdgePasting S) :
    ({pasting.boundaryPolygonWord} : LabellingScheme pasting.UsedLabel).Presents
      pasting.Realization := by
  -- Supply the boundary word's length and lookup formulas to the generic singleton bridge.
  exact pasting.singletonBoundaryWord_presents pasting.boundaryPolygonWord
    pasting.boundaryPolygonWord_length pasting.boundaryPolygonWord_get

end CyclicPolygon.EdgePasting

namespace LabellingScheme.Presents

/-- Helper for Theorem 77.1: a presentation may be postcomposed with a
homeomorphism of its target space. -/
theorem postcomposeHomeomorph {α : Type u} {scheme : LabellingScheme α}
    {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (hpresents : scheme.Presents X) (e : X ≃ₜ Y) :
    scheme.Presents Y := by
  -- Retain the polygonal family and postcompose its quotient map with the homeomorphism.
  rw [LabellingScheme.presents_iff] at hpresents ⊢
  obtain ⟨regions, hpolygonal, q, hrealizes⟩ := hpresents
  refine ⟨regions, hpolygonal, e ∘ q, ?_⟩
  constructor
  · exact e.isQuotientMap.comp hrealizes.isQuotientMap
  · intro x y
    -- Injectivity removes the postcomposition before applying the known fiber formula.
    exact e.injective.eq_iff.trans (hrealizes.fibers x y)

end LabellingScheme.Presents

namespace SurfaceWord.IsPaired

/-- Helper for Theorem 77.1: a paired singleton polygon presentation with at
least four boundary edges is homeomorphic to one of the four standard closed
surface models. -/
theorem classifiesSingletonPresentation {α : Type u} [Infinite α]
    {X : Type v} [TopologicalSpace X] {word : PolygonWord α}
    (hpaired : SurfaceWord.IsPaired word.val) (hlength : 4 ≤ word.val.length)
    (hpresents : ({word} : LabellingScheme α).Presents X) :
    Nonempty (X ≃ₜ StandardSphere 2) ∨
      (∃ (g : ℕ) (hg : 0 < g),
        Nonempty (X ≃ₜ OrientableSurfacePresentation.nFoldTorus g hg)) ∨
      Nonempty (X ≃ₜ RealProjectivePlane) ∨
      ∃ (m : ℕ) (hm : 1 < m),
        Nonempty
          (X ≃ₜ NonorientableSurfacePresentation.mFoldProjectivePlane m hm) := by
  -- First reduce the geometric conclusion to showing that this fixed singleton
  -- scheme presents one standard model; source comparison then supplies the
  -- required homeomorphism without reopening quotient or topology internals.
  suffices hstandard :
      ({word} : LabellingScheme α).Presents (StandardSphere 2) ∨
        (∃ (g : ℕ) (hg : 0 < g),
          ({word} : LabellingScheme α).Presents
            (OrientableSurfacePresentation.nFoldTorus g hg)) ∨
        ({word} : LabellingScheme α).Presents RealProjectivePlane ∨
        ∃ (m : ℕ) (hm : 1 < m),
          ({word} : LabellingScheme α).Presents
            (NonorientableSurfacePresentation.mFoldProjectivePlane m hm) by
    rcases hstandard with hsphere | ⟨g, hg, horientable⟩ |
      hprojective | ⟨m, hm, hnonorientable⟩
    · -- Compare the given target with the standard sphere presentation.
      exact Or.inl
        (LabellingScheme.Presents.homeomorphic_of_sameScheme hpresents hsphere)
    · -- Retain the positive genus while comparing the two targets of the scheme.
      exact Or.inr (Or.inl ⟨g, hg,
        LabellingScheme.Presents.homeomorphic_of_sameScheme hpresents horientable⟩)
    · -- The one-crosscap case uses the separate projective-plane model.
      exact Or.inr (Or.inr (Or.inl
        (LabellingScheme.Presents.homeomorphic_of_sameScheme hpresents hprojective)))
    · -- Retain the nonorientable genus bound in the final indexed alternative.
      exact Or.inr (Or.inr (Or.inr ⟨m, hm,
        LabellingScheme.Presents.homeomorphic_of_sameScheme hpresents hnonorientable⟩))
  -- Route correction: cancellation is now factored through the exact
  -- cut-compress-paste interface in `CancelCompression`; the remaining task is
  -- paired-word normalization and its iteration of `presents_iff_of_cancel`.
  -- TODO: normalize the paired word to a standard singleton scheme and rewrite
  -- each cancellation step with `LabellingScheme.presents_iff_of_cancel`.
  sorry

end SurfaceWord.IsPaired

/-- Theorem 77.1. The space obtained by pasting the edges of one polygonal region
in pairs is homeomorphic to `StandardSphere 2`, to an `n`-fold torus, or to an
`m`-fold projective plane. The case `m = 1` is represented by
`RealProjectivePlane`, while the indexed standard model covers `1 < m`. -/
theorem pairedEdgePastingClassification {n : ℕ} {S : Type u}
    (poly : CyclicPolygon n) (pasting : poly.EdgePasting S)
    (h_pairs : pasting.PairsEdges) :
    Nonempty (pasting.Realization ≃ₜ StandardSphere 2) ∨
      (∃ (g : ℕ) (hg : 0 < g),
        Nonempty (pasting.Realization ≃ₜ OrientableSurfacePresentation.nFoldTorus g hg)) ∨
      Nonempty (pasting.Realization ≃ₜ RealProjectivePlane) ∨
      ∃ (m : ℕ) (hm : 1 < m),
        Nonempty
          (pasting.Realization ≃ₜ
            NonorientableSurfacePresentation.mFoldProjectivePlane m hm) := by
  -- Begin with the source proof's controlled object: the paired signed boundary word.
  have hboundaryLength : 4 ≤ pasting.boundaryPolygonWord.val.length := by
    rw [pasting.boundaryPolygonWord_length]
    exact h_pairs.four_le pasting
  let boundary := pasting.boundaryPolygonWord
  have hboundaryPairs :
      ∀ i : Fin boundary.val.length, ∃! j : Fin boundary.val.length,
        j ≠ i ∧ (boundary.val.get j).1 = (boundary.val.get i).1 := by
    exact h_pairs.boundaryPolygonWordLabelsPaired pasting
  -- Route correction: `UsedLabel` is finite and has no fresh-label supply, so
  -- move once to a sum with `ℕ` before attempting the source normalization.
  let workingBoundary := boundary.mapLabels
    (Sum.inl : pasting.UsedLabel → pasting.UsedLabel ⊕ ℕ)
  have hworkingBoundaryLength : 4 ≤ workingBoundary.val.length := by
    -- The fresh-label embedding changes labels but not the boundary rank.
    rw [PolygonWord.mapLabels_length]
    exact hboundaryLength
  have hworkingBoundaryPairs :
      ∀ i : Fin workingBoundary.val.length,
        ∃! j : Fin workingBoundary.val.length,
          j ≠ i ∧
            (workingBoundary.val.get j).1 = (workingBoundary.val.get i).1 := by
    -- Injectivity of `Sum.inl` transports the unique-mate invariant.
    exact PolygonWord.mapLabelsPreservesLabelsPaired Sum.inl Sum.inl_injective
      boundary hboundaryPairs
  have hworkingPaired : SurfaceWord.IsPaired workingBoundary.val := by
    -- Convert once from the edge API's unique mate to raw unsigned multiplicity two.
    exact (SurfaceWord.isPaired_iff_uniqueMate workingBoundary.val).mpr
      hworkingBoundaryPairs
  let labelEmbedding : pasting.UsedLabel ↪ pasting.UsedLabel ⊕ ℕ :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hworkingPresents :
      ({workingBoundary} : LabellingScheme (pasting.UsedLabel ⊕ ℕ)).Presents
        pasting.Realization := by
    -- First present the original boundary quotient, then extend its label type once.
    have hmapped := LabellingScheme.Presents.mapLabels labelEmbedding
      (pasting.boundaryPolygonWord_presents)
    have hscheme :
        LabellingScheme.mapLabels labelEmbedding
            ({boundary} : LabellingScheme pasting.UsedLabel) =
          ({workingBoundary} : LabellingScheme (pasting.UsedLabel ⊕ ℕ)) := by
      rw [LabellingScheme.mapLabels_singleton]
      rfl
    rwa [hscheme] at hmapped
  -- The paired singleton classifier now consumes exactly the controlled word,
  -- its rank bound, and the transported geometric presentation assembled above.
  exact hworkingPaired.classifiesSingletonPresentation
    hworkingBoundaryLength hworkingPresents

/-- The canonical closed-surface classification predicate satisfied by every
realization obtained from paired polygon edges. -/
theorem pairedEdgePastingClassified {n : ℕ} {S : Type u}
    (poly : CyclicPolygon n) (pasting : poly.EdgePasting S)
    (h_pairs : pasting.PairsEdges) :
    ClassifiedClosedSurface pasting.Realization :=
  (classifiedClosedSurface_iff pasting.Realization).mpr
    (pairedEdgePastingClassification poly pasting h_pairs)
