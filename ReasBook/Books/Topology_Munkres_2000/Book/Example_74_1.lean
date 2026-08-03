module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Example_74_1.Presentation
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Topology.Homeomorph.Quotient
import all Topology_Munkres_2000.Book.Example_74_1.Presentation
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import Mathlib.Tactic.FinCases

public section

open scoped Topology

namespace TriangleDisk

/-- Helper for Example 74.1: every occurrence in the singleton scheme is `region`. -/
private lemma occurrence_eq_region (r : LabellingScheme.Occurrence scheme) : r = region := by
  -- The remainder of the cons-occurrence equivalence has no elements.
  unfold region
  apply (LabellingScheme.consOccurrenceEquiv boundaryWord 0).injective
  rw [Equiv.apply_symm_apply]
  cases h : LabellingScheme.consOccurrenceEquiv boundaryWord 0 r with
  | none => rfl
  | some remaining =>
      exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim

/-- Helper for Example 74.1: the unique occurrence carries the displayed boundary word. -/
private lemma region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head word.
  rfl

/-- Helper for Example 74.1: projection from the singleton source to the standard triangle is
a homeomorphism. -/
private lemma sourceProjectionIsHomeomorph :
    IsHomeomorph (fun x : regions.Source ↦ x.2) := by
  -- Insert the triangle into the unique source summand to obtain a continuous inverse.
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · rw [continuous_iSup_dom]
    intro r
    rw [continuous_coinduced_dom]
    letI : TopologicalSpace (regions.Point r) := regions.topology r
    exact continuous_id
  · have hinclusion : Continuous[regions.topology region, regions.sourceTopology]
        (Sigma.mk region : regions.Point region → regions.Source) :=
      continuous_iSup_rng (i := region) (f := Sigma.mk region)
        (continuous_coinduced_rng (f := Sigma.mk region))
    refine ⟨fun p ↦ (⟨region, p⟩ : regions.Source), ?_, ?_, ?_⟩
    · rintro ⟨r, p⟩
      rw [occurrence_eq_region r]
    · intro p
      rfl
    · unfold regions at hinclusion ⊢
      exact hinclusion

/-- Helper for Example 74.1: the three affine sectors fold the triangle across the two
edges carrying the label `a`. -/
private noncomputable def triangleFoldCoordinates
    (p : standardTriangle) : EuclideanSpace ℝ (Fin 2) :=
  let c := (1 - p.1 0 - p.1 1) / 3
  if 2 * p.1 0 ≤ p.1 1 then
    !₂[c + 3 * p.1 0, c]
  else if p.1 0 ≤ 2 * p.1 1 then
    !₂[c - p.1 0 + 2 * p.1 1, c + 2 * p.1 0 - p.1 1]
  else
    !₂[c, c + 3 * p.1 1]

/-- Helper for Example 74.1: the affine fold lands in the standard triangle. -/
private lemma triangleFoldCoordinates_mem (p : standardTriangle) :
    triangleFoldCoordinates p ∈ standardTriangle := by
  -- In each sector the three target barycentric coordinates are nonnegative.
  have hp := (mem_standardTriangle p.1).mp p.2
  unfold triangleFoldCoordinates
  split_ifs with hleft hmiddle
  · rw [mem_standardTriangle]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · linarith
    constructor <;> linarith
  · rw [mem_standardTriangle]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · linarith
    constructor <;> linarith
  · rw [mem_standardTriangle]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · linarith
    constructor <;> linarith

/-- Helper for Example 74.1: the bundled fold of the standard triangle. -/
private noncomputable def triangleFold : standardTriangle → standardTriangle :=
  fun p ↦ ⟨triangleFoldCoordinates p, triangleFoldCoordinates_mem p⟩

/-- Helper for Example 74.1: the piecewise-affine fold is continuous. -/
private lemma continuous_triangleFold : Continuous triangleFold := by
  -- Adjacent affine formulas agree on their common sector seam.
  rw [continuous_induced_rng]
  unfold triangleFold triangleFoldCoordinates
  have hinner : Continuous (fun p : standardTriangle ↦
      let c := (1 - p.1 0 - p.1 1) / 3
      if p.1 0 ≤ 2 * p.1 1 then
        !₂[c - p.1 0 + 2 * p.1 1, c + 2 * p.1 0 - p.1 1]
      else !₂[c, c + 3 * p.1 1]) := by
    apply continuous_if_le
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · intro p hp
      ext i
      fin_cases i <;> simp <;> linarith
  apply continuous_if_le
  · fun_prop
  · fun_prop
  · fun_prop
  · exact hinner.continuousOn
  · intro p hp
    have hpTriangle := (mem_standardTriangle p.1).mp p.2
    simp only
    rw [if_pos]
    · ext i
      fin_cases i <;> simp <;> linarith
    · linarith

/-- Helper for Example 74.1: two triangle points are axis-equivalent when they agree, or are
matching points of the bottom and left edges. -/
private def axisEquivalent (p q : standardTriangle) : Prop :=
  p = q ∨
    (p.1 1 = 0 ∧ q.1 0 = 0 ∧ p.1 0 = q.1 1) ∨
    (p.1 0 = 0 ∧ q.1 1 = 0 ∧ p.1 1 = q.1 0)

/-- Helper for Example 74.1: the fold has precisely the fibers prescribed by the two
`a`-labelled edges. -/
private lemma triangleFold_eq_iff (p q : standardTriangle) :
    triangleFold p = triangleFold q ↔ axisEquivalent p q := by
  -- Compare the three affine branches; different target sectors cannot overlap except
  -- for the diagonal images of the two coordinate axes.
  have hpTriangle := (mem_standardTriangle p.1).mp p.2
  have hqTriangle := (mem_standardTriangle q.1).mp q.2
  constructor
  · intro heq
    have hval : triangleFoldCoordinates p = triangleFoldCoordinates q :=
      congrArg Subtype.val heq
    have hzero := congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0) hval
    have hone := congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 1) hval
    by_cases hpLeft : 2 * p.1 0 ≤ p.1 1
    · by_cases hqLeft : 2 * q.1 0 ≤ q.1 1
      · left
        simp [triangleFoldCoordinates, hpLeft, hqLeft] at hzero hone
        have hcoord0 : p.1 0 = q.1 0 := by
          linarith
        have hcoord1 : p.1 1 = q.1 1 := by
          linarith
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i
        · exact hcoord0
        · exact hcoord1
      · by_cases hqMiddle : q.1 0 ≤ 2 * q.1 1
        · simp [triangleFoldCoordinates, hpLeft, hqLeft, hqMiddle] at hzero hone
          exfalso
          linarith
        · right
          right
          simp [triangleFoldCoordinates, hpLeft, hqLeft, hqMiddle] at hzero hone
          have hpNonpos : p.1 0 ≤ 0 := by
            linarith [hqTriangle.2.1]
          have hqNonpos : q.1 1 ≤ 0 := by
            linarith [hpTriangle.1]
          have hpZero : p.1 0 = 0 := le_antisymm hpNonpos hpTriangle.1
          have hqZero : q.1 1 = 0 := le_antisymm hqNonpos hqTriangle.2.1
          have hcoordinate : p.1 1 = q.1 0 := by
            linarith
          exact ⟨hpZero, hqZero, hcoordinate⟩
    · by_cases hpMiddle : p.1 0 ≤ 2 * p.1 1
      · by_cases hqLeft : 2 * q.1 0 ≤ q.1 1
        · simp [triangleFoldCoordinates, hpLeft, hpMiddle, hqLeft] at hzero hone
          exfalso
          linarith
        · by_cases hqMiddle : q.1 0 ≤ 2 * q.1 1
          · left
            simp [triangleFoldCoordinates, hpLeft, hpMiddle, hqLeft,
              hqMiddle] at hzero hone
            have hcoord0 : p.1 0 = q.1 0 := by
              linarith
            have hcoord1 : p.1 1 = q.1 1 := by
              linarith
            apply Subtype.ext
            apply PiLp.ext
            intro i
            fin_cases i
            · exact hcoord0
            · exact hcoord1
          · simp [triangleFoldCoordinates, hpLeft, hpMiddle, hqLeft,
              hqMiddle] at hzero hone
            exfalso
            linarith
      · by_cases hqLeft : 2 * q.1 0 ≤ q.1 1
        · right
          left
          simp [triangleFoldCoordinates, hpLeft, hpMiddle, hqLeft] at hzero hone
          have hpNonpos : p.1 1 ≤ 0 := by
            linarith [hqTriangle.1]
          have hqNonpos : q.1 0 ≤ 0 := by
            linarith [hpTriangle.2.1]
          have hpZero : p.1 1 = 0 := le_antisymm hpNonpos hpTriangle.2.1
          have hqZero : q.1 0 = 0 := le_antisymm hqNonpos hqTriangle.1
          have hcoordinate : p.1 0 = q.1 1 := by
            linarith
          exact ⟨hpZero, hqZero, hcoordinate⟩
        · by_cases hqMiddle : q.1 0 ≤ 2 * q.1 1
          · simp [triangleFoldCoordinates, hpLeft, hpMiddle, hqLeft,
              hqMiddle] at hzero hone
            exfalso
            linarith
          · left
            simp [triangleFoldCoordinates, hpLeft, hpMiddle, hqLeft,
              hqMiddle] at hzero hone
            have hcoord0 : p.1 0 = q.1 0 := by
              linarith
            have hcoord1 : p.1 1 = q.1 1 := by
              linarith
            apply Subtype.ext
            apply PiLp.ext
            intro i
            fin_cases i
            · exact hcoord0
            · exact hcoord1
  · rintro (hpq | hpq | hpq)
    · exact congrArg triangleFold hpq
    · rcases hpq with ⟨hpBottom, hqLeft, hcoordinate⟩
      by_cases hzero : p.1 0 = 0
      · have hpq : p = q := by
          apply Subtype.ext
          apply PiLp.ext
          intro i
          fin_cases i <;> simp_all
        exact congrArg triangleFold hpq
      · apply Subtype.ext
        have hpPos : 0 < p.1 0 := lt_of_le_of_ne hpTriangle.1 (Ne.symm hzero)
        have hpNotLeft : ¬2 * p.1 0 ≤ p.1 1 := by linarith
        have hpNotMiddle : ¬p.1 0 ≤ 2 * p.1 1 := by linarith
        have hqLeftBranch : 2 * q.1 0 ≤ q.1 1 := by linarith [hqTriangle.2.1]
        change triangleFoldCoordinates p = triangleFoldCoordinates q
        unfold triangleFoldCoordinates
        rw [if_neg hpNotLeft, if_neg hpNotMiddle, if_pos hqLeftBranch]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp <;> linarith
    · rcases hpq with ⟨hpLeft, hqBottom, hcoordinate⟩
      by_cases hzero : p.1 1 = 0
      · have hpq : p = q := by
          apply Subtype.ext
          apply PiLp.ext
          intro i
          fin_cases i <;> simp_all
        exact congrArg triangleFold hpq
      · apply Subtype.ext
        have hpPos : 0 < p.1 1 := lt_of_le_of_ne hpTriangle.2.1 (Ne.symm hzero)
        have hpLeftBranch : 2 * p.1 0 ≤ p.1 1 := by linarith
        have hqNotLeft : ¬2 * q.1 0 ≤ q.1 1 := by linarith
        have hqNotMiddle : ¬q.1 0 ≤ 2 * q.1 1 := by linarith
        change triangleFoldCoordinates p = triangleFoldCoordinates q
        unfold triangleFoldCoordinates
        rw [if_pos hpLeftBranch, if_neg hqNotLeft, if_neg hqNotMiddle]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp <;> linarith

/-- Helper for Example 74.1: the affine fold is surjective. -/
private lemma triangleFold_surjective : Function.Surjective triangleFold := by
  -- Invert the affine formula in whichever of the three target sectors contains the point.
  intro r
  have hr := (mem_standardTriangle r.1).mp r.2
  by_cases hleft : r.1 1 ≤ r.1 0 ∧ r.1 0 + 2 * r.1 1 ≤ 1
  · let p : EuclideanSpace ℝ (Fin 2) :=
      !₂[(r.1 0 - r.1 1) / 3, (3 - r.1 0 - 8 * r.1 1) / 3]
    have hp : p ∈ standardTriangle := by
      rw [mem_standardTriangle]
      dsimp [p]
      constructor
      · linarith
      constructor <;> linarith
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    unfold triangleFold triangleFoldCoordinates
    dsimp [p]
    split_ifs
    all_goals apply PiLp.ext
    all_goals intro i
    all_goals fin_cases i
    all_goals simp_all
    all_goals linarith
  · by_cases hright : r.1 0 ≤ r.1 1 ∧ 2 * r.1 0 + r.1 1 ≤ 1
    · let p : EuclideanSpace ℝ (Fin 2) :=
        !₂[(3 - 8 * r.1 0 - r.1 1) / 3, (r.1 1 - r.1 0) / 3]
      have hp : p ∈ standardTriangle := by
        rw [mem_standardTriangle]
        dsimp [p]
        constructor
        · linarith
        constructor <;> linarith
      refine ⟨⟨p, hp⟩, ?_⟩
      apply Subtype.ext
      unfold triangleFold triangleFoldCoordinates
      dsimp [p]
      split_ifs
      all_goals apply PiLp.ext
      all_goals intro i
      all_goals fin_cases i
      all_goals simp_all
      all_goals linarith
    · have hsector₁ : 1 < r.1 0 + 2 * r.1 1 := by
        by_cases horder : r.1 1 ≤ r.1 0
        · exact lt_of_not_ge fun h ↦ hleft ⟨horder, h⟩
        · have horder' : r.1 0 ≤ r.1 1 := le_of_not_ge horder
          by_contra h
          have hbound : 2 * r.1 0 + r.1 1 ≤ 1 := by linarith
          exact hright ⟨horder', hbound⟩
      have hsector₂ : 1 < 2 * r.1 0 + r.1 1 := by
        by_cases horder : r.1 0 ≤ r.1 1
        · exact lt_of_not_ge fun h ↦ hright ⟨horder, h⟩
        · have horder' : r.1 1 ≤ r.1 0 := le_of_not_ge horder
          by_contra h
          have hbound : r.1 0 + 2 * r.1 1 ≤ 1 := by linarith
          exact hleft ⟨horder', hbound⟩
      let p : EuclideanSpace ℝ (Fin 2) :=
        !₂[(4 * r.1 0 + 5 * r.1 1 - 3) / 3,
          (5 * r.1 0 + 4 * r.1 1 - 3) / 3]
      have hp : p ∈ standardTriangle := by
        rw [mem_standardTriangle]
        dsimp [p]
        constructor
        · linarith
        constructor <;> linarith
      refine ⟨⟨p, hp⟩, ?_⟩
      apply Subtype.ext
      unfold triangleFold triangleFoldCoordinates
      dsimp [p]
      split_ifs
      all_goals apply PiLp.ext
      all_goals intro i
      all_goals fin_cases i
      all_goals simp_all
      all_goals linarith

/-- Helper for Example 74.1: the standard triangle is closed. -/
private lemma isClosed_standardTriangle : IsClosed standardTriangle := by
  -- Express the triangle as the intersection of its three closed half-spaces.
  have htriangle : standardTriangle =
      {point | 0 ≤ point 0 ∧ 0 ≤ point 1 ∧ point 0 + point 1 ≤ 1} := by
    ext point
    exact mem_standardTriangle point
  rw [htriangle]
  have hcoord0 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 0) := by
    fun_prop
  have hcoord1 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 1) := by
    fun_prop
  exact (isClosed_le continuous_const hcoord0).inter
    ((isClosed_le continuous_const hcoord1).inter
      (isClosed_le (hcoord0.add hcoord1) continuous_const))

/-- Helper for Example 74.1: the standard triangle is bounded. -/
private lemma isBounded_standardTriangle : Bornology.IsBounded standardTriangle := by
  -- Its coordinate inequalities place the triangle in a fixed Euclidean ball.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  intro point hpoint
  rw [mem_standardTriangle] at hpoint
  rw [EuclideanSpace.norm_eq]
  have hcoord0 : point 0 ≤ 1 := by
    linarith [hpoint.2.2, hpoint.2.1]
  have hcoord1 : point 1 ≤ 1 := by
    linarith [hpoint.2.2, hpoint.1]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [abs_of_nonneg hpoint.1, abs_of_nonneg hpoint.2.1, Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [sq_nonneg (point 0), sq_nonneg (point 1)]

/-- Helper for Example 74.1: the standard triangle is compact. -/
private lemma isCompact_standardTriangle : IsCompact standardTriangle := by
  -- Closed bounded subsets of the Euclidean plane are compact.
  exact Metric.isCompact_of_isClosed_isBounded
    isClosed_standardTriangle isBounded_standardTriangle

/-- Helper for Example 74.1: the fold is a quotient map. -/
private lemma triangleFold_isQuotientMap : Topology.IsQuotientMap triangleFold := by
  -- A continuous surjection from the compact triangle to its Hausdorff target is quotient.
  letI : CompactSpace standardTriangle :=
    isCompact_iff_compactSpace.mp isCompact_standardTriangle
  exact Topology.IsQuotientMap.of_surjective_continuous
    triangleFold_surjective continuous_triangleFold

/-- Helper for Example 74.1: direct labelled-edge relatedness has its defining witness form. -/
private lemma edgeRelated_iff_witness (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : LabellingScheme.Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
          (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
          x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
          y = ⟨region₂, regions.edge region₂ edge₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t)⟩ := by
  -- Expose only the generating relation, leaving its equivalence closure opaque.
  rfl

/-- Helper for Example 74.1: the labelled-edge setoid is the equivalence closure of direct
edge pairings. -/
private lemma identified_iff_eqvGen (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- This is the defining relation of `PolygonalRegions.Identified`.
  rfl

/-- Helper for Example 74.1: every source point lies in the unique triangular summand. -/
private lemma source_eq_region_mk (x : regions.Source) : x = ⟨region, x.2⟩ := by
  -- Replace the dependent occurrence index by the unique occurrence.
  rcases x with ⟨r, p⟩
  have hr := occurrence_eq_region r
  subst r
  rfl

/-- Helper for Example 74.1: each coordinate of a triangle point belongs to the unit interval. -/
private lemma coordinate_mem_unitInterval (p : standardTriangle) (i : Fin 2) :
    p.1 i ∈ Set.Icc (0 : ℝ) 1 := by
  -- Nonnegativity is part of triangle membership, and the other coordinate gives the bound.
  have hp := (mem_standardTriangle p.1).mp p.2
  fin_cases i
  · change 0 ≤ p.1 0 ∧ p.1 0 ≤ 1
    have hupper : p.1 0 ≤ 1 := by
      linarith [hp.2.1, hp.2.2]
    exact ⟨hp.1, hupper⟩
  · change 0 ≤ p.1 1 ∧ p.1 1 ≤ 1
    have hupper : p.1 1 ≤ 1 := by
      linarith [hp.1, hp.2.2]
    exact ⟨hp.2.1, hupper⟩

/-- Helper for Example 74.1: corresponding bottom and left edge points are directly paired. -/
private lemma bottomLeftEdgesRelated (t : unitInterval) :
    regions.EdgeRelated
      (⟨region, edgePoint 0 t⟩ : regions.Source)
      (⟨region, edgePoint 2 (unitInterval.symm t)⟩ : regions.Source) := by
  -- Choose the two occurrences of `a`, whose opposite signs reverse the parameter.
  rw [edgeRelated_iff_witness]
  refine ⟨region, region,
    Fin.cast (occurrence_length region).symm (0 : Fin 3),
    Fin.cast (occurrence_length region).symm (2 : Fin 3), t, ?_⟩
  simp [regions, region_word, boundaryWord, boundaryLetters, edgePoint, edgeCoordinates]

/-- Helper for Example 74.1: every direct labelled-edge pairing has equal fold images. -/
private lemma edgeRelated_triangleFold {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) : triangleFold x.2 = triangleFold y.2 := by
  -- Normalize the unique occurrence, then enumerate the nine pairs of triangular edges.
  rw [edgeRelated_iff_witness] at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  apply (triangleFold_eq_iff _ _).mpr
  fin_cases edge₁
  all_goals fin_cases edge₂
  all_goals
    simp [regions, region_word, boundaryWord, boundaryLetters, edgePoint,
      edgeCoordinates, axisEquivalent] at hlabel ⊢

/-- Helper for Example 74.1: the generated edge relation is exactly the kernel of the fold. -/
private lemma identified_iff_triangleFold_eq (x y : regions.Source) :
    regions.Identified.r x y ↔ triangleFold x.2 = triangleFold y.2 := by
  -- Forward, extend the generator calculation through reflexivity, symmetry, and transitivity.
  rw [identified_iff_eqvGen]
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ hab => exact edgeRelated_triangleFold hab
    | refl a => rfl
    | symm _ _ _ hab => exact hab.symm
    | trans _ _ _ _ _ hab hbc => exact hab.trans hbc
  · intro hxy
    -- The fiber classification leaves equality or one of the two orientations of the
    -- bottom/left edge pairing.
    rcases (triangleFold_eq_iff x.2 y.2).mp hxy with hsecond | haxes | haxes
    · have hsource : x = y := by
        calc
          x = ⟨region, x.2⟩ := source_eq_region_mk x
          _ = ⟨region, y.2⟩ := congrArg (fun p ↦ Sigma.mk region p) hsecond
          _ = y := (source_eq_region_mk y).symm
      rw [hsource]
      exact Relation.EqvGen.refl y
    · rcases haxes with ⟨hxBottom, hyLeft, hcoordinate⟩
      let t : unitInterval := ⟨x.2.1 0, coordinate_mem_unitInterval x.2 0⟩
      have hxEdge : x.2 = edgePoint 0 t := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [t, edgePoint, edgeCoordinates, hxBottom]
      have hyEdge : y.2 = edgePoint 2 (unitInterval.symm t) := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i <;>
          simp [t, edgePoint, edgeCoordinates, hyLeft, hcoordinate]
      rw [source_eq_region_mk x, source_eq_region_mk y, hxEdge, hyEdge]
      exact Relation.EqvGen.rel _ _ (bottomLeftEdgesRelated t)
    · rcases haxes with ⟨hxLeft, hyBottom, hcoordinate⟩
      let t : unitInterval := ⟨x.2.1 1, coordinate_mem_unitInterval x.2 1⟩
      have hxEdge : x.2 = edgePoint 2 (unitInterval.symm t) := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [t, edgePoint, edgeCoordinates, hxLeft]
      have hyEdge : y.2 = edgePoint 0 t := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i <;>
          simp [t, edgePoint, edgeCoordinates, hyBottom, hcoordinate]
      rw [source_eq_region_mk x, source_eq_region_mk y, hxEdge, hyEdge]
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (bottomLeftEdgesRelated t))

/-- Helper for Example 74.1: the comparison map projects to the triangle and applies the
three-sector fold. -/
private noncomputable def triangleComparison : regions.Source → standardTriangle :=
  fun x ↦ triangleFold x.2

/-- Helper for Example 74.1: the comparison map realizes precisely the labelled-edge
identifications. -/
private lemma triangleComparison_realizes : regions.Realizes triangleComparison := by
  -- Compose the quotient fold with projection from the unique source summand.
  constructor
  · change Topology.IsQuotientMap (triangleFold ∘ fun x : regions.Source ↦ x.2)
    exact triangleFold_isQuotientMap.comp sourceProjectionIsHomeomorph.isQuotientMap
  · intro x y
    exact (identified_iff_triangleFold_eq x y).symm

/-- Helper for Example 74.1: the standard triangle is convex. -/
private lemma convex_standardTriangle : Convex ℝ standardTriangle := by
  -- Each defining coordinate inequality is preserved by convex combinations.
  rw [convex_iff_segment_subset]
  intro x hx y hy
  rw [segment_subset_iff]
  intro a b ha hb hab
  rw [mem_standardTriangle] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  constructor
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2),
      mul_nonneg hb (sub_nonneg.mpr hy.2.2)]

/-- Helper for Example 74.1: the standard triangle has nonempty interior. -/
private lemma interior_standardTriangle_nonempty : (interior standardTriangle).Nonempty := by
  -- A small ball around `(1/4, 1/4)` remains inside all three defining half-spaces.
  let c : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun _ ↦ 1 / 4)
  refine ⟨c, mem_interior_iff_mem_nhds.2 ?_⟩
  have hradius : 0 < (1 / 8 : ℝ) := by
    norm_num
  refine Filter.mem_of_superset (Metric.ball_mem_nhds c hradius) ?_
  intro x hx
  rw [Metric.mem_ball] at hx
  rw [mem_standardTriangle]
  have hcoord (i : Fin 2) : |x i - c i| < 1 / 8 := by
    rw [← Real.dist_eq]
    exact (PiLp.dist_apply_le x c i).trans_lt hx
  have hzero := hcoord 0
  have hone := hcoord 1
  change |x 0 - 1 / 4| < 1 / 8 at hzero
  change |x 1 - 1 / 4| < 1 / 8 at hone
  rw [abs_lt] at hzero hone
  constructor
  · linarith
  constructor <;> linarith

/-- Helper for Example 74.1: the standard triangle is homeomorphic to the closed unit disk. -/
private lemma standardTriangleHomeomorphicClosedUnitDisk :
    Nonempty (standardTriangle ≃ₜ B²) := by
  -- Restrict the ambient gauge-rescale homeomorphism to the two closed sets.
  obtain ⟨e, _, hclosure, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      convex_standardTriangle interior_standardTriangle_nonempty isBounded_standardTriangle
  rw [isClosed_standardTriangle.closure_eq] at hclosure
  exact ⟨(e.image standardTriangle).trans (Homeomorph.setCongr hclosure)⟩

/-- Example 74.1: Pasting the oriented edges of the triangular region according to
the scheme `a⁻¹ b a` gives a space homeomorphic to the closed unit disk. -/
theorem homeomorphicClosedUnitDisk :
    Nonempty (Realization ≃ₜ B²) := by
  -- Replace the labelled-edge relation by the kernel relation of the comparison map.
  let comparisonContinuous : C(regions.Source, standardTriangle) :=
    ⟨triangleComparison, triangleComparison_realizes.isQuotientMap.continuous⟩
  let relationEquiv : Realization ≃ₜ Quotient (Setoid.ker triangleComparison) :=
    Homeomorph.Quotient.congrRight
      (fun x y ↦ identified_iff_triangleFold_eq x y)
  have hcomparison : Topology.IsQuotientMap comparisonContinuous := by
    simpa only [comparisonContinuous, ContinuousMap.coe_mk] using
      triangleComparison_realizes.isQuotientMap
  obtain ⟨triangleDisk⟩ := standardTriangleHomeomorphicClosedUnitDisk
  -- The kernel quotient is the triangular target, which is then rescaled to `B²`.
  exact ⟨relationEquiv.trans hcomparison.homeomorph |>.trans triangleDisk⟩

end TriangleDisk
