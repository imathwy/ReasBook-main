module

public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Topology_Munkres_2000.Book.Example_74_5.MobiusBand
public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Homeomorph.Quotient
import all Topology_Munkres_2000.Book.Example_74_2.UnitSquare
import all Topology_Munkres_2000.Book.Example_74_5.MobiusBand
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

open scoped SignedLetter
open scoped Topology

universe u v w

/-- Helper for Example 74.5: a quotient map whose fibers are the labelled-edge
relation identifies the realization with its target. -/
theorem realizationHomeomorphicOfRealizes {α : Type u} {scheme : LabellingScheme α}
    (regions : LabellingScheme.PolygonalRegions.{u, v} scheme)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X)
    (hq : regions.Realizes q) : Nonempty (Quotient regions.Identified ≃ₜ X) := by
  -- First replace the labelled-edge relation by the kernel relation of `q`.
  let qContinuous : C(regions.Source, X) := ⟨q, hq.isQuotientMap.continuous⟩
  let relationEquiv : Quotient regions.Identified ≃ₜ Quotient (Setoid.ker q) :=
    Homeomorph.Quotient.congrRight (r := regions.Identified) (r' := Setoid.ker q)
      (fun x y ↦ (hq.fibers x y).symm)
  -- The standard quotient-kernel homeomorphism supplies the final comparison.
  exact ⟨relationEquiv.trans
    (Topology.IsQuotientMap.homeomorph (f := qContinuous) hq.isQuotientMap)⟩

/-- Helper for Example 74.5: the generating Möbius relation has the stated
left/right boundary coordinate description. -/
theorem mobiusBandGlue_iff (p q : UnitSquare) :
    mobiusBandGlue p q ↔
      p.1 = 0 ∧ q.1 = 1 ∧ p.2 = unitInterval.symm q.2 := by
  -- The private implementation import exposes the defining boundary relation.
  rfl

/-- Helper for Example 74.5: the explicit edge formula used by the square
presentations. -/
def explicitUnitSquareEdge (index : ℕ) (t : unitInterval) : UnitSquare :=
  match index with
  | 0 => (t, 0)
  | 1 => (1, t)
  | 2 => (unitInterval.symm t, 1)
  | _ => (0, unitInterval.symm t)

/-- Helper for Example 74.5: `UnitSquare.edge` agrees with its explicit formula
on the four square edges. -/
theorem unitSquare_edge_eq_explicit (index : ℕ) (t : unitInterval) :
    UnitSquare.edge index t = explicitUnitSquareEdge index t := by
  -- Both sides use the same four-way edge parametrization.
  rfl

/-- Helper for Example 74.5: direct labelled-edge relatedness has its defining
witness form. -/
theorem polygonalRegions_edgeRelated_iff {α : Type u} {scheme : LabellingScheme α}
    (regions : LabellingScheme.PolygonalRegions.{u, v} scheme)
    (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : LabellingScheme.Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
          (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
          x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
          y = ⟨region₂, regions.edge region₂ edge₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t)⟩ := by
  -- The private implementation import exposes the generating edge relation.
  rfl

/-- Helper for Example 74.5: the labelled-edge setoid is the equivalence closure
of direct edge relatedness. -/
theorem polygonalRegions_identified_iff_eqvGen {α : Type u}
    {scheme : LabellingScheme α} (regions : LabellingScheme.PolygonalRegions.{u, v} scheme)
    (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- The identified setoid is definitionally the generated equivalence relation.
  rfl

/-- Helper for Example 74.5: two points glued to the same right-boundary point
are equal. -/
theorem mobiusBandGlue_target_unique {p q r : UnitSquare}
    (hpq : mobiusBandGlue p q) (hrq : mobiusBandGlue r q) : p = r := by
  -- The first coordinates are both zero and the second coordinates have the same image.
  rw [mobiusBandGlue_iff] at hpq hrq
  rcases hpq with ⟨hp, _, hpq⟩
  rcases hrq with ⟨hr, _, hrq⟩
  apply Prod.ext
  · exact hp.trans hr.symm
  · exact hpq.trans hrq.symm

/-- Helper for Example 74.5: two right-boundary points glued to the same
left-boundary point are equal. -/
theorem mobiusBandGlue_source_unique {p q r : UnitSquare}
    (hpq : mobiusBandGlue p q) (hpr : mobiusBandGlue p r) : q = r := by
  -- Injectivity of interval reflection recovers the second coordinate.
  rw [mobiusBandGlue_iff] at hpq hpr
  rcases hpq with ⟨_, hq, hpq⟩
  rcases hpr with ⟨_, hr, hpr⟩
  apply Prod.ext
  · exact hq.trans hr.symm
  · apply unitInterval.symm_bijective.injective
    exact hpq.symm.trans hpr

/-- Helper for Example 74.5: a Möbius generating identification cannot be
followed immediately by another generating identification. -/
theorem mobiusBandGlue_not_chain {p q r : UnitSquare}
    (hpq : mobiusBandGlue p q) (hqr : mobiusBandGlue q r) : False := by
  -- The intermediate point would have first coordinate both one and zero.
  rw [mobiusBandGlue_iff] at hpq hqr
  have h : (1 : unitInterval) = 0 := hpq.2.1.symm.trans hqr.1
  norm_num at h

/-- Helper for Example 74.5: equality together with one Möbius gluing step in
either direction is already an equivalence relation. -/
theorem mobiusBandGlueClosure_equivalence :
    Equivalence (fun p q : UnitSquare ↦
      p = q ∨ mobiusBandGlue p q ∨ mobiusBandGlue q p) := by
  -- Reflexivity and symmetry merely choose or reverse one of the three alternatives.
  refine ⟨fun p ↦ Or.inl rfl, ?_, ?_⟩
  · intro p q hpq
    rcases hpq with hpq | hpq | hqp
    · exact Or.inl hpq.symm
    · exact Or.inr (Or.inr hpq)
    · exact Or.inr (Or.inl hqp)
  · intro p q r hpq hqr
    -- Two nontrivial steps either collapse by endpoint uniqueness or have incompatible ends.
    rcases hpq with rfl | hpq | hqp
    · exact hqr
    · rcases hqr with rfl | hqr | hrq
      · exact Or.inr (Or.inl hpq)
      · exact (mobiusBandGlue_not_chain hpq hqr).elim
      · exact Or.inl (mobiusBandGlue_target_unique hpq hrq)
    · rcases hqr with rfl | hqr | hrq
      · exact Or.inr (Or.inr hqp)
      · exact Or.inl (mobiusBandGlue_source_unique hqp hqr)
      · exact (mobiusBandGlue_not_chain hrq hqp).elim

/-- Helper for Example 74.5: equality in the standard Möbius quotient is
equality of representatives or one boundary gluing step in either direction. -/
theorem mobiusBandQuotient_mk_eq_iff (p q : UnitSquare) :
    Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) p =
        Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) q ↔
      p = q ∨ mobiusBandGlue p q ∨ mobiusBandGlue q p := by
  -- Quotient equality is the generated relation, whose closure was normalized above.
  rw [Quotient.eq'']
  change Relation.EqvGen mobiusBandGlue p q ↔ _
  constructor
  · intro hpq
    apply mobiusBandGlueClosure_equivalence.eqvGen_iff.mp
    exact Relation.EqvGen.mono (fun _ _ h ↦ Or.inr (Or.inl h)) p q hpq
  · intro hpq
    rcases hpq with rfl | hpq | hqp
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ hpq
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hqp)

/-- Helper for Example 74.5: the displayed quotient map into `MobiusBand` is a
quotient map. -/
theorem mobiusBandQuotientMap_isQuotientMap :
    Topology.IsQuotientMap (fun p : UnitSquare ↦
      (Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) p : MobiusBand)) := by
  -- The displayed map is the canonical quotient projection.
  exact isQuotientMap_quotient_mk'

namespace MobiusBandTwoSquares

/-- The six edge labels appearing in Figure 74.6. -/
inductive Label
  | a
  | b
  | c
  | d
  | e
  | f
  deriving DecidableEq

/-- The signed boundary letters `d b c⁻¹ a⁻¹` of the first square in Figure 74.6. -/
def firstBoundaryLetters : List (Label × Bool) :=
  [Label.d, Label.b, Label.c⁻¹, Label.a⁻¹]

/-- The polygon word `d b c⁻¹ a⁻¹` of the first square in Figure 74.6. -/
def firstBoundaryWord : PolygonWord Label :=
  ⟨firstBoundaryLetters, by decide⟩

/-- The signed boundary letters `f a⁻¹ e⁻¹ b⁻¹` of the second square in Figure 74.6. -/
def secondBoundaryLetters : List (Label × Bool) :=
  [Label.f, Label.a⁻¹, Label.e⁻¹, Label.b⁻¹]

/-- The polygon word `f a⁻¹ e⁻¹ b⁻¹` of the second square in Figure 74.6. -/
def secondBoundaryWord : PolygonWord Label :=
  ⟨secondBoundaryLetters, by decide⟩

/-- The two-square labelling scheme depicted in Figure 74.6. -/
def scheme : LabellingScheme Label :=
  firstBoundaryWord ::ₘ secondBoundaryWord ::ₘ 0

/-- The two unit squares with ordered boundary edges prescribed by Figure 74.6. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := unitInterval × unitInterval
  topology _ := inferInstance
  edge _ edge t := UnitSquare.edge edge t

/-- The labelled-edge realization of the two squares in Figure 74.6. -/
abbrev Realization := regions.Realization

/-- Helper for Example 74.5: the occurrence belonging to the first square. -/
noncomputable def firstRegion : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
    (secondBoundaryWord ::ₘ 0)).symm none

/-- Helper for Example 74.5: the occurrence belonging to the second square. -/
noncomputable def secondRegion : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
    (secondBoundaryWord ::ₘ 0)).symm
      (some ((LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0).symm none))

/-- Helper for Example 74.5: every occurrence in the two-square scheme is one
of its two displayed regions. -/
theorem occurrence_eq_firstRegion_or_secondRegion
    (region : LabellingScheme.Occurrence scheme) :
    region = firstRegion ∨ region = secondRegion := by
  classical
  -- The two successive occurrence equivalences enumerate the two cons cells.
  cases hfirst : LabellingScheme.consOccurrenceEquiv firstBoundaryWord
      (secondBoundaryWord ::ₘ 0) region with
  | none =>
      left
      apply (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
        (secondBoundaryWord ::ₘ 0)).injective
      simpa [firstRegion] using hfirst
  | some remaining =>
      cases hsecond : LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0 remaining with
      | none =>
          right
          apply (LabellingScheme.consOccurrenceEquiv firstBoundaryWord
            (secondBoundaryWord ::ₘ 0)).injective
          rw [hfirst]
          rw [secondRegion, Equiv.apply_symm_apply]
          congr 1
          apply (LabellingScheme.consOccurrenceEquiv secondBoundaryWord 0).injective
          rw [hsecond, Equiv.apply_symm_apply]
      | some impossible =>
          exact (Nat.not_lt_zero impossible.2 impossible.2.isLt).elim

/-- Helper for Example 74.5: the first occurrence carries the first displayed word. -/
theorem firstRegion_word : firstRegion.1 = firstBoundaryWord := by
  -- The outer occurrence equivalence selects its head word.
  rfl

/-- Helper for Example 74.5: the second occurrence carries the second displayed word. -/
theorem secondRegion_word : secondRegion.1 = secondBoundaryWord := by
  -- The nested occurrence equivalence selects the head of the remaining scheme.
  rfl

/-- Helper for Example 74.5: both displayed square occurrences have four edges. -/
theorem occurrence_length (region : LabellingScheme.Occurrence scheme) :
    region.1.1.length = 4 := by
  -- Reduce to either explicit occurrence, then compute its concrete word length.
  rcases occurrence_eq_firstRegion_or_secondRegion region with hregion | hregion
  · rw [hregion]
    decide
  · rw [hregion]
    decide

/-- Helper for Example 74.5: the affine half-coordinate lies in the unit interval. -/
theorem halfCoordinate_mem (right : Bool) (t : unitInterval) :
    (if right then (1 + (t : ℝ)) / 2 else (t : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Each branch follows from the two endpoint inequalities carried by `t`.
  rcases t.property with ⟨ht0, ht1⟩
  cases right
  · constructor <;> dsimp <;> linarith
  · constructor <;> dsimp <;> linarith

/-- Helper for Example 74.5: the coordinate rescaling a square into the left or
right half of the unit interval. -/
noncomputable def halfCoordinate (right : Bool) (t : unitInterval) : unitInterval :=
  ⟨if right then (1 + (t : ℝ)) / 2 else (t : ℝ) / 2, halfCoordinate_mem right t⟩

/-- Helper for Example 74.5: rescaling into either half of the unit interval is injective. -/
theorem halfCoordinate_injective (right : Bool) : Function.Injective (halfCoordinate right) := by
  intro s t hst
  -- Equality of the affine coordinates recovers equality of the original coordinates.
  apply Subtype.ext
  have hvalues := congrArg Subtype.val hst
  cases right
  · dsimp [halfCoordinate] at hvalues
    linarith
  · dsimp [halfCoordinate] at hvalues
    linarith

/-- Helper for Example 74.5: the two affine halves meet only at their common midpoint. -/
theorem halfCoordinate_false_eq_true_iff (s t : unitInterval) :
    halfCoordinate false s = halfCoordinate true t ↔ s = 1 ∧ t = 0 := by
  constructor
  · intro hst
    -- The interval bounds force the only solution of `s = 1 + t`.
    have hvalues := congrArg Subtype.val hst
    rcases s.property with ⟨hs0, hs1⟩
    rcases t.property with ⟨ht0, ht1⟩
    dsimp [halfCoordinate] at hvalues
    constructor
    · apply Subtype.ext
      dsimp
      linarith
    · apply Subtype.ext
      dsimp
      linarith
  · rintro ⟨rfl, rfl⟩
    -- Both endpoint representatives map to the midpoint.
    apply Subtype.ext
    norm_num [halfCoordinate]

/-- Helper for Example 74.5: an affine half-coordinate is zero exactly at the
left endpoint of the left half. -/
theorem halfCoordinate_eq_zero_iff (right : Bool) (t : unitInterval) :
    halfCoordinate right t = 0 ↔ right = false ∧ t = 0 := by
  constructor
  · intro ht
    -- The right half is strictly separated from zero; on the left half the map is injective.
    cases right
    · constructor
      · rfl
      · have hzero : (0 : unitInterval) = halfCoordinate false 0 := by
          apply Subtype.ext
          norm_num [halfCoordinate]
        apply halfCoordinate_injective false
        exact ht.trans hzero
    · have hvalues := congrArg Subtype.val ht
      rcases t.property with ⟨ht0, ht1⟩
      dsimp [halfCoordinate] at hvalues
      linarith
  · rintro ⟨rfl, rfl⟩
    -- Evaluate the left affine map at zero.
    apply Subtype.ext
    norm_num [halfCoordinate]

/-- Helper for Example 74.5: an affine half-coordinate is one exactly at the
right endpoint of the right half. -/
theorem halfCoordinate_eq_one_iff (right : Bool) (t : unitInterval) :
    halfCoordinate right t = 1 ↔ right = true ∧ t = 1 := by
  constructor
  · intro ht
    -- The left half is strictly separated from one; on the right half the map is injective.
    cases right
    · have hvalues := congrArg Subtype.val ht
      rcases t.property with ⟨ht0, ht1⟩
      dsimp [halfCoordinate] at hvalues
      linarith
    · constructor
      · rfl
      · have hone : (1 : unitInterval) = halfCoordinate true 1 := by
          apply Subtype.ext
          norm_num [halfCoordinate]
        apply halfCoordinate_injective true
        exact ht.trans hone
  · rintro ⟨rfl, rfl⟩
    -- Evaluate the right affine map at one.
    apply Subtype.ext
    norm_num [halfCoordinate]

/-- Helper for Example 74.5: affine rescaling into either half of the unit
interval is continuous. -/
theorem continuous_halfCoordinate (right : Bool) : Continuous (halfCoordinate right) := by
  -- Continuity is checked on real-valued coordinates before restoring the subtype codomain.
  cases right
  · unfold halfCoordinate
    simp only [Bool.false_eq_true, ↓reduceIte]
    fun_prop
  · unfold halfCoordinate
    simp only [↓reduceIte]
    fun_prop

/-- Helper for Example 74.5: whether an occurrence is the right-hand square. -/
noncomputable def isSecondRegion (region : LabellingScheme.Occurrence scheme) : Bool :=
  match LabellingScheme.consOccurrenceEquiv firstBoundaryWord
      (secondBoundaryWord ::ₘ 0) region with
  | none => false
  | some _ => true

/-- Helper for Example 74.5: the first occurrence selects the left half. -/
theorem isSecondRegion_first : isSecondRegion firstRegion = false := by
  -- Evaluate the outer occurrence equivalence on its first inverse branch.
  unfold isSecondRegion firstRegion
  rw [Equiv.apply_symm_apply]

/-- Helper for Example 74.5: the second occurrence selects the right half. -/
theorem isSecondRegion_second : isSecondRegion secondRegion = true := by
  -- Evaluate the outer occurrence equivalence on its second inverse branch.
  unfold isSecondRegion secondRegion
  rw [Equiv.apply_symm_apply]

/-- Helper for Example 74.5: flatten the two squares onto the two halves of one
unit square. -/
noncomputable def flatten : regions.Source → UnitSquare :=
  fun x ↦ (halfCoordinate (isSecondRegion x.1) x.2.1, x.2.2)

/-- Helper for Example 74.5: on the first square, flattening is left-half affine
rescaling in the first coordinate. -/
theorem flatten_firstRegion (x : UnitSquare) :
    flatten (⟨firstRegion, x⟩ : regions.Source) =
      (halfCoordinate false x.1, x.2) := by
  -- Evaluate the occurrence selector before simplifying the product coordinates.
  simp only [flatten, isSecondRegion_first]

/-- Helper for Example 74.5: on the second square, flattening is right-half affine
rescaling in the first coordinate. -/
theorem flatten_secondRegion (x : UnitSquare) :
    flatten (⟨secondRegion, x⟩ : regions.Source) =
      (halfCoordinate true x.1, x.2) := by
  -- Evaluate the occurrence selector before simplifying the product coordinates.
  simp only [flatten, isSecondRegion_second]

/-- Helper for Example 74.5: the two affine half-squares cover the entire unit square. -/
theorem flatten_surjective : Function.Surjective flatten := by
  intro z
  -- Choose the left or right square according to the first coordinate of the target.
  by_cases hhalf : (z.1 : ℝ) ≤ 1 / 2
  · have htwo : (0 : ℝ) < 2 := by norm_num
    have hcoordinate : 2 * (z.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      (unitInterval.mul_pos_mem_iff htwo).mpr
        ⟨z.1.property.1, hhalf⟩
    let t : unitInterval := ⟨2 * (z.1 : ℝ), hcoordinate⟩
    refine ⟨⟨firstRegion, (t, z.2)⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simp only [flatten, isSecondRegion_first, halfCoordinate, Bool.false_eq_true,
        ↓reduceIte]
      dsimp [t]
      ring
    · rfl
  · have hhalf' : (1 / 2 : ℝ) ≤ z.1 := (lt_of_not_ge hhalf).le
    have hcoordinate : 2 * (z.1 : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 :=
      unitInterval.two_mul_sub_one_mem_iff.mpr ⟨hhalf', z.1.property.2⟩
    let t : unitInterval := ⟨2 * (z.1 : ℝ) - 1, hcoordinate⟩
    refine ⟨⟨secondRegion, (t, z.2)⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simp only [flatten, isSecondRegion_second, halfCoordinate, ↓reduceIte]
      dsimp [t]
      ring
    · rfl

/-- Helper for Example 74.5: the comparison from the two squares to the standard
Möbius quotient. -/
noncomputable def comparison : regions.Source → MobiusBand :=
  fun x ↦ Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) (flatten x)

/-- Helper for Example 74.5: every directly paired pair of two-square edge points
has the same image under the flattening comparison. -/
theorem edgeRelated_comparison {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) : comparison x = comparison y := by
  classical
  -- Normalize the two occurrences, then exhaust the four-by-four edge pairs.
  rw [polygonalRegions_edgeRelated_iff] at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  rcases occurrence_eq_firstRegion_or_secondRegion region₁ with hregion₁ | hregion₁
  · subst region₁
    rcases occurrence_eq_firstRegion_or_secondRegion region₂ with hregion₂ | hregion₂
    · subst region₂
      fin_cases edge₁ <;> fin_cases edge₂ <;>
        simp [comparison, flatten, isSecondRegion_first, halfCoordinate, regions,
          firstRegion_word, firstBoundaryWord, firstBoundaryLetters,
          unitSquare_edge_eq_explicit, explicitUnitSquareEdge] at hlabel ⊢
    · subst region₂
      fin_cases edge₁ <;> fin_cases edge₂ <;>
        simp [comparison, flatten, isSecondRegion_first, isSecondRegion_second,
          halfCoordinate, regions,
          firstRegion_word, secondRegion_word, firstBoundaryWord, secondBoundaryWord,
          firstBoundaryLetters, secondBoundaryLetters, unitSquare_edge_eq_explicit,
          explicitUnitSquareEdge, mobiusBandQuotient_mk_eq_iff, mobiusBandGlue_iff] at hlabel ⊢
  · subst region₁
    rcases occurrence_eq_firstRegion_or_secondRegion region₂ with hregion₂ | hregion₂
    · subst region₂
      fin_cases edge₁ <;> fin_cases edge₂ <;>
        simp [comparison, flatten, isSecondRegion_first, isSecondRegion_second,
          halfCoordinate, regions,
          firstRegion_word, secondRegion_word, firstBoundaryWord, secondBoundaryWord,
          firstBoundaryLetters, secondBoundaryLetters, unitSquare_edge_eq_explicit,
          explicitUnitSquareEdge, mobiusBandQuotient_mk_eq_iff, mobiusBandGlue_iff] at hlabel ⊢
    · subst region₂
      fin_cases edge₁ <;> fin_cases edge₂ <;>
        simp [comparison, flatten, isSecondRegion_second, halfCoordinate, regions,
          secondRegion_word, secondBoundaryWord, secondBoundaryLetters,
          unitSquare_edge_eq_explicit, explicitUnitSquareEdge] at hlabel ⊢

/-- Helper for Example 74.5: the two-square comparison is constant on the
equivalence closure generated by its direct edge pairings. -/
theorem eqvGen_comparison {x y : regions.Source}
    (hxy : Relation.EqvGen regions.EdgeRelated x y) : comparison x = comparison y := by
  -- Extend the completed finite edge calculation through the closure constructors.
  induction hxy with
  | rel _ _ h => exact edgeRelated_comparison h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Helper for Example 74.5: the two copies of the midpoint seam are directly
paired by the label `b`. -/
theorem edgeRelated_midpointSeam (t : unitInterval) :
    regions.EdgeRelated
      (⟨firstRegion, ((1, t) : UnitSquare)⟩ : regions.Source)
      ⟨secondRegion, ((0, t) : UnitSquare)⟩ := by
  -- Use edge `1` of the first square and oppositely oriented edge `3` of the second.
  rw [polygonalRegions_edgeRelated_iff]
  refine ⟨firstRegion, secondRegion,
    Fin.cast (occurrence_length firstRegion).symm (1 : Fin 4),
    Fin.cast (occurrence_length secondRegion).symm (3 : Fin 4), t, ?_⟩
  simp [firstRegion_word, secondRegion_word, firstBoundaryWord, secondBoundaryWord,
    firstBoundaryLetters, secondBoundaryLetters, regions,
    unitSquare_edge_eq_explicit, explicitUnitSquareEdge]

/-- Helper for Example 74.5: the two outer vertical sides are directly paired
with the Möbius reversal by the label `a`. -/
theorem edgeRelated_outerSides (t : unitInterval) :
    regions.EdgeRelated
      (⟨firstRegion, ((0, unitInterval.symm t) : UnitSquare)⟩ : regions.Source)
      ⟨secondRegion, ((1, t) : UnitSquare)⟩ := by
  -- Use edge `3` of the first square and equally oriented edge `1` of the second.
  rw [polygonalRegions_edgeRelated_iff]
  refine ⟨firstRegion, secondRegion,
    Fin.cast (occurrence_length firstRegion).symm (3 : Fin 4),
    Fin.cast (occurrence_length secondRegion).symm (1 : Fin 4), t, ?_⟩
  simp [firstRegion_word, secondRegion_word, firstBoundaryWord, secondBoundaryWord,
    firstBoundaryLetters, secondBoundaryLetters, regions,
    unitSquare_edge_eq_explicit, explicitUnitSquareEdge]

/-- Helper for Example 74.5: equality in the Möbius quotient between points in
the same affine half forces equality before quotienting. -/
theorem sameHalf_eq_of_mobiusQuotient_eq (right : Bool) (x y : UnitSquare)
    (hxy : Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
        (halfCoordinate right x.1, x.2) =
      Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
        (halfCoordinate right y.1, y.2)) : x = y := by
  -- Normalize quotient equality into equality or a single boundary gluing.
  rw [mobiusBandQuotient_mk_eq_iff] at hxy
  rcases hxy with hxy | hxy | hyx
  · injection hxy with hfirst hsecond
    apply Prod.ext
    · exact halfCoordinate_injective right hfirst
    · exact hsecond
  · -- A gluing cannot start and end inside the same closed half.
    rw [mobiusBandGlue_iff] at hxy
    cases right
    · have hone := (halfCoordinate_eq_one_iff false y.1).mp hxy.2.1
      simp at hone
    · have hzero := (halfCoordinate_eq_zero_iff true x.1).mp hxy.1
      simp at hzero
  · -- The reversed gluing has the same incompatible endpoint condition.
    rw [mobiusBandGlue_iff] at hyx
    cases right
    · have hone := (halfCoordinate_eq_one_iff false x.1).mp hyx.2.1
      simp at hone
    · have hzero := (halfCoordinate_eq_zero_iff true y.1).mp hyx.1
      simp at hzero

/-- Helper for Example 74.5: equal Möbius-quotient images from opposite affine
halves are generated by the midpoint seam or the two outer sides. -/
theorem comparisonAcrossRegions_eqvGen (x y : UnitSquare)
    (hxy : Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
        (halfCoordinate false x.1, x.2) =
      Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
        (halfCoordinate true y.1, y.2)) :
    Relation.EqvGen regions.EdgeRelated
      (⟨firstRegion, x⟩ : regions.Source) ⟨secondRegion, y⟩ := by
  -- Normalize quotient equality into equality or one directed boundary gluing.
  rw [mobiusBandQuotient_mk_eq_iff] at hxy
  rcases hxy with hxy | hxy | hyx
  · -- Equality of opposite halves occurs exactly on their common midpoint seam.
    injection hxy with hfirst hsecond
    have hends := (halfCoordinate_false_eq_true_iff x.1 y.1).mp hfirst
    have hx : x = (1, x.2) := Prod.ext hends.1 rfl
    have hy : y = (0, x.2) := Prod.ext hends.2 hsecond.symm
    rw [hx, hy]
    exact Relation.EqvGen.rel _ _ (edgeRelated_midpointSeam x.2)
  · -- A forward gluing is precisely the Möbius-reversed outer-side pairing.
    rw [mobiusBandGlue_iff] at hxy
    have hx0 := (halfCoordinate_eq_zero_iff false x.1).mp hxy.1
    have hy1 := (halfCoordinate_eq_one_iff true y.1).mp hxy.2.1
    have hx : x = (0, unitInterval.symm y.2) := Prod.ext hx0.2 hxy.2.2
    have hy : y = (1, y.2) := Prod.ext hy1.2 rfl
    rw [hx, hy]
    exact Relation.EqvGen.rel _ _ (edgeRelated_outerSides y.2)
  · -- A gluing cannot run from the right affine half back to the left one.
    rw [mobiusBandGlue_iff] at hyx
    have hy0 := (halfCoordinate_eq_zero_iff true y.1).mp hyx.1
    simp at hy0

/-- Helper for Example 74.5: equality under the two-square comparison is
generated by labelled-edge pairings. -/
theorem comparison_eq_imp_eqvGen (x y : regions.Source)
    (hxy : comparison x = comparison y) :
    Relation.EqvGen regions.EdgeRelated x y := by
  -- Route correction: imported relation bodies stay opaque here, so use their isolated normal
  -- forms and reduce the kernel calculation to affine same-half and cross-half lemmas.
  -- Normalize both occurrence indices, leaving the same-half and cross-half kernel lemmas.
  rcases x with ⟨region₁, x⟩
  rcases y with ⟨region₂, y⟩
  rcases occurrence_eq_firstRegion_or_secondRegion region₁ with hregion₁ | hregion₁
  · subst region₁
    rcases occurrence_eq_firstRegion_or_secondRegion region₂ with hregion₂ | hregion₂
    · subst region₂
      have hquotient : Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
          (halfCoordinate false x.1, x.2) =
          Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
            (halfCoordinate false y.1, y.2) := by
        simpa [comparison, flatten, isSecondRegion_first] using hxy
      have hpoints : x = y := sameHalf_eq_of_mobiusQuotient_eq false x y hquotient
      subst y
      exact Relation.EqvGen.refl _
    · subst region₂
      apply comparisonAcrossRegions_eqvGen x y
      simpa [comparison, flatten, isSecondRegion_first, isSecondRegion_second] using hxy
  · subst region₁
    rcases occurrence_eq_firstRegion_or_secondRegion region₂ with hregion₂ | hregion₂
    · subst region₂
      apply Relation.EqvGen.symm
      apply comparisonAcrossRegions_eqvGen y x
      simpa [comparison, flatten, isSecondRegion_first, isSecondRegion_second] using hxy.symm
    · subst region₂
      have hquotient : Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
          (halfCoordinate true x.1, x.2) =
          Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
            (halfCoordinate true y.1, y.2) := by
        simpa [comparison, flatten, isSecondRegion_second] using hxy
      have hpoints : x = y := sameHalf_eq_of_mobiusQuotient_eq true x y hquotient
      subst y
      exact Relation.EqvGen.refl _

/-- Helper for Example 74.5: flattening is continuous on the coproduct of the two
square occurrences. -/
theorem continuous_flatten : Continuous flatten := by
  -- Check continuity independently on each summand of the exposed coproduct topology.
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  letI : TopologicalSpace (regions.Point region) := regions.topology region
  rcases occurrence_eq_firstRegion_or_secondRegion region with rfl | rfl
  · -- On the first square, flattening rescales the first coordinate into the left half.
    have hmap : flatten ∘
        (Sigma.mk firstRegion : regions.Point firstRegion → regions.Source) =
        fun p : regions.Point firstRegion ↦ (halfCoordinate false p.1, p.2) := by
      funext p
      exact flatten_firstRegion p
    rw [hmap]
    have hfirst : Continuous (fun p : UnitSquare ↦ p.1) := continuous_fst
    have hsecond : Continuous (fun p : UnitSquare ↦ p.2) := continuous_snd
    unfold regions at this ⊢
    exact ((continuous_halfCoordinate false).comp hfirst).prodMk hsecond
  · -- On the second square, flattening rescales the first coordinate into the right half.
    have hmap : flatten ∘
        (Sigma.mk secondRegion : regions.Point secondRegion → regions.Source) =
        fun p : regions.Point secondRegion ↦ (halfCoordinate true p.1, p.2) := by
      funext p
      exact flatten_secondRegion p
    rw [hmap]
    have hfirst : Continuous (fun p : UnitSquare ↦ p.1) := continuous_fst
    have hsecond : Continuous (fun p : UnitSquare ↦ p.2) := continuous_snd
    unfold regions at this ⊢
    exact ((continuous_halfCoordinate true).comp hfirst).prodMk hsecond

/-- Helper for Example 74.5: flattening the disjoint union of the two squares
onto the two half-squares is a quotient map. -/
theorem flatten_isQuotientMap : Topology.IsQuotientMap flatten := by
  -- Route correction: private imports now expose the source as a standard coproduct topology.
  letI (region : LabellingScheme.Occurrence scheme) :
      TopologicalSpace (regions.Point region) := by
    unfold regions
    infer_instance
  letI (region : LabellingScheme.Occurrence scheme) :
      CompactSpace (regions.Point region) := by
    unfold regions
    exact (inferInstance : CompactSpace UnitSquare)
  have hinclusion : ∀ region : LabellingScheme.Occurrence scheme,
      Continuous[regions.topology region, regions.sourceTopology]
        (Sigma.mk region : regions.Point region → regions.Source) := by
    intro region
    exact continuous_iSup_rng (i := region) (f := Sigma.mk region)
      (continuous_coinduced_rng (f := Sigma.mk region))
  have sourceUniv : (Set.univ : Set regions.Source) =
      ⋃ region, Set.range (Sigma.mk region) := by
    -- Every dependent pair lies in the image of the inclusion indexed by its first component.
    ext source
    constructor
    · intro _
      exact Set.mem_iUnion.mpr ⟨source.1, ⟨source.2, rfl⟩⟩
    · intro _
      exact Set.mem_univ source
  let occurrenceOfBool : Bool → LabellingScheme.Occurrence scheme :=
    fun right ↦ if right then secondRegion else firstRegion
  have occurrenceOfBoolSurjective : Function.Surjective occurrenceOfBool := by
    intro region
    rcases occurrence_eq_firstRegion_or_secondRegion region with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  letI : Finite (LabellingScheme.Occurrence scheme) :=
    Finite.of_surjective occurrenceOfBool occurrenceOfBoolSurjective
  have sourceIsCompact : IsCompact (Set.univ : Set regions.Source) := by
    -- The finite coproduct is the union of the compact images of its summands.
    rw [sourceUniv]
    apply isCompact_iUnion
    intro region
    simpa only [Set.image_univ] using
      (isCompact_univ : IsCompact (Set.univ : Set (regions.Point region))).image
        (hinclusion region)
  letI : CompactSpace regions.Source := ⟨sourceIsCompact⟩
  -- A continuous surjection from this finite compact coproduct to the Hausdorff square is quotient.
  exact Topology.IsQuotientMap.of_surjective_continuous flatten_surjective continuous_flatten

/-- Helper for Example 74.5: the comparison is the Möbius quotient map after flattening. -/
theorem comparison_eq_composition : comparison =
    fun x : regions.Source ↦
      (Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) (flatten x) : MobiusBand) := by
  -- Record the stable factorization used by the quotient-map proof.
  rfl

/-- Helper for Example 74.5: the two-square comparison is a quotient map and
has exactly the labelled-edge fibers. -/
theorem comparison_realizes : regions.Realizes comparison := by
  constructor
  · -- Compose flattening with the canonical Möbius quotient map.
    rw [comparison_eq_composition]
    exact mobiusBandQuotientMap_isQuotientMap.comp flatten_isQuotientMap
  · intro x y
    rw [polygonalRegions_identified_iff_eqvGen]
    constructor
    · exact comparison_eq_imp_eqvGen x y
    · exact eqvGen_comparison

/-- Example 74.5 (1): The quotient specified by Figure 74.6 is connected. -/
instance instConnectedSpaceRealization : ConnectedSpace Realization := by
  -- Compare both the canonical realization and the concrete map through their kernel quotients.
  obtain ⟨canonicalEquiv⟩ := realizationHomeomorphicOfRealizes regions regions.quotientMap
    (LabellingScheme.PolygonalRegions.quotientMap_realizes regions)
  obtain ⟨mobiusEquiv⟩ := realizationHomeomorphicOfRealizes regions comparison comparison_realizes
  -- Connectedness of the standard Möbius quotient transfers across the resulting homeomorphism.
  exact (canonicalEquiv.symm.trans mobiusEquiv).connectedSpace_iff.mpr inferInstance

/-- Companion to Example 74.5 (2): The quotient specified by Figure 74.6 is homeomorphic to
`MobiusBand`. -/
theorem homeomorphicMobiusBand : Nonempty (Realization ≃ₜ MobiusBand) := by
  -- Both spaces are targets of quotient maps with the same labelled-edge fibers.
  obtain ⟨canonicalEquiv⟩ := realizationHomeomorphicOfRealizes regions regions.quotientMap
    (LabellingScheme.PolygonalRegions.quotientMap_realizes regions)
  obtain ⟨mobiusEquiv⟩ := realizationHomeomorphicOfRealizes regions comparison comparison_realizes
  exact ⟨canonicalEquiv.symm.trans mobiusEquiv⟩


end MobiusBandTwoSquares

namespace MobiusBandSquare

/-- The signed boundary letters `a b a c`, with labels `0 = a`, `1 = b`, and `2 = c`. -/
def boundaryLetters : List (Fin 3 × Bool) :=
  [(0 : Fin 3), (1 : Fin 3), (0 : Fin 3), (2 : Fin 3)]

/-- The polygon word encoding the one-square presentation `a b a c`. -/
def boundaryWord : PolygonWord (Fin 3) :=
  ⟨boundaryLetters, by decide⟩

/-- The singleton labelling scheme whose boundary word is `a b a c`. -/
def scheme : LabellingScheme (Fin 3) :=
  boundaryWord ::ₘ 0

/-- The unit square with its ordered boundary edges prescribed by the word `a b a c`. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := unitInterval × unitInterval
  topology _ := inferInstance
  edge _ edge t := UnitSquare.edge edge t

/-- The labelled-edge realization of the square carrying the word `a b a c`. -/
abbrev Realization := regions.Realization

/-- Helper for Example 74.5: the unique occurrence of the one-square scheme. -/
noncomputable def region : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv boundaryWord 0).symm none

/-- Helper for Example 74.5: every occurrence of the one-square scheme is its
displayed region. -/
theorem occurrence_eq_region (r : LabellingScheme.Occurrence scheme) : r = region := by
  classical
  -- The cons occurrence is the only possible branch because the remainder is empty.
  apply (LabellingScheme.consOccurrenceEquiv boundaryWord 0).injective
  cases h : LabellingScheme.consOccurrenceEquiv boundaryWord 0 r with
  | none => simp [region]
  | some impossible => exact (Nat.not_lt_zero impossible.2 impossible.2.isLt).elim

/-- Helper for Example 74.5: the unique occurrence carries the displayed boundary word. -/
theorem region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head word of the singleton scheme.
  rfl

/-- Helper for Example 74.5: the unique square occurrence has four edges. -/
theorem occurrence_length (r : LabellingScheme.Occurrence scheme) : r.1.1.length = 4 := by
  -- Normalize to the unique occurrence and compute the concrete word length.
  rw [occurrence_eq_region r]
  decide

/-- Helper for Example 74.5: the coordinate-swapping comparison from the
one-square presentation to the standard Möbius quotient. -/
noncomputable def comparison : regions.Source → MobiusBand :=
  fun x ↦ Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) (x.2.2, x.2.1)

/-- Helper for Example 74.5: the one-square comparison factors as projection,
coordinate swap, and the Möbius quotient map. -/
theorem comparison_eq_composition : comparison =
    fun x : regions.Source ↦
      (Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue)
        (Prod.swap (x.2 : UnitSquare)) : MobiusBand) := by
  -- Record this normal form once so quotient-map composition avoids projection unfolding.
  rfl

/-- Helper for Example 74.5: the comparison on the unique square is coordinate swap
followed by the Möbius quotient map. -/
theorem comparison_region (x : UnitSquare) :
    comparison (⟨region, x⟩ : regions.Source) =
      Quotient.mk (Relation.EqvGen.setoid mobiusBandGlue) (x.2, x.1) := by
  -- Evaluate only this stable component of the comparison construction.
  rfl

/-- Helper for Example 74.5: every directly paired pair of square-edge points
has the same image under the coordinate-swapping comparison. -/
theorem edgeRelated_comparison {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) : comparison x = comparison y := by
  classical
  -- Normalize both occurrence indices before enumerating the four boundary edges.
  rw [polygonalRegions_edgeRelated_iff] at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  fin_cases edge₁ <;> fin_cases edge₂ <;>
    simp [comparison, regions, region_word, boundaryWord, boundaryLetters,
      unitSquare_edge_eq_explicit, explicitUnitSquareEdge,
      mobiusBandQuotient_mk_eq_iff, mobiusBandGlue_iff] at hlabel ⊢

/-- Helper for Example 74.5: the comparison is constant on the equivalence
closure generated by direct edge pairing. -/
theorem eqvGen_comparison {x y : regions.Source}
    (hxy : Relation.EqvGen regions.EdgeRelated x y) : comparison x = comparison y := by
  -- Extend preservation of a generating edge step through the four closure constructors.
  induction hxy with
  | rel _ _ h => exact edgeRelated_comparison h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Helper for Example 74.5: a Möbius gluing of swapped coordinates is the
direct pairing of the two `a`-edges of the one-square presentation. -/
theorem edgeRelated_of_swapped_mobiusBandGlue (x y : UnitSquare)
    (hxy : mobiusBandGlue (x.2, x.1) (y.2, y.1)) :
    regions.EdgeRelated (⟨region, x⟩ : regions.Source) ⟨region, y⟩ := by
  -- Choose the bottom and top occurrences of `a`, then evaluate their parametrizations.
  rw [polygonalRegions_edgeRelated_iff]
  refine ⟨region, region,
    Fin.cast (occurrence_length region).symm (0 : Fin 4),
    Fin.cast (occurrence_length region).symm (2 : Fin 4), x.1, ?_⟩
  rw [mobiusBandGlue_iff] at hxy
  rcases hxy with ⟨hx₂, hy₂, hx₁⟩
  have hy₁ : y.1 = unitInterval.symm x.1 := by
    calc
      y.1 = unitInterval.symm (unitInterval.symm y.1) :=
        (unitInterval.symm_symm y.1).symm
      _ = unitInterval.symm x.1 := congrArg unitInterval.symm hx₁.symm
  have hpoints : x = (x.1, 0) ∧ y = (unitInterval.symm x.1, 1) :=
    ⟨Prod.ext rfl hx₂, Prod.ext hy₁ hy₂⟩
  simpa [region_word, boundaryWord, boundaryLetters, regions,
    unitSquare_edge_eq_explicit, explicitUnitSquareEdge] using hpoints

/-- Helper for Example 74.5: on the unique square, comparison-map equality is
exactly the equivalence closure of direct edge pairing. -/
theorem comparison_region_fibers (x y : UnitSquare) :
    comparison (⟨region, x⟩ : regions.Source) = comparison ⟨region, y⟩ ↔
      Relation.EqvGen regions.EdgeRelated
        (⟨region, x⟩ : regions.Source) ⟨region, y⟩ := by
  -- Classify a Möbius quotient equality into equality or one of the two gluing directions.
  constructor
  · intro hcomparison
    rw [comparison_region, comparison_region, mobiusBandQuotient_mk_eq_iff] at hcomparison
    rcases hcomparison with hxy | hxy | hyx
    · have hpoints : x = y := (Equiv.prodComm unitInterval unitInterval).injective hxy
      subst y
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ (edgeRelated_of_swapped_mobiusBandGlue x y hxy)
    · exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (edgeRelated_of_swapped_mobiusBandGlue y x hyx))
  · -- Equality is preserved by direct edge steps, hence by their equivalence closure.
    intro hidentified
    exact eqvGen_comparison hidentified

/-- Helper for Example 74.5: the one-square comparison has precisely the
labelled-edge setoid as its kernel. -/
theorem comparison_fibers (source₁ source₂ : regions.Source) :
    comparison source₁ = comparison source₂ ↔ regions.Identified.r source₁ source₂ := by
  -- Normalize both source occurrences, then apply the fixed-region fiber calculation.
  rw [polygonalRegions_identified_iff_eqvGen]
  rcases source₁ with ⟨region₁, x⟩
  rcases source₂ with ⟨region₂, y⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  exact comparison_region_fibers x y

/-- Helper for Example 74.5: inserting a point into the unique square occurrence
is a section of source projection. -/
theorem projection_leftInverse_section : Function.LeftInverse
    (fun x : regions.Source ↦ (x.2 : UnitSquare))
    (fun x : UnitSquare ↦ (⟨region, x⟩ : regions.Source)) := by
  intro x
  -- Projection immediately recovers the point inserted into the unique occurrence.
  rfl

/-- Helper for Example 74.5: projection from the unique square occurrence is surjective. -/
theorem projection_surjective : Function.Surjective
    (fun x : regions.Source ↦ (x.2 : UnitSquare)) := by
  -- The fixed-occurrence section supplies a preimage of every square point.
  exact projection_leftInverse_section.surjective

/-- Helper for Example 74.5: projection from the singleton region source to its
square is a homeomorphism. -/
theorem sourceProjectionIsHomeomorph :
    IsHomeomorph (fun x : regions.Source ↦ (x.2 : UnitSquare)) := by
  -- Expose the homeomorphism as projection together with its fixed-region inverse.
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · -- Projection is continuous when restricted to every coproduct summand.
    rw [continuous_iSup_dom]
    intro sourceRegion
    rw [continuous_coinduced_dom]
    letI : TopologicalSpace (regions.Point sourceRegion) := regions.topology sourceRegion
    exact continuous_id
  · -- Inclusion into the unique summand is continuous and inverse to projection.
    have hinclusion : Continuous[regions.topology region, regions.sourceTopology]
        (Sigma.mk region : regions.Point region → regions.Source) :=
      continuous_iSup_rng (i := region) (f := Sigma.mk region)
        (continuous_coinduced_rng (f := Sigma.mk region))
    refine ⟨fun point ↦ (⟨region, point⟩ : regions.Source), ?_, ?_, ?_⟩
    · rintro ⟨sourceRegion, point⟩
      rw [occurrence_eq_region sourceRegion]
    · intro point
      rfl
    · unfold regions at hinclusion ⊢
      exact hinclusion

/-- Helper for Example 74.5: projection from the unique square occurrence to
its point space is a quotient map. -/
theorem projection_isQuotientMap :
    Topology.IsQuotientMap (fun x : regions.Source ↦ (x.2 : UnitSquare)) := by
  -- Every homeomorphism is a quotient map.
  exact sourceProjectionIsHomeomorph.isQuotientMap

/-- Helper for Example 74.5: the one-square comparison is a quotient map and
has exactly the labelled-edge fibers. -/
theorem comparison_realizes : regions.Realizes comparison := by
  constructor
  · -- Compose source projection, coordinate swap, and the Möbius quotient map.
    have swapQuotient : Topology.IsQuotientMap (Prod.swap : UnitSquare → UnitSquare) :=
      (Homeomorph.prodComm unitInterval unitInterval).isQuotientMap
    rw [comparison_eq_composition]
    simpa [Function.comp_def] using
      mobiusBandQuotientMap_isQuotientMap.comp
        (swapQuotient.comp projection_isQuotientMap)
  · -- The finite edge calculation already identifies the full kernel.
    exact comparison_fibers

/-- Companion to Example 74.5 (3): The realization of the one-square labelling scheme `a b a c` is
homeomorphic to `MobiusBand`. -/
theorem homeomorphicMobiusBand : Nonempty (Realization ≃ₜ MobiusBand) := by
  -- Identify the canonical realization and the concrete Möbius target through their kernels.
  obtain ⟨canonicalEquiv⟩ := realizationHomeomorphicOfRealizes regions regions.quotientMap
    (LabellingScheme.PolygonalRegions.quotientMap_realizes regions)
  obtain ⟨mobiusEquiv⟩ := realizationHomeomorphicOfRealizes regions comparison comparison_realizes
  exact ⟨canonicalEquiv.symm.trans mobiusEquiv⟩


end MobiusBandSquare
