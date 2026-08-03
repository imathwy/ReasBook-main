module

public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Topology_Munkres_2000.Book.Notation_74_1.SignedLetter
public import Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Example_22_5.Torus
import all Topology_Munkres_2000.Book.Example_74_2.UnitSquare
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Homeomorph.Quotient

public section

open scoped SignedLetter
open scoped Topology

namespace TorusSquare

/-- The signed boundary letters `a b a⁻¹ b⁻¹`, with labels `0 = a` and `1 = b`. -/
def boundaryLetters : List (Fin 2 × Bool) :=
  [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)⁻¹, (1 : Fin 2)⁻¹]

/-- The polygon word encoding the oriented boundary scheme `a b a⁻¹ b⁻¹`. -/
def boundaryWord : PolygonWord (Fin 2) :=
  ⟨boundaryLetters, by decide⟩

/-- The singleton labelling scheme whose boundary word is `a b a⁻¹ b⁻¹`. -/
def scheme : LabellingScheme (Fin 2) :=
  boundaryWord ::ₘ 0

/-- The unit square with its ordered boundary edges prescribed by the word `a b a⁻¹ b⁻¹`. -/
@[expose]
def regions : LabellingScheme.PolygonalRegions scheme where
  Point _ := unitInterval × unitInterval
  topology _ := inferInstance
  edge _ edge t := UnitSquare.edge edge t

/-- The unique polygonal-region occurrence in the square presentation. -/
noncomputable def region : LabellingScheme.Occurrence scheme :=
  (LabellingScheme.consOccurrenceEquiv boundaryWord 0).symm none

/-- The four square vertices as points of the presentation's source region. -/
noncomputable def vertex (i : Fin 4) : regions.Source :=
  ⟨region, UnitSquare.edge i 0⟩

/-- The quotient of the unit square specified by the scheme `a b a⁻¹ b⁻¹`. -/
abbrev Realization := regions.Realization

/-- Helper for Example 74.3: every occurrence in the singleton scheme is `region`. -/
lemma occurrence_eq_region (r : LabellingScheme.Occurrence scheme) : r = region := by
  -- The remainder of the cons-occurrence equivalence has no elements.
  unfold region
  apply (LabellingScheme.consOccurrenceEquiv boundaryWord 0).injective
  rw [Equiv.apply_symm_apply]
  cases h : LabellingScheme.consOccurrenceEquiv boundaryWord 0 r with
  | none => rfl
  | some remaining =>
      exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim

/-- Helper for Example 74.3: the unique occurrence carries the displayed boundary word. -/
lemma region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head word.
  rfl

/-- Helper for Example 74.3: every occurrence in the square scheme has four edges. -/
lemma occurrence_length (r : LabellingScheme.Occurrence scheme) : r.1.1.length = 4 := by
  -- Normalize to the unique occurrence and compute the concrete word length.
  rw [occurrence_eq_region r, region_word]
  decide

/-- Helper for Example 74.3: projection from the singleton region source to its square is a
homeomorphism. -/
lemma sourceProjectionIsHomeomorph :
    IsHomeomorph (fun x : regions.Source ↦ x.2) := by
  -- Exhibit insertion into the unique summand as the continuous inverse.
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

/-- Helper for Example 74.3: direct labelled-edge relatedness has its canonical witness form. -/
lemma edgeRelated_iff_witness (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : LabellingScheme.Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
          (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
          x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
          y = ⟨region₂, regions.edge region₂ edge₂
            (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
              else unitInterval.symm t)⟩ := by
  -- Unfold only the generating relation, not the generated quotient setoid.
  rfl

/-- Helper for Example 74.3: the labelled-edge setoid is the equivalence closure of direct
edge relatedness. -/
lemma identified_iff_eqvGen (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- This is the defining relation of `PolygonalRegions.Identified`.
  rfl

/-- Helper for Example 74.3: every directly paired pair of square edges is identified by the
coordinatewise endpoint relation. -/
lemma edgeRelated_identified {x y : regions.Source} (hxy : regions.EdgeRelated x y) :
    identified x.2 y.2 := by
  -- Normalize both occurrence indices, then enumerate the sixteen edge pairs.
  rw [edgeRelated_iff_witness] at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  fin_cases edge₁
  all_goals fin_cases edge₂
  all_goals
    simp [regions, region_word, boundaryWord, boundaryLetters, UnitSquare.edge,
      identified_iff, unitInterval.endpointSetoid_iff] at hlabel ⊢

/-- Helper for Example 74.3: corresponding points of the bottom and top edges are directly
paired, as are corresponding points of the left and right edges. -/
lemma oppositeEdgesRelated (t : unitInterval) :
    regions.EdgeRelated (⟨region, (t, 0)⟩ : regions.Source) ⟨region, (t, 1)⟩ ∧
      regions.EdgeRelated (⟨region, (0, t)⟩ : regions.Source) ⟨region, (1, t)⟩ := by
  -- Select the two occurrences of each label in the concrete boundary word.
  rw [edgeRelated_iff_witness, edgeRelated_iff_witness]
  constructor
  · refine ⟨region, region,
      Fin.cast (occurrence_length region).symm (0 : Fin 4),
      Fin.cast (occurrence_length region).symm (2 : Fin 4), t, ?_⟩
    simp [regions, region_word, boundaryWord, boundaryLetters, UnitSquare.edge]
  · refine ⟨region, region,
      Fin.cast (occurrence_length region).symm (3 : Fin 4),
      Fin.cast (occurrence_length region).symm (1 : Fin 4), unitInterval.symm t, ?_⟩
    simp [regions, region_word, boundaryWord, boundaryLetters, UnitSquare.edge]

/-- Helper for Example 74.3: corresponding bottom and top edge points are related in the
generated labelled-edge relation. -/
lemma bottomTopIdentified (t : unitInterval) :
    Relation.EqvGen regions.EdgeRelated
      (⟨region, (t, 0)⟩ : regions.Source) ⟨region, (t, 1)⟩ := by
  -- A direct opposite-edge pairing is a generator of the closure.
  exact Relation.EqvGen.rel _ _ (oppositeEdgesRelated t).1

/-- Helper for Example 74.3: corresponding left and right edge points are related in the
generated labelled-edge relation. -/
lemma leftRightIdentified (t : unitInterval) :
    Relation.EqvGen regions.EdgeRelated
      (⟨region, (0, t)⟩ : regions.Source) ⟨region, (1, t)⟩ := by
  -- A direct opposite-edge pairing is a generator of the closure.
  exact Relation.EqvGen.rel _ _ (oppositeEdgesRelated t).2

/-- Helper for Example 74.3: the coordinate endpoint setoid contains the equivalence closure
of every direct labelled-edge pairing. -/
lemma eqvGen_identified {x y : regions.Source}
    (hxy : Relation.EqvGen regions.EdgeRelated x y) : identified x.2 y.2 := by
  -- Extend the finite generator calculation through the closure constructors.
  induction hxy with
  | rel _ _ h => exact edgeRelated_identified h
  | refl a => exact identified.refl a.2
  | symm _ _ _ h => exact identified.symm h
  | trans _ _ _ _ _ hab hbc => exact identified.trans hab hbc

/-- Helper for Example 74.3: coordinatewise endpoint identification is generated by the two
opposite-edge pairings of the square. -/
lemma eqvGen_of_endpointSetoid (x y : unitInterval × unitInterval)
    (hx : unitInterval.endpointSetoid x.1 y.1)
    (hy : unitInterval.endpointSetoid x.2 y.2) :
    Relation.EqvGen regions.EdgeRelated
      (⟨region, x⟩ : regions.Source) ⟨region, y⟩ := by
  -- Normalize each coordinate relation to equality or one of the two endpoint orders.
  rw [unitInterval.endpointSetoid_iff] at hx hy
  rcases hx with hx | hx | hx
  all_goals rcases hy with hy | hy | hy
  · have hpoints : x = y := Prod.ext hx hy
    rw [hpoints]
    exact Relation.EqvGen.refl _
  · rcases hy with ⟨hy₀, hy₁⟩
    have hxPoint : x = (x.1, 0) := Prod.ext rfl hy₀
    have hyPoint : y = (x.1, 1) := Prod.ext hx.symm hy₁
    rw [hxPoint, hyPoint]
    exact bottomTopIdentified _
  · rcases hy with ⟨hy₁, hy₀⟩
    have hxPoint : x = (x.1, 1) := Prod.ext rfl hy₁
    have hyPoint : y = (x.1, 0) := Prod.ext hx.symm hy₀
    rw [hxPoint, hyPoint]
    exact Relation.EqvGen.symm _ _ (bottomTopIdentified _)
  · rcases hx with ⟨hx₀, hx₁⟩
    have hxPoint : x = (0, x.2) := Prod.ext hx₀ rfl
    have hyPoint : y = (1, x.2) := Prod.ext hx₁ hy.symm
    rw [hxPoint, hyPoint]
    exact leftRightIdentified _
  · rcases hx with ⟨hx₀, hx₁⟩
    rcases hy with ⟨hy₀, hy₁⟩
    have hxPoint : x = (0, 0) := Prod.ext hx₀ hy₀
    have hyPoint : y = (1, 1) := Prod.ext hx₁ hy₁
    rw [hxPoint, hyPoint]
    exact Relation.EqvGen.trans _ (⟨region, (1, 0)⟩ : regions.Source) _
      (leftRightIdentified 0) (bottomTopIdentified 1)
  · rcases hx with ⟨hx₀, hx₁⟩
    rcases hy with ⟨hy₁, hy₀⟩
    have hxPoint : x = (0, 1) := Prod.ext hx₀ hy₁
    have hyPoint : y = (1, 0) := Prod.ext hx₁ hy₀
    rw [hxPoint, hyPoint]
    exact Relation.EqvGen.trans _ (⟨region, (1, 1)⟩ : regions.Source) _
      (leftRightIdentified 1) (Relation.EqvGen.symm _ _ (bottomTopIdentified 1))
  · rcases hx with ⟨hx₁, hx₀⟩
    have hxPoint : x = (1, x.2) := Prod.ext hx₁ rfl
    have hyPoint : y = (0, x.2) := Prod.ext hx₀ hy.symm
    rw [hxPoint, hyPoint]
    exact Relation.EqvGen.symm _ _ (leftRightIdentified _)
  · rcases hx with ⟨hx₁, hx₀⟩
    rcases hy with ⟨hy₀, hy₁⟩
    have hxPoint : x = (1, 0) := Prod.ext hx₁ hy₀
    have hyPoint : y = (0, 1) := Prod.ext hx₀ hy₁
    rw [hxPoint, hyPoint]
    exact Relation.EqvGen.trans _ (⟨region, (0, 0)⟩ : regions.Source) _
      (Relation.EqvGen.symm _ _ (leftRightIdentified 0)) (bottomTopIdentified 0)
  · rcases hx with ⟨hx₁, hx₀⟩
    rcases hy with ⟨hy₁, hy₀⟩
    have hxPoint : x = (1, 1) := Prod.ext hx₁ hy₁
    have hyPoint : y = (0, 0) := Prod.ext hx₀ hy₀
    rw [hxPoint, hyPoint]
    exact Relation.EqvGen.trans _ (⟨region, (0, 1)⟩ : regions.Source) _
      (Relation.EqvGen.symm _ _ (leftRightIdentified 1))
      (Relation.EqvGen.symm _ _ (bottomTopIdentified 0))

/-- Helper for Example 74.3: the generated labelled-edge relation is exactly coordinatewise
endpoint identification after projecting to the unique square. -/
lemma identified_projection_iff (x y : regions.Source) :
    regions.Identified.r x y ↔ identified x.2 y.2 := by
  -- First replace both dependent occurrence indices by the unique region.
  rcases x with ⟨region₁, x⟩
  rcases y with ⟨region₂, y⟩
  have hregion₁ := occurrence_eq_region region₁
  have hregion₂ := occurrence_eq_region region₂
  subst region₁
  subst region₂
  rw [identified_iff_eqvGen, identified_iff]
  constructor
  · intro hxy
    -- The coordinate endpoint setoid contains every generator and all closure operations.
    exact (identified_iff x y).mp (eqvGen_identified hxy)
  · rintro ⟨hx, hy⟩
    -- The two opposite-edge generators realize all coordinate endpoint cases.
    exact eqvGen_of_endpointSetoid x y hx hy

/-- The square realization specified by `a b a⁻¹ b⁻¹` is homeomorphic to the quotient of the
unit square by coordinatewise endpoint identification. -/
theorem homeomorphicSpace : Nonempty (Realization ≃ₜ Space) := by
  -- Transport the two equivalent setoids across projection from the unique source summand.
  let projectionHomeomorph : regions.Source ≃ₜ unitInterval × unitInterval :=
    IsHomeomorph.homeomorph (fun x : regions.Source ↦ x.2) sourceProjectionIsHomeomorph
  have hrelation (x y : regions.Source) :
      regions.Identified.r x y ↔ identified (projectionHomeomorph x) (projectionHomeomorph y) := by
    simpa only [projectionHomeomorph, IsHomeomorph.homeomorph_apply] using
      identified_projection_iff x y
  exact ⟨Homeomorph.Quotient.congr projectionHomeomorph hrelation⟩

/-- Example 74.3: The square realization specified by the oriented boundary scheme
`a b a⁻¹ b⁻¹` is homeomorphic to the torus `UnitAddCircle × UnitAddCircle`. -/
theorem homeomorphicTorus :
    Nonempty (Realization ≃ₜ UnitAddCircle × UnitAddCircle) := by
  -- The canonical square-to-torus quotient identifies `Space` with the product torus.
  let torusMap : C(unitInterval × unitInterval, UnitAddCircle × UnitAddCircle) :=
    ⟨toTorus, toTorus_isQuotientMap.continuous⟩
  have htorusMap : Topology.IsQuotientMap torusMap := by
    simpa only [torusMap, ContinuousMap.coe_mk] using toTorus_isQuotientMap
  exact Nonempty.map (fun e ↦ e.trans htorusMap.homeomorph) homeomorphicSpace


end TorusSquare
