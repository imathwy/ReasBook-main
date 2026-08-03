module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Topology.UnitInterval

public section

universe u v w

namespace LabellingScheme

/-- The occurrences of polygon words in a labelling scheme, retaining multiplicity. -/
@[expose]
noncomputable def Occurrence (scheme : LabellingScheme α) : Type u :=
  @Multiset.ToType (PolygonWord α) (Classical.decEq _) scheme

/-- Adjoining one polygon word splits its occurrences into the new occurrence and the remainder. -/
@[expose]
noncomputable def consOccurrenceEquiv (word : PolygonWord α) (scheme : LabellingScheme α) :
    Occurrence (word ::ₘ scheme) ≃ Option (Occurrence scheme) :=
  @Multiset.consEquiv (PolygonWord α) (Classical.decEq _) scheme word

/-- Geometric regions whose ordered boundary edges carry a labelling scheme. -/
structure PolygonalRegions {α : Type u} (scheme : LabellingScheme α) where
  Point (region : Occurrence scheme) : Type v
  topology (region : Occurrence scheme) : TopologicalSpace (Point region)
  edge (region : Occurrence scheme) (index : Fin region.1.1.length) (t : unitInterval) :
    Point region

namespace PolygonalRegions

variable {α : Type u} {scheme : LabellingScheme α}

/-- The disjoint union of the points of the polygonal regions. -/
abbrev Source (regions : PolygonalRegions scheme) :=
  (region : Occurrence scheme) × regions.Point region

/-- The disjoint-union topology on a family of polygonal regions. -/
@[reducible]
def sourceTopology (regions : PolygonalRegions scheme) : TopologicalSpace regions.Source :=
  ⨆ region, TopologicalSpace.coinduced (Sigma.mk region) (regions.topology region)

/-- Helper for Proposition 76.2: the source topology is the canonical dependent
coproduct topology of the stored component topologies. -/
theorem sourceTopology_eq_sigma (regions : PolygonalRegions scheme) :
    regions.sourceTopology =
      ⨆ region, TopologicalSpace.coinduced (Sigma.mk region) (regions.topology region) := by
  -- Expose the owner formula once so downstream reindexing can use sigma topology API.
  rfl

/-- The canonical topology on the disjoint union of polygonal regions. -/
instance (regions : PolygonalRegions scheme) : TopologicalSpace regions.Source :=
  regions.sourceTopology

/-- Two boundary points are directly paired when their labels agree, with the edge
parameter preserved for equal signs and reversed for unequal signs. -/
def EdgeRelated (regions : PolygonalRegions scheme) (x y : regions.Source) : Prop :=
  ∃ (region₁ region₂ : Occurrence scheme)
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (t : unitInterval),
      (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
      x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
      y = ⟨region₂, regions.edge region₂ edge₂
        (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
          else unitInterval.symm t)⟩

/-- Helper for Proposition 76.2: a direct labelled-edge pairing is exactly its
canonical pair of parametrized boundary witnesses. -/
theorem edgeRelated_iff (regions : PolygonalRegions scheme) (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      ∃ (region₁ region₂ : Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
        (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
        x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
        y = ⟨region₂, regions.edge region₂ edge₂
          (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
            else unitInterval.symm t)⟩ := by
  rfl

/-- Two boundary points are directly paired along occurrences of the label `c`. -/
def EdgeRelatedAt (regions : PolygonalRegions scheme) (c : α)
    (x y : regions.Source) : Prop :=
  ∃ (region₁ region₂ : Occurrence scheme)
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (t : unitInterval),
      (region₁.1.1.get edge₁).1 = c ∧
      (region₂.1.1.get edge₂).1 = c ∧
      x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
      y = ⟨region₂, regions.edge region₂ edge₂
        (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
          else unitInterval.symm t)⟩

/-- Helper for Proposition 76.2: a direct pairing at `c` is exactly the canonical
pair of parametrized edge points carrying `c`. -/
theorem edgeRelatedAt_iff (regions : PolygonalRegions scheme) (c : α)
    (x y : regions.Source) :
    regions.EdgeRelatedAt c x y ↔
      ∃ (region₁ region₂ : Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
        (region₁.1.1.get edge₁).1 = c ∧
        (region₂.1.1.get edge₂).1 = c ∧
        x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
        y = ⟨region₂, regions.edge region₂ edge₂
          (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
            else unitInterval.symm t)⟩ := by
  -- Reveal the witnesses without making downstream proofs unfold the owner definition.
  rfl

/-- Two boundary points are directly paired along a label other than `c`. -/
def EdgeRelatedAwayFrom (regions : PolygonalRegions scheme) (c : α)
    (x y : regions.Source) : Prop :=
  ∃ (region₁ region₂ : Occurrence scheme)
    (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
    (t : unitInterval),
      (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
      (region₁.1.1.get edge₁).1 ≠ c ∧
      x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
      y = ⟨region₂, regions.edge region₂ edge₂
        (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
          else unitInterval.symm t)⟩

/-- Helper for Proposition 76.2: a direct pairing away from `c` is exactly its
canonical pair of parametrized boundary witnesses. -/
theorem edgeRelatedAwayFrom_iff (regions : PolygonalRegions scheme) (c : α)
    (x y : regions.Source) :
    regions.EdgeRelatedAwayFrom c x y ↔
      ∃ (region₁ region₂ : Occurrence scheme)
        (edge₁ : Fin region₁.1.1.length) (edge₂ : Fin region₂.1.1.length)
        (t : unitInterval),
        (region₁.1.1.get edge₁).1 = (region₂.1.1.get edge₂).1 ∧
        (region₁.1.1.get edge₁).1 ≠ c ∧
        x = ⟨region₁, regions.edge region₁ edge₁ t⟩ ∧
        y = ⟨region₂, regions.edge region₂ edge₂
          (if (region₁.1.1.get edge₁).2 = (region₂.1.1.get edge₂).2 then t
            else unitInterval.symm t)⟩ := by
  rfl

/-- Helper for Proposition 76.1: every labelled-edge pairing occurs either at `c`
or away from `c`. -/
theorem edgeRelated_iff_at_or_awayFrom (regions : PolygonalRegions scheme) (c : α)
    (x y : regions.Source) :
    regions.EdgeRelated x y ↔
      regions.EdgeRelatedAt c x y ∨ regions.EdgeRelatedAwayFrom c x y := by
  classical
  constructor
  · rintro ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hx, hy⟩
    by_cases hc : (region₁.1.1.get edge₁).1 = c
    · left
      exact ⟨region₁, region₂, edge₁, edge₂, t, hc, hlabels.symm.trans hc, hx, hy⟩
    · right
      exact ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hc, hx, hy⟩
  · rintro (hAt | hAway)
    · rcases hAt with ⟨region₁, region₂, edge₁, edge₂, t, hc₁, hc₂, hx, hy⟩
      exact ⟨region₁, region₂, edge₁, edge₂, t, hc₁.trans hc₂.symm, hx, hy⟩
    · rcases hAway with ⟨region₁, region₂, edge₁, edge₂, t, hlabels, _, hx, hy⟩
      exact ⟨region₁, region₂, edge₁, edge₂, t, hlabels, hx, hy⟩

/-- Helper for Proposition 76.1: an edge pairing at `c` is an unrestricted
labelled-edge pairing. -/
theorem edgeRelatedAt_le_edgeRelated (regions : PolygonalRegions scheme) (c : α) :
    regions.EdgeRelatedAt c ≤ regions.EdgeRelated := by
  intro x y hxy
  exact (regions.edgeRelated_iff_at_or_awayFrom c x y).mpr (Or.inl hxy)

/-- Helper for Proposition 76.1: an edge pairing away from `c` is an unrestricted
labelled-edge pairing. -/
theorem edgeRelated_of_awayFrom (regions : PolygonalRegions scheme) (c : α)
    {x y : regions.Source} (hxy : regions.EdgeRelatedAwayFrom c x y) :
    regions.EdgeRelated x y := by
  exact (regions.edgeRelated_iff_at_or_awayFrom c x y).mpr (Or.inr hxy)

/-- The equivalence relation generated by all labelled-edge pairings. -/
def Identified (regions : PolygonalRegions scheme) : Setoid regions.Source :=
  Relation.EqvGen.setoid regions.EdgeRelated

/-- The quotient space obtained by performing every labelled-edge identification. -/
def Realization (regions : PolygonalRegions scheme) :=
  Quotient regions.Identified

/-- The canonical quotient topology on the labelled-edge realization. -/
instance instTopologicalSpaceRealization (regions : PolygonalRegions scheme) :
    TopologicalSpace regions.Realization :=
  inferInstanceAs (TopologicalSpace (Quotient regions.Identified))

/-- The canonical map from the regions to their labelled-edge quotient. -/
def quotientMap (regions : PolygonalRegions scheme) : regions.Source → regions.Realization :=
  Quotient.mk regions.Identified

/-- A map obtains a space from the regions exactly by the scheme's edge identifications. -/
structure Realizes (regions : PolygonalRegions scheme) {X : Type w} [TopologicalSpace X]
    (q : regions.Source → X) : Prop where
  isQuotientMap : Topology.IsQuotientMap q
  fibers (x y : regions.Source) : q x = q y ↔ regions.Identified.r x y

/-- The canonical quotient map realizes exactly the generated labelled-edge relation. -/
theorem quotientMap_realizes (regions : PolygonalRegions scheme) :
    regions.Realizes regions.quotientMap := by
  constructor
  · -- The realization carries the canonical quotient topology.
    exact isQuotientMap_quotient_mk'
  · intro x y
    -- Equality of quotient classes is precisely the defining setoid relation.
    exact Quotient.eq''

/-- A quotient map that identifies precisely the edges bearing the label `c`. -/
structure PastesLabel (regions : PolygonalRegions scheme) (c : α)
    {Y : Type w} [TopologicalSpace Y] (q : regions.Source → Y) : Prop where
  isQuotientMap : Topology.IsQuotientMap q
  fibers (x y : regions.Source) :
    q x = q y ↔ Relation.EqvGen (regions.EdgeRelatedAt c) x y

/-- The remaining labelled-edge relation induced after the `c`-edge quotient. -/
def RemainingRelated (regions : PolygonalRegions scheme) (c : α)
    {Y : Type w} (firstPaste : regions.Source → Y) (a b : Y) : Prop :=
  ∃ x y, firstPaste x = a ∧ firstPaste y = b ∧ regions.EdgeRelatedAwayFrom c x y

/-- Helper for Proposition 76.2: a remaining direct pairing is represented by
an original boundary pairing away from the pasted label. -/
theorem remainingRelated_iff (regions : PolygonalRegions scheme) (c : α)
    {Y : Type w} (firstPaste : regions.Source → Y) (a b : Y) :
    regions.RemainingRelated c firstPaste a b ↔
      ∃ x y, firstPaste x = a ∧ firstPaste y = b ∧
        regions.EdgeRelatedAwayFrom c x y := by
  rfl

/-- The equivalence relation generated by the remaining edge identifications on the
intermediate quotient. -/
def RemainingIdentified (regions : PolygonalRegions scheme) (c : α)
    {Y : Type w} (firstPaste : regions.Source → Y) : Setoid Y :=
  Relation.EqvGen.setoid (regions.RemainingRelated c firstPaste)

/-- A quotient map that performs precisely the remaining labelled-edge identifications. -/
structure PastesRemaining (regions : PolygonalRegions scheme) (c : α)
    {Y : Type v} {X : Type w} [TopologicalSpace Y] [TopologicalSpace X]
    (firstPaste : regions.Source → Y) (remainingPastes : Y → X) : Prop where
  isQuotientMap : Topology.IsQuotientMap remainingPastes
  fibers (a b : Y) :
    remainingPastes a = remainingPastes b ↔
      (regions.RemainingIdentified c firstPaste).r a b

/-- A realization of the original regions transports across an intermediate
homeomorphism to the remaining pasting stage of the cut regions. -/
theorem pastesRemaining_of_homeomorph {originalScheme : LabellingScheme α}
    (cutRegions : PolygonalRegions scheme) (originalRegions : PolygonalRegions originalScheme)
    (c : α) {Y : Type v} {X : Type w} [TopologicalSpace Y] [TopologicalSpace X]
    (firstPaste : cutRegions.Source → Y) (remainingPastes : Y → X)
    (intermediate : Y ≃ₜ originalRegions.Source)
    (hboundaryCompatibility : ∀ a b,
      (cutRegions.RemainingIdentified c firstPaste).r a b ↔
        originalRegions.Identified.r (intermediate a) (intermediate b))
    (hremaining : originalRegions.Realizes (remainingPastes ∘ intermediate.symm)) :
    cutRegions.PastesRemaining c firstPaste remainingPastes := by
  constructor
  · -- Cancel the intermediate homeomorphism from the known quotient composite.
    exact intermediate.symm.isQuotientMap.of_comp_isQuotientMap hremaining.isQuotientMap
  · intro a b
    -- The supplied compatibility identifies exactly the fibers of the remaining map.
    calc
      remainingPastes a = remainingPastes b ↔
          originalRegions.Identified.r (intermediate a) (intermediate b) := by
        simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using
          hremaining.fibers (intermediate a) (intermediate b)
      _ ↔ (cutRegions.RemainingIdentified c firstPaste).r a b :=
        (hboundaryCompatibility a b).symm

/-- Helper for Proposition 76.1: a generated remaining-edge relation has lifts
that are related by all labelled-edge identifications. -/
theorem exists_identified_lifts_of_remainingIdentified
    (regions : PolygonalRegions scheme) (c : α)
    {Y : Type w} [TopologicalSpace Y] (firstPaste : regions.Source → Y)
    (hfirstPaste : regions.PastesLabel c firstPaste) {a b : Y}
    (hab : (regions.RemainingIdentified c firstPaste).r a b) :
    ∃ x y, firstPaste x = a ∧ firstPaste y = b ∧ regions.Identified.r x y := by
  induction hab with
  | rel a b hab =>
      rcases hab with ⟨x, y, hx, hy, hxy⟩
      exact ⟨x, y, hx, hy,
        Relation.EqvGen.rel x y (regions.edgeRelated_of_awayFrom c hxy)⟩
  | refl a =>
      obtain ⟨x, hx⟩ := hfirstPaste.isQuotientMap.surjective a
      exact ⟨x, x, hx, hx, Relation.EqvGen.refl x⟩
  | symm a b _ ih =>
      rcases ih with ⟨x, y, hx, hy, hxy⟩
      exact ⟨y, x, hy, hx, Relation.EqvGen.symm x y hxy⟩
  | trans a b d _ _ ihab ihbd =>
      rcases ihab with ⟨x, y, hx, hy, hxy⟩
      rcases ihbd with ⟨z, t, hz, ht, hzt⟩
      have hyzAt : Relation.EqvGen (regions.EdgeRelatedAt c) y z :=
        (hfirstPaste.fibers y z).mp (hy.trans hz.symm)
      have hyz : regions.Identified.r y z :=
        Relation.EqvGen.mono (regions.edgeRelatedAt_le_edgeRelated c) y z hyzAt
      exact ⟨x, t, hx, ht,
        Relation.EqvGen.trans x y t hxy
          (Relation.EqvGen.trans y z t hyz hzt)⟩

/-- After first pasting the `c`-edges, pulling the remaining identifications back to
the original regions recovers all labelled-edge identifications. -/
theorem identified_iff_remainingIdentified_pullback (regions : PolygonalRegions scheme)
    (c : α) {Y : Type w} [TopologicalSpace Y] (firstPaste : regions.Source → Y)
    (hfirstPaste : regions.PastesLabel c firstPaste) (x y : regions.Source) :
    regions.Identified.r x y ↔
      (regions.RemainingIdentified c firstPaste).r (firstPaste x) (firstPaste y) := by
  constructor
  · intro hxy
    -- Send each generating edge either to equality in the first quotient or to a
    -- generator of the remaining quotient.
    induction hxy with
    | rel a b hab =>
        rcases (regions.edgeRelated_iff_at_or_awayFrom c a b).mp hab with hAt | hAway
        · have hpaste : firstPaste a = firstPaste b :=
            (hfirstPaste.fibers a b).mpr (Relation.EqvGen.rel a b hAt)
          rw [hpaste]
        · exact Relation.EqvGen.rel (firstPaste a) (firstPaste b)
            ⟨a, b, rfl, rfl, hAway⟩
    | refl a => exact Relation.EqvGen.refl (firstPaste a)
    | symm a b _ ih => exact Relation.EqvGen.symm (firstPaste a) (firstPaste b) ih
    | trans a b d _ _ ihab ihbd =>
        exact Relation.EqvGen.trans (firstPaste a) (firstPaste b) (firstPaste d) ihab ihbd
  · intro hxy
    -- Lift the remaining relation and reconnect the chosen lifts inside first-paste fibers.
    rcases regions.exists_identified_lifts_of_remainingIdentified c firstPaste hfirstPaste hxy with
      ⟨x', y', hx', hy', hidentified⟩
    have hleftAt : Relation.EqvGen (regions.EdgeRelatedAt c) x x' :=
      (hfirstPaste.fibers x x').mp hx'.symm
    have hrightAt : Relation.EqvGen (regions.EdgeRelatedAt c) y' y :=
      (hfirstPaste.fibers y' y).mp hy'
    have hleft : regions.Identified.r x x' :=
      Relation.EqvGen.mono (regions.edgeRelatedAt_le_edgeRelated c) x x' hleftAt
    have hright : regions.Identified.r y' y :=
      Relation.EqvGen.mono (regions.edgeRelatedAt_le_edgeRelated c) y' y hrightAt
    exact Relation.EqvGen.trans x x' y hleft
      (Relation.EqvGen.trans x' y' y hidentified hright)

/-- Successive quotient maps for one label and then the remaining labels realize the
quotient by all labelled-edge identifications. -/
theorem realizes_comp (regions : PolygonalRegions scheme) (c : α)
    {Y : Type v} {X : Type w} [TopologicalSpace Y] [TopologicalSpace X]
    (firstPaste : regions.Source → Y) (remainingPastes : Y → X)
    (hfirstPaste : regions.PastesLabel c firstPaste)
    (hremainingPastes : regions.PastesRemaining c firstPaste remainingPastes) :
    regions.Realizes (remainingPastes ∘ firstPaste) := by
  constructor
  · -- Quotient maps remain quotient maps under composition.
    exact hremainingPastes.isQuotientMap.comp hfirstPaste.isQuotientMap
  · intro x y
    -- The two fiber specifications identify the composite with the full relation.
    calc
      (remainingPastes ∘ firstPaste) x = (remainingPastes ∘ firstPaste) y ↔
          (regions.RemainingIdentified c firstPaste).r (firstPaste x) (firstPaste y) := by
        simpa only [Function.comp_apply] using
          hremainingPastes.fibers (firstPaste x) (firstPaste y)
      _ ↔ regions.Identified.r x y :=
        (regions.identified_iff_remainingIdentified_pullback c firstPaste
          hfirstPaste x y).symm


end PolygonalRegions

end LabellingScheme
