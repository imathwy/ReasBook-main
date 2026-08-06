import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Comparison

open scoped unitInterval

universe u

noncomputable section

/-- An auxiliary quotient-model carrier for the suspension `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`, retained as a bridge
presentation for unbased transport-sensitive arguments. The canonical public boundary map below
lands in `suspensionSpace (previousSkeletonQuotientPointed h x₀)`. -/
abbrev previousSkeletonQuotientSuspensionCarrier {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :=
  Unit ⊕
    ((collapseSubsetType Xnm1 (previousSkeletonLowerSubset Xnm2 Xnm1) × I) ⊕ Unit)

/-- The south pole in the bridge suspension presentation of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. -/
def previousSkeletonQuotientSuspensionSouth {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1 :=
  Sum.inl ()

/-- A cylinder point in the bridge suspension presentation of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. -/
def previousSkeletonQuotientSuspensionMk {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X)
    (q : collapseSubsetType Xnm1 (previousSkeletonLowerSubset Xnm2 Xnm1)) (t : I) :
    previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1 :=
  Sum.inr (Sum.inl (q, t))

/-- The north pole in the bridge suspension presentation of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. -/
def previousSkeletonQuotientSuspensionNorth {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1 :=
  Sum.inr (Sum.inr ())

/-- The quotient relation collapsing the two ends of the cylinder in the bridge suspension
presentation. -/
def previousSkeletonQuotientSuspensionRel {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1 →
      previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1 → Prop
  | Sum.inl _, Sum.inr (Sum.inl (_, t)) => t = 0
  | Sum.inr (Sum.inl (_, t)), Sum.inl _ => t = 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl (_, t)) => t = 1
  | Sum.inr (Sum.inl (_, t)), Sum.inr (Sum.inr _) => t = 1
  | _, _ => False

/-- The setoid for the bridge suspension presentation of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. -/
def previousSkeletonQuotientSuspensionSetoid {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    Setoid (previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1) :=
  Relation.EqvGen.setoid (previousSkeletonQuotientSuspensionRel Xnm2 Xnm1)

/-- A legacy alias for the chosen suspension-model owner of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. Prefer
`previousSkeletonQuotientSuspension` for the public source-facing owner. -/
abbrev previousSkeletonQuotientSuspensionType {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :=
  Quotient (previousSkeletonQuotientSuspensionSetoid Xnm2 Xnm1)

/-- The chosen public suspension-model owner of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. It is the quotient-model
presentation used by Construction 13.2.4 before comparing to the repository's reduced suspension
owner. -/
abbrev previousSkeletonQuotientSuspension {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :=
  previousSkeletonQuotientSuspensionType Xnm2 Xnm1

/-- The chosen suspension-model owner of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)` carries the compactly generated
replacement of its quotient topology. -/
instance previousSkeletonQuotientSuspensionTypeTopologicalSpace {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    TopologicalSpace (previousSkeletonQuotientSuspensionType Xnm2 Xnm1) :=
  TopologicalSpace.compactlyGenerated.{u, u}
    (previousSkeletonQuotientSuspensionType Xnm2 Xnm1)

/-- The representative-level map from the bridge suspension presentation to the repository's
canonical reduced-suspension owner. -/
private def previousSkeletonQuotientSuspensionComparisonRaw {X : Type u} [TopologicalSpace X]
    {Xnm2 Xnm1 : Set X} (h : Xnm2 ⊆ Xnm1) (x0 : Xnm2) :
    previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1 →
      (suspensionSpace (previousSkeletonQuotientPointed h x0)).toCompactlyGenerated
  | Sum.inl _ =>
      reducedSuspensionPoint (previousSkeletonQuotientPointed h x0)
  | Sum.inr (Sum.inl (q, t)) =>
      reducedSuspensionMk (previousSkeletonQuotientPointed h x0) (q, t)
  | Sum.inr (Sum.inr _) =>
      reducedSuspensionPoint (previousSkeletonQuotientPointed h x0)

/-- Helper for Construction 13.2.4: the representative-level bridge map from the auxiliary
suspension presentation to the canonical reduced suspension is continuous before descending to the
quotient. -/
private theorem previousSkeletonQuotientSuspensionComparisonRaw_continuous
    {X : Type u} [TopologicalSpace X] {Xnm2 Xnm1 : Set X}
    (h : Xnm2 ⊆ Xnm1) (x0 : Xnm2) :
    Continuous (previousSkeletonQuotientSuspensionComparisonRaw h x0) := by
  let southBranch :
      Unit → (suspensionSpace (previousSkeletonQuotientPointed h x0)).toCompactlyGenerated :=
    fun _ ↦ reducedSuspensionPoint (previousSkeletonQuotientPointed h x0)
  let cylinderBranch :
      collapseSubsetType Xnm1 (previousSkeletonLowerSubset Xnm2 Xnm1) × I →
        (suspensionSpace (previousSkeletonQuotientPointed h x0)).toCompactlyGenerated :=
    fun p ↦ reducedSuspensionMk (previousSkeletonQuotientPointed h x0) p
  let northBranch :
      Unit → (suspensionSpace (previousSkeletonQuotientPointed h x0)).toCompactlyGenerated :=
    fun _ ↦ reducedSuspensionPoint (previousSkeletonQuotientPointed h x0)
  have hsouth : Continuous southBranch := by
    -- The south pole branch is constant.
    exact continuous_const
  have hcylinder : Continuous cylinderBranch := by
    -- The middle branch is the standard reduced-suspension quotient map.
    simpa [cylinderBranch] using
      (continuous_reducedSuspensionMk (previousSkeletonQuotientPointed h x0))
  have hnorth : Continuous northBranch := by
    -- The north pole branch is constant as well.
    exact continuous_const
  have hfactor :
      previousSkeletonQuotientSuspensionComparisonRaw h x0 =
        Sum.elim southBranch (Sum.elim cylinderBranch northBranch) := by
    -- Expanding the nested sum carrier shows the raw bridge is exactly this branchwise formula.
    funext p
    rcases p with _ | (⟨q, t⟩ | _) <;> rfl
  rw [hfactor]
  exact Continuous.sumElim hsouth (Continuous.sumElim hcylinder hnorth)

/-- The bridge from the auxiliary suspension presentation respects the quotient relation. -/
private theorem previousSkeletonQuotientSuspensionComparisonRaw_respects
    {X : Type u} [TopologicalSpace X] {Xnm2 Xnm1 : Set X}
    (h : Xnm2 ⊆ Xnm1) (x0 : Xnm2)
    {p q : previousSkeletonQuotientSuspensionCarrier Xnm2 Xnm1}
    (hpq : previousSkeletonQuotientSuspensionSetoid Xnm2 Xnm1 p q) :
    previousSkeletonQuotientSuspensionComparisonRaw h x0 p =
      previousSkeletonQuotientSuspensionComparisonRaw h x0 q := by
  -- TODO: descend the four endpoint generator cases of
  -- `previousSkeletonQuotientSuspensionRel` through `Relation.EqvGen`.
  sorry

/-- The canonical comparison from the chosen suspension-model owner of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)` to the
repository's reduced-suspension owner `suspensionSpace (previousSkeletonQuotientPointed h x₀)`. -/
def previousSkeletonQuotientSuspensionComparison {X : Type u} [TopologicalSpace X]
    {Xnm2 Xnm1 : Set X} (h : Xnm2 ⊆ Xnm1) (x0 : Xnm2) :
    C(previousSkeletonQuotientSuspensionType Xnm2 Xnm1,
      (suspensionSpace (previousSkeletonQuotientPointed h x0)).toCompactlyGenerated) where
  toFun := Quotient.lift (previousSkeletonQuotientSuspensionComparisonRaw h x0)
    (fun a b hab ↦ previousSkeletonQuotientSuspensionComparisonRaw_respects h x0 hab)
  -- TODO: prove that the raw quotient lift remains continuous for the public `k`-ified
  -- suspension owner.
  continuous_toFun := sorry

/-- The representative-level map from the cofiber model of `Xⁿ⁻¹ ↪ Xⁿ` to the chosen
suspension-model owner of `Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. -/
private def topologicalBoundaryMapModelRaw {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    X ⊕ (Xnm1 × I) → previousSkeletonQuotientSuspensionType Xnm2 Xnm1
  | Sum.inl _ =>
      Quotient.mk'' (previousSkeletonQuotientSuspensionSouth Xnm2 Xnm1)
  | Sum.inr (a, t) =>
      Quotient.mk''
        (previousSkeletonQuotientSuspensionMk Xnm2 Xnm1 (Quotient.mk'' a) t)

/-- Helper for Construction 13.2.4: the representative-level cofiber-to-suspension bridge is
continuous before descending to the cofiber quotient. -/
private theorem topologicalBoundaryMapModelRaw_continuous
    {X : Type u} [TopologicalSpace X] (Xnm2 Xnm1 : Set X) :
    Continuous (topologicalBoundaryMapModelRaw Xnm2 Xnm1) := by
  -- TODO: prove continuity branchwise and then transport the quotient map to the public
  -- `k`-ified suspension owner.
  sorry

/-- The cofiber-level bridge formula respects the cofiber quotient relation. -/
private theorem topologicalBoundaryMapModelRaw_respects {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X)
    {p q : X ⊕ (Xnm1 × I)}
    (hpq : topologicalBoundaryCofiberSetoid Xnm1 p q) :
    topologicalBoundaryMapModelRaw Xnm2 Xnm1 p =
      topologicalBoundaryMapModelRaw Xnm2 Xnm1 q := by
  -- TODO: reduce the cofiber relation to its generators and connect the top-point case by an
  -- explicit `Relation.EqvGen` chain through the suspension north pole.
  sorry

/-- The cofiber-model boundary map landing in the chosen suspension-model owner of
`Σ(Xⁿ⁻¹ / Xⁿ⁻²)`. -/
def topologicalBoundaryCofiberMapModel {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) :
    C(topologicalBoundaryCofiberType Xnm1, previousSkeletonQuotientSuspension Xnm2 Xnm1)
    where
  toFun := Quotient.lift (topologicalBoundaryMapModelRaw Xnm2 Xnm1)
    (fun a b hab ↦ topologicalBoundaryMapModelRaw_respects Xnm2 Xnm1 hab)
  -- TODO: descend continuity from the raw cofiber quotient to the public `k`-ified cofiber owner.
  continuous_toFun := sorry

/-- The source-facing quotient-model boundary map
`Xⁿ / Xⁿ⁻¹ ⟶ previousSkeletonQuotientSuspension Xⁿ⁻² Xⁿ⁻¹`, obtained from a chosen comparison
`Xⁿ / Xⁿ⁻¹ ⟶ cofiber(Xⁿ⁻¹ ↪ Xⁿ)`. This chosen suspension-model owner is the public target for
Construction 13.2.4, while `previousSkeletonQuotientSuspensionComparison` gives the companion
comparison to the repository's reduced-suspension owner. -/
noncomputable abbrev topologicalBoundaryMapModel {X : Type u} [TopologicalSpace X]
    (Xnm2 Xnm1 : Set X) (quotientToCofiber : topologicalBoundaryQuotientToCofiber Xnm1) :
    C(collapseSubsetType X Xnm1, previousSkeletonQuotientSuspension Xnm2 Xnm1) :=
  (topologicalBoundaryCofiberMapModel Xnm2 Xnm1).comp quotientToCofiber
