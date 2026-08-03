module

public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Topology_Munkres_2000.Book.Definition_35_4.AdjunctionSpace
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Category.CompHaus.Basic
import all Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
import all Topology_Munkres_2000.Book.Definition_35_4.AdjunctionSpace
import Topology_Munkres_2000.Book.Exercise_31_6.ClosedMap
import Topology_Munkres_2000.Book.Exercise_31_7

noncomputable section

public section

namespace TwoDimensionalCWComplex

/-- The family consisting of a basepoint and `n` circles. -/
abbrev CircleFamily (n : ℕ) : Option (Fin n) → Type :=
  fun i ↦ Option.rec PUnit (fun _ ↦ Circle) i

/-- The canonical topology on the family consisting of a basepoint and `n` circles. -/
instance instTopologicalSpaceCircleFamily (n : ℕ) (i : Option (Fin n)) :
    TopologicalSpace (CircleFamily n i) :=
  match i with
  | none => inferInstance
  | some _ => inferInstance

/-- Helper for Exercise 73.2: every member of the finite circle family is compact. -/
instance instCompactSpaceCircleFamily (n : ℕ) (i : Option (Fin n)) :
    CompactSpace (CircleFamily n i) := by
  cases i <;> infer_instance

/-- Helper for Exercise 73.2: every member of the finite circle family is normal and `T₁`. -/
instance instT4SpaceCircleFamily (n : ℕ) (i : Option (Fin n)) :
    T4Space (CircleFamily n i) := by
  cases i <;> infer_instance

/-- Helper for Exercise 73.2: every member of the finite circle family is second countable. -/
instance instSecondCountableTopologyCircleFamily (n : ℕ) (i : Option (Fin n)) :
    SecondCountableTopology (CircleFamily n i) := by
  cases i <;> infer_instance

/-- The designated basepoint in each member of `CircleFamily n`. -/
def circlePoints (n : ℕ) : ∀ i, CircleFamily n i
  | none => PUnit.unit
  | some _ => 1

/-- The wedge of `n` circles, including a canonical basepoint when `n = 0`. -/
abbrev OneSkeleton (n : ℕ) :=
  Topology.IndexedPointedWedge.Space (CircleFamily n) (circlePoints n)

/-- The wedge point of the one-skeleton. -/
def oneSkeletonBasepoint (n : ℕ) : OneSkeleton n :=
  Topology.IndexedPointedWedge.point (CircleFamily n) (circlePoints n) none

/-- Helper for Exercise 73.2: the unique point in the extra `PUnit` factor represents
the one-skeleton basepoint. -/
theorem oneSkeleton_none_eq_basepoint (n : ℕ) (x : PUnit) :
    Topology.IndexedPointedWedge.quotientMap (CircleFamily n) (circlePoints n)
      ⟨none, x⟩ = oneSkeletonBasepoint n := by
  -- The `PUnit` representative is the designated point in the extra factor.
  cases x
  rfl

/-- Helper for Exercise 73.2: the designated point of every circle factor represents
the common one-skeleton basepoint. -/
theorem oneSkeleton_circlePoint_eq_basepoint (n : ℕ) (i : Fin n) :
    Topology.IndexedPointedWedge.inclusion (CircleFamily n) (circlePoints n)
      (some i) 1 = oneSkeletonBasepoint n := by
  -- Independence of the wedge-point representative compares the circle and `PUnit` factors.
  exact Topology.IndexedPointedWedge.point_eq
    (CircleFamily n) (circlePoints n) (some i) none

/-- Helper for Exercise 73.2: a circle factor includes continuously into the canonical
one-skeleton. -/
theorem continuous_oneSkeleton_circleInclusion (n : ℕ) (i : Fin n) :
    Continuous
      (Topology.IndexedPointedWedge.inclusion (CircleFamily n) (circlePoints n) (some i)) := by
  -- Compose the sigma injection with the defining quotient map.
  change Continuous (fun x : Circle ↦
    Quotient.mk
      (Topology.IndexedPointedWedge.setoid (CircleFamily n) (circlePoints n))
      (⟨some i, x⟩ : Σ j, CircleFamily n j))
  exact continuous_quotient_mk'.comp continuous_sigmaMk

/-- The disjoint union of `m` closed two-dimensional cells. -/
abbrev ClosedCells (m : ℕ) := Σ _ : Fin m, ClosedUnitBall 1

/-- The union of the boundary circles of the closed cells. -/
def boundary (m : ℕ) : Set (ClosedCells m) :=
  {x | x.2 ∈ StandardSphere.boundary 1}

/-- Helper for Exercise 73.2: package a point of one standard boundary circle as a
point of the selected cell boundary. -/
def boundaryMk {m : ℕ} (i : Fin m) (z : StandardSphere.boundary 1) : boundary m :=
  ⟨⟨i, z.1⟩, z.2⟩

/-- Helper for Exercise 73.2: the underlying closed-cell point of `boundaryMk`. -/
@[simp] theorem boundaryMk_val {m : ℕ} (i : Fin m)
    (z : StandardSphere.boundary 1) :
    (boundaryMk i z : ClosedCells m) = ⟨i, z.1⟩ := by
  -- This is the projection computation for the canonical boundary constructor.
  rfl

/-- Helper for Exercise 73.2: inserting one standard boundary component into the
finite boundary family is continuous. -/
theorem continuous_boundaryMk {m : ℕ} (i : Fin m) :
    Continuous (boundaryMk i) := by
  -- Continuity is checked on the underlying sigma point and then lifted to the subtype.
  apply Continuous.subtype_mk
  exact continuous_sigmaMk.comp continuous_subtype_val

/-- Helper for Exercise 73.2: recover the standard boundary-circle point from a
point of the finite boundary family. -/
def boundaryPoint {m : ℕ} (a : boundary m) : StandardSphere.boundary 1 :=
  ⟨a.1.2, a.2⟩

/-- Helper for Exercise 73.2: the recovered boundary-circle point has the original
cell coordinate. -/
@[simp] theorem boundaryPoint_val {m : ℕ} (a : boundary m) :
    (boundaryPoint a : ClosedUnitBall 1) = a.1.2 := by
  -- This is the value projection of `boundaryPoint`.
  rfl

/-- Helper for Exercise 73.2: every finite-boundary point is reconstructed from its
cell index and standard boundary point. -/
theorem boundaryMk_eta {m : ℕ} (a : boundary m) :
    boundaryMk a.1.1 (boundaryPoint a) = a := by
  -- Equality of boundary subtypes reduces to equality of their underlying sigma points.
  exact Subtype.ext rfl

/-- An attaching map for `m` two-cells on a wedge of `n` circles. -/
abbrev AttachingMap (n m : ℕ) := C(boundary m, OneSkeleton n)

/-- The two-dimensional CW complex obtained by attaching `m` two-cells to a wedge of
`n` circles. -/
abbrev Space {n m : ℕ} (f : AttachingMap n m) :=
  AdjunctionSpace (boundary m) f

/-- The canonical quotient map defining a two-dimensional CW complex. -/
def quotientMap {n m : ℕ} (f : AttachingMap n m) :
    ClosedCells m ⊕ OneSkeleton n → Space f :=
  AdjunctionSpace.quotientMap (boundary m) f

/-- The canonical basepoint inherited from the one-skeleton. -/
def basepoint {n m : ℕ} (f : AttachingMap n m) : Space f :=
  AdjunctionSpace.includeY (boundary m) f (oneSkeletonBasepoint n)

/-- Helper for Exercise 73.2: the named basepoint is the image of the one-skeleton
basepoint under the canonical inclusion. -/
@[simp] theorem basepoint_eq_includeY {n m : ℕ} (f : AttachingMap n m) :
    basepoint f =
      AdjunctionSpace.includeY (boundary m) f (oneSkeletonBasepoint n) := by
  -- Unfold the owner definition once, exposing the stable inclusion formula.
  rfl

/-- Helper for Exercise 73.2: the explicit and implicit quotient constructors define
the same projection. -/
private lemma quotientMk_eq_quotientMk' {X : Type*} (setoid : Setoid X) :
    Quotient.mk setoid = @Quotient.mk' X setoid := by
  -- Both functions send a representative to its quotient class.
  rfl

/-- Helper for Exercise 73.2: a closed equivalence relation on a compact Hausdorff
space has a closed quotient projection. -/
private lemma isClosedMap_quotientMk_of_isClosed_relation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (setoid : Setoid X)
    (hrelation : IsClosed {pair : X × X | setoid pair.1 pair.2}) :
    IsClosedMap (Quotient.mk setoid) := by
  -- Pull the image of a closed set back to its relation-saturation.
  rw [quotientMk_eq_quotientMk' setoid]
  intro C hC
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  have hsaturation :
      (@Quotient.mk' X setoid) ⁻¹' ((@Quotient.mk' X setoid) '' C) =
        Prod.fst ''
          ({pair : X × X | setoid pair.1 pair.2} ∩ (Set.univ ×ˢ C)) := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      exact ⟨(x, y), ⟨Quotient.exact heq.symm, Set.mem_prod.2 ⟨Set.mem_univ x, hy⟩⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hxy, _, hy⟩, rfl⟩
      exact ⟨y, hy, (Quotient.sound hxy).symm⟩
  rw [hsaturation]
  exact ((hrelation.inter (isClosed_univ.prod hC)).isCompact.image continuous_fst).isClosed

/-- Helper for Exercise 73.2: the generated pointed-wedge relation identifies exactly
equal representatives or two designated representatives. -/
private lemma oneSkeleton_eqvGen_iff (n : ℕ)
    (x y : Σ i, CircleFamily n i) :
    Relation.EqvGen
        (Topology.IndexedPointedWedge.Related (CircleFamily n) (circlePoints n)) x y ↔
      x = y ∨ (x.2 = circlePoints n x.1 ∧ y.2 = circlePoints n y.1) := by
  constructor
  · intro hxy
    -- The equality-or-designated normal form is stable under equivalence generation.
    induction hxy with
    | rel x y h =>
        obtain ⟨i, j, rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl⟩
    | refl x =>
        exact Or.inl rfl
    | symm x y _ ih =>
        rcases ih with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨h.2, h.1⟩
    | trans x y z _ _ hxy hyz =>
        rcases hxy with hxy | hxy
        · subst y
          exact hyz
        · rcases hyz with hyz | hyz
          · subst z
            exact Or.inr hxy
          · exact Or.inr ⟨hxy.1, hyz.2⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact Relation.EqvGen.refl x
    · apply Relation.EqvGen.rel
      exact ⟨x.1, y.1, Sigma.ext rfl (heq_of_eq hx), Sigma.ext rfl (heq_of_eq hy)⟩

/-- Helper for Exercise 73.2: the graph of the one-skeleton quotient relation is closed. -/
private lemma oneSkeletonSetoidGraph_isClosed (n : ℕ) :
    IsClosed {pair : (Σ i, CircleFamily n i) × (Σ i, CircleFamily n i) |
      Topology.IndexedPointedWedge.setoid (CircleFamily n) (circlePoints n)
        pair.1 pair.2} := by
  let designated : Set (Σ i, CircleFamily n i) :=
    Set.range (fun i ↦ ⟨i, circlePoints n i⟩)
  have hdesignated : designated.Finite := Set.finite_range _
  have hgraph :
      {pair : (Σ i, CircleFamily n i) × (Σ i, CircleFamily n i) |
          Topology.IndexedPointedWedge.setoid (CircleFamily n) (circlePoints n)
            pair.1 pair.2} =
        Set.diagonal (Σ i, CircleFamily n i) ∪ (designated ×ˢ designated) := by
    ext pair
    rcases pair with ⟨x, y⟩
    rw [Set.mem_union, Set.mem_diagonal_iff, Set.mem_prod]
    change Relation.EqvGen
        (Topology.IndexedPointedWedge.Related (CircleFamily n) (circlePoints n)) x y ↔ _
    rw [oneSkeleton_eqvGen_iff]
    constructor
    · rintro (hxy | ⟨hx, hy⟩)
      · exact Or.inl hxy
      · right
        constructor
        · exact ⟨x.1, Sigma.ext rfl (heq_of_eq hx.symm)⟩
        · exact ⟨y.1, Sigma.ext rfl (heq_of_eq hy.symm)⟩
    · rintro (hxy | ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
      · exact Or.inl hxy
      · right
        cases hi
        cases hj
        exact ⟨rfl, rfl⟩
  rw [hgraph]
  exact isClosed_diagonal.union (hdesignated.isClosed.prod hdesignated.isClosed)

/-- Helper for Exercise 73.2: the canonical projection onto the finite pointed wedge is closed. -/
private lemma oneSkeletonQuotientMap_isClosedMap (n : ℕ) :
    IsClosedMap
      (Topology.IndexedPointedWedge.quotientMap (CircleFamily n) (circlePoints n)) := by
  -- Apply the compact closed-relation quotient criterion.
  exact isClosedMap_quotientMk_of_isClosed_relation _
    (oneSkeletonSetoidGraph_isClosed n)

/-- Helper for Exercise 73.2: the finite pointed wedge is normal and `T₁`. -/
private theorem oneSkeletonT4Space (n : ℕ) : T4Space (OneSkeleton n) := by
  -- Closed quotients preserve normality and the `T₁` property.
  exact (oneSkeletonQuotientMap_isClosedMap n).t4Space continuous_quotient_mk'
    Quotient.mk_surjective

/-- Helper for Exercise 73.2: the canonical projection onto the finite pointed wedge is perfect. -/
private theorem oneSkeletonQuotientMap_isPerfectMap (n : ℕ) :
    IsPerfectMap
      (Topology.IndexedPointedWedge.quotientMap (CircleFamily n) (circlePoints n)) := by
  letI : T4Space (OneSkeleton n) := oneSkeletonT4Space n
  rw [isPerfectMap_iff]
  refine ⟨continuous_quotient_mk', oneSkeletonQuotientMap_isClosedMap n,
    Quotient.mk_surjective, ?_⟩
  intro y
  -- Hausdorffness makes each fiber closed in the compact source.
  exact (isClosed_singleton.preimage continuous_quotient_mk').isCompact

/-- Helper for Exercise 73.2: the canonical label of a point before forming an
adjunction-space quotient. -/
private noncomputable def adjunctionCode
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) : X ⊕ Y → X ⊕ Y :=
  Sum.elim
    (fun x ↦ @dite (X ⊕ Y) (x ∈ A) (Classical.propDecidable (x ∈ A))
      (fun hx ↦ Sum.inr (f ⟨x, hx⟩)) (fun _ ↦ Sum.inl x))
    Sum.inr

/-- Helper for Exercise 73.2: an attaching point receives the label of its image. -/
private lemma adjunctionCode_inl_of_mem
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) {x : X} (hx : x ∈ A) :
    adjunctionCode A f (Sum.inl x) = Sum.inr (f ⟨x, hx⟩) := by
  -- Select the attaching branch of the canonical label.
  simp [adjunctionCode, hx]

/-- Helper for Exercise 73.2: a point outside the attaching set retains its left label. -/
private lemma adjunctionCode_inl_of_not_mem
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) {x : X} (hx : x ∉ A) :
    adjunctionCode A f (Sum.inl x) = Sum.inl x := by
  -- Select the unattached branch of the canonical label.
  simp [adjunctionCode, hx]

/-- Helper for Exercise 73.2: a right-summand point retains its label. -/
private lemma adjunctionCode_inr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) (y : Y) :
    adjunctionCode A f (Sum.inr y) = Sum.inr y := by
  -- The right summand is already in normal form.
  rfl

/-- Helper for Exercise 73.2: the canonical label is constant on the generated
adjunction-space equivalence classes. -/
private lemma adjunctionCode_eq_of_eqvGen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) {x y : X ⊕ Y}
    (hxy : Relation.EqvGen (AdjunctionSpace.identifies A f) x y) :
    adjunctionCode A f x = adjunctionCode A f y := by
  induction hxy with
  | rel x y h =>
      unfold AdjunctionSpace.identifies at h
      obtain ⟨a, rfl, rfl⟩ := h
      exact adjunctionCode_inl_of_mem A f a.property
  | refl x =>
      rfl
  | symm x y _ ih =>
      exact ih.symm
  | trans x y z _ _ hxy hyz =>
      exact hxy.trans hyz

/-- Helper for Exercise 73.2: attaching a closed subset of a compact Hausdorff
space gives a closed equivalence-relation graph. -/
private lemma adjunctionSetoidGraph_isClosed
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [T2Space Y]
    {A : Set X} (hA : IsClosed A) (f : C(A, Y)) :
    IsClosed {pair : (X ⊕ Y) × (X ⊕ Y) |
      AdjunctionSpace.setoid A f pair.1 pair.2} := by
  let sameFiber : Set (A × A) := {ab | f ab.1 = f ab.2}
  let leftPairs : Set ((X ⊕ Y) × (X ⊕ Y)) :=
    Set.range (fun ab : sameFiber ↦
      (Sum.inl (ab.1.1 : X), Sum.inl (ab.1.2 : X)))
  let attachingGraph : Set ((X ⊕ Y) × (X ⊕ Y)) :=
    Set.range (fun a : A ↦ (Sum.inl (a : X), Sum.inr (f a)))
  let reverseAttachingGraph : Set ((X ⊕ Y) × (X ⊕ Y)) :=
    Set.range (fun a : A ↦ (Sum.inr (f a), Sum.inl (a : X)))
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  have hsameFiber : IsClosed sameFiber := by
    exact isClosed_eq (f.continuous.comp continuous_fst)
      (f.continuous.comp continuous_snd)
  letI : CompactSpace sameFiber :=
    isCompact_iff_compactSpace.mp hsameFiber.isCompact
  have hleftPairs : IsClosed leftPairs := by
    -- The equal-fiber pairs form a compact subtype, whose displayed image is closed.
    apply IsCompact.isClosed
    apply isCompact_range
    fun_prop
  have hattachingGraph : IsClosed attachingGraph := by
    -- The graph over the compact attaching set has compact, hence closed, range.
    apply IsCompact.isClosed
    apply isCompact_range
    fun_prop
  have hreverseAttachingGraph : IsClosed reverseAttachingGraph := by
    -- Reversing the graph coordinates preserves the same compact-range argument.
    apply IsCompact.isClosed
    apply isCompact_range
    fun_prop
  have hgraph :
      {pair : (X ⊕ Y) × (X ⊕ Y) |
          AdjunctionSpace.setoid A f pair.1 pair.2} =
        Set.diagonal (X ⊕ Y) ∪ leftPairs ∪ attachingGraph ∪ reverseAttachingGraph := by
    ext pair
    rcases pair with ⟨s, t⟩
    simp only [Set.mem_union]
    constructor
    · intro hst
      unfold AdjunctionSpace.setoid at hst
      have hcode := adjunctionCode_eq_of_eqvGen A f hst
      cases s with
      | inl x =>
          cases t with
          | inl x' =>
              by_cases hx : x ∈ A
              · by_cases hx' : x' ∈ A
                · rw [adjunctionCode_inl_of_mem A f hx,
                    adjunctionCode_inl_of_mem A f hx'] at hcode
                  have hfx : f ⟨x, hx⟩ = f ⟨x', hx'⟩ := Sum.inr.inj hcode
                  exact Or.inl (Or.inl (Or.inr
                    ⟨⟨(⟨x, hx⟩, ⟨x', hx'⟩), hfx⟩, rfl⟩))
                · rw [adjunctionCode_inl_of_mem A f hx,
                    adjunctionCode_inl_of_not_mem A f hx'] at hcode
                  exact (Sum.inr_ne_inl hcode).elim
              · by_cases hx' : x' ∈ A
                · rw [adjunctionCode_inl_of_not_mem A f hx,
                    adjunctionCode_inl_of_mem A f hx'] at hcode
                  exact (Sum.inl_ne_inr hcode).elim
                · rw [adjunctionCode_inl_of_not_mem A f hx,
                    adjunctionCode_inl_of_not_mem A f hx'] at hcode
                  exact Or.inl (Or.inl (Or.inl (Set.mem_diagonal_iff.mpr hcode)))
          | inr y =>
              by_cases hx : x ∈ A
              · rw [adjunctionCode_inl_of_mem A f hx,
                  adjunctionCode_inr A f y] at hcode
                have hfy : f ⟨x, hx⟩ = y := Sum.inr.inj hcode
                subst y
                exact Or.inl (Or.inr ⟨⟨x, hx⟩, rfl⟩)
              · rw [adjunctionCode_inl_of_not_mem A f hx,
                  adjunctionCode_inr A f y] at hcode
                exact (Sum.inl_ne_inr hcode).elim
      | inr y =>
          cases t with
          | inl x =>
              by_cases hx : x ∈ A
              · rw [adjunctionCode_inr A f y,
                  adjunctionCode_inl_of_mem A f hx] at hcode
                have hyf : y = f ⟨x, hx⟩ := Sum.inr.inj hcode
                subst y
                exact Or.inr ⟨⟨x, hx⟩, rfl⟩
              · rw [adjunctionCode_inr A f y,
                  adjunctionCode_inl_of_not_mem A f hx] at hcode
                exact (Sum.inr_ne_inl hcode).elim
          | inr y' =>
              rw [adjunctionCode_inr A f y,
                adjunctionCode_inr A f y'] at hcode
              exact Or.inl (Or.inl (Or.inl (Set.mem_diagonal_iff.mpr hcode)))
    · intro hst
      unfold AdjunctionSpace.setoid
      rcases hst with hst | hst
      · rcases hst with hst | hst
        · rcases hst with hst | hst
          · have hst' := Set.mem_diagonal_iff.mp hst
            change s = t at hst'
            subst t
            exact Relation.EqvGen.refl s
          · rcases hst with ⟨ab, habPair⟩
            rw [← habPair]
            rcases ab with ⟨⟨a, b⟩, hab⟩
            have ha : Relation.EqvGen (AdjunctionSpace.identifies A f)
                (Sum.inl (a : X)) (Sum.inr (f a)) :=
              Relation.EqvGen.rel _ _ ⟨a, rfl, rfl⟩
            have hb : Relation.EqvGen (AdjunctionSpace.identifies A f)
                (Sum.inl (b : X)) (Sum.inr (f b)) :=
              Relation.EqvGen.rel _ _ ⟨b, rfl, rfl⟩
            rw [hab] at ha
            exact Relation.EqvGen.trans _ _ _ ha hb.symm
        · rcases hst with ⟨a, haPair⟩
          rw [← haPair]
          exact Relation.EqvGen.rel _ _ ⟨a, rfl, rfl⟩
      · rcases hst with ⟨a, haPair⟩
        rw [← haPair]
        exact (Relation.EqvGen.rel _ _ ⟨a, rfl, rfl⟩).symm
  rw [hgraph]
  exact ((isClosed_diagonal.union hleftPairs).union hattachingGraph).union
    hreverseAttachingGraph

/-- A finite wedge of circles is compact. -/
instance instCompactSpaceOneSkeleton (n : ℕ) : CompactSpace (OneSkeleton n) :=
  Quotient.compactSpace

/-- A finite wedge of circles is Hausdorff. -/
instance instT2SpaceOneSkeleton (n : ℕ) : T2Space (OneSkeleton n) := by
  letI : T4Space (OneSkeleton n) := oneSkeletonT4Space n
  infer_instance

/-- A finite wedge of circles is regular. -/
instance instT3SpaceOneSkeleton (n : ℕ) : T3Space (OneSkeleton n) := by
  letI : T4Space (OneSkeleton n) := oneSkeletonT4Space n
  infer_instance

/-- A finite wedge of circles is second countable. -/
instance instSecondCountableTopologyOneSkeleton (n : ℕ) :
    SecondCountableTopology (OneSkeleton n) :=
  (oneSkeletonQuotientMap_isPerfectMap n).secondCountableTopology

/-- The source of the quotient map is regular. -/
instance instT3SpaceQuotientSource (n m : ℕ) : T3Space (ClosedCells m ⊕ OneSkeleton n) := by
  infer_instance

/-- The source of the quotient map is second countable. -/
instance instSecondCountableTopologyQuotientSource (n m : ℕ) :
    SecondCountableTopology (ClosedCells m ⊕ OneSkeleton n) := by
  infer_instance

/-- Helper for Exercise 73.2: the finite union of cell boundaries is closed in the
finite union of closed cells. -/
private lemma boundary_isClosed (m : ℕ) : IsClosed (boundary m) := by
  -- Check closedness separately on every closed-ball component.
  unfold boundary
  rw [isClosed_sigma_iff]
  intro i
  have hpreimage :
      Sigma.mk i ⁻¹' {x : ClosedCells m | x.2 ∈ StandardSphere.boundary 1} =
        {x : ClosedUnitBall 1 |
          ‖(x : EuclideanSpace ℝ (Fin (1 + 1)))‖ = (1 : ℝ)} := by
    ext x
    exact StandardSphere.mem_boundary_iff_norm_eq 1 x
  rw [hpreimage]
  have hnorm : Continuous (fun x : ClosedUnitBall 1 ↦
      ‖(x : EuclideanSpace ℝ (Fin (1 + 1)))‖) :=
    continuous_norm.comp continuous_subtype_val
  exact isClosed_eq hnorm continuous_const

/-- Helper for Exercise 73.2: the defining adjunction-space quotient projection is closed. -/
private lemma quotientMap_isClosedMap {n m : ℕ} (f : AttachingMap n m) :
    IsClosedMap (quotientMap f) := by
  -- The attachment relation has the closed graph established above.
  unfold quotientMap AdjunctionSpace.quotientMap
  exact isClosedMap_quotientMk_of_isClosed_relation _
    (adjunctionSetoidGraph_isClosed (boundary_isClosed m) f)

/-- Helper for Exercise 73.2: a finite two-dimensional adjunction complex is normal
and `T₁`. -/
private theorem spaceT4Space {n m : ℕ} (f : AttachingMap n m) :
    T4Space (Space f) := by
  -- Transfer separation across the closed continuous quotient projection.
  exact (quotientMap_isClosedMap f).t4Space
    (AdjunctionSpace.continuous_quotientMap (boundary m) f)
    Quotient.mk_surjective

/-- The adjunction space defining a finite two-dimensional CW complex is compact. -/
instance instCompactSpaceSpace {n m : ℕ} (f : AttachingMap n m) : CompactSpace (Space f) := by
  exact Quotient.compactSpace

/-- The adjunction space defining a finite two-dimensional CW complex is Hausdorff. -/
instance instT2SpaceSpace {n m : ℕ} (f : AttachingMap n m) : T2Space (Space f) := by
  letI : T4Space (Space f) := spaceT4Space f
  infer_instance

/-- The defining quotient map of a finite two-dimensional CW complex is perfect. -/
theorem quotientMap_isPerfectMap {n m : ℕ} (f : AttachingMap n m) :
    IsPerfectMap (quotientMap f) := by
  rw [isPerfectMap_iff]
  refine ⟨AdjunctionSpace.continuous_quotientMap (boundary m) f,
    quotientMap_isClosedMap f, Quotient.mk_surjective, ?_⟩
  intro y
  -- Every fiber is closed in the compact quotient source.
  exact (isClosed_singleton.preimage
    (AdjunctionSpace.continuous_quotientMap (boundary m) f)).isCompact

/-- A finite two-dimensional CW complex as a compact Hausdorff space. -/
abbrev compHaus {n m : ℕ} (f : AttachingMap n m) : CompHaus :=
  CompHaus.of (Space f)


end TwoDimensionalCWComplex
