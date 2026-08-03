module

public import Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
import all Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
public import Topology_Munkres_2000.Book.Theorem_59_3.Sphere

public section

noncomputable section

open Set
open scoped ContinuousMap EuclideanSpace

universe u v

namespace Topology.PointedWedge

/-- Helper for Exercise 59.1: a wedge region is the union of the images of chosen subsets
of its two factors. -/
private def region {X : Type u} (x₀ : X) {Y : Type v} (y₀ : Y)
    (A : Set X) (B : Set Y) : Set (PointedWedge X x₀ Y y₀) :=
  left x₀ y₀ '' A ∪ right x₀ y₀ '' B

/-- Helper for Exercise 59.1: the representative-side predicate for a two-factor wedge region. -/
private def representativeMem {X : Type u} {Y : Type v} (A : Set X) (B : Set Y)
    (z : Σ i, Family X Y i) : Prop :=
  match z with
  | ⟨false, x⟩ => x.down ∈ A
  | ⟨true, y⟩ => y.down ∈ B

/-- Helper for Exercise 59.1: equality of canonical representatives is exactly the
relation of the indexed-wedge setoid. -/
private lemma quotientMk_eq_iff_setoid
    {I : Type*} (X : I → Type*) [∀ i, TopologicalSpace (X i)] (p : ∀ i, X i)
    (z w : Σ i, X i) :
    @Quotient.mk' _ (IndexedPointedWedge.setoid X p) z =
        @Quotient.mk' _ (IndexedPointedWedge.setoid X p) w ↔
      IndexedPointedWedge.setoid X p z w := by
  -- Apply the canonical equality characterization without unfolding the opaque setoid.
  exact Quotient.eq

/-- Helper for Exercise 59.1: the canonical quotient constructor for the indexed wedge is
a quotient map. -/
private lemma quotientMk_isQuotientMap
    {I : Type*} (X : I → Type*) [∀ i, TopologicalSpace (X i)] (p : ∀ i, X i) :
    Topology.IsQuotientMap
      (@Quotient.mk' _ (IndexedPointedWedge.setoid X p)) := by
  -- The topology on a quotient is defined precisely by this canonical quotient map.
  exact isQuotientMap_quotient_mk'

/-- Helper for Exercise 59.1: the equivalence closure of the relation joining every pair
of designated sigma points only adds reflexivity. -/
private lemma eqvGen_designated_iff
    {I : Type*} (X : I → Type*) (p : ∀ i, X i) (z w : Σ i, X i) :
    Relation.EqvGen
        (fun z w ↦ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩) z w ↔
      z = w ∨ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩ := by
  -- Induction on the generated equivalence shows that designated endpoints remain
  -- designated under symmetry and transitivity.
  constructor
  · intro h
    induction h with
    | rel z w hzw => exact Or.inr hzw
    | refl z => exact Or.inl rfl
    | symm z w _ ih =>
        rcases ih with rfl | ⟨i, j, hz, hw⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨j, i, hw, hz⟩
    | trans z w q _ _ hzw hwq =>
        rcases hzw with rfl | ⟨i, j, hz, hw⟩
        · exact hwq
        · rcases hwq with rfl | ⟨k, l, _, hq⟩
          · exact Or.inr ⟨i, j, hz, hw⟩
          · exact Or.inr ⟨i, l, hz, hq⟩
  · intro h
    rcases h with rfl | h
    · exact Relation.EqvGen.refl z
    · exact Relation.EqvGen.rel z w h

/-- Helper for Exercise 59.1: equality in the canonical quotient by the designated-point
relation has the expected representative normal form. -/
private lemma quotientMk_eq_iff_designated
    {I : Type*} (X : I → Type*) (p : ∀ i, X i) (z w : Σ i, X i) :
    @Quotient.mk' _
          (Relation.EqvGen.setoid
            (fun z w ↦ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩)) z =
        @Quotient.mk' _
          (Relation.EqvGen.setoid
            (fun z w ↦ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩)) w ↔
      z = w ∨ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩ := by
  -- Quotient equality exposes the generated relation, whose closure was classified above.
  exact Quotient.eq.trans (eqvGen_designated_iff X p z w)

/-- Helper for Exercise 59.1: two representatives determine the same indexed wedge point exactly
when they are equal or are both designated factor points. -/
private lemma quotientMap_eq_iff
    {I : Type*} (X : I → Type*) [∀ i, TopologicalSpace (X i)] (p : ∀ i, X i)
    (z w : Σ i, X i) :
    @Quotient.mk' _ (IndexedPointedWedge.setoid X p) z =
        @Quotient.mk' _ (IndexedPointedWedge.setoid X p) w ↔
      z = w ∨ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩ := by
  -- Route correction: exposing the owner definitions locally identifies the wedge setoid
  -- with the generated designated-point relation, so the established normal form applies.
  rw [quotientMk_eq_iff_setoid]
  change
    Relation.EqvGen
        (fun z w ↦ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩) z w ↔
      z = w ∨ ∃ i j, z = ⟨i, p i⟩ ∧ w = ⟨j, p j⟩
  exact eqvGen_designated_iff X p z w

/-- Helper for Exercise 59.1: the left inclusion is the public quotient map on a left-factor
representative. -/
private lemma left_eq_quotientMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (x : X) :
    left x₀ y₀ x =
      @Quotient.mk' _ (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))
        ⟨false, ULift.up x⟩ := by
  -- Exposing the owner definitions reduces the public inclusion to its quotient constructor.
  rfl

/-- Helper for Exercise 59.1: the right inclusion is the public quotient map on a right-factor
representative. -/
private lemma right_eq_quotientMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (y : Y) :
    right x₀ y₀ y =
      @Quotient.mk' _ (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))
        ⟨true, ULift.up y⟩ := by
  -- The right inclusion has the same definitional quotient computation on its branch.
  rfl

/-- Helper for Exercise 59.1: membership of a quotient representative in a wedge region is
exactly membership of its factor coordinate in the corresponding chosen subset. -/
private lemma quotientMap_mem_region_iff
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (z : Σ i, Family X Y i) :
    @Quotient.mk' _
        (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) z ∈ region x₀ y₀ A B ↔
      representativeMem A B z := by
  -- Route correction: use the local quotient-fiber normal form instead of unfolding the setoid.
  constructor
  · intro hz
    rcases hz with ⟨x, hx, hzx⟩ | ⟨y, hy, hzy⟩
    · rw [left_eq_quotientMap] at hzx
      rcases (quotientMap_eq_iff (Family X Y) (points x₀ y₀) _ _).mp hzx with h | h
      · rw [← h]
        simpa only [representativeMem, ULift.down_up] using hx
      · rcases h with ⟨i, j, _, rfl⟩
        cases j with
        | false => simpa only [representativeMem, ULift.down_up] using hx₀
        | true => simpa only [representativeMem, ULift.down_up] using hy₀
    · rw [right_eq_quotientMap] at hzy
      rcases (quotientMap_eq_iff (Family X Y) (points x₀ y₀) _ _).mp hzy with h | h
      · rw [← h]
        simpa only [representativeMem, ULift.down_up] using hy
      · rcases h with ⟨i, j, _, rfl⟩
        cases j with
        | false => simpa only [representativeMem, ULift.down_up] using hx₀
        | true => simpa only [representativeMem, ULift.down_up] using hy₀
  · intro hz
    rcases z with ⟨i, z⟩
    cases i with
    | false =>
        cases z with
        | up x =>
            exact Or.inl ⟨x, hz, left_eq_quotientMap x₀ y₀ x⟩
    | true =>
        cases z with
        | up y =>
            exact Or.inr ⟨y, hz, right_eq_quotientMap x₀ y₀ y⟩

/-- Helper for Exercise 59.1: a wedge region built from open factor subsets containing the
selected points is open. -/
private lemma isOpen_region
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    IsOpen (region x₀ y₀ A B) := by
  -- The quotient criterion reduces openness to the two factorwise preimages.
  rw [← (quotientMk_isQuotientMap (Family X Y) (points x₀ y₀)).isOpen_preimage,
    isOpen_sigma_iff]
  intro i
  cases i with
  | false =>
      have hpreimage :
          Sigma.mk false ⁻¹'
              ((@Quotient.mk' _
                (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))) ⁻¹'
                  region x₀ y₀ A B) = ULift.down ⁻¹' A := by
        ext z
        simpa only [Set.mem_preimage, representativeMem] using
          quotientMap_mem_region_iff x₀ y₀ A B hx₀ hy₀ (Sigma.mk false z)
      rw [hpreimage]
      exact hA.preimage continuous_uliftDown
  | true =>
      have hpreimage :
          Sigma.mk true ⁻¹'
              ((@Quotient.mk' _
                (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))) ⁻¹'
                  region x₀ y₀ A B) = ULift.down ⁻¹' B := by
        ext z
        simpa only [Set.mem_preimage, representativeMem] using
          quotientMap_mem_region_iff x₀ y₀ A B hx₀ hy₀ (Sigma.mk true z)
      rw [hpreimage]
      exact hB.preimage continuous_uliftDown

/-- Helper for Exercise 59.1: representatives of a wedge region, organized factor by factor. -/
private abbrev RegionRepresentative
    {X : Type u} {Y : Type v} (A : Set X) (B : Set Y) :=
  Σ i, {z : Family X Y i // representativeMem A B ⟨i, z⟩}

/-- Helper for Exercise 59.1: the restricted canonical representative space of a wedge region. -/
private abbrev RestrictedRegionRepresentative
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :=
  {z : Σ i, Family X Y i //
    @Quotient.mk' _
        (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) z ∈
      region x₀ y₀ A B}

/-- Helper for Exercise 59.1: forget the membership proof of a normalized representative. -/
private def regionRepresentativeVal
    {X : Type u} {Y : Type v} (A : Set X) (B : Set Y) :
    RegionRepresentative A B → Σ i, Family X Y i :=
  Sigma.map id (fun _ ↦ Subtype.val)

/-- Helper for Exercise 59.1: forgetting a normalized representative preserves its sigma data. -/
private lemma regionRepresentativeVal_apply
    {X : Type u} {Y : Type v} (A : Set X) (B : Set Y) (z : RegionRepresentative A B) :
    regionRepresentativeVal A B z = ⟨z.1, z.2.1⟩ := by
  -- Both sides retain exactly the same index and underlying factor point.
  rcases z with ⟨i, z⟩
  rfl

/-- Helper for Exercise 59.1: forget the factorwise membership packaging while retaining
membership in the restricted quotient presentation. -/
private def regionRepresentativeToRestricted
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    RegionRepresentative A B → RestrictedRegionRepresentative x₀ y₀ A B :=
  Set.codRestrict
    (regionRepresentativeVal A B)
    {z : Σ i, Family X Y i |
      @Quotient.mk' _
          (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) z ∈
        region x₀ y₀ A B}
    (fun z ↦ (quotientMap_mem_region_iff x₀ y₀ A B hx₀ hy₀ _).mpr z.2.2)

/-- Helper for Exercise 59.1: each factorwise representative subset is open when the
corresponding factor region is open. -/
private lemma isOpen_representativeMem_fiber
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (i : Bool) :
    IsOpen {z : Family X Y i | representativeMem A B ⟨i, z⟩} := by
  -- On either Boolean branch this is the inverse image under `ULift.down`.
  cases i with
  | false => exact hA.preimage continuous_uliftDown
  | true => exact hB.preimage continuous_uliftDown

/-- Helper for Exercise 59.1: forgetting factorwise membership is an embedding into the
restricted representative space. -/
private lemma regionRepresentativeToRestricted_isEmbedding
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    Topology.IsEmbedding
      (regionRepresentativeToRestricted x₀ y₀ A B hx₀ hy₀) := by
  -- The map is the sigma of the two open subtype inclusions, followed by a codomain restriction.
  have hSigma : Topology.IsEmbedding
      (regionRepresentativeVal A B) :=
    ((Topology.isOpenEmbedding_sigmaMap Function.injective_id).2 fun i ↦
      (isOpen_representativeMem_fiber A B hA hB i).isOpenEmbedding_subtypeVal).isEmbedding
  exact hSigma.codRestrict _ _

/-- Helper for Exercise 59.1: every restricted representative has the corresponding
factorwise membership packaging. -/
private lemma regionRepresentativeToRestricted_surjective
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    Function.Surjective (regionRepresentativeToRestricted x₀ y₀ A B hx₀ hy₀) := by
  -- Recover factor membership from the already-proved region membership characterization.
  rintro ⟨⟨i, z⟩, hz⟩
  refine ⟨⟨i, ⟨z, (quotientMap_mem_region_iff x₀ y₀ A B hx₀ hy₀ _).mp hz⟩⟩, ?_⟩
  apply Subtype.ext
  exact regionRepresentativeVal_apply A B _

/-- Helper for Exercise 59.1: the two presentations of restricted wedge representatives
are homeomorphic. -/
private noncomputable def regionRepresentativeHomeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    RegionRepresentative A B ≃ₜ RestrictedRegionRepresentative x₀ y₀ A B :=
  (regionRepresentativeToRestricted_isEmbedding x₀ y₀ A B hA hB hx₀ hy₀).toHomeomorphOfSurjective
    (regionRepresentativeToRestricted_surjective x₀ y₀ A B hx₀ hy₀)

/-- Helper for Exercise 59.1: the normalized representatives map canonically onto the
wedge region. -/
private noncomputable def regionQuotientMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    RegionRepresentative A B → region x₀ y₀ A B :=
  (region x₀ y₀ A B).restrictPreimage
      (@Quotient.mk' _
        (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))) ∘
    regionRepresentativeHomeomorph x₀ y₀ A B hA hB hx₀ hy₀

/-- Helper for Exercise 59.1: the normalized representative map is a quotient map. -/
private lemma regionQuotientMap_isQuotientMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    Topology.IsQuotientMap (regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀) := by
  -- Restrict the canonical quotient over the open region, then precompose with the homeomorphism.
  exact
    ((quotientMk_isQuotientMap (Family X Y) (points x₀ y₀)).restrictPreimage_isOpen
      (isOpen_region x₀ y₀ A B hA hB hx₀ hy₀)).comp
        (regionRepresentativeHomeomorph x₀ y₀ A B hA hB hx₀ hy₀).isQuotientMap

/-- Helper for Exercise 59.1: the normalized quotient map has the expected representative value. -/
private lemma regionQuotientMap_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (z : RegionRepresentative A B) :
    ↑(regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀ z) =
      @Quotient.mk' _
        (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨z.1, z.2.1⟩ := by
  -- The embedding homeomorphism and the restricted quotient both preserve the underlying value.
  simp only [regionQuotientMap, Function.comp_apply, regionRepresentativeHomeomorph,
    Topology.IsEmbedding.toHomeomorphOfSurjective_apply, regionRepresentativeToRestricted,
    Set.restrictPreimage, Set.MapsTo.restrict, Subtype.map, Set.val_codRestrict_apply]
  rw [regionRepresentativeVal_apply]

/-- Helper for Exercise 59.1: a continuous parameterized map that is fiberwise constant
descends jointly continuously along a quotient map. -/
private lemma exists_quotientLiftProduct
    {D : Type u} {Q : Type v} {T Z : Type*}
    [TopologicalSpace D] [TopologicalSpace Q] [TopologicalSpace T] [TopologicalSpace Z]
    [LocallyCompactSpace T]
    (q : C(D, Q)) (hq : Topology.IsQuotientMap q) (K : C(T × D, Z))
    (hK : ∀ t, Function.FactorsThrough (fun d ↦ K (t, d)) q) :
    ∃ L : C(T × Q, Z), ∀ t d, L (t, q d) = K (t, d) := by
  -- Lift each time slice, then use the product quotient criterion for joint continuity.
  let slice : T → C(D, Z) := fun t ↦
    ⟨fun d ↦ K (t, d), K.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let Lfun : T × Q → Z := fun z ↦ hq.lift (slice z.1) (hK z.1) z.2
  have hpre : Continuous (fun z : T × D ↦ Lfun (z.1, q z.2)) := by
    have heq : (fun z : T × D ↦ Lfun (z.1, q z.2)) = K := by
      funext z
      exact DFunLike.congr_fun (hq.lift_comp (slice z.1) (hK z.1)) z.2
    rw [heq]
    exact K.continuous
  have hL : Continuous Lfun := hq.continuous_lift_prod_right hpre
  refine ⟨⟨Lfun, hL⟩, ?_⟩
  intro t d
  exact DFunLike.congr_fun (hq.lift_comp (slice t) (hK t)) d

/-- Helper for Exercise 59.1: projecting normalized representatives onto the right factor
collapses the left branch to the selected point. -/
private def regionProjectionRight
    {X : Type u} {Y : Type v} (y₀ : Y) (A : Set X) (B : Set Y) (hy₀ : y₀ ∈ B) :
    RegionRepresentative A B → B
  | ⟨false, _⟩ => ⟨y₀, hy₀⟩
  | ⟨true, y⟩ => ⟨y.1.down, y.2⟩

/-- Helper for Exercise 59.1: the right representative projection is continuous. -/
private lemma continuous_regionProjectionRight
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (y₀ : Y) (A : Set X) (B : Set Y) (hy₀ : y₀ ∈ B) :
    Continuous (regionProjectionRight y₀ A B hy₀) := by
  -- Continuity is constant on the left branch and induced by `ULift.down` on the right.
  apply continuous_sigma
  intro i
  cases i with
  | false => exact continuous_const
  | true => exact (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _

/-- Helper for Exercise 59.1: projecting a designated representative to the right always
gives the selected right point. -/
private lemma regionProjectionRight_designated
    {X : Type u} {Y : Type v} (x₀ : X) (y₀ : Y)
    (A : Set X) (B : Set Y) (hy₀ : y₀ ∈ B) (z : RegionRepresentative A B) (i : Bool)
    (hz : regionRepresentativeVal A B z = ⟨i, points x₀ y₀ i⟩) :
    regionProjectionRight y₀ A B hy₀ z = ⟨y₀, hy₀⟩ := by
  -- Both possible designated branches are sent to the chosen right basepoint.
  rw [regionRepresentativeVal_apply] at hz
  rcases z with ⟨j, z⟩
  cases j <;> cases i
  · rfl
  · cases congrArg Sigma.fst hz
  · cases congrArg Sigma.fst hz
  · apply Subtype.ext
    have hz' : (z : Family X Y true) = points x₀ y₀ true := by
      exact sigma_mk_injective (by simpa using hz)
    exact congrArg ULift.down hz'

/-- Helper for Exercise 59.1: the right representative projection is constant on fibers
of the normalized region quotient. -/
private lemma regionProjectionRight_factors
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    Function.FactorsThrough (regionProjectionRight y₀ A B hy₀)
      (regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀) := by
  -- Quotient-equal representatives are either identical or both designated points.
  intro z w hzw
  have hq := congrArg Subtype.val hzw
  rw [regionQuotientMap_apply, regionQuotientMap_apply] at hq
  rcases (quotientMap_eq_iff (Family X Y) (points x₀ y₀)
      (regionRepresentativeVal A B z) (regionRepresentativeVal A B w)).mp
      (by simpa only [regionRepresentativeVal_apply] using hq) with h | h
  · exact congrArg (regionProjectionRight y₀ A B hy₀)
      (Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) h)
  · rcases h with ⟨i, j, hi, hj⟩
    exact (regionProjectionRight_designated x₀ y₀ A B hy₀ z i hi).trans
      (regionProjectionRight_designated x₀ y₀ A B hy₀ w j hj).symm

/-- Helper for Exercise 59.1: include the right factor in a wedge region. -/
private def regionRightInclusion
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :
    B → region x₀ y₀ A B :=
  fun y ↦ ⟨right x₀ y₀ y.1, Or.inr ⟨y.1, y.2, rfl⟩⟩

/-- Helper for Exercise 59.1: the right-factor inclusion into a wedge region is continuous. -/
private lemma continuous_regionRightInclusion
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :
    Continuous (regionRightInclusion x₀ y₀ A B) := by
  -- Compose the public right inclusion with the subtype projection and restrict its codomain.
  exact ((continuous_right x₀ y₀).comp continuous_subtype_val).subtype_mk _

/-- Helper for Exercise 59.1: projecting normalized representatives onto the left factor
collapses the right branch to the selected point. -/
private def regionProjectionLeft
    {X : Type u} {Y : Type v} (x₀ : X) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) :
    RegionRepresentative A B → A
  | ⟨false, x⟩ => ⟨x.1.down, x.2⟩
  | ⟨true, _⟩ => ⟨x₀, hx₀⟩

/-- Helper for Exercise 59.1: the left representative projection is continuous. -/
private lemma continuous_regionProjectionLeft
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) :
    Continuous (regionProjectionLeft x₀ A B hx₀) := by
  -- Continuity is induced by `ULift.down` on the left and constant on the right.
  apply continuous_sigma
  intro i
  cases i with
  | false => exact (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
  | true => exact continuous_const

/-- Helper for Exercise 59.1: projecting a designated representative to the left always
gives the selected left point. -/
private lemma regionProjectionLeft_designated
    {X : Type u} {Y : Type v} (x₀ : X) (y₀ : Y)
    (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (z : RegionRepresentative A B) (i : Bool)
    (hz : regionRepresentativeVal A B z = ⟨i, points x₀ y₀ i⟩) :
    regionProjectionLeft x₀ A B hx₀ z = ⟨x₀, hx₀⟩ := by
  -- Both possible designated branches are sent to the chosen left basepoint.
  rw [regionRepresentativeVal_apply] at hz
  rcases z with ⟨j, z⟩
  cases j <;> cases i
  · apply Subtype.ext
    have hz' : (z : Family X Y false) = points x₀ y₀ false := by
      exact sigma_mk_injective (by simpa using hz)
    exact congrArg ULift.down hz'
  · cases congrArg Sigma.fst hz
  · cases congrArg Sigma.fst hz
  · rfl

/-- Helper for Exercise 59.1: the left representative projection is constant on fibers
of the normalized region quotient. -/
private lemma regionProjectionLeft_factors
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    Function.FactorsThrough (regionProjectionLeft x₀ A B hx₀)
      (regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀) := by
  -- Apply the same quotient-fiber dichotomy with the two Boolean branches exchanged.
  intro z w hzw
  have hq := congrArg Subtype.val hzw
  rw [regionQuotientMap_apply, regionQuotientMap_apply] at hq
  rcases (quotientMap_eq_iff (Family X Y) (points x₀ y₀)
      (regionRepresentativeVal A B z) (regionRepresentativeVal A B w)).mp
      (by simpa only [regionRepresentativeVal_apply] using hq) with h | h
  · exact congrArg (regionProjectionLeft x₀ A B hx₀)
      (Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) h)
  · rcases h with ⟨i, j, hi, hj⟩
    exact (regionProjectionLeft_designated x₀ y₀ A B hx₀ z i hi).trans
      (regionProjectionLeft_designated x₀ y₀ A B hx₀ w j hj).symm

/-- Helper for Exercise 59.1: include the left factor in a wedge region. -/
private def regionLeftInclusion
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :
    A → region x₀ y₀ A B :=
  fun x ↦ ⟨left x₀ y₀ x.1, Or.inl ⟨x.1, x.2, rfl⟩⟩

/-- Helper for Exercise 59.1: the left-factor inclusion into a wedge region is continuous. -/
private lemma continuous_regionLeftInclusion
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :
    Continuous (regionLeftInclusion x₀ y₀ A B) := by
  -- Compose the public left inclusion with the subtype projection and restrict its codomain.
  exact ((continuous_left x₀ y₀).comp continuous_subtype_val).subtype_mk _

/-- Helper for Exercise 59.1: extract the left-factor point carried by a normalized
left representative. -/
private def leftRepresentativePoint
    {X : Type u} {Y : Type v} (A : Set X) (B : Set Y)
    (x : {z : Family X Y false // representativeMem A B ⟨false, z⟩}) : A :=
  ⟨x.1.down, x.2⟩

/-- Helper for Exercise 59.1: extracting the left-factor point is continuous. -/
private lemma continuous_leftRepresentativePoint
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) : Continuous (leftRepresentativePoint A B) := by
  -- Forget the representative proof, lower the universe, and retain membership in `A`.
  exact (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _

/-- Helper for Exercise 59.1: the left-factor contraction, extended by the stationary
right branch, on normalized representatives. -/
private def regionContractionRightRepresentative
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩}) :
    unitInterval × RegionRepresentative A B → region x₀ y₀ A B :=
  fun z ↦
    match z.2 with
    | ⟨false, x⟩ =>
        let xA : A := leftRepresentativePoint A B x
        ⟨left x₀ y₀ (H (z.1, xA)).1,
          Or.inl ⟨(H (z.1, xA)).1, (H (z.1, xA)).2, rfl⟩⟩
    | ⟨true, y⟩ =>
        ⟨right x₀ y₀ y.1.down, Or.inr ⟨y.1.down, y.2, rfl⟩⟩

/-- Helper for Exercise 59.1: the representative-side right collapse is continuous. -/
private lemma continuous_regionContractionRightRepresentative
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩}) :
    Continuous (regionContractionRightRepresentative x₀ y₀ A B hx₀ H) := by
  -- Move the time coordinate past the sigma, then check continuity on the two branches.
  let G : (Σ i, ({z : Family X Y i // representativeMem A B ⟨i, z⟩} × unitInterval)) →
      region x₀ y₀ A B := fun z ↦
    regionContractionRightRepresentative x₀ y₀ A B hx₀ H (z.2.2, ⟨z.1, z.2.1⟩)
  have hG : Continuous G := by
    apply continuous_sigma
    intro i
    cases i with
    | false =>
        dsimp only [G, regionContractionRightRepresentative]
        apply Continuous.subtype_mk
        exact (continuous_left x₀ y₀).comp
          (continuous_subtype_val.comp ((map_continuous H).comp
            (continuous_snd.prodMk
              ((continuous_leftRepresentativePoint A B).comp continuous_fst))))
    | true =>
        dsimp only [G, regionContractionRightRepresentative]
        apply Continuous.subtype_mk
        exact (continuous_right x₀ y₀).comp
          ((continuous_uliftDown.comp continuous_subtype_val).comp continuous_fst)
  have heq : regionContractionRightRepresentative x₀ y₀ A B hx₀ H =
      G ∘ Homeomorph.sigmaProdDistrib ∘ Prod.swap := by
    funext z
    rfl
  rw [heq]
  exact hG.comp
    ((Homeomorph.sigmaProdDistrib (Y := unitInterval)).continuous.comp continuous_swap)

/-- Helper for Exercise 59.1: the representative-side right collapse starts at the
normalized quotient map. -/
private lemma regionContractionRightRepresentative_zero
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩})
    (z : RegionRepresentative A B) :
    regionContractionRightRepresentative x₀ y₀ A B hx₀ H (0, z) =
      regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀ z := by
  -- At time zero the supplied contraction is the identity on the left branch.
  rcases z with ⟨i, z⟩
  cases i with
  | false =>
      rcases z with ⟨⟨x⟩, hx⟩
      apply Subtype.ext
      rw [regionQuotientMap_apply]
      change left x₀ y₀ (H (0, leftRepresentativePoint A B ⟨ULift.up x, hx⟩)).1 = _
      calc
        _ = left x₀ y₀ x := congrArg (fun a : A ↦ left x₀ y₀ a.1)
          (H.map_zero_left (leftRepresentativePoint A B ⟨ULift.up x, hx⟩))
        _ = _ := left_eq_quotientMap x₀ y₀ x
  | true =>
      rcases z with ⟨⟨y⟩, hy⟩
      apply Subtype.ext
      rw [regionQuotientMap_apply]
      exact right_eq_quotientMap x₀ y₀ y

/-- Helper for Exercise 59.1: the representative-side right collapse ends at inclusion
after projection. -/
private lemma regionContractionRightRepresentative_one
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩})
    (z : RegionRepresentative A B) :
    regionContractionRightRepresentative x₀ y₀ A B hx₀ H (1, z) =
      regionRightInclusion x₀ y₀ A B (regionProjectionRight y₀ A B hy₀ z) := by
  -- At time one the left branch reaches the common basepoint and the right stays fixed.
  rcases z with ⟨i, z⟩
  cases i with
  | false =>
      apply Subtype.ext
      change left x₀ y₀ (H (1, leftRepresentativePoint A B z)).1 = right x₀ y₀ y₀
      calc
        _ = left x₀ y₀ x₀ := congrArg (fun a : A ↦ left x₀ y₀ a.1)
          (H.map_one_left (leftRepresentativePoint A B z))
        _ = _ := left_basepoint_eq_right_basepoint x₀ y₀
  | true => rfl

/-- Helper for Exercise 59.1: throughout the right collapse, every designated representative
is the common wedge point. -/
private lemma regionContractionRightRepresentative_designated
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩})
    (t : unitInterval) (z : RegionRepresentative A B) (i : Bool)
    (hz : regionRepresentativeVal A B z = ⟨i, points x₀ y₀ i⟩) :
    regionContractionRightRepresentative x₀ y₀ A B hx₀ H (t, z) =
      regionRightInclusion x₀ y₀ A B ⟨y₀, hy₀⟩ := by
  -- The relative condition fixes the selected left point; the right point is stationary.
  rw [regionRepresentativeVal_apply] at hz
  rcases z with ⟨j, z⟩
  cases j <;> cases i
  · have hz' : (z : Family X Y false) = points x₀ y₀ false := by
      exact sigma_mk_injective (by simpa using hz)
    rcases z with ⟨⟨x⟩, hx⟩
    have hxx : x = x₀ := congrArg ULift.down hz'
    subst x
    apply Subtype.ext
    change left x₀ y₀ (H (t, leftRepresentativePoint A B ⟨ULift.up x₀, hx⟩)).1 =
      right x₀ y₀ y₀
    calc
      _ = left x₀ y₀ x₀ := congrArg (fun a : A ↦ left x₀ y₀ a.1)
        (H.eq_fst t (Set.mem_singleton_iff.mpr (Subtype.ext rfl)))
      _ = _ := left_basepoint_eq_right_basepoint x₀ y₀
  · cases congrArg Sigma.fst hz
  · cases congrArg Sigma.fst hz
  · have hz' : (z : Family X Y true) = points x₀ y₀ true := by
      exact sigma_mk_injective (by simpa using hz)
    rcases z with ⟨⟨y⟩, hy⟩
    have hyy : y = y₀ := congrArg ULift.down hz'
    subst y
    rfl

/-- Helper for Exercise 59.1: every time slice of the representative right collapse is
constant on normalized quotient fibers. -/
private lemma regionContractionRightRepresentative_factors
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩})
    (t : unitInterval) :
    Function.FactorsThrough
      (fun z ↦ regionContractionRightRepresentative x₀ y₀ A B hx₀ H (t, z))
      (regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀) := by
  -- Use the same equal-or-designated fiber normal form as for the projection.
  intro z w hzw
  have hq := congrArg Subtype.val hzw
  rw [regionQuotientMap_apply, regionQuotientMap_apply] at hq
  rcases (quotientMap_eq_iff (Family X Y) (points x₀ y₀)
      (regionRepresentativeVal A B z) (regionRepresentativeVal A B w)).mp
      (by simpa only [regionRepresentativeVal_apply] using hq) with h | h
  · exact congrArg
      (fun z ↦ regionContractionRightRepresentative x₀ y₀ A B hx₀ H (t, z))
      (Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) h)
  · rcases h with ⟨i, j, hi, hj⟩
    exact (regionContractionRightRepresentative_designated
      x₀ y₀ A B hx₀ hy₀ H t z i hi).trans
        (regionContractionRightRepresentative_designated
          x₀ y₀ A B hx₀ hy₀ H t w j hj).symm

/-- Helper for Exercise 59.1: contracting the left factor of an open wedge region gives a
homotopy equivalence with its right factor. -/
private lemma region_homotopyEquiv_right
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopicRel
      (ContinuousMap.id A) (ContinuousMap.const A ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩}) :
    Nonempty (region x₀ y₀ A B ≃ₕ B) := by
  -- Choose the supplied relative contraction and package the normalized quotient presentation.
  obtain ⟨H⟩ := H
  let q : C(RegionRepresentative A B, region x₀ y₀ A B) :=
    ⟨regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀,
      (regionQuotientMap_isQuotientMap x₀ y₀ A B hA hB hx₀ hy₀).continuous⟩
  have hq : Topology.IsQuotientMap q :=
    regionQuotientMap_isQuotientMap x₀ y₀ A B hA hB hx₀ hy₀
  let r : C(RegionRepresentative A B, B) :=
    ⟨regionProjectionRight y₀ A B hy₀, continuous_regionProjectionRight y₀ A B hy₀⟩
  have hr : Function.FactorsThrough r q :=
    regionProjectionRight_factors x₀ y₀ A B hA hB hx₀ hy₀
  let f : C(region x₀ y₀ A B, B) := hq.lift r hr
  let g : C(B, region x₀ y₀ A B) :=
    ⟨regionRightInclusion x₀ y₀ A B, continuous_regionRightInclusion x₀ y₀ A B⟩
  -- Descend the extended contraction jointly in time along the quotient map.
  let K : C(unitInterval × RegionRepresentative A B, region x₀ y₀ A B) :=
    ⟨regionContractionRightRepresentative x₀ y₀ A B hx₀ H,
      continuous_regionContractionRightRepresentative x₀ y₀ A B hx₀ H⟩
  have hK : ∀ t, Function.FactorsThrough (fun z ↦ K (t, z)) q :=
    fun t ↦ regionContractionRightRepresentative_factors
      x₀ y₀ A B hA hB hx₀ hy₀ H t
  obtain ⟨L, hL⟩ := exists_quotientLiftProduct q hq K hK
  have hzero : ∀ z, L (0, z) = ContinuousMap.id (region x₀ y₀ A B) z := by
    intro z
    obtain ⟨w, rfl⟩ := hq.surjective z
    calc
      L (0, q w) = K (0, w) := hL 0 w
      _ = q w := regionContractionRightRepresentative_zero
        x₀ y₀ A B hA hB hx₀ hy₀ H w
      _ = ContinuousMap.id (region x₀ y₀ A B) (q w) := rfl
  have hone : ∀ z, L (1, z) = (g.comp f) z := by
    intro z
    obtain ⟨w, rfl⟩ := hq.surjective z
    have hfw : f (q w) = r w :=
      DFunLike.congr_fun (hq.lift_comp r hr) w
    calc
      L (1, q w) = K (1, w) := hL 1 w
      _ = g (r w) := regionContractionRightRepresentative_one x₀ y₀ A B hx₀ hy₀ H w
      _ = g (f (q w)) := congrArg g hfw.symm
      _ = (g.comp f) (q w) := rfl
  let collapse : ContinuousMap.Homotopy (ContinuousMap.id (region x₀ y₀ A B)) (g.comp f) :=
    { toFun := L
      map_zero_left := hzero
      map_one_left := hone }
  -- The projection is a strict inverse on the stationary right branch.
  have hrightEq : f.comp g = ContinuousMap.id B := by
    apply ContinuousMap.ext
    intro y
    let w : RegionRepresentative A B :=
      ⟨true, ⟨ULift.up y.1, y.2⟩⟩
    have hqw : q w = g y := by
      apply Subtype.ext
      change
        @Quotient.mk' _
            (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))
              ⟨true, ULift.up y.1⟩ = right x₀ y₀ y.1
      exact (right_eq_quotientMap x₀ y₀ y.1).symm
    have hfw : f (q w) = r w :=
      DFunLike.congr_fun (hq.lift_comp r hr) w
    calc
      (f.comp g) y = f (g y) := rfl
      _ = f (q w) := congrArg f hqw.symm
      _ = r w := hfw
      _ = ContinuousMap.id B y := Subtype.ext rfl
  have hright : (f.comp g).Homotopic (ContinuousMap.id B) := by
    rw [hrightEq]
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := ⟨collapse.symm⟩
    right_inv := hright }⟩

/-- Helper for Exercise 59.1: extract the right-factor point carried by a normalized
right representative. -/
private def rightRepresentativePoint
    {X : Type u} {Y : Type v} (A : Set X) (B : Set Y)
    (y : {z : Family X Y true // representativeMem A B ⟨true, z⟩}) : B :=
  ⟨y.1.down, y.2⟩

/-- Helper for Exercise 59.1: extracting the right-factor point is continuous. -/
private lemma continuous_rightRepresentativePoint
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) : Continuous (rightRepresentativePoint A B) := by
  -- Forget the representative proof, lower the universe, and retain membership in `B`.
  exact (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _

/-- Helper for Exercise 59.1: the right-factor contraction, extended by the stationary
left branch, on normalized representatives. -/
private def regionContractionLeftRepresentative
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩}) :
    unitInterval × RegionRepresentative A B → region x₀ y₀ A B :=
  fun z ↦
    match z.2 with
    | ⟨false, x⟩ =>
        ⟨left x₀ y₀ x.1.down, Or.inl ⟨x.1.down, x.2, rfl⟩⟩
    | ⟨true, y⟩ =>
        let yB : B := rightRepresentativePoint A B y
        ⟨right x₀ y₀ (H (z.1, yB)).1,
          Or.inr ⟨(H (z.1, yB)).1, (H (z.1, yB)).2, rfl⟩⟩

/-- Helper for Exercise 59.1: the representative-side left collapse is continuous. -/
private lemma continuous_regionContractionLeftRepresentative
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩}) :
    Continuous (regionContractionLeftRepresentative x₀ y₀ A B hy₀ H) := by
  -- Move the time coordinate past the sigma, then check continuity on the two branches.
  let G : (Σ i, ({z : Family X Y i // representativeMem A B ⟨i, z⟩} × unitInterval)) →
      region x₀ y₀ A B := fun z ↦
    regionContractionLeftRepresentative x₀ y₀ A B hy₀ H (z.2.2, ⟨z.1, z.2.1⟩)
  have hG : Continuous G := by
    apply continuous_sigma
    intro i
    cases i with
    | false =>
        dsimp only [G, regionContractionLeftRepresentative]
        apply Continuous.subtype_mk
        exact (continuous_left x₀ y₀).comp
          ((continuous_uliftDown.comp continuous_subtype_val).comp continuous_fst)
    | true =>
        dsimp only [G, regionContractionLeftRepresentative]
        apply Continuous.subtype_mk
        exact (continuous_right x₀ y₀).comp
          (continuous_subtype_val.comp ((map_continuous H).comp
            (continuous_snd.prodMk
              ((continuous_rightRepresentativePoint A B).comp continuous_fst))))
  have heq : regionContractionLeftRepresentative x₀ y₀ A B hy₀ H =
      G ∘ Homeomorph.sigmaProdDistrib ∘ Prod.swap := by
    funext z
    rfl
  rw [heq]
  exact hG.comp
    ((Homeomorph.sigmaProdDistrib (Y := unitInterval)).continuous.comp continuous_swap)

/-- Helper for Exercise 59.1: the representative-side left collapse starts at the
normalized quotient map. -/
private lemma regionContractionLeftRepresentative_zero
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩})
    (z : RegionRepresentative A B) :
    regionContractionLeftRepresentative x₀ y₀ A B hy₀ H (0, z) =
      regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀ z := by
  -- At time zero the supplied contraction is the identity on the right branch.
  rcases z with ⟨i, z⟩
  cases i with
  | false =>
      rcases z with ⟨⟨x⟩, hx⟩
      apply Subtype.ext
      rw [regionQuotientMap_apply]
      exact left_eq_quotientMap x₀ y₀ x
  | true =>
      rcases z with ⟨⟨y⟩, hy⟩
      apply Subtype.ext
      rw [regionQuotientMap_apply]
      change right x₀ y₀ (H (0, rightRepresentativePoint A B ⟨ULift.up y, hy⟩)).1 = _
      calc
        _ = right x₀ y₀ y := congrArg (fun b : B ↦ right x₀ y₀ b.1)
          (H.map_zero_left (rightRepresentativePoint A B ⟨ULift.up y, hy⟩))
        _ = _ := right_eq_quotientMap x₀ y₀ y

/-- Helper for Exercise 59.1: the representative-side left collapse ends at inclusion
after projection. -/
private lemma regionContractionLeftRepresentative_one
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩})
    (z : RegionRepresentative A B) :
    regionContractionLeftRepresentative x₀ y₀ A B hy₀ H (1, z) =
      regionLeftInclusion x₀ y₀ A B (regionProjectionLeft x₀ A B hx₀ z) := by
  -- At time one the right branch reaches the common basepoint and the left stays fixed.
  rcases z with ⟨i, z⟩
  cases i with
  | false => rfl
  | true =>
      apply Subtype.ext
      change right x₀ y₀ (H (1, rightRepresentativePoint A B z)).1 = left x₀ y₀ x₀
      calc
        _ = right x₀ y₀ y₀ := congrArg (fun b : B ↦ right x₀ y₀ b.1)
          (H.map_one_left (rightRepresentativePoint A B z))
        _ = _ := (left_basepoint_eq_right_basepoint x₀ y₀).symm

/-- Helper for Exercise 59.1: throughout the left collapse, every designated representative
is the common wedge point. -/
private lemma regionContractionLeftRepresentative_designated
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩})
    (t : unitInterval) (z : RegionRepresentative A B) (i : Bool)
    (hz : regionRepresentativeVal A B z = ⟨i, points x₀ y₀ i⟩) :
    regionContractionLeftRepresentative x₀ y₀ A B hy₀ H (t, z) =
      regionLeftInclusion x₀ y₀ A B ⟨x₀, hx₀⟩ := by
  -- The left point is stationary, while the relative condition fixes the selected right point.
  rw [regionRepresentativeVal_apply] at hz
  rcases z with ⟨j, z⟩
  cases j <;> cases i
  · have hz' : (z : Family X Y false) = points x₀ y₀ false := by
      exact sigma_mk_injective (by simpa using hz)
    rcases z with ⟨⟨x⟩, hx⟩
    have hxx : x = x₀ := congrArg ULift.down hz'
    subst x
    rfl
  · cases congrArg Sigma.fst hz
  · cases congrArg Sigma.fst hz
  · have hz' : (z : Family X Y true) = points x₀ y₀ true := by
      exact sigma_mk_injective (by simpa using hz)
    rcases z with ⟨⟨y⟩, hy⟩
    have hyy : y = y₀ := congrArg ULift.down hz'
    subst y
    apply Subtype.ext
    change right x₀ y₀ (H (t, rightRepresentativePoint A B ⟨ULift.up y₀, hy⟩)).1 =
      left x₀ y₀ x₀
    calc
      _ = right x₀ y₀ y₀ := congrArg (fun b : B ↦ right x₀ y₀ b.1)
        (H.eq_fst t (Set.mem_singleton_iff.mpr (Subtype.ext rfl)))
      _ = _ := (left_basepoint_eq_right_basepoint x₀ y₀).symm

/-- Helper for Exercise 59.1: every time slice of the representative left collapse is
constant on normalized quotient fibers. -/
private lemma regionContractionLeftRepresentative_factors
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopyRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩})
    (t : unitInterval) :
    Function.FactorsThrough
      (fun z ↦ regionContractionLeftRepresentative x₀ y₀ A B hy₀ H (t, z))
      (regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀) := by
  -- Use the equal-or-designated fiber normal form with the contraction on the right branch.
  intro z w hzw
  have hq := congrArg Subtype.val hzw
  rw [regionQuotientMap_apply, regionQuotientMap_apply] at hq
  rcases (quotientMap_eq_iff (Family X Y) (points x₀ y₀)
      (regionRepresentativeVal A B z) (regionRepresentativeVal A B w)).mp
      (by simpa only [regionRepresentativeVal_apply] using hq) with h | h
  · exact congrArg
      (fun z ↦ regionContractionLeftRepresentative x₀ y₀ A B hy₀ H (t, z))
      (Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) h)
  · rcases h with ⟨i, j, hi, hj⟩
    exact (regionContractionLeftRepresentative_designated
      x₀ y₀ A B hx₀ hy₀ H t z i hi).trans
        (regionContractionLeftRepresentative_designated
          x₀ y₀ A B hx₀ hy₀ H t w j hj).symm

/-- Helper for Exercise 59.1: contracting the right factor of an open wedge region gives a
homotopy equivalence with its left factor. -/
private lemma region_homotopyEquiv_left
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B)
    (H : ContinuousMap.HomotopicRel
      (ContinuousMap.id B) (ContinuousMap.const B ⟨y₀, hy₀⟩) {⟨y₀, hy₀⟩}) :
    Nonempty (region x₀ y₀ A B ≃ₕ A) := by
  -- Mirror the verified right-collapse construction with the contraction on the right branch.
  obtain ⟨H⟩ := H
  let q : C(RegionRepresentative A B, region x₀ y₀ A B) :=
    ⟨regionQuotientMap x₀ y₀ A B hA hB hx₀ hy₀,
      (regionQuotientMap_isQuotientMap x₀ y₀ A B hA hB hx₀ hy₀).continuous⟩
  have hq : Topology.IsQuotientMap q :=
    regionQuotientMap_isQuotientMap x₀ y₀ A B hA hB hx₀ hy₀
  let r : C(RegionRepresentative A B, A) :=
    ⟨regionProjectionLeft x₀ A B hx₀, continuous_regionProjectionLeft x₀ A B hx₀⟩
  have hr : Function.FactorsThrough r q :=
    regionProjectionLeft_factors x₀ y₀ A B hA hB hx₀ hy₀
  let f : C(region x₀ y₀ A B, A) := hq.lift r hr
  let g : C(A, region x₀ y₀ A B) :=
    ⟨regionLeftInclusion x₀ y₀ A B, continuous_regionLeftInclusion x₀ y₀ A B⟩
  -- Descend the extended contraction jointly in time along the same normalized quotient.
  let K : C(unitInterval × RegionRepresentative A B, region x₀ y₀ A B) :=
    ⟨regionContractionLeftRepresentative x₀ y₀ A B hy₀ H,
      continuous_regionContractionLeftRepresentative x₀ y₀ A B hy₀ H⟩
  have hK : ∀ t, Function.FactorsThrough (fun z ↦ K (t, z)) q :=
    fun t ↦ regionContractionLeftRepresentative_factors
      x₀ y₀ A B hA hB hx₀ hy₀ H t
  obtain ⟨L, hL⟩ := exists_quotientLiftProduct q hq K hK
  have hzero : ∀ z, L (0, z) = ContinuousMap.id (region x₀ y₀ A B) z := by
    intro z
    obtain ⟨w, rfl⟩ := hq.surjective z
    calc
      L (0, q w) = K (0, w) := hL 0 w
      _ = q w := regionContractionLeftRepresentative_zero
        x₀ y₀ A B hA hB hx₀ hy₀ H w
      _ = ContinuousMap.id (region x₀ y₀ A B) (q w) := rfl
  have hone : ∀ z, L (1, z) = (g.comp f) z := by
    intro z
    obtain ⟨w, rfl⟩ := hq.surjective z
    have hfw : f (q w) = r w :=
      DFunLike.congr_fun (hq.lift_comp r hr) w
    calc
      L (1, q w) = K (1, w) := hL 1 w
      _ = g (r w) := regionContractionLeftRepresentative_one x₀ y₀ A B hx₀ hy₀ H w
      _ = g (f (q w)) := congrArg g hfw.symm
      _ = (g.comp f) (q w) := rfl
  let collapse : ContinuousMap.Homotopy (ContinuousMap.id (region x₀ y₀ A B)) (g.comp f) :=
    { toFun := L
      map_zero_left := hzero
      map_one_left := hone }
  -- The projection is a strict inverse on the stationary left branch.
  have hrightEq : f.comp g = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro x
    let w : RegionRepresentative A B :=
      ⟨false, ⟨ULift.up x.1, x.2⟩⟩
    have hqw : q w = g x := by
      apply Subtype.ext
      change
        @Quotient.mk' _
            (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀))
              ⟨false, ULift.up x.1⟩ = left x₀ y₀ x.1
      exact (left_eq_quotientMap x₀ y₀ x.1).symm
    have hfw : f (q w) = r w :=
      DFunLike.congr_fun (hq.lift_comp r hr) w
    calc
      (f.comp g) x = f (g x) := rfl
      _ = f (q w) := congrArg f hqw.symm
      _ = r w := hfw
      _ = ContinuousMap.id A x := Subtype.ext rfl
  have hright : (f.comp g).Homotopic (ContinuousMap.id A) := by
    rw [hrightEq]
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := ⟨collapse.symm⟩
    right_inv := hright }⟩

/-- Helper for Exercise 59.1: the two complementary wedge regions cover the entire wedge. -/
private lemma region_compl_cover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    region x₀ y₀ A Set.univ ∪ region x₀ y₀ Set.univ B = Set.univ := by
  -- Check the cover on an arbitrary quotient representative.
  ext q
  induction q using Quotient.inductionOn' with
  | _ z =>
      cases z with
      | mk i z =>
          simp only [Set.mem_union, Set.mem_univ, iff_true]
          cases i with
          | false =>
              change
                (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨false, z⟩ ∈
                    region x₀ y₀ A Set.univ) ∨
                  (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨false, z⟩ ∈
                    region x₀ y₀ Set.univ B)
              right
              rw [quotientMap_mem_region_iff x₀ y₀ Set.univ B (Set.mem_univ x₀) hy₀]
              exact Set.mem_univ z.down
          | true =>
              change
                (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨true, z⟩ ∈
                    region x₀ y₀ A Set.univ) ∨
                  (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨true, z⟩ ∈
                    region x₀ y₀ Set.univ B)
              left
              rw [quotientMap_mem_region_iff x₀ y₀ A Set.univ hx₀ (Set.mem_univ y₀)]
              exact Set.mem_univ z.down

/-- Helper for Exercise 59.1: the intersection of the two complementary wedge regions is
the region formed from both smaller factor subsets. -/
private lemma region_compl_inter
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ B) :
    region x₀ y₀ A Set.univ ∩ region x₀ y₀ Set.univ B = region x₀ y₀ A B := by
  -- Check the intersection identity on an arbitrary quotient representative.
  ext q
  induction q using Quotient.inductionOn' with
  | _ z =>
      cases z with
      | mk i z =>
          simp only [Set.mem_inter_iff]
          cases i with
          | false =>
              change
                ((@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨false, z⟩ ∈
                    region x₀ y₀ A Set.univ) ∧
                  (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨false, z⟩ ∈
                    region x₀ y₀ Set.univ B)) ↔
                  (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨false, z⟩ ∈
                    region x₀ y₀ A B)
              rw [quotientMap_mem_region_iff x₀ y₀ A Set.univ hx₀ (Set.mem_univ y₀),
                quotientMap_mem_region_iff x₀ y₀ Set.univ B (Set.mem_univ x₀) hy₀,
                quotientMap_mem_region_iff x₀ y₀ A B hx₀ hy₀]
              simp only [representativeMem, Set.mem_univ, and_true]
          | true =>
              change
                ((@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨true, z⟩ ∈
                    region x₀ y₀ A Set.univ) ∧
                  (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨true, z⟩ ∈
                    region x₀ y₀ Set.univ B)) ↔
                  (@Quotient.mk' _
                    (IndexedPointedWedge.setoid (Family X Y) (points x₀ y₀)) ⟨true, z⟩ ∈
                    region x₀ y₀ A B)
              rw [quotientMap_mem_region_iff x₀ y₀ A Set.univ hx₀ (Set.mem_univ y₀),
                quotientMap_mem_region_iff x₀ y₀ Set.univ B (Set.mem_univ x₀) hy₀,
                quotientMap_mem_region_iff x₀ y₀ A B hx₀ hy₀]
              simp only [representativeMem, Set.mem_univ, true_and]

end Topology.PointedWedge

/-- Helper for Exercise 59.1: stereographic projection identifies a punctured standard sphere
with Euclidean space. -/
private def standardSpherePuncturedHomeomorph (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  ((Homeomorph.setCongr (stereographic'_source (n := 2) p).symm).trans
    (stereographic' 2 p).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target (n := 2) p)).trans
        (Homeomorph.Set.univ _))

/-- Helper for Exercise 59.1: affine interpolation in homeomorphic vector-space coordinates. -/
private def affineContraction
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : unitInterval × X → X :=
  fun z ↦ e.symm (((1 - (z.1 : ℝ)) • e z.2) + ((z.1 : ℝ) • e x))

/-- Helper for Exercise 59.1: affine interpolation in homeomorphic vector-space coordinates
is continuous. -/
private lemma continuous_affineContraction
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) : Continuous (affineContraction e x) := by
  -- All coordinate operations in the affine formula are continuous.
  unfold affineContraction
  fun_prop

/-- Helper for Exercise 59.1: affine interpolation starts at the identity. -/
private lemma affineContraction_zero
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x y : X) :
    affineContraction e x (0, y) = ContinuousMap.id X y := by
  -- At time zero the original coordinate has coefficient one.
  simp [affineContraction]

/-- Helper for Exercise 59.1: affine interpolation ends at the chosen point. -/
private lemma affineContraction_one
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x y : X) :
    affineContraction e x (1, y) = ContinuousMap.const X x y := by
  -- At time one only the chosen center remains.
  simp [affineContraction]

/-- Helper for Exercise 59.1: affine interpolation fixes its chosen point. -/
private lemma affineContraction_fixed
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) (t : unitInterval) {y : X} (hy : y ∈ ({x} : Set X)) :
    affineContraction e x (t, y) = ContinuousMap.id X y := by
  -- Substitute the singleton point and combine the complementary coefficients.
  rw [Set.mem_singleton_iff.mp hy]
  simp only [affineContraction, ContinuousMap.id_apply]
  rw [← add_smul]
  simp

/-- Helper for Exercise 59.1: a space homeomorphic to a real normed vector space contracts
to any chosen point while fixing that point. -/
private def affineContractionRel
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : X ≃ₜ E) (x : X) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X) (ContinuousMap.const X x) {x} :=
  { toFun := affineContraction e x
    continuous_toFun := continuous_affineContraction e x
    map_zero_left := affineContraction_zero e x
    map_one_left := affineContraction_one e x
    prop' := affineContraction_fixed e x }

/-- Exercise 59.1: the fundamental group of two copies of the standard two-sphere joined
at their selected points is trivial. -/
instance instSubsingletonFundamentalGroupTwoSphereWedge
    (x₀ y₀ : StandardSphere 2) :
    Subsingleton
      (FundamentalGroup
        (Topology.PointedWedge (StandardSphere 2) x₀ (StandardSphere 2) y₀)
        (Topology.PointedWedge.basepoint x₀ y₀)) := by
  -- Delete the antipode of each selected point to obtain based contractible chart domains.
  have hx₀ : x₀ ∈ ({-x₀}ᶜ : Set (StandardSphere 2)) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ x₀
  have hy₀ : y₀ ∈ ({-y₀}ᶜ : Set (StandardSphere 2)) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ y₀
  have hcontractX : ContinuousMap.HomotopicRel
      (ContinuousMap.id ({-x₀}ᶜ : Set (StandardSphere 2)))
      (ContinuousMap.const ({-x₀}ᶜ : Set (StandardSphere 2)) ⟨x₀, hx₀⟩)
      {⟨x₀, hx₀⟩} := by
    -- Stereographic coordinates turn the punctured sphere into a vector space.
    exact ⟨affineContractionRel (standardSpherePuncturedHomeomorph (-x₀)) ⟨x₀, hx₀⟩⟩
  have hcontractY : ContinuousMap.HomotopicRel
      (ContinuousMap.id ({-y₀}ᶜ : Set (StandardSphere 2)))
      (ContinuousMap.const ({-y₀}ᶜ : Set (StandardSphere 2)) ⟨y₀, hy₀⟩)
      {⟨y₀, hy₀⟩} := by
    -- Use the identical affine contraction in the second stereographic chart.
    exact ⟨affineContractionRel (standardSpherePuncturedHomeomorph (-y₀)) ⟨y₀, hy₀⟩⟩
  let U := Topology.PointedWedge.region x₀ y₀ ({-x₀}ᶜ : Set (StandardSphere 2)) Set.univ
  let V := Topology.PointedWedge.region x₀ y₀ Set.univ ({-y₀}ᶜ : Set (StandardSphere 2))
  have hUopen : IsOpen U := by
    -- Openness is checked on the two summands of the quotient presentation.
    exact Topology.PointedWedge.isOpen_region x₀ y₀ _ _ isOpen_compl_singleton
      isOpen_univ hx₀ (Set.mem_univ y₀)
  have hVopen : IsOpen V := by
    -- The second region is the mirrored open chart.
    exact Topology.PointedWedge.isOpen_region x₀ y₀ _ _ isOpen_univ
      isOpen_compl_singleton (Set.mem_univ x₀) hy₀
  have hcover : U ∪ V = Set.univ := by
    -- Every representative lies in the region whose corresponding factor is unrestricted.
    exact Topology.PointedWedge.region_compl_cover x₀ y₀ _ _ hx₀ hy₀
  have hUsc : IsSimplyConnected U := by
    -- Collapse the punctured left factor and retain the simply connected right sphere.
    obtain ⟨eU⟩ := Topology.PointedWedge.region_homotopyEquiv_right
      x₀ y₀ ({-x₀}ᶜ : Set (StandardSphere 2)) Set.univ
      isOpen_compl_singleton isOpen_univ hx₀ (Set.mem_univ y₀) hcontractX
    exact (eU.trans (Homeomorph.Set.univ _).toHomotopyEquiv).simplyConnectedSpace
  have hVsc : IsSimplyConnected V := by
    -- Collapse the punctured right factor and retain the simply connected left sphere.
    obtain ⟨eV⟩ := Topology.PointedWedge.region_homotopyEquiv_left
      x₀ y₀ Set.univ ({-y₀}ᶜ : Set (StandardSphere 2))
      isOpen_univ isOpen_compl_singleton (Set.mem_univ x₀) hy₀ hcontractY
    exact (eV.trans (Homeomorph.Set.univ _).toHomotopyEquiv).simplyConnectedSpace
  have hXpath : IsPathConnected ({-x₀}ᶜ : Set (StandardSphere 2)) := by
    -- The first punctured sphere is homeomorphic to Euclidean two-space.
    letI : SimplyConnectedSpace ({-x₀}ᶜ : Set (StandardSphere 2)) :=
      (standardSpherePuncturedHomeomorph (-x₀)).toHomotopyEquiv.simplyConnectedSpace
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hYpath : IsPathConnected ({-y₀}ᶜ : Set (StandardSphere 2)) := by
    -- The same argument handles the second punctured sphere.
    letI : SimplyConnectedSpace ({-y₀}ᶜ : Set (StandardSphere 2)) :=
      (standardSpherePuncturedHomeomorph (-y₀)).toHomotopyEquiv.simplyConnectedSpace
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hleftPath : IsPathConnected
      (Topology.PointedWedge.left x₀ y₀ '' ({-x₀}ᶜ : Set (StandardSphere 2))) := by
    -- Continuous inclusion preserves path connectedness of the left chart.
    exact hXpath.image (Topology.PointedWedge.continuous_left x₀ y₀)
  have hrightPath : IsPathConnected
      (Topology.PointedWedge.right x₀ y₀ '' ({-y₀}ᶜ : Set (StandardSphere 2))) := by
    -- Continuous inclusion preserves path connectedness of the right chart.
    exact hYpath.image (Topology.PointedWedge.continuous_right x₀ y₀)
  have himagesMeet :
      ((Topology.PointedWedge.left x₀ y₀ '' ({-x₀}ᶜ : Set (StandardSphere 2))) ∩
        (Topology.PointedWedge.right x₀ y₀ '' ({-y₀}ᶜ : Set (StandardSphere 2)))).Nonempty := by
    -- Both factor images contain the common wedge point.
    refine ⟨Topology.PointedWedge.left x₀ y₀ x₀, ?_, ?_⟩
    · exact ⟨x₀, hx₀, rfl⟩
    · exact ⟨y₀, hy₀, (Topology.PointedWedge.left_basepoint_eq_right_basepoint x₀ y₀).symm⟩
  have hUVpath : IsPathConnected (U ∩ V) := by
    -- The intersection is the union of the two punctured factor images meeting at the basepoint.
    rw [Topology.PointedWedge.region_compl_inter x₀ y₀ _ _ hx₀ hy₀]
    exact hleftPath.union hrightPath himagesMeet
  -- Van Kampen on the verified open cover makes the whole wedge simply connected.
  letI : SimplyConnectedSpace
      (Topology.PointedWedge (StandardSphere 2) x₀ (StandardSphere 2) y₀) :=
    SimplyConnectedSpace.of_isOpen_cover U V hUopen hVopen hcover hUVpath hUsc hVsc
  infer_instance
