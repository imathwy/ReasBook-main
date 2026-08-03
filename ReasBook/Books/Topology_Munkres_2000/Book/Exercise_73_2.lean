module

public import Topology_Munkres_2000.Book.Exercise_73_2.CWComplex
import Topology_Munkres_2000.Book.Exercise_73_2.RelatorAttachment
import all Topology_Munkres_2000.Book.Exercise_73_2.CWComplex
import all Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
public import Topology_Munkres_2000.Book.Exercise_66_1.LoopQuotient
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_71_3
public import Topology_Munkres_2000.Book.Theorem_72_1
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.FinitelyPresentedGroup

public section

universe u

/-- Helper for Exercise 73.2: the equivalence closure defining an indexed pointed wedge
identifies exactly equal representatives or pairs of designated representatives. -/
private lemma indexedPointedWedge_eqvGen_iff
    {I : Type*} (X : I → Type*) (p : ∀ i, X i) (x y : Σ i, X i) :
    Relation.EqvGen (Topology.IndexedPointedWedge.Related X p) x y ↔
      x = y ∨ (x.2 = p x.1 ∧ y.2 = p y.1) := by
  constructor
  · intro h
    -- The equality-or-designated normal form is stable under the four constructors
    -- of the generated equivalence relation.
    induction h with
    | rel x y hxy =>
        unfold Topology.IndexedPointedWedge.Related at hxy
        rcases hxy with ⟨i, j, rfl, rfl⟩
        exact Or.inr ⟨rfl, rfl⟩
    | refl x =>
        exact Or.inl rfl
    | symm x y _ ih =>
        rcases ih with hxy | hxy
        · exact Or.inl hxy.symm
        · exact Or.inr ⟨hxy.2, hxy.1⟩
    | trans x y z _ _ hxy hyz =>
        rcases hxy with hxy | hxy
        · subst y
          exact hyz
        · rcases hyz with hyz | hyz
          · subst z
            exact Or.inr hxy
          · exact Or.inr ⟨hxy.1, hyz.2⟩
  · intro h
    rcases h with rfl | h
    · exact Relation.EqvGen.refl x
    · -- Any two designated representatives are related in one generating step.
      apply Relation.EqvGen.rel
      unfold Topology.IndexedPointedWedge.Related
      exact ⟨x.1, y.1, Sigma.ext rfl (heq_of_eq h.1),
        Sigma.ext rfl (heq_of_eq h.2)⟩

/-- Helper for Exercise 73.2: the image of a circle factor in the canonical
one-skeleton. -/
private def oneSkeletonCircle (n : ℕ) (i : Fin n) :
    Set (TwoDimensionalCWComplex.OneSkeleton n) :=
  Set.range
    (Topology.IndexedPointedWedge.inclusion
      (TwoDimensionalCWComplex.CircleFamily n)
      (TwoDimensionalCWComplex.circlePoints n) (some i))

/-- Helper for Exercise 73.2: every circle factor embeds in the canonical one-skeleton. -/
private lemma oneSkeletonCircleInclusion_isClosedEmbedding (n : ℕ) (i : Fin n) :
    Topology.IsClosedEmbedding
      (Topology.IndexedPointedWedge.inclusion
        (TwoDimensionalCWComplex.CircleFamily n)
        (TwoDimensionalCWComplex.circlePoints n) (some i)) := by
  -- Compactness of the circle and Hausdorffness of the one-skeleton reduce the
  -- claim to continuity and injectivity of the quotient inclusion.
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_quotient_mk'.comp continuous_sigmaMk
  · intro x y hxy
    unfold Topology.IndexedPointedWedge.inclusion
      Topology.IndexedPointedWedge.quotientMap at hxy
    have hrel := (indexedPointedWedge_eqvGen_iff
      (TwoDimensionalCWComplex.CircleFamily n)
      (TwoDimensionalCWComplex.circlePoints n) ⟨some i, x⟩ ⟨some i, y⟩).mp
        (Quotient.exact hxy)
    rcases hrel with hrel | hrel
    · exact eq_of_heq (Sigma.mk.inj_iff.mp hrel).2
    · exact hrel.1.trans hrel.2.symm
  · intro C hC
    -- A closed subset of a compact circle has compact, hence closed, image.
    exact (hC.isCompact.image
      (continuous_quotient_mk'.comp continuous_sigmaMk)).isClosed

/-- Helper for Exercise 73.2: when `n > 0`, the circle-factor images exhibit the
canonical one-skeleton as a finite wedge of `n` circles. -/
private theorem oneSkeletonIsFiniteWedgeOfCircles {n : ℕ} (hn : 0 < n) :
    Topology.IsFiniteWedgeOfCircles (oneSkeletonCircle n)
      (TwoDimensionalCWComplex.oneSkeletonBasepoint n) := by
  apply Topology.IsFiniteWedgeOfCircles.of
  · -- Every quotient representative is either on a circle factor or is the
    -- extra `PUnit` representative of the common wedge point.
    ext q
    constructor
    · intro _
      exact Set.mem_univ q
    · intro _
      induction q using Quotient.inductionOn with
      | _ x =>
          rcases x with ⟨_ | i, x⟩
          · let i₀ : Fin n := ⟨0, hn⟩
            apply Set.mem_iUnion.mpr
            refine ⟨i₀, 1, ?_⟩
            cases x
            simpa only [Topology.IndexedPointedWedge.point,
              Topology.IndexedPointedWedge.inclusion,
              Topology.IndexedPointedWedge.quotientMap,
              TwoDimensionalCWComplex.circlePoints] using
              (Topology.IndexedPointedWedge.point_eq
                (TwoDimensionalCWComplex.CircleFamily n)
                (TwoDimensionalCWComplex.circlePoints n) (some i₀) none)
          · apply Set.mem_iUnion.mpr
            refine ⟨i, x, ?_⟩
            unfold Topology.IndexedPointedWedge.inclusion
              Topology.IndexedPointedWedge.quotientMap
            rfl
  · intro i
    -- The embedding homeomorphism identifies each range subtype with `Circle`.
    exact ⟨(oneSkeletonCircleInclusion_isClosedEmbedding n i).isEmbedding.toHomeomorph.symm⟩
  · intro i j hij
    ext q
    constructor
    · rintro ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
      unfold Topology.IndexedPointedWedge.inclusion
        Topology.IndexedPointedWedge.quotientMap at hxy
      have hrel := (indexedPointedWedge_eqvGen_iff
        (TwoDimensionalCWComplex.CircleFamily n)
        (TwoDimensionalCWComplex.circlePoints n) ⟨some i, x⟩ ⟨some j, y⟩).mp
          (Quotient.exact hxy.symm)
      rcases hrel with hrel | hrel
      · exact (hij (Option.some.inj (Sigma.mk.inj_iff.mp hrel).1)).elim
      · rw [Set.mem_singleton_iff]
        calc
          Topology.IndexedPointedWedge.inclusion
                (TwoDimensionalCWComplex.CircleFamily n)
                (TwoDimensionalCWComplex.circlePoints n) (some i) x =
              Topology.IndexedPointedWedge.point
                (TwoDimensionalCWComplex.CircleFamily n)
                (TwoDimensionalCWComplex.circlePoints n) (some i) :=
            congrArg _ hrel.1
          _ = TwoDimensionalCWComplex.oneSkeletonBasepoint n :=
            Topology.IndexedPointedWedge.point_eq
              (TwoDimensionalCWComplex.CircleFamily n)
              (TwoDimensionalCWComplex.circlePoints n) (some i) none
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst q
      constructor
      · refine ⟨1, ?_⟩
        simpa only [Topology.IndexedPointedWedge.point,
          TwoDimensionalCWComplex.circlePoints,
          TwoDimensionalCWComplex.oneSkeletonBasepoint] using
          (Topology.IndexedPointedWedge.point_eq
            (TwoDimensionalCWComplex.CircleFamily n)
            (TwoDimensionalCWComplex.circlePoints n) (some i) none)
      · refine ⟨1, ?_⟩
        simpa only [Topology.IndexedPointedWedge.point,
          TwoDimensionalCWComplex.circlePoints,
          TwoDimensionalCWComplex.oneSkeletonBasepoint] using
          (Topology.IndexedPointedWedge.point_eq
            (TwoDimensionalCWComplex.CircleFamily n)
            (TwoDimensionalCWComplex.circlePoints n) (some j) none)

/-- Helper for Exercise 73.2: the rank-zero canonical one-skeleton has only one point. -/
private theorem oneSkeletonZero_subsingleton :
    Subsingleton (TwoDimensionalCWComplex.OneSkeleton 0) := by
  constructor
  intro q r
  -- Both quotient representatives necessarily lie in the sole `PUnit` factor.
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          rcases x with ⟨_ | i, x⟩
          · rcases y with ⟨_ | j, y⟩
            · cases x
              cases y
              rfl
            · exact Fin.elim0 j
          · exact Fin.elim0 i

/-- Helper for Exercise 73.2: every circle component of a finite wedge has cyclic
fundamental group. -/
private theorem circleWedgeComponent_isCyclic
    {J : Type*} {X : Type*} [TopologicalSpace X]
    (S : J → Set X) (p : X) [Topology.IsWedgeOfCircles S p] (i : J) :
    IsCyclic
      (FundamentalGroup (S i) ⟨p, Topology.IsWedgeOfCircles.mem_basepoint i⟩) := by
  -- Circle coordinates, followed by a basepoint-change path, identify the
  -- component group with the cyclic group `Multiplicative ℤ`.
  obtain ⟨e⟩ := Topology.IsWedgeOfCircles.homeomorphic_circle (S := S) (p := p) i
  let coordinates :=
    (e.fundamentalGroupMulEquiv
      ⟨p, Topology.IsWedgeOfCircles.mem_basepoint i⟩).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        (e ⟨p, Topology.IsWedgeOfCircles.mem_basepoint i⟩) 1).trans
        Circle.fundamentalGroupEquivInt)
  exact coordinates.isCyclic.mpr inferInstance

/-- Helper for Exercise 73.2: the fundamental group of the canonical one-skeleton is free on
its `n` circle factors. -/
private theorem oneSkeletonFreeBasis (n : ℕ) :
    Nonempty
      (FreeGroupBasis (Fin n)
        (FundamentalGroup (TwoDimensionalCWComplex.OneSkeleton n)
          (TwoDimensionalCWComplex.oneSkeletonBasepoint n))) := by
  classical
  by_cases hn : n = 0
  · subst n
    -- At rank zero both the one-skeleton group and the empty free group are unique.
    letI : Subsingleton (TwoDimensionalCWComplex.OneSkeleton 0) :=
      oneSkeletonZero_subsingleton
    letI : Nonempty (TwoDimensionalCWComplex.OneSkeleton 0) :=
      ⟨TwoDimensionalCWComplex.oneSkeletonBasepoint 0⟩
    letI : ContractibleSpace (TwoDimensionalCWComplex.OneSkeleton 0) := inferInstance
    letI : SimplyConnectedSpace (TwoDimensionalCWComplex.OneSkeleton 0) := inferInstance
    letI : Unique
        (FundamentalGroup (TwoDimensionalCWComplex.OneSkeleton 0)
          (TwoDimensionalCWComplex.oneSkeletonBasepoint 0)) :=
      { default := 1
        uniq := fun _ ↦ Subsingleton.elim _ _ }
    exact ⟨FreeGroupBasis.ofRepr MulEquiv.ofUnique⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    letI : Topology.IsFiniteWedgeOfCircles (oneSkeletonCircle n)
        (TwoDimensionalCWComplex.oneSkeletonBasepoint n) :=
      oneSkeletonIsFiniteWedgeOfCircles hnpos
    letI : Topology.IsWedgeOfCircles (oneSkeletonCircle n)
        (TwoDimensionalCWComplex.oneSkeletonBasepoint n) :=
      Topology.IsWedgeOfCircles.ofFinite inferInstance
    -- Choose a cyclic generator in each component and then a representing loop.
    choose g hg using fun i : Fin n ↦
      isCyclic_iff_exists_zpowers_eq_top.mp
        (circleWedgeComponent_isCyclic (oneSkeletonCircle n)
          (TwoDimensionalCWComplex.oneSkeletonBasepoint n) i)
    choose f hf using fun i : Fin n ↦ Quotient.exists_rep (g i)
    have hfgenerates : ∀ i, Subgroup.zpowers
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (f i))) = ⊤ := by
      intro i
      have hclass : FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (f i)) = g i := hf i
      rw [hclass]
      exact hg i
    obtain ⟨b, _⟩ := fundamentalGroup_freeBasis_of_circleWedge
      (oneSkeletonCircle n) (TwoDimensionalCWComplex.oneSkeletonBasepoint n) f
      hfgenerates
    exact ⟨b⟩

/-- Helper for Exercise 73.2: adjoining one normally generating element after a surjection
adds that element to the normal generators of the composite kernel. -/
private lemma ker_comp_eq_normalClosure_union_singleton
    {F H K : Type*} [Group F] [Group H] [MulOneClass K]
    (f : F →* H) (g : H →* K) (hf : Function.Surjective f) (x : F)
    (hg : g.ker = Subgroup.normalClosure ({f x} : Set H)) :
    (g.comp f).ker = Subgroup.normalClosure ((f.ker : Set F) ∪ {x}) := by
  -- Pull the composite kernel back along `f`, then transport normal closure through the
  -- surjection and combine it with the already existing kernel.
  rw [← MonoidHom.comap_ker, hg, ← Set.image_singleton,
    ← Subgroup.map_normalClosure {x} f hf, Subgroup.comap_map_eq,
    Subgroup.normalClosure_union, Subgroup.normalClosure_eq_self, sup_comm]

/-- Helper for Exercise 73.2: the canonical inclusion of the one-skeleton into a
two-dimensional CW complex. -/
private noncomputable def oneSkeletonInclusion {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m) :
    C(TwoDimensionalCWComplex.OneSkeleton n, TwoDimensionalCWComplex.Space f) :=
  -- Reuse the canonical owner construction used by the append comparison.
  TwoDimensionalCWComplex.skeletonInclusion f

/-- Helper for Exercise 73.2: the one-skeleton inclusion preserves the canonical
basepoint. -/
private lemma oneSkeletonInclusion_basepoint {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m) :
    oneSkeletonInclusion f (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
      TwoDimensionalCWComplex.basepoint f := by
  -- Both sides are the same canonical `includeY` value.
  unfold oneSkeletonInclusion
  rw [TwoDimensionalCWComplex.skeletonInclusion_apply,
    ← TwoDimensionalCWComplex.basepoint_eq_includeY]

/-- Helper for Exercise 73.2: the homomorphism on fundamental groups induced by the
canonical one-skeleton inclusion. -/
private noncomputable def oneSkeletonFundamentalGroupMap {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m) :
    FundamentalGroup (TwoDimensionalCWComplex.OneSkeleton n)
        (TwoDimensionalCWComplex.oneSkeletonBasepoint n) →*
      FundamentalGroup (TwoDimensionalCWComplex.Space f)
        (TwoDimensionalCWComplex.basepoint f) :=
  -- Use the named basepoint bridge so the definition remains proof-free.
  FundamentalGroup.mapOfEq (oneSkeletonInclusion f)
    (oneSkeletonInclusion_basepoint f)

/-- Helper for Exercise 73.2: the attaching map with no two-cells. -/
private noncomputable def emptyAttachingMap (n : ℕ) :
    TwoDimensionalCWComplex.AttachingMap n 0 :=
  -- The boundary is empty, so the constant map is its unique attaching datum.
  ContinuousMap.const _ (TwoDimensionalCWComplex.oneSkeletonBasepoint n)

/-- Helper for Exercise 73.2: every map out of the empty family of closed cells is
continuous. -/
private lemma continuous_closedCellsZeroElim {Z : Type*} [TopologicalSpace Z] :
    Continuous (fun x : TwoDimensionalCWComplex.ClosedCells 0 ↦
      (Fin.elim0 x.1 : Z)) := by
  rw [continuous_def]
  intro s _
  -- The preimage is empty because a closed cell would carry an index in `Fin 0`.
  have hempty : (fun x : TwoDimensionalCWComplex.ClosedCells 0 ↦
      (Fin.elim0 x.1 : Z)) ⁻¹' s = ∅ := by
    ext x
    exact Fin.elim0 x.1
  rw [hempty]
  exact isOpen_empty

/-- Helper for Exercise 73.2: the unique map from the empty family of closed cells
to the one-skeleton. -/
private noncomputable def emptyCellsProjection (n : ℕ) :
    C(TwoDimensionalCWComplex.ClosedCells 0,
      TwoDimensionalCWComplex.OneSkeleton n) :=
  -- Its continuity is isolated in `continuous_closedCellsZeroElim`.
  ⟨fun x ↦ Fin.elim0 x.1, continuous_closedCellsZeroElim⟩

/-- Helper for Exercise 73.2: the empty-cell projection is compatible with the
empty attaching map. -/
private lemma emptyCellsProjection_agrees (n : ℕ)
    (a : TwoDimensionalCWComplex.boundary 0) :
    emptyCellsProjection n a =
      ContinuousMap.id _ (emptyAttachingMap n a) := by
  -- A boundary point would contain an impossible index in `Fin 0`.
  exact Fin.elim0 a.1.1

/-- Helper for Exercise 73.2: forgetting the vacuous cell summand retracts the
zero-cell adjunction space onto its one-skeleton. -/
private noncomputable def emptyAttachingSpaceProjection (n : ℕ) :
    C(TwoDimensionalCWComplex.Space (emptyAttachingMap n),
      TwoDimensionalCWComplex.OneSkeleton n) :=
  -- Descend the empty left map and the identity right map through the quotient.
  ⟨AdjunctionSpace.lift (TwoDimensionalCWComplex.boundary 0) (emptyAttachingMap n)
      (emptyCellsProjection n) (ContinuousMap.id _)
      (emptyCellsProjection_agrees n),
    AdjunctionSpace.continuous_lift (TwoDimensionalCWComplex.boundary 0)
      (emptyAttachingMap n) (emptyCellsProjection n) (ContinuousMap.id _)
      (emptyCellsProjection_agrees n)⟩

/-- Helper for Exercise 73.2: projection after inclusion is the identity for the
zero-cell adjunction space. -/
private lemma emptyAttachingSpaceProjection_includeY (n : ℕ)
    (x : TwoDimensionalCWComplex.OneSkeleton n) :
    emptyAttachingSpaceProjection n
        (AdjunctionSpace.includeY (TwoDimensionalCWComplex.boundary 0)
          (emptyAttachingMap n) x) = x := by
  -- Compute the adjunction-space lift on the right summand.
  exact AdjunctionSpace.lift_includeY (TwoDimensionalCWComplex.boundary 0)
    (emptyAttachingMap n) (emptyCellsProjection n) (ContinuousMap.id _)
    (emptyCellsProjection_agrees n) x

/-- Helper for Exercise 73.2: inclusion after projection is the identity for the
zero-cell adjunction space. -/
private lemma includeY_emptyAttachingSpaceProjection (n : ℕ)
    (q : TwoDimensionalCWComplex.Space (emptyAttachingMap n)) :
    AdjunctionSpace.includeY (TwoDimensionalCWComplex.boundary 0)
        (emptyAttachingMap n) (emptyAttachingSpaceProjection n q) = q := by
  -- Every quotient point is represented by one summand; the cell case is impossible.
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      (TwoDimensionalCWComplex.boundary 0) (emptyAttachingMap n) q with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact Fin.elim0 x.1
  · rw [emptyAttachingSpaceProjection_includeY]

/-- Helper for Exercise 73.2: attaching no two-cells leaves the one-skeleton
homeomorphic to the resulting adjunction space. -/
private noncomputable def emptyAttachingSpaceHomeomorph (n : ℕ) :
    TwoDimensionalCWComplex.OneSkeleton n ≃ₜ
      TwoDimensionalCWComplex.Space (emptyAttachingMap n) :=
  -- Package the two explicit inverse laws and the already bundled continuity facts.
  Homeomorph.mk
    (Equiv.mk
      (AdjunctionSpace.includeY (TwoDimensionalCWComplex.boundary 0)
        (emptyAttachingMap n))
      (emptyAttachingSpaceProjection n)
      (emptyAttachingSpaceProjection_includeY n)
      (includeY_emptyAttachingSpaceProjection n))
    (AdjunctionSpace.continuous_includeY (TwoDimensionalCWComplex.boundary 0)
      (emptyAttachingMap n))
    (emptyAttachingSpaceProjection n).continuous

/-- Helper for Exercise 73.2: the append homeomorphism carries the flat canonical
basepoint to the canonical basepoint of the successive one-cell attachment. -/
private lemma appendHomeomorph_basepoint {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m)
    (g : C(StandardSphere.boundary 1,
      TwoDimensionalCWComplex.OneSkeleton n)) :
    TwoDimensionalCWComplex.appendHomeomorph f g
        (TwoDimensionalCWComplex.basepoint
          (TwoDimensionalCWComplex.appendAttachingMap f g)) =
      AdjunctionSpace.includeY (StandardSphere.boundary 1)
        ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
        (TwoDimensionalCWComplex.basepoint f) := by
  -- Compute the flat basepoint through the one-skeleton compatibility theorem.
  rw [TwoDimensionalCWComplex.basepoint_eq_includeY,
    TwoDimensionalCWComplex.appendHomeomorph_includeY,
    TwoDimensionalCWComplex.basepoint_eq_includeY]

/-- Helper for Exercise 73.2: the map on fundamental groups induced by the
append homeomorphism, with the canonical basepoints. -/
private noncomputable def appendHomeomorphFundamentalGroupMap {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m)
    (g : C(StandardSphere.boundary 1,
      TwoDimensionalCWComplex.OneSkeleton n)) :
    FundamentalGroup
        (TwoDimensionalCWComplex.Space
          (TwoDimensionalCWComplex.appendAttachingMap f g))
        (TwoDimensionalCWComplex.basepoint
          (TwoDimensionalCWComplex.appendAttachingMap f g)) →*
      FundamentalGroup
        (TwoDimensionalCWComplex.successiveSpace f g)
        (AdjunctionSpace.includeY (StandardSphere.boundary 1)
          ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
          (TwoDimensionalCWComplex.basepoint f)) :=
  FundamentalGroup.mapOfEq
    (TwoDimensionalCWComplex.appendHomeomorph f g : C(_, _))
    (appendHomeomorph_basepoint f g)

/-- Helper for Exercise 73.2: the append homeomorphism identifies the two
continuous composites from the fixed one-skeleton. -/
private lemma appendHomeomorph_oneSkeletonInclusion {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m)
    (g : C(StandardSphere.boundary 1,
      TwoDimensionalCWComplex.OneSkeleton n)) :
    (TwoDimensionalCWComplex.appendHomeomorph f g : C(_, _)).comp
        (oneSkeletonInclusion
          (TwoDimensionalCWComplex.appendAttachingMap f g)) =
      (AdjunctionSpace.twoCellInclusion
        ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)).comp
        (oneSkeletonInclusion f) := by
  -- Both composites send a skeleton point through the two canonical inclusions.
  apply ContinuousMap.ext
  intro y
  unfold oneSkeletonInclusion
  simp only [ContinuousMap.comp_apply,
    TwoDimensionalCWComplex.skeletonInclusion_apply,
    AdjunctionSpace.twoCellInclusion_apply]
  exact TwoDimensionalCWComplex.appendHomeomorph_includeY f g y

/-- Helper for Exercise 73.2: the induced append equivalence commutes with the
canonical one-skeleton maps on fundamental groups. -/
private lemma appendHomeomorph_comp_oneSkeletonFundamentalGroupMap {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m)
    (g : C(StandardSphere.boundary 1,
      TwoDimensionalCWComplex.OneSkeleton n)) :
    (appendHomeomorphFundamentalGroupMap f g).comp
        (oneSkeletonFundamentalGroupMap
          (TwoDimensionalCWComplex.appendAttachingMap f g)) =
      (AdjunctionSpace.twoCellInclusionHom
        ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
        (TwoDimensionalCWComplex.basepoint f)).comp
        (oneSkeletonFundamentalGroupMap f) := by
  let appendMap : C(
      TwoDimensionalCWComplex.Space
        (TwoDimensionalCWComplex.appendAttachingMap f g),
      TwoDimensionalCWComplex.successiveSpace f g) :=
    (TwoDimensionalCWComplex.appendHomeomorph f g : C(_, _))
  let flatInclusion := oneSkeletonInclusion
    (TwoDimensionalCWComplex.appendAttachingMap f g)
  let oldInclusion := oneSkeletonInclusion f
  let cellInclusion := AdjunctionSpace.twoCellInclusion
    ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
  have flatBasepoint :
      flatInclusion (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
        TwoDimensionalCWComplex.basepoint
          (TwoDimensionalCWComplex.appendAttachingMap f g) :=
    oneSkeletonInclusion_basepoint _
  have oldBasepoint :
      oldInclusion (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
        TwoDimensionalCWComplex.basepoint f :=
    oneSkeletonInclusion_basepoint f
  have cellBasepoint :
      cellInclusion (TwoDimensionalCWComplex.basepoint f) =
        AdjunctionSpace.includeY (StandardSphere.boundary 1)
          ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
          (TwoDimensionalCWComplex.basepoint f) := by
    exact AdjunctionSpace.twoCellInclusion_apply _ _
  have leftBasepoint :
      (appendMap.comp flatInclusion)
          (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
        AdjunctionSpace.includeY (StandardSphere.boundary 1)
          ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
          (TwoDimensionalCWComplex.basepoint f) := by
    rw [ContinuousMap.comp_apply, flatBasepoint]
    exact appendHomeomorph_basepoint f g
  have rightBasepoint :
      (cellInclusion.comp oldInclusion)
          (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
        AdjunctionSpace.includeY (StandardSphere.boundary 1)
          ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
          (TwoDimensionalCWComplex.basepoint f) := by
    rw [ContinuousMap.comp_apply, oldBasepoint]
    exact cellBasepoint
  have cellHomEq : FundamentalGroup.mapOfEq cellInclusion cellBasepoint =
      AdjunctionSpace.twoCellInclusionHom
        ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
        (TwoDimensionalCWComplex.basepoint f) := by
    calc
      FundamentalGroup.mapOfEq cellInclusion cellBasepoint =
          FundamentalGroup.mapOfEq
            (AdjunctionSpace.twoCellInclusion
              ((TwoDimensionalCWComplex.skeletonInclusion f).comp g))
            (AdjunctionSpace.twoCellInclusion_apply _ _) :=
        FundamentalGroup.mapOfEq_congr _ _ rfl _ _
      _ = AdjunctionSpace.twoCellInclusionHom
          ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
          (TwoDimensionalCWComplex.basepoint f) :=
        AdjunctionSpace.mapOfEq_twoCellInclusion _ _
  -- Functoriality and the underlying continuous square give the homomorphism square.
  unfold appendHomeomorphFundamentalGroupMap
  unfold oneSkeletonFundamentalGroupMap
  calc
    (FundamentalGroup.mapOfEq appendMap (appendHomeomorph_basepoint f g)).comp
        (FundamentalGroup.mapOfEq flatInclusion flatBasepoint) =
      FundamentalGroup.mapOfEq (appendMap.comp flatInclusion) leftBasepoint :=
        FundamentalGroup.mapOfEq_comp flatInclusion appendMap flatBasepoint
          (appendHomeomorph_basepoint f g) leftBasepoint
    _ = FundamentalGroup.mapOfEq
        (cellInclusion.comp oldInclusion) rightBasepoint :=
      FundamentalGroup.mapOfEq_congr _ _
        (appendHomeomorph_oneSkeletonInclusion f g) _ _
    _ = (FundamentalGroup.mapOfEq cellInclusion cellBasepoint).comp
        (FundamentalGroup.mapOfEq oldInclusion oldBasepoint) :=
      (FundamentalGroup.mapOfEq_comp oldInclusion cellInclusion oldBasepoint
        cellBasepoint rightBasepoint).symm
    _ = (AdjunctionSpace.twoCellInclusionHom
        ((TwoDimensionalCWComplex.skeletonInclusion f).comp g)
        (TwoDimensionalCWComplex.basepoint f)).comp
        (FundamentalGroup.mapOfEq oldInclusion oldBasepoint) :=
      congrArg (fun k ↦ k.comp (FundamentalGroup.mapOfEq oldInclusion oldBasepoint))
        cellHomEq

/-- Helper for Exercise 73.2: any finite list of relators is realized by attaching the
corresponding two-cells, with the expected surjective fundamental-group map and kernel. -/
private theorem existsRelatorAttachingMap_kernel {n m : ℕ}
    (r : Fin m → FreeGroup (Fin n))
    (b : FreeGroupBasis (Fin n)
      (FundamentalGroup (TwoDimensionalCWComplex.OneSkeleton n)
        (TwoDimensionalCWComplex.oneSkeletonBasepoint n))) :
    ∃ f : TwoDimensionalCWComplex.AttachingMap n m,
      Function.Surjective
          ((oneSkeletonFundamentalGroupMap f).comp b.repr.symm.toMonoidHom) ∧
        ((oneSkeletonFundamentalGroupMap f).comp
          b.repr.symm.toMonoidHom).ker =
            Subgroup.normalClosure (Set.range r) := by
  classical
  induction m with
  | zero =>
      -- With no relators, the empty adjunction homeomorphism transports the chosen
      -- free basis to a bijective homomorphism, hence one with trivial kernel.
      let e := emptyAttachingSpaceHomeomorph n
      let ψ : FreeGroup (Fin n) →*
          FundamentalGroup
            (TwoDimensionalCWComplex.Space (emptyAttachingMap n))
            (TwoDimensionalCWComplex.basepoint (emptyAttachingMap n)) :=
        (oneSkeletonFundamentalGroupMap (emptyAttachingMap n)).comp
          b.repr.symm.toMonoidHom
      have eMapEq : (e : C(_, _)) =
          oneSkeletonInclusion (emptyAttachingMap n) := by
        apply ContinuousMap.ext
        intro x
        unfold e emptyAttachingSpaceHomeomorph oneSkeletonInclusion
        rw [TwoDimensionalCWComplex.skeletonInclusion_apply]
        rfl
      have eBasepoint :
          e (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
            TwoDimensionalCWComplex.basepoint (emptyAttachingMap n) := by
        calc
          e (TwoDimensionalCWComplex.oneSkeletonBasepoint n) =
              oneSkeletonInclusion (emptyAttachingMap n)
                (TwoDimensionalCWComplex.oneSkeletonBasepoint n) :=
            congrArg
              (fun k : C(_, _) ↦
                k (TwoDimensionalCWComplex.oneSkeletonBasepoint n)) eMapEq
          _ = TwoDimensionalCWComplex.basepoint (emptyAttachingMap n) :=
            oneSkeletonInclusion_basepoint _
      have skeletonMapEq : oneSkeletonFundamentalGroupMap (emptyAttachingMap n) =
          FundamentalGroup.mapOfEq (e : C(_, _)) eBasepoint := by
        unfold oneSkeletonFundamentalGroupMap
        exact FundamentalGroup.mapOfEq_congr _ _ eMapEq.symm _ _
      have skeletonMapBijective : Function.Bijective
          (oneSkeletonFundamentalGroupMap (emptyAttachingMap n)) := by
        rw [skeletonMapEq]
        exact e.fundamentalGroupMapOfEq_bijective
          (TwoDimensionalCWComplex.oneSkeletonBasepoint n)
            (TwoDimensionalCWComplex.basepoint (emptyAttachingMap n)) eBasepoint
      have hψsurjective : Function.Surjective ψ :=
        skeletonMapBijective.2.comp b.repr.symm.surjective
      have hψinjective : Function.Injective ψ :=
        skeletonMapBijective.1.comp b.repr.symm.injective
      have hrange : Set.range r = ∅ := by
        ext x
        constructor
        · rintro ⟨i, _⟩
          exact Fin.elim0 i
        · intro hx
          exact hx.elim
      have hnormal : Subgroup.normalClosure (Set.range r) = ⊥ := by
        rw [hrange, Subgroup.normalClosure_empty]
      have hψker : ψ.ker = Subgroup.normalClosure (Set.range r) :=
        (MonoidHom.ker_eq_bot_iff ψ).mpr hψinjective |>.trans hnormal.symm
      exact ⟨emptyAttachingMap n, hψsurjective, hψker⟩
  | succ m ih =>
      -- Route correction: control the canonical one-skeleton map throughout the induction,
      -- so the final relator is represented before passing to the old attached space.
      let rOld : Fin m → FreeGroup (Fin n) := fun i ↦ r i.castSucc
      obtain ⟨f, oldSurjective, oldKernel⟩ := ih rOld
      let skeletonMap := oneSkeletonFundamentalGroupMap f
      let basisMap := b.repr.symm.toMonoidHom
      let oldCanonical := skeletonMap.comp basisMap
      have oldCanonicalSurjective : Function.Surjective oldCanonical :=
        oldSurjective
      have skeletonMapSurjective : Function.Surjective skeletonMap :=
        Function.Surjective.of_comp oldCanonicalSurjective
      let lastRelator := r (Fin.last m)
      let loopClass := b.repr.symm lastRelator
      -- Choose a concrete loop representing the final free-group relator.
      obtain ⟨gamma, hgamma⟩ := Path.Homotopic.Quotient.mk_surjective
        (FundamentalGroup.toPath loopClass)
      have loopClassEq :
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma) =
            loopClass := by
        calc
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma) =
              FundamentalGroup.fromPath (FundamentalGroup.toPath loopClass) :=
            congrArg FundamentalGroup.fromPath hgamma
          _ = loopClass := rfl
      obtain ⟨g, p, hp, boundaryClosure⟩ :=
        FundamentalGroup.existsBoundaryMapNormalClosureEqLoopClass gamma
      let attachingMap := (TwoDimensionalCWComplex.skeletonInclusion f).comp g
      have attachingBasepoint :
          attachingMap p = TwoDimensionalCWComplex.basepoint f := by
        unfold attachingMap
        rw [ContinuousMap.comp_apply, hp,
          TwoDimensionalCWComplex.skeletonInclusion_apply,
          ← TwoDimensionalCWComplex.basepoint_eq_includeY]
      let cellMap := AdjunctionSpace.twoCellInclusionHom attachingMap
        (TwoDimensionalCWComplex.basepoint f)
      let boundaryMap := FundamentalGroup.mapOfEq g hp
      have boundarySquare : skeletonMap.comp boundaryMap =
          FundamentalGroup.mapOfEq attachingMap attachingBasepoint := by
        unfold skeletonMap oneSkeletonFundamentalGroupMap oneSkeletonInclusion
        exact FundamentalGroup.mapOfEq_comp g
          (TwoDimensionalCWComplex.skeletonInclusion f) hp
          (oneSkeletonInclusion_basepoint f) attachingBasepoint
      letI : PathConnectedSpace (TwoDimensionalCWComplex.Space f) :=
        TwoDimensionalCWComplex.spacePathConnectedSpace f
      obtain ⟨cellSurjective, cellKernel⟩ :=
        AdjunctionSpace.twoCellInclusionHom_spec attachingMap p
          (TwoDimensionalCWComplex.basepoint f) attachingBasepoint
      have cellKernelLast : cellMap.ker =
          Subgroup.normalClosure ({oldCanonical lastRelator} :
            Set (FundamentalGroup (TwoDimensionalCWComplex.Space f)
              (TwoDimensionalCWComplex.basepoint f))) := by
        calc
          cellMap.ker = Subgroup.normalClosure
              (Set.range (FundamentalGroup.mapOfEq attachingMap attachingBasepoint)) :=
            cellKernel
          _ = Subgroup.normalClosure (Set.range (skeletonMap.comp boundaryMap)) := by
            rw [boundarySquare]
          _ = (Subgroup.normalClosure (Set.range boundaryMap)).map skeletonMap :=
            (Subgroup.map_normalClosure_range_comp boundaryMap skeletonMap
              skeletonMapSurjective).symm
          _ = (Subgroup.normalClosure
              ({FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)} :
                Set _)).map skeletonMap :=
            congrArg (fun H : Subgroup _ ↦ H.map skeletonMap) boundaryClosure
          _ = (Subgroup.normalClosure ({loopClass} : Set _)).map skeletonMap := by
            rw [loopClassEq]
          _ = Subgroup.normalClosure (skeletonMap '' ({loopClass} : Set _)) :=
            Subgroup.map_normalClosure _ skeletonMap skeletonMapSurjective
          _ = Subgroup.normalClosure ({skeletonMap loopClass} : Set _) := by
            rw [Set.image_singleton]
          _ = Subgroup.normalClosure ({oldCanonical lastRelator} : Set _) := by
            rfl
      have successiveSurjective : Function.Surjective (cellMap.comp oldCanonical) :=
        cellSurjective.comp oldCanonicalSurjective
      have successiveKernel : (cellMap.comp oldCanonical).ker =
          Subgroup.normalClosure (Set.range r) := by
        calc
          (cellMap.comp oldCanonical).ker =
              Subgroup.normalClosure
                ((oldCanonical.ker : Set (FreeGroup (Fin n))) ∪ {lastRelator}) :=
            ker_comp_eq_normalClosure_union_singleton oldCanonical cellMap
              oldCanonicalSurjective lastRelator cellKernelLast
          _ = Subgroup.normalClosure
              ((Subgroup.normalClosure (Set.range rOld) :
                Subgroup (FreeGroup (Fin n))) ∪ {lastRelator}) := by
            rw [oldKernel]
          _ = Subgroup.normalClosure (Set.range rOld ∪ {lastRelator}) := by
            rw [Subgroup.normalClosure_union, Subgroup.normalClosure_eq_self,
              ← Subgroup.normalClosure_union]
          _ = Subgroup.normalClosure (Set.range r) := by
            congr 1
            ext x
            constructor
            · rintro (⟨i, rfl⟩ | hx)
              · exact ⟨i.castSucc, rfl⟩
              · rw [Set.mem_singleton_iff] at hx
                subst x
                exact ⟨Fin.last m, rfl⟩
            · rintro ⟨i, rfl⟩
              refine Fin.lastCases ?_ (fun j ↦ ?_) i
              · exact Or.inr rfl
              · exact Or.inl ⟨j, rfl⟩
      let newAttachingMap := TwoDimensionalCWComplex.appendAttachingMap f g
      let newCanonical :=
        (oneSkeletonFundamentalGroupMap newAttachingMap).comp basisMap
      let appendMap := appendHomeomorphFundamentalGroupMap f g
      have appendBijective : Function.Bijective appendMap := by
        unfold appendMap appendHomeomorphFundamentalGroupMap
        exact (TwoDimensionalCWComplex.appendHomeomorph f g).fundamentalGroupMapOfEq_bijective
          (TwoDimensionalCWComplex.basepoint newAttachingMap)
          (AdjunctionSpace.includeY (StandardSphere.boundary 1) attachingMap
            (TwoDimensionalCWComplex.basepoint f))
          (appendHomeomorph_basepoint f g)
      have canonicalSquare : appendMap.comp newCanonical =
          cellMap.comp oldCanonical := by
        calc
          appendMap.comp newCanonical =
              ((appendMap.comp
                (oneSkeletonFundamentalGroupMap newAttachingMap)).comp basisMap) := rfl
          _ = ((cellMap.comp skeletonMap).comp basisMap) :=
            congrArg (fun k ↦ k.comp basisMap)
              (appendHomeomorph_comp_oneSkeletonFundamentalGroupMap f g)
          _ = cellMap.comp oldCanonical := rfl
      have newSurjective : Function.Surjective newCanonical := by
        have compositeSurjective :
            Function.Surjective (appendMap.comp newCanonical) := by
          rw [canonicalSquare]
          exact successiveSurjective
        exact Function.Surjective.of_comp_left
          (f := appendMap) (g := newCanonical) compositeSurjective appendBijective.1
      have newKernel : newCanonical.ker =
          Subgroup.normalClosure (Set.range r) := by
        calc
          newCanonical.ker = (appendMap.comp newCanonical).ker :=
            (MonoidHom.ker_comp_of_injective newCanonical appendMap
              appendBijective.1).symm
          _ = (cellMap.comp oldCanonical).ker :=
            congrArg MonoidHom.ker canonicalSquare
          _ = Subgroup.normalClosure (Set.range r) := successiveKernel
      exact ⟨newAttachingMap, newSurjective, newKernel⟩

/-- Helper for Exercise 73.2: two surjective group homomorphisms with the same kernel have
isomorphic codomains. -/
private noncomputable def mulEquivOfSurjectiveWithEqualKernels
    {F H K : Type*} [Group F] [Group H] [Group K]
    (f : F →* H) (g : F →* K) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hker : f.ker = g.ker) : H ≃* K :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

/-- Helper for Exercise 73.2: a finite presentation is realized by attaching finitely many
two-cells to a finite wedge of circles. -/
theorem exists_twoDimensionalCWComplex_fundamentalGroup_mulEquiv
    (G : Type u) [Group G] [Group.IsFinitelyPresented G] :
    ∃ n m, ∃ f : TwoDimensionalCWComplex.AttachingMap n m,
      Nonempty
        (FundamentalGroup (TwoDimensionalCWComplex.Space f)
            (TwoDimensionalCWComplex.basepoint f) ≃* G) := by
  classical
  -- Choose a finite free presentation and enumerate its finite normal generating set by `Fin m`.
  obtain ⟨n, φ, hφsurj, s, hsfinite, hsclosure⟩ :=
    Group.IsFinitelyPresented.out (G := G)
  letI : Fintype s := hsfinite.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let r : Fin (Fintype.card s) → FreeGroup (Fin n) := fun i ↦ (e.symm i).1
  have hrange : Set.range r = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  -- Realize the enumerated relators geometrically and compare the resulting kernel with `φ.ker`.
  obtain ⟨b⟩ := oneSkeletonFreeBasis n
  obtain ⟨f, hfsurj, hfker⟩ := existsRelatorAttachingMap_kernel r b
  let ψ := (oneSkeletonFundamentalGroupMap f).comp b.repr.symm.toMonoidHom
  have hker : ψ.ker = φ.ker := by
    calc
      ψ.ker = Subgroup.normalClosure (Set.range r) := hfker
      _ = Subgroup.normalClosure s := congrArg Subgroup.normalClosure hrange
      _ = φ.ker := hsclosure
  -- The first isomorphism theorem now identifies the fundamental group with the presented group.
  exact ⟨n, Fintype.card s, f,
    ⟨mulEquivOfSurjectiveWithEqualKernels ψ φ hfsurj hφsurj hker⟩⟩

/-- Exercise 73.2: Every finitely presented group is isomorphic to the fundamental group of a
pointed compact Hausdorff space. -/
theorem exists_compHaus_fundamentalGroup_mulEquiv (G : Type u) [Group G]
    [Group.IsFinitelyPresented G] :
    ∃ X : CompHaus.{0}, ∃ x : X, Nonempty (FundamentalGroup X x ≃* G) := by
  obtain ⟨n, m, f, h⟩ := exists_twoDimensionalCWComplex_fundamentalGroup_mulEquiv G
  exact ⟨TwoDimensionalCWComplex.compHaus f, TwoDimensionalCWComplex.basepoint f, h⟩
