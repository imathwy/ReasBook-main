module

public import Topology_Munkres_2000.Book.Exercise_73_2.CWComplex
public import Topology_Munkres_2000.Book.Exercise_72_2
public import Topology_Munkres_2000.Book.Theorem_9_0_1.BorsukNoRetraction
public import Mathlib.Topology.Homeomorph.Lemmas
import all Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge

public section

noncomputable section

namespace TwoDimensionalCWComplex

/-- Helper for Exercise 73.2: the canonical finite wedge of circles is path-connected. -/
theorem oneSkeletonPathConnectedSpace (n : ℕ) : PathConnectedSpace (OneSkeleton n) := by
  let toBasepoint : ∀ x : OneSkeleton n, Joined x (oneSkeletonBasepoint n) := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
        rcases x with ⟨_ | i, x⟩
        · cases x
          have hpoint : (⟦⟨none, PUnit.unit⟩⟧ : OneSkeleton n) =
              oneSkeletonBasepoint n := oneSkeleton_none_eq_basepoint n PUnit.unit
          rw [hpoint]
        · -- Move inside the selected circle to its designated point, whose quotient
          -- image is the common wedge point.
          change Circle at x
          have hcircle : Joined x (1 : Circle) := PathConnectedSpace.joined _ _
          let inclusion : Circle → OneSkeleton n :=
            Topology.IndexedPointedWedge.inclusion (CircleFamily n) (circlePoints n) (some i)
          have hmapped : Joined (inclusion x) (inclusion 1) :=
            ⟨hcircle.somePath.map
              (continuous_oneSkeleton_circleInclusion n i)⟩
          have hpoint : inclusion 1 = oneSkeletonBasepoint n := by
            exact oneSkeleton_circlePoint_eq_basepoint n i
          rw [hpoint] at hmapped
          exact hmapped
  refine
    { nonempty := ⟨oneSkeletonBasepoint n⟩
      joined := ?_ }
  intro x y
  -- Join both points through the common wedge point.
  exact (toBasepoint x).trans (toBasepoint y).symm

/-- Helper for Exercise 73.2: every concrete finite two-dimensional CW complex is
path-connected. -/
theorem spacePathConnectedSpace {n m : ℕ} (f : AttachingMap n m) :
    PathConnectedSpace (Space f) := by
  letI : PathConnectedSpace (OneSkeleton n) := oneSkeletonPathConnectedSpace n
  letI : PathConnectedSpace B² :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
  let toBasepoint : ∀ x : Space f, Joined x (basepoint f) := by
    intro x
    rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY (boundary m) f x with
      ⟨z, rfl⟩ | ⟨y, rfl⟩
    · -- In a disk component, first move to one fixed boundary point and glue it
      -- into the one-skeleton.
      let p : StandardSphere.boundary 1 := closedUnitDiskBoundaryHomeomorphCircle.symm 1
      let a : boundary m := boundaryMk z.1 p
      have hcell : Joined z.2 p.1 := PathConnectedSpace.joined _ _
      have hcellMapped : Joined
          (AdjunctionSpace.includeX (boundary m) f z)
          (AdjunctionSpace.includeX (boundary m) f a.1) := by
        rw [boundaryMk_val]
        have hcontinuous : Continuous (fun w : B² ↦
            AdjunctionSpace.includeX (boundary m) f ⟨z.1, w⟩) :=
          (AdjunctionSpace.continuous_includeX (boundary m) f).comp
            continuous_sigmaMk
        exact ⟨hcell.somePath.map hcontinuous⟩
      have hglue : Joined
          (AdjunctionSpace.includeX (boundary m) f a.1)
          (AdjunctionSpace.includeY (boundary m) f (f a)) :=
        (AdjunctionSpace.glue (boundary m) f a) ▸ Joined.refl _
      have hbase : Joined
          (AdjunctionSpace.includeY (boundary m) f (f a))
          (basepoint f) := by
        rw [basepoint_eq_includeY]
        exact ⟨(PathConnectedSpace.somePath (f a) (oneSkeletonBasepoint n)).map
          (AdjunctionSpace.continuous_includeY (boundary m) f)⟩
      exact hcellMapped.trans (hglue.trans hbase)
    · -- Points already in the one-skeleton move to the basepoint there.
      rw [basepoint_eq_includeY]
      exact ⟨(PathConnectedSpace.somePath y (oneSkeletonBasepoint n)).map
        (AdjunctionSpace.continuous_includeY (boundary m) f)⟩
  refine
    { nonempty := ⟨basepoint f⟩
      joined := ?_ }
  intro x y
  exact (toBasepoint x).trans (toBasepoint y).symm

/-- Helper for Exercise 73.2: the easy componentwise map from the finite sigma
family of boundary circles to the boundary subtype. -/
private def boundarySigmaMap (m : ℕ) :
    C((Σ _ : Fin m, StandardSphere.boundary 1), boundary m) :=
  ContinuousMap.sigma (fun i ↦ ⟨boundaryMk i, continuous_boundaryMk i⟩)

/-- Helper for Exercise 73.2: the componentwise boundary map computes by the
canonical boundary constructor. -/
@[simp] private lemma boundarySigmaMap_apply (m : ℕ) (i : Fin m)
    (z : StandardSphere.boundary 1) :
    boundarySigmaMap m ⟨i, z⟩ = boundaryMk i z := by
  -- Evaluate `ContinuousMap.sigma` on its selected component.
  rfl

/-- Helper for Exercise 73.2: the componentwise boundary map is bijective. -/
private lemma boundarySigmaMap_bijective (m : ℕ) :
    Function.Bijective (boundarySigmaMap m) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    rw [boundarySigmaMap_apply, boundarySigmaMap_apply] at h
    have hval : (⟨i, x.1⟩ : ClosedCells m) = ⟨j, y.1⟩ := by
      simpa only [boundaryMk_val] using congrArg Subtype.val h
    have hij : i = j := (Sigma.mk.inj_iff.mp hval).1
    subst j
    have hxy : x.1 = y.1 := eq_of_heq (Sigma.mk.inj_iff.mp hval).2
    have hxy' : x = y := Subtype.ext hxy
    subst y
    rfl
  · intro a
    exact ⟨⟨a.1.1, boundaryPoint a⟩, boundaryMk_eta a⟩

/-- Helper for Exercise 73.2: the boundary subtype is homeomorphic to the finite
sigma family of standard boundary circles. -/
private def boundarySigmaHomeomorph (m : ℕ) :
    (Σ _ : Fin m, StandardSphere.boundary 1) ≃ₜ boundary m :=
  letI : CompactSpace (StandardSphere.boundary 1) :=
    closedUnitDiskBoundaryHomeomorphCircle.symm.compactSpace
  let hhome : IsHomeomorph (boundarySigmaMap m) :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨(boundarySigmaMap m).continuous, boundarySigmaMap_bijective m⟩
  hhome.homeomorph (boundarySigmaMap m)

/-- Helper for Exercise 73.2: the boundary homeomorphism computes componentwise. -/
@[simp] private lemma boundarySigmaHomeomorph_apply (m : ℕ) (i : Fin m)
    (z : StandardSphere.boundary 1) :
    boundarySigmaHomeomorph m ⟨i, z⟩ = boundaryMk i z := by
  -- The homeomorphism retains the original continuous bijection as its forward map.
  simp only [boundarySigmaHomeomorph, IsHomeomorph.homeomorph_apply,
    boundarySigmaMap_apply]

/-- Helper for Exercise 73.2: the inverse boundary normalization recovers the
component index and boundary point of a canonical constructor. -/
private lemma boundarySigmaHomeomorph_symm_boundaryMk (m : ℕ) (i : Fin m)
    (z : StandardSphere.boundary 1) :
    (boundarySigmaHomeomorph m).symm (boundaryMk i z) = ⟨i, z⟩ := by
  -- Apply the forward homeomorphism, where both sides compute componentwise.
  apply (boundarySigmaHomeomorph m).injective
  rw [(boundarySigmaHomeomorph m).apply_symm_apply]
  exact boundarySigmaHomeomorph_apply m i z

/-- Helper for Exercise 73.2: the inclusion of one boundary component into the
finite boundary family. -/
private def boundaryComponent (m : ℕ) (i : Fin m) :
    C(StandardSphere.boundary 1, boundary m) :=
  ⟨fun z ↦ boundarySigmaHomeomorph m ⟨i, z⟩,
    (boundarySigmaHomeomorph m).continuous.comp continuous_sigmaMk⟩

/-- Helper for Exercise 73.2: append one boundary attaching map to a finite family. -/
def appendAttachingMap {n m : ℕ} (f : AttachingMap n m)
  (g : C(StandardSphere.boundary 1, OneSkeleton n)) : AttachingMap n (m + 1) :=
  (ContinuousMap.sigma (Fin.lastCases g (fun i ↦ f.comp (boundaryComponent m i)))).comp
    ⟨(boundarySigmaHomeomorph (m + 1)).symm,
      (boundarySigmaHomeomorph (m + 1)).symm.continuous⟩

/-- Helper for Exercise 73.2: the appended map restricts to the old attaching map on
every old cell. -/
@[simp] theorem appendAttachingMap_castSucc {n m : ℕ} (f : AttachingMap n m)
    (g : C(StandardSphere.boundary 1, OneSkeleton n))
    (i : Fin m) (z : StandardSphere.boundary 1) :
    appendAttachingMap f g (boundaryMk i.castSucc z) =
      f (boundaryMk i z) := by
  -- Evaluate the sigma family at an old index.
  change (ContinuousMap.sigma
    (Fin.lastCases g (fun i ↦ f.comp (boundaryComponent m i))))
      ((boundarySigmaHomeomorph (m + 1)).symm (boundaryMk i.castSucc z)) = _
  rw [boundarySigmaHomeomorph_symm_boundaryMk]
  rw [ContinuousMap.sigma_apply, Fin.lastCases_castSucc]
  exact congrArg f (boundarySigmaHomeomorph_apply m i z)

/-- Helper for Exercise 73.2: the final component of the appended map is the new
attaching map. -/
@[simp] theorem appendAttachingMap_last {n m : ℕ} (f : AttachingMap n m)
    (g : C(StandardSphere.boundary 1, OneSkeleton n))
    (z : StandardSphere.boundary 1) :
    appendAttachingMap f g (boundaryMk (Fin.last m) z) = g z := by
  -- Evaluate the sigma family at its final index.
  change (ContinuousMap.sigma
    (Fin.lastCases g (fun i ↦ f.comp (boundaryComponent m i))))
      ((boundarySigmaHomeomorph (m + 1)).symm (boundaryMk (Fin.last m) z)) = _
  rw [boundarySigmaHomeomorph_symm_boundaryMk]
  rw [ContinuousMap.sigma_apply, Fin.lastCases_last]

/-- Helper for Exercise 73.2: the canonical one-skeleton inclusion into a finite
two-dimensional CW complex. -/
def skeletonInclusion {n m : ℕ} (f : AttachingMap n m) :
    C(OneSkeleton n, Space f) :=
  ⟨AdjunctionSpace.includeY (boundary m) f,
    AdjunctionSpace.continuous_includeY (boundary m) f⟩

/-- Helper for Exercise 73.2: the bundled one-skeleton inclusion computes as the
canonical right-summand map. -/
@[simp] theorem skeletonInclusion_apply {n m : ℕ} (f : AttachingMap n m)
    (y : OneSkeleton n) :
    skeletonInclusion f y = AdjunctionSpace.includeY (boundary m) f y := by
  -- This is the function field of the bundled inclusion.
  rfl

section AppendComparison

variable {n m : ℕ} (f : AttachingMap n m)
  (g : C(StandardSphere.boundary 1, OneSkeleton n))

/-- Helper for Exercise 73.2: the space obtained by attaching the new disk after
the old finite complex. -/
abbrev successiveSpace :=
  AdjunctionSpace (StandardSphere.boundary 1) ((skeletonInclusion f).comp g)

/-- Helper for Exercise 73.2: an old closed cell maps into the old stage of the
successive attachment. -/
private def oldCellForward (i : Fin m) : C(B², successiveSpace f g) :=
  ⟨fun z ↦ AdjunctionSpace.includeY (StandardSphere.boundary 1)
      ((skeletonInclusion f).comp g)
      (AdjunctionSpace.includeX (boundary m) f ⟨i, z⟩),
    (AdjunctionSpace.continuous_includeY (StandardSphere.boundary 1)
      ((skeletonInclusion f).comp g)).comp
      ((AdjunctionSpace.continuous_includeX (boundary m) f).comp continuous_sigmaMk)⟩

/-- Helper for Exercise 73.2: the new closed cell maps to the outer disk of the
successive attachment. -/
private def lastCellForward : C(B², successiveSpace f g) :=
  ⟨AdjunctionSpace.includeX (StandardSphere.boundary 1) ((skeletonInclusion f).comp g),
    AdjunctionSpace.continuous_includeX (StandardSphere.boundary 1)
      ((skeletonInclusion f).comp g)⟩

/-- Helper for Exercise 73.2: the componentwise map on all closed cells. -/
private def closedCellsForward : C(ClosedCells (m + 1), successiveSpace f g) :=
  ContinuousMap.sigma (Fin.lastCases (lastCellForward f g) (oldCellForward f g))

/-- Helper for Exercise 73.2: the closed-cell forward map sends the final cell to
the outer disk. -/
private lemma closedCellsForward_last (z : B²) :
    closedCellsForward f g ⟨Fin.last m, z⟩ =
      AdjunctionSpace.includeX (StandardSphere.boundary 1)
        ((skeletonInclusion f).comp g) z := by
  -- Evaluate the last-case sigma family at its final component.
  rw [closedCellsForward, ContinuousMap.sigma_apply, Fin.lastCases_last]
  rfl

/-- Helper for Exercise 73.2: the closed-cell forward map sends an old cell through
the old stage inclusion. -/
private lemma closedCellsForward_castSucc (i : Fin m) (z : B²) :
    closedCellsForward f g ⟨i.castSucc, z⟩ =
      AdjunctionSpace.includeY (StandardSphere.boundary 1)
        ((skeletonInclusion f).comp g)
        (AdjunctionSpace.includeX (boundary m) f ⟨i, z⟩) := by
  -- Evaluate the last-case sigma family at an old component.
  rw [closedCellsForward, ContinuousMap.sigma_apply, Fin.lastCases_castSucc]
  rfl

/-- Helper for Exercise 73.2: the one-skeleton maps through both successive inclusions. -/
private def skeletonForward : C(OneSkeleton n, successiveSpace f g) :=
  ⟨fun y ↦ AdjunctionSpace.includeY (StandardSphere.boundary 1)
      ((skeletonInclusion f).comp g)
      (AdjunctionSpace.includeY (boundary m) f y),
    (AdjunctionSpace.continuous_includeY (StandardSphere.boundary 1)
      ((skeletonInclusion f).comp g)).comp
      (AdjunctionSpace.continuous_includeY (boundary m) f)⟩

/-- Helper for Exercise 73.2: the forward one-skeleton map is the composite of the
two canonical inclusions. -/
private lemma skeletonForward_apply (y : OneSkeleton n) :
    skeletonForward f g y =
      AdjunctionSpace.includeY (StandardSphere.boundary 1)
        ((skeletonInclusion f).comp g)
        (AdjunctionSpace.includeY (boundary m) f y) := by
  -- This is the function field of the bundled composite inclusion.
  rfl

/-- Helper for Exercise 73.2: the componentwise forward map respects every gluing
relation of the flat attachment. -/
private lemma closedCellsForward_agrees
    (a : boundary (m + 1)) :
    closedCellsForward f g a.1 = skeletonForward f g (appendAttachingMap f g a) := by
  -- First prove the computation for a canonical component constructor, then use
  -- the owner eta law to normalize an arbitrary boundary subtype element.
  have hcomponent (j : Fin (m + 1)) (z : StandardSphere.boundary 1) :
      closedCellsForward f g (boundaryMk j z).1 =
        skeletonForward f g (appendAttachingMap f g (boundaryMk j z)) := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [boundaryMk_val, closedCellsForward_last, appendAttachingMap_last,
          skeletonForward_apply]
      exact
        (AdjunctionSpace.glue (StandardSphere.boundary 1)
          ((skeletonInclusion f).comp g) z)
    · rw [boundaryMk_val, closedCellsForward_castSucc,
          appendAttachingMap_castSucc, skeletonForward_apply]
      simpa only [boundaryMk_val] using
        congrArg
          (AdjunctionSpace.includeY (StandardSphere.boundary 1)
            ((skeletonInclusion f).comp g))
          (AdjunctionSpace.glue (boundary m) f (boundaryMk i z))
  simpa only [boundaryMk_eta a] using hcomponent a.1.1 (boundaryPoint a)

/-- Helper for Exercise 73.2: the continuous quotient map from the flat attachment
to the successive attachment. -/
private def appendForward : C(Space (appendAttachingMap f g), successiveSpace f g) :=
  ⟨AdjunctionSpace.lift (boundary (m + 1)) (appendAttachingMap f g)
      (closedCellsForward f g) (skeletonForward f g)
      (closedCellsForward_agrees f g),
    AdjunctionSpace.continuous_lift (boundary (m + 1)) (appendAttachingMap f g)
      (closedCellsForward f g) (skeletonForward f g)
      (closedCellsForward_agrees f g)⟩

/-- Helper for Exercise 73.2: the forward quotient lift computes on a closed-cell
representative. -/
private lemma appendForward_includeX (z : ClosedCells (m + 1)) :
    appendForward f g
        (AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g) z) =
      closedCellsForward f g z := by
  -- Apply the left-summand computation rule for `AdjunctionSpace.lift`.
  exact AdjunctionSpace.lift_includeX (boundary (m + 1)) (appendAttachingMap f g)
    (closedCellsForward f g) (skeletonForward f g)
    (closedCellsForward_agrees f g) z

/-- Helper for Exercise 73.2: the forward quotient lift computes on a one-skeleton
representative. -/
private lemma appendForward_includeY (y : OneSkeleton n) :
    appendForward f g
        (AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) y) =
      skeletonForward f g y := by
  -- Apply the right-summand computation rule for `AdjunctionSpace.lift`.
  exact AdjunctionSpace.lift_includeY (boundary (m + 1)) (appendAttachingMap f g)
    (closedCellsForward f g) (skeletonForward f g)
    (closedCellsForward_agrees f g) y

/-- Helper for Exercise 73.2: the old-cell reindexing respects the flat attaching
relation. -/
private lemma oldStageBackward_agrees (a : boundary m) :
    AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
        ⟨a.1.1.castSucc, a.1.2⟩ =
      AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) (f a) := by
  -- Normalize the old boundary point, apply the flat gluing equation, and compute
  -- the appended attaching map on an old component.
  let a' := boundaryMk a.1.1.castSucc (boundaryPoint a)
  calc
    AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
          ⟨a.1.1.castSucc, a.1.2⟩ =
        AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g) a'.1 := by
          simpa only [boundaryPoint_val] using congrArg
            (AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g))
            (boundaryMk_val a.1.1.castSucc (boundaryPoint a)).symm
    _ = AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g)
          (appendAttachingMap f g a') :=
      AdjunctionSpace.glue (boundary (m + 1)) (appendAttachingMap f g) a'
    _ = AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g)
          (f (boundaryMk a.1.1 (boundaryPoint a))) := by
      rw [appendAttachingMap_castSucc]
    _ = AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) (f a) :=
      congrArg _ (congrArg f (boundaryMk_eta a))

/-- Helper for Exercise 73.2: the old stage maps set-theoretically into the flat
attachment through the old cell indices. -/
private def oldStageBackward : Space f → Space (appendAttachingMap f g) :=
  AdjunctionSpace.lift (boundary m) f
    (fun z ↦ AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
      ⟨z.1.castSucc, z.2⟩)
    (AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g))
    (oldStageBackward_agrees f g)

/-- Helper for Exercise 73.2: the old-stage inverse lift computes on an old cell. -/
private lemma oldStageBackward_includeX (z : ClosedCells m) :
    oldStageBackward f g (AdjunctionSpace.includeX (boundary m) f z) =
      AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
        ⟨z.1.castSucc, z.2⟩ := by
  -- Apply the old lift's left-summand computation rule.
  exact AdjunctionSpace.lift_includeX (boundary m) f _ _ _ z

/-- Helper for Exercise 73.2: the old-stage inverse lift computes on the one-skeleton. -/
private lemma oldStageBackward_includeY (y : OneSkeleton n) :
    oldStageBackward f g (AdjunctionSpace.includeY (boundary m) f y) =
      AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) y := by
  -- Apply the old lift's right-summand computation rule.
  exact AdjunctionSpace.lift_includeY (boundary m) f _ _ _ y

/-- Helper for Exercise 73.2: the outer disk maps set-theoretically to the final flat
cell. -/
private def newCellBackward : B² → Space (appendAttachingMap f g) :=
  fun z ↦ AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
    ⟨Fin.last m, z⟩

/-- Helper for Exercise 73.2: the new-cell inverse map is the final flat cell
inclusion. -/
private lemma newCellBackward_apply (z : B²) :
    newCellBackward f g z =
      AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
        ⟨Fin.last m, z⟩ := by
  -- This is the defining function equation.
  rfl

/-- Helper for Exercise 73.2: the set-theoretic inverse respects the outer attaching
relation. -/
private lemma appendBackward_agrees (a : StandardSphere.boundary 1) :
    newCellBackward f g a.1 =
      oldStageBackward f g ((skeletonInclusion f).comp g a) := by
  -- Both sides are the two representatives identified by the final flat gluing relation.
  rw [newCellBackward_apply, ContinuousMap.comp_apply, skeletonInclusion_apply,
    oldStageBackward_includeY]
  calc
    AdjunctionSpace.includeX (boundary (m + 1)) (appendAttachingMap f g)
          ⟨Fin.last m, a.1⟩ =
        AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g)
          (appendAttachingMap f g (boundaryMk (Fin.last m) a)) := by
      simpa only [boundaryMk_val] using
        (AdjunctionSpace.glue (boundary (m + 1)) (appendAttachingMap f g)
          (boundaryMk (Fin.last m) a))
    _ = AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) (g a) := by
      rw [appendAttachingMap_last]

/-- Helper for Exercise 73.2: a set-theoretic inverse to the flat-to-successive map. -/
private def appendBackward : successiveSpace f g → Space (appendAttachingMap f g) :=
  AdjunctionSpace.lift (StandardSphere.boundary 1) ((skeletonInclusion f).comp g)
    (newCellBackward f g) (oldStageBackward f g) (appendBackward_agrees f g)

/-- Helper for Exercise 73.2: the set-theoretic inverse computes on the outer disk. -/
private lemma appendBackward_includeX (z : B²) :
    appendBackward f g
        (AdjunctionSpace.includeX (StandardSphere.boundary 1)
          ((skeletonInclusion f).comp g) z) = newCellBackward f g z := by
  -- Apply the outer lift's left-summand computation rule.
  exact AdjunctionSpace.lift_includeX (StandardSphere.boundary 1)
    ((skeletonInclusion f).comp g) _ _ _ z

/-- Helper for Exercise 73.2: the set-theoretic inverse computes on the old stage. -/
private lemma appendBackward_includeY (y : Space f) :
    appendBackward f g
        (AdjunctionSpace.includeY (StandardSphere.boundary 1)
          ((skeletonInclusion f).comp g) y) = oldStageBackward f g y := by
  -- Apply the outer lift's right-summand computation rule.
  exact AdjunctionSpace.lift_includeY (StandardSphere.boundary 1)
    ((skeletonInclusion f).comp g) _ _ _ y

/-- Helper for Exercise 73.2: the set-theoretic inverse is a left inverse. -/
private lemma appendBackward_leftInverse :
    Function.LeftInverse (appendBackward f g) (appendForward f g) := by
  intro q
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      (boundary (m + 1)) (appendAttachingMap f g) q with ⟨z, rfl⟩ | ⟨y, rfl⟩
  · rcases z with ⟨j, z⟩
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [appendForward_includeX, closedCellsForward_last,
        appendBackward_includeX, newCellBackward_apply]
    · rw [appendForward_includeX, closedCellsForward_castSucc,
        appendBackward_includeY, oldStageBackward_includeX]
  · rw [appendForward_includeY, skeletonForward_apply,
      appendBackward_includeY, oldStageBackward_includeY]

/-- Helper for Exercise 73.2: the set-theoretic inverse is a right inverse. -/
private lemma appendBackward_rightInverse :
    Function.RightInverse (appendBackward f g) (appendForward f g) := by
  intro q
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      (StandardSphere.boundary 1) ((skeletonInclusion f).comp g) q with
    ⟨z, rfl⟩ | ⟨y, rfl⟩
  · rw [appendBackward_includeX, newCellBackward_apply,
      appendForward_includeX, closedCellsForward_last]
  · rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
        (boundary m) f y with ⟨z, rfl⟩ | ⟨x, rfl⟩
    · rw [appendBackward_includeY, oldStageBackward_includeX,
        appendForward_includeX, closedCellsForward_castSucc]
    · rw [appendBackward_includeY, oldStageBackward_includeY,
        appendForward_includeY, skeletonForward_apply]

/-- Helper for Exercise 73.2: appending one cell flatly is homeomorphic to attaching
that cell after the old finite complex. -/
def appendHomeomorph :
    Space (appendAttachingMap f g) ≃ₜ successiveSpace f g :=
  letI : T4Space (Space f) := inferInstance
  letI : T4Space (successiveSpace f g) := twoCellAdjunctionSpaceT4Space _
  let hhome : IsHomeomorph (appendForward f g) :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨(appendForward f g).continuous,
        ⟨(appendBackward_leftInverse f g).injective,
          (appendBackward_rightInverse f g).surjective⟩⟩
  hhome.homeomorph (appendForward f g)

/-- Helper for Exercise 73.2: the append comparison carries the one-skeleton inclusion
through the two successive inclusions. -/
theorem appendHomeomorph_includeY (y : OneSkeleton n) :
    appendHomeomorph f g
        (AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) y) =
      AdjunctionSpace.includeY (StandardSphere.boundary 1)
        ((skeletonInclusion f).comp g)
        (AdjunctionSpace.includeY (boundary m) f y) := by
  -- Compute the forward quotient lift on the one-skeleton representative.
  change appendForward f g
      (AdjunctionSpace.includeY (boundary (m + 1)) (appendAttachingMap f g) y) = _
  rw [appendForward_includeY, skeletonForward_apply]

end AppendComparison

end TwoDimensionalCWComplex
