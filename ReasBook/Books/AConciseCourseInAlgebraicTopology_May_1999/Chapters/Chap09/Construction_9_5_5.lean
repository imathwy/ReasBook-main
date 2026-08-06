import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Connected.PathConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_4

open scoped Topology Topology.Homotopy

universe u

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: the available mathlib hits were generic homotopy-group
-- APIs rather than this pair-mapping-space fibration. Local Chapter 7 precedent already packages
-- fibrations and their fibers with `IsFibration`/`fiber`, so this item formalizes the source
-- evaluation map together with its explicit actual-fiber owner on the standard disk-boundary
-- model `(unitDisk ((n : ℕ) - 1), sphereBoundary ((n : ℕ) - 1))` of `(CS^(n - 1), S^(n - 1))`.

/-- A chosen basepoint of `S^(n - 1)`, realized in `sphereBoundary ((n : ℕ) - 1)` by the first
standard basis vector. -/
noncomputable def diskBoundaryBasepoint (n : ℕ+) : sphereBoundary ((n : ℕ) - 1) :=
  sphereBoundaryBasepoint ((n : ℕ) - 1)

/-- A map `unitDisk ((n : ℕ) - 1) → X` is a map of pairs
`(CS^(n - 1), S^(n - 1)) → (X, A)` when it sends the boundary sphere into `A`. -/
def IsDiskBoundaryPairMap (n : ℕ+) (A : Set X) (f : C(unitDisk ((n : ℕ) - 1), X)) : Prop :=
  ∀ y : sphereBoundary ((n : ℕ) - 1), f (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A

/-- Unfolding `IsDiskBoundaryPairMap` recovers the defining boundary condition for a map of pairs
`(CS^(n - 1), S^(n - 1)) → (X, A)` in the disk-boundary model. -/
@[simp] theorem isDiskBoundaryPairMap_iff
    (n : ℕ+) (A : Set X) (f : C(unitDisk ((n : ℕ) - 1), X)) :
    IsDiskBoundaryPairMap n A f ↔
      ∀ y : sphereBoundary ((n : ℕ) - 1),
        f (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A := by
  rfl

/-- The concrete mapping space of pairs `(CS^(n - 1), S^(n - 1)) → (X, A)`, realized by the
standard disk-boundary model. -/
abbrev diskBoundaryPairMap (n : ℕ+) (A : Set X) :=
  { f : C(unitDisk ((n : ℕ) - 1), X) // IsDiskBoundaryPairMap n A f }

/-- Evaluation at the chosen boundary basepoint of `S^(n - 1)` on the mapping space of pairs
`(CS^(n - 1), S^(n - 1)) → (X, A)`. -/
noncomputable def diskBoundaryPairMapEvalAtBasepoint (n : ℕ+) (A : Set X) :
    C(diskBoundaryPairMap n A, A) where
  toFun f :=
    ⟨f.1 (sphereBoundaryInclusion ((n : ℕ) - 1) (diskBoundaryBasepoint n)),
      f.2 (diskBoundaryBasepoint n)⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (((continuous_eval_const
          (sphereBoundaryInclusion ((n : ℕ) - 1) (diskBoundaryBasepoint n)))).comp
        continuous_subtype_val)
      (fun f : diskBoundaryPairMap n A ↦ f.2 (diskBoundaryBasepoint n))

/-- Construction 9.5.5 (1): evaluation at the chosen basepoint of `S^(n - 1)` gives a fibration
from the mapping space of pairs `(CS^(n - 1), S^(n - 1)) → (X, A)` to `A`. -/
theorem diskBoundaryPairMapEvalAtBasepoint_isFibration (n : ℕ+) (A : Set X) :
    IsFibration (diskBoundaryPairMapEvalAtBasepoint n A) := sorry

/-- The evaluation map at `diskBoundaryBasepoint n` carries the canonical `IsFibration` instance
from Construction 9.5.5 (1). -/
instance diskBoundaryPairMapEvalAtBasepointInstIsFibration (n : ℕ+) (A : Set X) :
    IsFibration (diskBoundaryPairMapEvalAtBasepoint n A) :=
  diskBoundaryPairMapEvalAtBasepoint_isFibration n A

/-- The fiber over `a : A` of the evaluation fibration
`diskBoundaryPairMapEvalAtBasepoint n A : diskBoundaryPairMap n A ⟶ A`. -/
abbrev diskBoundaryPairMapFiber (n : ℕ+) (A : Set X) (a : A) :=
  fiber (diskBoundaryPairMapEvalAtBasepoint n A) a

/-- A map of pairs belongs to the fiber over `a : A` exactly when it sends the chosen boundary
basepoint of `S^(n - 1)` to `a`. -/
def IsBasedDiskBoundaryPairMap (n : ℕ+) (A : Set X) (a : A)
    (f : C(unitDisk ((n : ℕ) - 1), X)) : Prop :=
  IsDiskBoundaryPairMap n A f ∧
    f (sphereBoundaryInclusion ((n : ℕ) - 1) (diskBoundaryBasepoint n)) = a.1

/-- Unfolding `IsBasedDiskBoundaryPairMap` recovers the boundary condition together with the
chosen-boundary-basepoint condition over `a`. -/
@[simp] theorem isBasedDiskBoundaryPairMap_iff
    (n : ℕ+) (A : Set X) (a : A) (f : C(unitDisk ((n : ℕ) - 1), X)) :
    IsBasedDiskBoundaryPairMap n A a f ↔
      IsDiskBoundaryPairMap n A f ∧
        f (sphereBoundaryInclusion ((n : ℕ) - 1) (diskBoundaryBasepoint n)) = a.1 := by
  rfl

/-- The concrete fiber owner: maps of pairs `(CS^(n - 1), S^(n - 1)) → (X, A)` sending the chosen
boundary basepoint of `S^(n - 1)` to `a`. -/
abbrev basedDiskBoundaryPairMap (n : ℕ+) (A : Set X) (a : A) :=
  { f : C(unitDisk ((n : ℕ) - 1), X) // IsBasedDiskBoundaryPairMap n A a f }

/-- Forgetting the explicit basepoint equation identifies a boundary-based pair map with a point of
the evaluation fiber over `a`. -/
def basedDiskBoundaryPairMapToFiber (n : ℕ+) (A : Set X) (a : A) :
    basedDiskBoundaryPairMap n A a → diskBoundaryPairMapFiber n A a
  | ⟨f, hfA, hfa⟩ =>
      ⟨⟨f, hfA⟩, Subtype.ext hfa⟩

/-- Reading the fiber condition as a value constraint at the chosen boundary basepoint recovers a
boundary-based pair map. -/
def diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap (n : ℕ+) (A : Set X) (a : A) :
    diskBoundaryPairMapFiber n A a → basedDiskBoundaryPairMap n A a
  | ⟨⟨f, hfA⟩, hfa⟩ =>
      ⟨f, hfA, congrArg Subtype.val hfa⟩

/-- The explicit map from boundary-based pair maps to the fiber over `a` has the expected left
inverse. -/
theorem diskBoundaryPairMapFiber_left_inv (n : ℕ+) (A : Set X) (a : A) :
    Function.LeftInverse
      (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a)
      (basedDiskBoundaryPairMapToFiber n A a) := by
  intro f
  cases f with
  | mk f hf =>
      cases hf with
      | intro hfA hfa =>
          apply Subtype.ext
          rfl

/-- The explicit map from the fiber over `a` back to boundary-based pair maps has the expected
right inverse. -/
theorem diskBoundaryPairMapFiber_right_inv (n : ℕ+) (A : Set X) (a : A) :
    Function.RightInverse
      (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a)
      (basedDiskBoundaryPairMapToFiber n A a) := by
  intro z
  cases z with
  | mk z hz =>
      cases z with
      | mk f hfA =>
          cases hz
          change
            basedDiskBoundaryPairMapToFiber n A
              ((diskBoundaryPairMapEvalAtBasepoint n A) ⟨f, hfA⟩)
              ⟨f, ⟨hfA, rfl⟩⟩
              =
            ⟨⟨f, hfA⟩, rfl⟩
          rfl

/-- The actual fiber over `a` of `diskBoundaryPairMapEvalAtBasepoint n A` is explicitly
equivalent to the space of maps of pairs `(CS^(n - 1), S^(n - 1)) → (X, A)` sending the chosen
boundary basepoint of `S^(n - 1)` to `a`. -/
def basedDiskBoundaryPairMapFiberEquiv (n : ℕ+) (A : Set X) (a : A) :
    basedDiskBoundaryPairMap n A a ≃ diskBoundaryPairMapFiber n A a where
  toFun := basedDiskBoundaryPairMapToFiber n A a
  invFun := diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a
  left_inv := diskBoundaryPairMapFiber_left_inv n A a
  right_inv := diskBoundaryPairMapFiber_right_inv n A a

/-- Unfolding `basedDiskBoundaryPairMapFiberEquiv n A a` gives the explicit equivalence between
boundary-based pair maps over `a` and the actual fiber of
`diskBoundaryPairMapEvalAtBasepoint n A` over `a`. -/
theorem basedDiskBoundaryPairMapFiberEquiv_def
    (n : ℕ+) (A : Set X) (a : A) :
    basedDiskBoundaryPairMapFiberEquiv n A a =
      Equiv.mk
        (basedDiskBoundaryPairMapToFiber n A a)
        (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a)
        (diskBoundaryPairMapFiber_left_inv n A a)
        (diskBoundaryPairMapFiber_right_inv n A a) := rfl

/-- The comparison `basedDiskBoundaryPairMapFiberEquiv n A a` sends a boundary-based pair map to
the same continuous map together with its chosen-basepoint equation viewed as a fiber equation. -/
@[simp] theorem basedDiskBoundaryPairMapFiberEquiv_toFun
    (n : ℕ+) (A : Set X) (a : A) :
    (basedDiskBoundaryPairMapFiberEquiv n A a).toFun =
      basedDiskBoundaryPairMapToFiber n A a := rfl

/-- The inverse comparison `basedDiskBoundaryPairMapFiberEquiv n A a` reads a point of the fiber
over `a` as the same continuous map together with its fiber equation viewed as the corresponding
chosen-basepoint condition. -/
@[simp] theorem basedDiskBoundaryPairMapFiberEquiv_symm_toFun
    (n : ℕ+) (A : Set X) (a : A) :
    (basedDiskBoundaryPairMapFiberEquiv n A a).symm.toFun =
      diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a := rfl

/-- The comparison `basedDiskBoundaryPairMapFiberEquiv n A a` sends a boundary-based pair map to
the same continuous map together with its chosen-basepoint equation viewed as a fiber equation. -/
@[simp] theorem basedDiskBoundaryPairMapFiberEquiv_apply
    (n : ℕ+) (A : Set X) (a : A) (f : basedDiskBoundaryPairMap n A a) :
    basedDiskBoundaryPairMapFiberEquiv n A a f = basedDiskBoundaryPairMapToFiber n A a f := rfl

/-- The inverse comparison `basedDiskBoundaryPairMapFiberEquiv n A a` sends a point of the fiber
over `a` to the same continuous map together with its fiber equation viewed as the corresponding
chosen-basepoint condition. -/
@[simp] theorem basedDiskBoundaryPairMapFiberEquiv_symm_apply
    (n : ℕ+) (A : Set X) (a : A) (f : diskBoundaryPairMapFiber n A a) :
    (basedDiskBoundaryPairMapFiberEquiv n A a).symm f =
      diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a f := rfl

/-- Two boundary-based pair maps are equivalent when they are homotopic through maps of the same
boundary-based type. -/
instance basedDiskBoundaryPairMapSetoid (n : ℕ+) (A : Set X) (a : A) :
    Setoid (basedDiskBoundaryPairMap n A a) where
  r f g := ContinuousMap.HomotopicWith f.1 g.1 (IsBasedDiskBoundaryPairMap n A a)
  iseqv :=
    ⟨fun f ↦ ContinuousMap.HomotopicWith.refl f.1 f.2,
      fun {_ _} hfg ↦ ContinuousMap.HomotopicWith.symm hfg,
      fun {_ _ _} hfg hgh ↦ ContinuousMap.HomotopicWith.trans hfg hgh⟩

/-- The quotient of boundary-based pair maps by homotopy through maps of the same boundary-based
type. -/
abbrev basedDiskBoundaryPairMapHomotopyClass (n : ℕ+) (A : Set X) (a : A) :=
  Quotient (basedDiskBoundaryPairMapSetoid n A a)

/-- Two points of the evaluation fiber over `a` are equivalent when their underlying continuous
maps are homotopic through boundary-based pair maps over `a`. -/
instance diskBoundaryPairMapFiberSetoid (n : ℕ+) (A : Set X) (a : A) :
    Setoid (diskBoundaryPairMapFiber n A a) where
  r z z' := ContinuousMap.HomotopicWith z.1.1 z'.1.1 (IsBasedDiskBoundaryPairMap n A a)
  iseqv :=
    ⟨fun z ↦
        ContinuousMap.HomotopicWith.refl z.1.1
          (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a z).2,
      fun {_ _} hzz' ↦ ContinuousMap.HomotopicWith.symm hzz',
      fun {_ _ _} hzz' hz'z'' ↦ ContinuousMap.HomotopicWith.trans hzz' hz'z''⟩

/-- The quotient of the evaluation fiber over `a` by homotopy through the same boundary-based
fiber condition. -/
abbrev diskBoundaryPairMapFiberHomotopyClass (n : ℕ+) (A : Set X) (a : A) :=
  Quotient (diskBoundaryPairMapFiberSetoid n A a)

/-- The path-component class of a point of the evaluation fiber over `a`. -/
def diskBoundaryPairMapFiberPathClass (n : ℕ+) (A : Set X) (a : A) :
    diskBoundaryPairMapFiber n A a → ZerothHomotopy (diskBoundaryPairMapFiber n A a) :=
  Quotient.mk (pathSetoid _)

/-- A homotopy through boundary-based pair maps over `a` determines a single path component of the
evaluation fiber over `a`. -/
theorem diskBoundaryPairMapFiberPathClass_eq_of_homotopy
    (n : ℕ+) (A : Set X) (a : A)
    {z z' : diskBoundaryPairMapFiber n A a}
    (hzz' : (diskBoundaryPairMapFiberSetoid n A a).r z z') :
    diskBoundaryPairMapFiberPathClass n A a z =
      diskBoundaryPairMapFiberPathClass n A a z' := sorry

/-- A path in the evaluation fiber over `a` determines a single homotopy class through the same
boundary-based fiber condition. -/
theorem diskBoundaryPairMapFiberHomotopyClass_eq_of_joined
    (n : ℕ+) (A : Set X) (a : A)
    {z z' : diskBoundaryPairMapFiber n A a} (hzz' : Joined z z') :
    (Quotient.mk (diskBoundaryPairMapFiberSetoid n A a) z :
      diskBoundaryPairMapFiberHomotopyClass n A a) =
        Quotient.mk (diskBoundaryPairMapFiberSetoid n A a) z' := sorry

/-- The source-facing quotient of the evaluation fiber by homotopy through boundary-based pair
maps maps to the canonical path-component quotient of the fiber space itself. -/
def diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy
    (n : ℕ+) (A : Set X) (a : A) :
    diskBoundaryPairMapFiberHomotopyClass n A a →
      ZerothHomotopy (diskBoundaryPairMapFiber n A a) :=
  Quotient.lift
    (diskBoundaryPairMapFiberPathClass n A a)
    (fun _ _ hzz' ↦ diskBoundaryPairMapFiberPathClass_eq_of_homotopy n A a hzz')

/-- The canonical path-component quotient of the evaluation fiber maps back to the source-facing
quotient by homotopy through boundary-based pair maps. -/
def zerothHomotopyToDiskBoundaryPairMapFiberHomotopyClass
    (n : ℕ+) (A : Set X) (a : A) :
    ZerothHomotopy (diskBoundaryPairMapFiber n A a) →
      diskBoundaryPairMapFiberHomotopyClass n A a :=
  Quotient.lift
    (fun z : diskBoundaryPairMapFiber n A a ↦
      (Quotient.mk (diskBoundaryPairMapFiberSetoid n A a) z :
        diskBoundaryPairMapFiberHomotopyClass n A a))
    (fun _ _ hzz' ↦ diskBoundaryPairMapFiberHomotopyClass_eq_of_joined n A a hzz')

/-- The source-facing fiber homotopy quotient and the canonical path-component quotient of the
evaluation fiber are inverse identifications. -/
theorem diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy_left_inv
    (n : ℕ+) (A : Set X) (a : A) :
    Function.LeftInverse
      (zerothHomotopyToDiskBoundaryPairMapFiberHomotopyClass n A a)
      (diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy n A a) := sorry

/-- The source-facing fiber homotopy quotient and the canonical path-component quotient of the
evaluation fiber are inverse identifications. -/
theorem diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy_right_inv
    (n : ℕ+) (A : Set X) (a : A) :
    Function.RightInverse
      (zerothHomotopyToDiskBoundaryPairMapFiberHomotopyClass n A a)
      (diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy n A a) := sorry

/-- The source-facing quotient `diskBoundaryPairMapFiberHomotopyClass n A a` is canonically the
path-component quotient `ZerothHomotopy (diskBoundaryPairMapFiber n A a)` of the evaluation
fiber. -/
def diskBoundaryPairMapFiberHomotopyClassEquivZerothHomotopy
    (n : ℕ+) (A : Set X) (a : A) :
    diskBoundaryPairMapFiberHomotopyClass n A a ≃
      ZerothHomotopy (diskBoundaryPairMapFiber n A a) where
  toFun := diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy n A a
  invFun := zerothHomotopyToDiskBoundaryPairMapFiberHomotopyClass n A a
  left_inv := diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy_left_inv n A a
  right_inv := diskBoundaryPairMapFiberHomotopyClassToZerothHomotopy_right_inv n A a

/-- The explicit map from boundary-based pair maps to the evaluation fiber over `a` respects the
corresponding homotopy relations. -/
theorem basedDiskBoundaryPairMapToFiber_respects
    (n : ℕ+) (A : Set X) (a : A)
    {f g : basedDiskBoundaryPairMap n A a}
    (hfg : (basedDiskBoundaryPairMapSetoid n A a).r f g) :
    (diskBoundaryPairMapFiberSetoid n A a).r
      (basedDiskBoundaryPairMapToFiber n A a f)
      (basedDiskBoundaryPairMapToFiber n A a g) := by
  rcases f with ⟨f, hfA, hfa⟩
  rcases g with ⟨g, hgA, hga⟩
  simpa [basedDiskBoundaryPairMapToFiber] using hfg

/-- The explicit map from the evaluation fiber over `a` back to boundary-based pair maps respects
the corresponding homotopy relations. -/
theorem diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap_respects
    (n : ℕ+) (A : Set X) (a : A)
    {f g : diskBoundaryPairMapFiber n A a}
    (hfg : (diskBoundaryPairMapFiberSetoid n A a).r f g) :
    (basedDiskBoundaryPairMapSetoid n A a).r
      (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a f)
      (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a g) := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          change ContinuousMap.HomotopicWith
            (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a ⟨f, hf⟩).1
            (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a ⟨g, hg⟩).1
            (IsBasedDiskBoundaryPairMap n A a)
          simpa [diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap] using hfg

/-- Passing to quotients sends a boundary-based pair-map class over `a` to the corresponding
homotopy class in the actual evaluation fiber over `a`. -/
def basedDiskBoundaryPairMapHomotopyClassToDiskBoundaryPairMapFiberHomotopyClass
    (n : ℕ+) (A : Set X) (a : A) :
    basedDiskBoundaryPairMapHomotopyClass n A a →
      diskBoundaryPairMapFiberHomotopyClass n A a :=
  Quotient.map
    (basedDiskBoundaryPairMapToFiber n A a)
    (fun _ _ hfg ↦ basedDiskBoundaryPairMapToFiber_respects n A a hfg)

/-- Passing to quotients sends a fiber homotopy class over `a` back to the corresponding
boundary-based pair-map class. -/
def diskBoundaryPairMapFiberHomotopyClassToBasedDiskBoundaryPairMapHomotopyClass
    (n : ℕ+) (A : Set X) (a : A) :
    diskBoundaryPairMapFiberHomotopyClass n A a →
      basedDiskBoundaryPairMapHomotopyClass n A a :=
  Quotient.map
    (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a)
    (fun _ _ hfg ↦ diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap_respects n A a hfg)

/-- The quotient map induced by `basedDiskBoundaryPairMapToFiber n A a` has the expected left
inverse. -/
theorem basedDiskBoundaryPairMapHomotopyClass_left_inv
    (n : ℕ+) (A : Set X) (a : A) :
    Function.LeftInverse
      (diskBoundaryPairMapFiberHomotopyClassToBasedDiskBoundaryPairMapHomotopyClass n A a)
      (basedDiskBoundaryPairMapHomotopyClassToDiskBoundaryPairMapFiberHomotopyClass n A a) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro f
  change
    Quotient.mk _ (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a
      (basedDiskBoundaryPairMapToFiber n A a f)) =
      Quotient.mk _ f
  rw [diskBoundaryPairMapFiber_left_inv]

/-- The quotient map induced by `basedDiskBoundaryPairMapToFiber n A a` has the expected right
inverse. -/
theorem basedDiskBoundaryPairMapHomotopyClass_right_inv
    (n : ℕ+) (A : Set X) (a : A) :
    Function.RightInverse
      (diskBoundaryPairMapFiberHomotopyClassToBasedDiskBoundaryPairMapHomotopyClass n A a)
      (basedDiskBoundaryPairMapHomotopyClassToDiskBoundaryPairMapFiberHomotopyClass n A a) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro f
  change
    Quotient.mk _ (basedDiskBoundaryPairMapToFiber n A a
      (diskBoundaryPairMapFiberToBasedDiskBoundaryPairMap n A a f)) =
      Quotient.mk _ f
  rw [diskBoundaryPairMapFiber_right_inv]

/-- The explicit equivalence `basedDiskBoundaryPairMapFiberEquiv n A a` induces the corresponding
equivalence on homotopy classes. -/
def basedDiskBoundaryPairMapHomotopyClassEquivDiskBoundaryPairMapFiberHomotopyClass
    (n : ℕ+) (A : Set X) (a : A) :
    basedDiskBoundaryPairMapHomotopyClass n A a ≃
      diskBoundaryPairMapFiberHomotopyClass n A a where
  toFun := basedDiskBoundaryPairMapHomotopyClassToDiskBoundaryPairMapFiberHomotopyClass n A a
  invFun := diskBoundaryPairMapFiberHomotopyClassToBasedDiskBoundaryPairMapHomotopyClass n A a
  left_inv := basedDiskBoundaryPairMapHomotopyClass_left_inv n A a
  right_inv := basedDiskBoundaryPairMapHomotopyClass_right_inv n A a

/-- Applying the quotient equivalence induced by `basedDiskBoundaryPairMapFiberEquiv n A a`
amounts to passing to the corresponding fiber homotopy class. -/
theorem basedDiskBoundaryPairMapHomotopyClassEquivDiskBoundaryPairMapFiberHomotopyClass_apply
    (n : ℕ+) (A : Set X) (a : A)
    (f : basedDiskBoundaryPairMapHomotopyClass n A a) :
    basedDiskBoundaryPairMapHomotopyClassEquivDiskBoundaryPairMapFiberHomotopyClass n A a f =
      basedDiskBoundaryPairMapHomotopyClassToDiskBoundaryPairMapFiberHomotopyClass n A a f := rfl

/-- Construction 9.5.5 (2): any explicit comparison from the Chapter 9 owner
`relativeHomotopyGroup n A a` to the boundary-based disk model yields the corresponding
comparison with homotopy classes in the actual evaluation fiber over `a`. -/
def relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv
    (n : ℕ+) (A : Set X) (a : A)
    (e : relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a) :
    relativeHomotopyGroup n A a ≃ diskBoundaryPairMapFiberHomotopyClass n A a :=
  e.trans (basedDiskBoundaryPairMapHomotopyClassEquivDiskBoundaryPairMapFiberHomotopyClass n A a)

/-- Applying `relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a e` amounts to first apply
the supplied comparison with the boundary-based disk model and then pass to the corresponding
fiber homotopy class. -/
@[simp] theorem relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv_apply
    (n : ℕ+) (A : Set X) (a : A)
    (e : relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)
    (x : relativeHomotopyGroup n A a) :
    relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a e x =
      basedDiskBoundaryPairMapHomotopyClassToDiskBoundaryPairMapFiberHomotopyClass n A a (e x) :=
  rfl
