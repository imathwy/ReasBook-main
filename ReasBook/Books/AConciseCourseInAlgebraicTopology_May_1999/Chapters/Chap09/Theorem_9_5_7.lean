import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_6

open scoped Topology Topology.Homotopy

noncomputable section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set X} {B : Set Y} {n : ℕ+}
variable
  (eA :
    ∀ a : A, relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)
  (eB :
    ∀ b : B, relativeHomotopyGroup n B b ≃ basedDiskBoundaryPairMapHomotopyClass n B b)

-- Semantic recall via `lean_leansearch`: `α.map g` is the canonical map on path classes, while
-- local Chapter 9 precedent already fixes `relativeHomotopyGroup` and
-- `relativeHomotopyGroupEquivOfPathClass` as the public owners for relative homotopy groups and
-- change of basepoint, relative to explicit disk-boundary model comparisons.

/-- A map of pairs `(X, A) → (Y, B)` induces a continuous map `A → B` on the distinguished
subspaces. -/
abbrev pairMapSubspace {A : Set X} {B : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨Set.MapsTo.restrict (⇑f) A B hf, Continuous.restrict hf f.continuous⟩

@[simp] theorem pairMapSubspace_apply {A : Set X} {B : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f A B) (a : A) :
    pairMapSubspace f hf a = ⟨f a.1, hf a.2⟩ := rfl

/-- Postcomposition with a map of pairs preserves the disk-boundary condition. -/
theorem isDiskBoundaryPairMap_comp_ofPairMap {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (g : diskBoundaryPairMap n A) :
    IsDiskBoundaryPairMap n B (f.comp g.1) :=
  fun y ↦ hf (g.2 y)

/-- Postcomposition with a map of pairs sends disk-boundary pair maps in `(X, A)` to
disk-boundary pair maps in `(Y, B)`. -/
def diskBoundaryPairMapMapOfPairMap {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    C(diskBoundaryPairMap n A, diskBoundaryPairMap n B) where
  toFun g := ⟨f.comp g.1, isDiskBoundaryPairMap_comp_ofPairMap n f hf g⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk
      (fun g ↦ isDiskBoundaryPairMap_comp_ofPairMap n f hf g)

@[simp] theorem diskBoundaryPairMapMapOfPairMap_apply {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (g : diskBoundaryPairMap n A) :
    diskBoundaryPairMapMapOfPairMap n f hf g = ⟨f.comp g.1, fun y ↦ hf (g.2 y)⟩ := rfl

@[simp] theorem diskBoundaryPairMapEvalAtBasepoint_mapOfPairMap {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (g : diskBoundaryPairMap n A) :
    diskBoundaryPairMapEvalAtBasepoint n B (diskBoundaryPairMapMapOfPairMap n f hf g) =
      pairMapSubspace f hf (diskBoundaryPairMapEvalAtBasepoint n A g) := rfl

/-- Postcomposition with a map of pairs preserves the corresponding evaluation fibers. -/
theorem diskBoundaryPairMapMapOfPairMap_mapsToFiber {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (a : A) :
    Set.MapsTo
      (diskBoundaryPairMapMapOfPairMap n f hf)
      (diskBoundaryPairMapFiber n A a)
      (diskBoundaryPairMapFiber n B (pairMapSubspace f hf a)) := by
  intro z hz
  change diskBoundaryPairMapEvalAtBasepoint n A z = a at hz
  change diskBoundaryPairMapEvalAtBasepoint n B
      (diskBoundaryPairMapMapOfPairMap n f hf z) = pairMapSubspace f hf a
  apply Subtype.ext
  change f ((diskBoundaryPairMapEvalAtBasepoint n A z).1) = f a.1
  simpa using congrArg f (congrArg Subtype.val hz)

/-- Postcomposition with a map of pairs sends the evaluation fiber for `(X, A)` over `a` to the
evaluation fiber for `(Y, B)` over `f(a)`. -/
def diskBoundaryPairMapFiberMapOfPairMap {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (a : A) :
    C(diskBoundaryPairMapFiber n A a, diskBoundaryPairMapFiber n B (pairMapSubspace f hf a)) :=
  ⟨Set.MapsTo.restrict
      (diskBoundaryPairMapMapOfPairMap n f hf)
      (diskBoundaryPairMapFiber n A a)
      (diskBoundaryPairMapFiber n B (pairMapSubspace f hf a))
      (diskBoundaryPairMapMapOfPairMap_mapsToFiber n f hf a),
    Continuous.restrict
      (diskBoundaryPairMapMapOfPairMap_mapsToFiber n f hf a)
      (diskBoundaryPairMapMapOfPairMap n f hf).continuous⟩

/-- The fiber map induced by a map of pairs respects the boundary-based homotopy relation on the
evaluation fibers. -/
theorem diskBoundaryPairMapFiberMapOfPairMap_respects {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (a : A)
    {z z' : diskBoundaryPairMapFiber n A a}
    (hzz' : (diskBoundaryPairMapFiberSetoid n A a).r z z') :
    (diskBoundaryPairMapFiberSetoid n B (pairMapSubspace f hf a)).r
      (diskBoundaryPairMapFiberMapOfPairMap n f hf a z)
      (diskBoundaryPairMapFiberMapOfPairMap n f hf a z') := sorry

/-- A map of pairs induces a map on the homotopy classes of the evaluation fibers from
Construction 9.5.5. -/
def diskBoundaryPairMapFiberHomotopyClassMapOfPairMap {A : Set X} {B : Set Y}
    (n : ℕ+) (f : C(X, Y)) (hf : Set.MapsTo f A B) (a : A) :
    diskBoundaryPairMapFiberHomotopyClass n A a →
      diskBoundaryPairMapFiberHomotopyClass n B (pairMapSubspace f hf a) :=
  Quotient.map
    (diskBoundaryPairMapFiberMapOfPairMap n f hf a)
    (fun _ _ hzz' ↦ diskBoundaryPairMapFiberMapOfPairMap_respects n f hf a hzz')

/-- Relative to the supplied disk-boundary model comparisons, a map of pairs induces the
corresponding map on the Chapter 9 relative homotopy groups. -/
def relativeHomotopyGroupMapOfPairMap
    (f : C(X, Y)) (hf : Set.MapsTo f A B) (a : A) :
    relativeHomotopyGroup n A a →
      relativeHomotopyGroup n B (pairMapSubspace f hf a) :=
  (relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n B (pairMapSubspace f hf a)
      (eB (pairMapSubspace f hf a))).symm ∘
    diskBoundaryPairMapFiberHomotopyClassMapOfPairMap n f hf a ∘
      relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a (eA a)

/-- Theorem 9.5.7: for a map of pairs `f : (X, A) → (Y, B)` and a path class `α` in `A`,
change of basepoint commutes with the induced map on relative homotopy groups. Equivalently, the
square whose horizontal arrows are `τ[α]` and `τ[α.map (pairMapSubspace f hf)]` and whose
vertical arrows are the two maps `f_*` commutes, relative to the supplied disk-boundary model
comparisons. -/
theorem relativeHomotopyGroupMapOfPairMap_comp_equivOfPathClass
    (f : C(X, Y)) (hf : Set.MapsTo f A B) {a a' : A}
    (α : Path.Homotopic.Quotient a a') :
    relativeHomotopyGroupMapOfPairMap eA eB f hf a' ∘
        relativeHomotopyGroupEquivOfPathClass eA α =
      relativeHomotopyGroupEquivOfPathClass eB
          (α.map (pairMapSubspace f hf)) ∘
        relativeHomotopyGroupMapOfPairMap eA eB f hf a := sorry

/-- Applying Theorem 9.5.7 to an element gives the pointwise basepoint-change compatibility of
the induced map of pairs on relative homotopy groups. -/
theorem relativeHomotopyGroupMapOfPairMap_comp_equivOfPathClass_apply
    (f : C(X, Y)) (hf : Set.MapsTo f A B) {a a' : A}
    (α : Path.Homotopic.Quotient a a') (x : relativeHomotopyGroup n A a) :
    relativeHomotopyGroupMapOfPairMap eA eB f hf a'
        (relativeHomotopyGroupEquivOfPathClass eA α x) =
      relativeHomotopyGroupEquivOfPathClass eB
          (α.map (pairMapSubspace f hf))
          (relativeHomotopyGroupMapOfPairMap eA eB f hf a x) := by
  exact congrFun (relativeHomotopyGroupMapOfPairMap_comp_equivOfPathClass eA eB f hf α) x
