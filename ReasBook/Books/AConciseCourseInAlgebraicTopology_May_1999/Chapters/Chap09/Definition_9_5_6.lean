import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

open Path.Homotopic.Quotient
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]
variable {A : Set X} {n : ℕ+}
variable
  (e :
    ∀ a : A, relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)

/-
The former implementation below applied Chapter 7 fiber translation directly to the raw
compact-open pair-mapping space. That total space is not the May-category mapping-space owner.

/-- A homotopy class of continuous maps induces a map on path components. -/
private def zerothHomotopyMapClass {Y : Type u} {Z : Type u}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (τ : continuousMapHomotopyClasses Y Z) :
    ZerothHomotopy Y → ZerothHomotopy Z :=
  Quotient.liftOn τ
    zerothHomotopyMap
    (fun _ _ hfg ↦ zerothHomotopyMap_eq_of_homotopic hfg)

/-- Transport along a path class in `A` induces a map on the path components of the evaluation
fibers of `diskBoundaryPairMapEvalAtBasepoint n A`. -/
private def diskBoundaryPairMapFiberZerothHomotopyMap
    (n : ℕ+) (A : Set X) {a a' : A} (α : Path.Homotopic.Quotient a a') :
    ZerothHomotopy (diskBoundaryPairMapFiber n A a) →
      ZerothHomotopy (diskBoundaryPairMapFiber n A a') :=
  zerothHomotopyMapClass
    (fiberTranslationClass (diskBoundaryPairMapEvalAtBasepoint n A) α)
-/

/-- Transport along a path class in `A` induces an equivalence on the path components of the
evaluation fibers of `diskBoundaryPairMapEvalAtBasepoint n A`. -/
private noncomputable def diskBoundaryPairMapFiberZerothHomotopyEquivOfPathClass
    (n : ℕ+) (A : Set X) {a a' : A} (α : Path.Homotopic.Quotient a a') :
    ZerothHomotopy (diskBoundaryPairMapFiber n A a) ≃
      ZerothHomotopy (diskBoundaryPairMapFiber n A a') := by
  sorry

-- Semantic recall via `lean_leansearch`: mathlib exposes basepoint-change on `π₁` via
-- `FundamentalGroup.fundamentalGroupMulEquivOfPath`, while local Chapter 9 precedent models
-- `π_n(X, A, a)` by the fiber of `diskBoundaryPairMapEvalAtBasepoint n A`. This item therefore
-- uses Construction 9.5.5 together with an explicit comparison to the boundary-based disk model
-- and the path-class fiber transport from Theorem 7.6.5.

/-- A path class in `A` gives an equivalence between the homotopy classes of the corresponding
fibers of `diskBoundaryPairMapEvalAtBasepoint n A`. -/
def diskBoundaryPairMapFiberHomotopyClassEquivOfPathClass
    (n : ℕ+) (A : Set X) {a a' : A} (α : Path.Homotopic.Quotient a a') :
    diskBoundaryPairMapFiberHomotopyClass n A a ≃
      diskBoundaryPairMapFiberHomotopyClass n A a' :=
  (diskBoundaryPairMapFiberHomotopyClassEquivZerothHomotopy n A a).trans
    ((diskBoundaryPairMapFiberZerothHomotopyEquivOfPathClass n A α).trans
      (diskBoundaryPairMapFiberHomotopyClassEquivZerothHomotopy n A a').symm)

/-- Transport along a path class in `A` induces a map on the homotopy classes of the fibers of
`diskBoundaryPairMapEvalAtBasepoint n A`. -/
def diskBoundaryPairMapFiberHomotopyClassMap
    (n : ℕ+) (A : Set X) {a a' : A} (α : Path.Homotopic.Quotient a a') :
    diskBoundaryPairMapFiberHomotopyClass n A a →
      diskBoundaryPairMapFiberHomotopyClass n A a' :=
  diskBoundaryPairMapFiberHomotopyClassEquivOfPathClass n A α

/-- Definition 9.5.6. A path class `α` in `A` from `a` to `a'` induces the basepoint-change
isomorphism `τ[α] : π_n(X, A, a) ≃ π_n(X, A, a')`, obtained by transporting the evaluation fiber
of Construction 9.5.5 along `α` and comparing with the supplied disk-boundary model
identifications `e a` and `e a'`. -/
def relativeHomotopyGroupEquivOfPathClass
    {a a' : A} (α : Path.Homotopic.Quotient a a') :
    relativeHomotopyGroup n A a ≃ relativeHomotopyGroup n A a' :=
  (relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a (e a)).trans
    ((diskBoundaryPairMapFiberHomotopyClassEquivOfPathClass n A α).trans
      (relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a' (e a')).symm)

/-- Applying `relativeHomotopyGroupEquivOfPathClass` amounts to passing to the
Construction 9.5.5 fiber model determined by `e`, transporting along `α`, and comparing back. -/
theorem relativeHomotopyGroupEquivOfPathClass_apply
    {a a' : A} (α : Path.Homotopic.Quotient a a')
    (x : relativeHomotopyGroup n A a) :
    relativeHomotopyGroupEquivOfPathClass e α x =
      (relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a' (e a')).symm
        (diskBoundaryPairMapFiberHomotopyClassMap n A α
          (relativeHomotopyGroupDiskBoundaryPairMapFiberEquiv n A a (e a) x)) := sorry
