import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3.Skeleton

open Topology
open scoped TopCat Topology Topology.Homotopy
open scoped CellularCohomology

noncomputable section

universe u

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable [CWComplex (Set.univ : Set X)]
variable (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
variable [Topology.RelCWComplex (Set.univ : Set X) (A : Set X)]
variable {Y : Type u} [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: no exact obstruction-theory theorem surfaced, so this
-- file follows local Chapter 18 precedent `relativeSkeletonRestriction` /
-- `Hˢᶜ[n](X, A, data; π)` together with mathlib's canonical relative-homotopy owner
-- `ContinuousMap.HomotopyRel`.

/-- The points of the relative `n`-skeleton whose underlying points lie in the distinguished
subcomplex `A`. -/
def relativeBaseInSkeleton (n : ℕ) : Set (relativePairSkeleton A n) :=
  (Subtype.val : relativePairSkeleton A n → X) ⁻¹' (A : Set X)

/-- Membership in `relativeBaseInSkeleton A n` means exactly that the underlying point lies in
`A`. -/
@[simp] theorem mem_relativeBaseInSkeleton (n : ℕ) (x : relativePairSkeleton A n) :
    x ∈ relativeBaseInSkeleton A n ↔ x.1 ∈ (A : Set X) :=
  Iff.rfl

/-- The canonical inclusion `X^(n - 1) ↪ X^n` preserves the distinguished base subset coming from
`A`. -/
theorem relativeSkeletonInclusion_mem_relativeBaseInSkeleton
    (n : ℕ) {x : relativePairSkeleton A (n - 1)}
    (hx : x ∈ relativeBaseInSkeleton A (n - 1)) :
    relativeSkeletonInclusion A (n - 1) n (Nat.sub_le n 1) x ∈
      relativeBaseInSkeleton A n := by
  simpa [relativeSkeletonInclusion_apply] using hx

/-- Restrict a homotopy rel `A` on `X^n` to the predecessor skeleton `X^(n - 1)`. -/
def relativeSkeletonHomotopyRestriction (n : ℕ)
    {f f' : C(relativePairSkeleton A n, Y)}
    (H : f.HomotopyRel f' (relativeBaseInSkeleton A n)) :
    (relativeSkeletonRestriction A n f).HomotopyRel
      (relativeSkeletonRestriction A n f')
      (relativeBaseInSkeleton A (n - 1)) where
  toHomotopy :=
    H.toHomotopy.compContinuousMap
      (relativeSkeletonInclusion A (n - 1) n (Nat.sub_le n 1))
  prop' t x hx :=
    H.prop t
      (relativeSkeletonInclusion A (n - 1) n (Nat.sub_le n 1) x)
      (relativeSkeletonInclusion_mem_relativeBaseInSkeleton A n hx)

/-- Unfolding `relativeSkeletonHomotopyRestriction` shows that its underlying homotopy is obtained
by precomposing with the canonical inclusion `X^(n - 1) ↪ X^n`. -/
theorem relativeSkeletonHomotopyRestriction_toHomotopy (n : ℕ)
    {f f' : C(relativePairSkeleton A n, Y)}
    (H : f.HomotopyRel f' (relativeBaseInSkeleton A n)) :
    (relativeSkeletonHomotopyRestriction A n H).toHomotopy =
      H.toHomotopy.compContinuousMap
        (relativeSkeletonInclusion A (n - 1) n (Nat.sub_le n 1)) :=
  rfl

/-- A chosen homotopy on `X^(n - 1)` extends rel `A` over `X^n` when it is the restriction of a
homotopy rel `A` between the maps on `X^n`. -/
def extendsRelativeSkeletonHomotopy (n : ℕ)
    (f f' : C(relativePairSkeleton A n, Y))
    (H :
      (relativeSkeletonRestriction A n f).HomotopyRel
        (relativeSkeletonRestriction A n f')
        (relativeBaseInSkeleton A (n - 1))) : Prop :=
  ∃ K : f.HomotopyRel f' (relativeBaseInSkeleton A n),
    (relativeSkeletonHomotopyRestriction A n K).toHomotopy = H.toHomotopy

/-- Unfolding `extendsRelativeSkeletonHomotopy` expresses extension rel `A` as the existence of a
homotopy on `X^n` whose restriction has the prescribed boundary homotopy. -/
theorem extendsRelativeSkeletonHomotopy_iff (n : ℕ)
    (f f' : C(relativePairSkeleton A n, Y))
    (H :
      (relativeSkeletonRestriction A n f).HomotopyRel
        (relativeSkeletonRestriction A n f')
        (relativeBaseInSkeleton A (n - 1))) :
    extendsRelativeSkeletonHomotopy A n f f' H ↔
      ∃ K : f.HomotopyRel f' (relativeBaseInSkeleton A n),
        (relativeSkeletonHomotopyRestriction A n K).toHomotopy = H.toHomotopy :=
  Iff.rfl

/-- A cohomology class is an obstruction class for extending the chosen relative boundary homotopy
`H` between `f` and `f'` when its vanishing detects whether `H` extends rel `A` over `X^n`. -/
def IsRelativeSkeletonHomotopyExtensionObstructionClass
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f f' : C(relativePairSkeleton A n, Y))
    (H :
      (relativeSkeletonRestriction A n f).HomotopyRel
        (relativeSkeletonRestriction A n f')
        (relativeBaseInSkeleton A (n - 1)))
    (c_H : Hˢᶜ[n](X, A, data; Additive (π_ n Y y₀))) : Prop :=
  c_H = 0 ↔ extendsRelativeSkeletonHomotopy A n f f' H

/-- Unfolding `IsRelativeSkeletonHomotopyExtensionObstructionClass` identifies it with the
vanishing criterion for the chosen class `c_H`. -/
theorem isRelativeSkeletonHomotopyExtensionObstructionClass_iff
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f f' : C(relativePairSkeleton A n, Y))
    (H :
      (relativeSkeletonRestriction A n f).HomotopyRel
        (relativeSkeletonRestriction A n f')
        (relativeBaseInSkeleton A (n - 1)))
    (c_H : Hˢᶜ[n](X, A, data; Additive (π_ n Y y₀))) :
    IsRelativeSkeletonHomotopyExtensionObstructionClass A n y₀ data f f' H c_H ↔
      (c_H = 0 ↔ extendsRelativeSkeletonHomotopy A n f f' H) :=
  Iff.rfl

/-- Any obstruction class in the sense of
`IsRelativeSkeletonHomotopyExtensionObstructionClass A n y₀ data f f' H c_H`
vanishes exactly when the chosen boundary homotopy extends rel `A` over `X^n`. -/
theorem isRelativeSkeletonHomotopyExtensionObstructionClass_vanishing_iff
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f f' : C(relativePairSkeleton A n, Y))
    (H :
      (relativeSkeletonRestriction A n f).HomotopyRel
        (relativeSkeletonRestriction A n f')
        (relativeBaseInSkeleton A (n - 1)))
    {c_H : Hˢᶜ[n](X, A, data; Additive (π_ n Y y₀))}
    (hc_H : IsRelativeSkeletonHomotopyExtensionObstructionClass A n y₀ data f f' H c_H) :
    c_H = 0 ↔ extendsRelativeSkeletonHomotopy A n f f' H :=
  hc_H

-- As in Theorem 18.5.3, the actual obstruction-class construction is kept external to this file.
-- The source-facing theorem therefore records the vanishing criterion for a class attached to
-- `f`, `f'`, and `H`, while `IsRelativeSkeletonHomotopyExtensionObstructionClass` is the
-- companion API for a chosen class.

/-- Theorem 18.5.4. Given a homotopy `H` between the restrictions of `f, f' : X^n ⟶ Y` to
`X^(n - 1)`, fixed on `A`, there exists an obstruction class
`c_H : Hˢᶜ[n](X, A, data; Additive (π_ n Y y₀))` attached to `H` whose
vanishing is equivalent to extending `H` rel `A` over `X^n`. As in
`relativeSkeletonExtensionObstructionCriterion`, the source writes an explicit `1 ≤ n`
hypothesis, but in Lean that condition is absorbed by the ambient coefficient-group assumption
`[CommGroup (π_ n Y y₀)]`. -/
theorem relativeSkeletonHomotopyExtensionObstructionCriterion
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f f' : C(relativePairSkeleton A n, Y))
    (H :
      (relativeSkeletonRestriction A n f).HomotopyRel
        (relativeSkeletonRestriction A n f')
        (relativeBaseInSkeleton A (n - 1))) :
    ∃ c_H : Hˢᶜ[n](X, A, data; Additive (π_ n Y y₀)),
      IsRelativeSkeletonHomotopyExtensionObstructionClass A n y₀ data f f' H c_H := sorry

end
