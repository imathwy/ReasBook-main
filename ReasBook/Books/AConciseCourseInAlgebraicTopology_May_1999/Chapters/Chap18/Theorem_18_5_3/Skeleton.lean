module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex

public section

open Topology
open scoped Topology

noncomputable section

universe u

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable [CWComplex (Set.univ : Set X)]
variable (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
variable [Topology.RelCWComplex (Set.univ : Set X) (A : Set X)]
variable {Y : Type u} [TopologicalSpace Y]

/-- The canonical relative `n`-skeleton `X^n` determined by the pair `(X, A)`. This short owner is
the reusable item-local vocabulary for the repeated type expression
`Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)`. -/
@[expose] abbrev relativePairSkeleton (n : ℕ) :=
  Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)

/-- The canonical inclusion `X^m ↪ X^n` of the chosen relative skeleta for `m ≤ n`. -/
@[expose]
def relativeSkeletonInclusion (m n : ℕ) (hmn : m ≤ n) :
    C(relativePairSkeleton A m, relativePairSkeleton A n) where
  toFun x :=
    ⟨x.1, Topology.RelCWComplex.skeleton_mono (ENat.coe_le_coe.2 hmn) x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Applying `relativeSkeletonInclusion` only changes the target skeletal stage. -/
@[simp] theorem relativeSkeletonInclusion_apply
    (m n : ℕ) (hmn : m ≤ n) (x : relativePairSkeleton A m) :
    relativeSkeletonInclusion A m n hmn x =
      ⟨x.1, Topology.RelCWComplex.skeleton_mono (ENat.coe_le_coe.2 hmn) x.2⟩ :=
  rfl

/-- Restrict a map `f : X^n ⟶ Y` to `X^(n - 1)` along the canonical skeletal inclusion
`X^(n - 1) ↪ X^n`. -/
@[expose]
def relativeSkeletonRestriction (n : ℕ) (f : C(relativePairSkeleton A n, Y)) :
    C(relativePairSkeleton A (n - 1), Y) :=
  f.comp (relativeSkeletonInclusion A (n - 1) n (Nat.sub_le n 1))

/-- Unfolding `relativeSkeletonRestriction` shows that it is composition with the canonical
skeletal inclusion `X^(n - 1) ↪ X^n`. -/
@[simp] theorem relativeSkeletonRestriction_def
    (n : ℕ) (f : C(relativePairSkeleton A n, Y)) :
    relativeSkeletonRestriction A n f =
      f.comp (relativeSkeletonInclusion A (n - 1) n (Nat.sub_le n 1)) :=
  rfl

end
