import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_0_1 (from Chap01) -/
open Set
open scoped Pointwise

universe u

section Additive

variable {X : Type u} [AddCommGroup X]

/-- Pointwise addition of two subsets of an additive commutative group is the set of all
pairwise sums. -/
theorem pointwise_add_eq_setOf_add (C D : Set X) :
    C + D = {x | ∃ c ∈ C, ∃ d ∈ D, c + d = x} := by
  ext x
  simp [Set.mem_add]

/-- Pointwise subtraction of two subsets of an additive commutative group is the set of all
pairwise differences. -/
theorem pointwise_sub_eq_setOf_sub (C D : Set X) :
    C - D = {x | ∃ c ∈ C, ∃ d ∈ D, c - d = x} := by
  ext x
  simp [Set.mem_sub]

end Additive

section Module

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Scalar multiplication of a singleton subset by a set of scalars is the set of all scalar
multiples of the chosen vector. -/
theorem set_smul_singleton_eq_setOf_smul (Λ : Set ℝ) (z : X) :
    Λ • ({z} : Set X) = {x | ∃ r ∈ Λ, r • z = x} := by
  ext x
  simp

end Module

/-! ### Text_1_0_2 (from Chap01) -/
open Set
open scoped Pointwise

universe u

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.2 (1): A subset of a real vector space is a cone when it equals its set of positive
real multiples. -/
def IsCone (C : Set X) : Prop :=
  C = (Ioi (0 : ℝ) : Set ℝ) • C

/-- A cone is exactly a set equal to its positive scalar multiples. -/
theorem isCone_iff {C : Set X} :
    IsCone C ↔ C = (Ioi (0 : ℝ) : Set ℝ) • C :=
  Iff.rfl

/-- Text 1.0.2 (2): A subset of a real vector space is a ray when it is the set of nonnegative
real multiples of some nonzero vector. -/
def IsRay (C : Set X) : Prop :=
  ∃ u : X, u ≠ 0 ∧ C = (Ici (0 : ℝ) : Set ℝ) • ({u} : Set X)

/-- A ray is exactly a set of the form `ℝ_+ • {u}` for some nonzero vector `u`. -/
theorem isRay_iff {C : Set X} :
    IsRay C ↔ ∃ u : X, u ≠ 0 ∧ C = (Ici (0 : ℝ) : Set ℝ) • ({u} : Set X) :=
  Iff.rfl

/-- Text 1.0.2 (3): A subset of a real vector space is a line when it is the set of all real
scalar multiples of some nonzero vector. -/
def IsLine (C : Set X) : Prop :=
  ∃ u : X, u ≠ 0 ∧ C = (↑(ℝ ∙ u) : Set X)

/-- A line is exactly the underlying set of a one-dimensional submodule `ℝ ∙ u`
for some nonzero vector `u`. -/
theorem isLine_iff {C : Set X} :
    IsLine C ↔ ∃ u : X, u ≠ 0 ∧ C = (↑(ℝ ∙ u) : Set X) :=
  Iff.rfl

/-- Textbook formulation of `IsLine`: a line is exactly a set of the form `ℝ • {u}` for some
nonzero vector `u`. -/
theorem isLine_iff_eq_univ_smul_singleton {C : Set X} :
    IsLine C ↔ ∃ u : X, u ≠ 0 ∧ C = (univ : Set ℝ) • ({u} : Set X) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    ext x
    simp [Submodule.mem_span_singleton]
  · rintro ⟨u, hu, hC⟩
    refine ⟨u, hu, hC.trans ?_⟩
    ext x
    simp [Submodule.mem_span_singleton]

end

/-! ### Text_1_0_3 (from Chap01) -/
open scoped Pointwise

universe u

namespace Set

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.3: a subset of a real vector space is the nonempty carrier of a real affine
subspace exactly when it is nonempty and equal to its affine span. -/
theorem exists_nonempty_affineSubspace_iff_nonempty_eq_affineSpan (C : Set X) :
    (∃ S : AffineSubspace ℝ X, (S : Set X) = C ∧ (S : Set X).Nonempty) ↔
      C.Nonempty ∧ (affineSpan ℝ C : Set X) = C := by
  constructor
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS, by simp⟩
  · rintro ⟨hC, hCspan⟩
    exact ⟨affineSpan ℝ C, hCspan, hC.affineSpan ℝ⟩

/-- A subset of a real vector space is the nonempty carrier of an affine subspace exactly when it
is nonempty and closed under binary affine combinations. -/
theorem exists_nonempty_affineSubspace_iff_nonempty_lineMap_mem (C : Set X) :
    (∃ S : AffineSubspace ℝ X, (S : Set X) = C ∧ (S : Set X).Nonempty) ↔
      C.Nonempty ∧
        ∀ ⦃x y : X⦄, x ∈ C → y ∈ C → ∀ t : ℝ, AffineMap.lineMap x y t ∈ C := by
  sorry

/-- A subset of a real vector space is the nonempty carrier of an affine subspace exactly when it
is nonempty and stable under binary affine combinations. -/
-- Proof sketch: identify nonempty affine subsets with nonempty carriers of `AffineSubspace ℝ X`
-- and rewrite binary affine combinations with `AffineMap.lineMap_apply_module`.
theorem exists_nonempty_affineSubspace_iff_ne_empty_eq_smul_add (C : Set X) :
    (∃ S : AffineSubspace ℝ X, (S : Set X) = C ∧ (S : Set X).Nonempty) ↔
      C ≠ ∅ ∧ ∀ t : ℝ, C = t • C + (1 - t) • C := by
  sorry

end Set

/-! ### Text_1_0_4 (from Chap01) -/
open Set

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.4 (1): the span of `C` is the intersection of all linear subspaces of `X`
containing `C`. -/
-- Proof sketch: use the Galois insertion between `Submodule.span ℝ` and coercion from submodules
-- to sets to identify the generated submodule with the infimum of all containing submodules.
theorem span_eq_sInf_submodule (C : Set X) :
    Submodule.span ℝ C = sInf {S : Submodule ℝ X | C ⊆ S} := by
  refine le_antisymm ?_ ?_
  · exact le_sInf fun S hS ↦ Submodule.span_le.2 hS
  · exact sInf_le Submodule.subset_span

/-- Text 1.0.4 (2): the affine hull of `C` is the intersection of all affine subspaces of `X`
containing `C`. -/
-- Proof sketch: apply the existing `AffineSubspace.affineSpan_eq_sInf` characterization of
-- `affineSpan ℝ C` as the infimum of all affine subspaces containing `C`.
theorem affine_hull_eq_sInf_affineSubspace (C : Set X) :
    affineSpan ℝ C = sInf {S : AffineSubspace ℝ X | C ⊆ S} := by
  simpa using AffineSubspace.affineSpan_eq_sInf ℝ X C

/-! ### Text_1_0_5 (from Chap01) -/
universe u

open Set
open AffineSubspace

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.5: if `C` is a nonempty affine subspace of a real vector space, then the textbook
difference set `C - C` is the carrier of the canonical direction subspace `C.direction`, and `C`
is the translate of this direction through any point of `C`. -/
-- Proof sketch: use `coe_direction_eq_vsub_set` to identify the textbook difference set with
-- `C.direction`, then characterize the translate through `x ∈ C` pointwise using
-- `vsub_mem_direction` and `vadd_mem_of_mem_direction`.
theorem text_1_0_5 (C : AffineSubspace ℝ X) (hC : (C : Set X).Nonempty) :
    (C.direction : Set X) = (C : Set X) -ᵥ (C : Set X) ∧
    ∀ ⦃x : X⦄, x ∈ C → (C : Set X) = (fun v ↦ v +ᵥ x) '' (C.direction : Set X) := by
  refine ⟨?_, ?_⟩
  · -- The textbook difference set `C - C` is exactly the canonical direction set of `C`.
    simpa using coe_direction_eq_vsub_set hC
  · -- Any point of `C` together with the direction determines `C` again.
    intro x hx
    ext y
    constructor
    · intro hy
      refine ⟨y -ᵥ x, vsub_mem_direction hy hx, ?_⟩
      simp
    · rintro ⟨v, hv, rfl⟩
      exact vadd_mem_of_mem_direction hv hx

/-! ### Text_1_0_6 (from Chap01) -/
open Set

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/- Text 1.0.6 (1): The closed line segment `[x,y]` in a real vector space is mathlib's
`segment ℝ x y`. -/
recall segment

/- Text 1.0.6 (2): The open line segment `]x,y[` in a real vector space is mathlib's
`openSegment ℝ x y`. -/
recall openSegment

/-- Text 1.0.6 (1): The half-open line segment `[x,y[` is the image of the interval
`Set.Ico (0 : ℝ) 1` under the affine line map from `x` to `y`. -/
def closedOpenSegment (x y : X) : Set X :=
  AffineMap.lineMap x y '' Set.Ico (0 : ℝ) 1

/-- Membership in `closedOpenSegment x y` means lying on the affine line from `x` to `y`
with parameter in `[0,1)`. -/
theorem mem_closedOpenSegment_iff {x y z : X} :
    z ∈ closedOpenSegment x y ↔
      ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ AffineMap.lineMap x y t = z := by
  simp [closedOpenSegment]

/-- Text 1.0.6 (2): The half-open line segment `]x,y]` is the image of the interval
`Set.Ioc (0 : ℝ) 1` under the affine line map from `x` to `y`. -/
def openClosedSegment (x y : X) : Set X :=
  AffineMap.lineMap x y '' Set.Ioc (0 : ℝ) 1

/-- Membership in `openClosedSegment x y` means lying on the affine line from `x` to `y`
with parameter in `(0,1]`. -/
theorem mem_openClosedSegment_iff {x y z : X} :
    z ∈ openClosedSegment x y ↔
      ∃ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 ∧ AffineMap.lineMap x y t = z := by
  simp [openClosedSegment]

/-! ### Text_1_0_7 (from Chap01) -/
universe u

open Set

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.7: the half-open segment `]x,y]` coincides with the half-open segment `[y,x[`. -/
-- Proof sketch: rewrite both sides as images of `AffineMap.lineMap` on `Ioc 0 1` and `Ico 0 1`,
-- then use the change of variables `s = 1 - t` together with `AffineMap.lineMap_apply_one_sub`.
theorem text_1_0_7 (x y : X) :
    openClosedSegment x y = closedOpenSegment y x := by
  ext z
  constructor
  · intro hz
    rcases mem_openClosedSegment_iff.mp hz with ⟨t, ht, htz⟩
    -- Reverse the parameter by sending `t` to `1 - t`.
    refine mem_closedOpenSegment_iff.mpr ?_
    refine ⟨1 - t, ?_, ?_⟩
    · simpa using (Set.sub_mem_Ico_zero_iff_right : 1 - t ∈ Set.Ico (0 : ℝ) 1 ↔
        t ∈ Set.Ioc (0 : ℝ) 1).2 ht
    -- Reversing the endpoints of the line map matches the textbook identity.
    exact (AffineMap.lineMap_apply_one_sub y x t).trans htz
  · intro hz
    rcases mem_closedOpenSegment_iff.mp hz with ⟨s, hs, hsz⟩
    -- Apply the inverse parameter change `s ↦ 1 - s`.
    refine mem_openClosedSegment_iff.mpr ?_
    refine ⟨1 - s, ?_, ?_⟩
    · simpa using (Set.sub_mem_Ioc_zero_iff_right : 1 - s ∈ Set.Ioc (0 : ℝ) 1 ↔
        s ∈ Set.Ico (0 : ℝ) 1).2 hs
    -- The same line-map symmetry gives the converse inclusion.
    exact (AffineMap.lineMap_apply_one_sub x y s).trans hsz

/-! ### Text_1_0_8 (from Chap01) -/
universe u v

section

variable (X : Type u) (Y : Type v)

/-
Text 1.0.8: a set-valued operator from `X` to `Y` is canonically just a map
`X → Set Y`.
-/
#check X → Set Y

end

-- Compatibility alias used by subsequent textbook items.
abbrev SetValuedOperator (X : Type u) (Y : Type v) : Type (max u v) := X → Set Y

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- The graph of a set-valued operator consists of the pairs `(x, u)` with `u ∈ A x`. -/
def graph (A : SetValuedOperator X Y) : SetRel X Y := { xu | xu.2 ∈ A xu.1 }

prefix:100 "gra " => SetValuedOperator.graph

/-- Membership in the graph of a set-valued operator is equivalent to membership in the
corresponding value set. -/
@[simp] theorem mem_graph (A : SetValuedOperator X Y) (x : X) (u : Y) :
    (x, u) ∈ A.graph ↔ u ∈ A x :=
  Iff.rfl

/-- Compatibility form of `mem_graph` using the original `_iff` suffix. -/
theorem mem_graph_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    (x, u) ∈ A.graph ↔ u ∈ A x :=
  mem_graph A x u

end SetValuedOperator

/-! ### Text_1_0_9 (from Chap01) -/
universe u v w

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Text 1.0.9: The image `A(C)` of a set `C` under a set-valued operator `A` is the union of
the value sets `A x` for `x ∈ C`. -/
def image (A : SetValuedOperator X Y) (C : Set X) : Set Y := ⋃ x ∈ C, A x

/-- Membership in the image of a set under a set-valued operator is equivalent to belonging to
one of the value sets over that set. -/
@[simp] theorem mem_image (A : SetValuedOperator X Y) (C : Set X) (y : Y) :
    y ∈ A.image C ↔ ∃ x ∈ C, y ∈ A x := by
  simp [image]

/-- The composition of set-valued operators sends `x` to the image of the value set `A x` under
`B`. -/
def comp (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) : SetValuedOperator X Z :=
  fun x ↦ B.image (A x)

/-- Evaluating the composition of set-valued operators amounts to taking the image of the value
set under the second operator. -/
@[simp] theorem comp_apply (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) (x : X) :
    B.comp A x = B.image (A x) :=
  rfl

/-- Membership in the composition of set-valued operators is equivalent to the existence of an
intermediate point in the first value set whose image under the second operator contains the
element. -/
@[simp] theorem mem_comp (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) (x : X) (z : Z) :
    z ∈ B.comp A x ↔ ∃ y ∈ A x, z ∈ B y := by
  simp [comp]

end SetValuedOperator

/-! ### Text_1_0_10 (from Chap01) -/
universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.10: The domain of a set-valued operator `A` is the set of points `x` for which
`A x` is nonempty. -/
def dom (A : SetValuedOperator X Y) : Set X := { x | (A x).Nonempty }

/-- The range of a set-valued operator `A` is the union of all of its value sets. -/
def range (A : SetValuedOperator X Y) : Set Y := ⋃ x, A x

/-- A point belongs to the domain exactly when the corresponding value set is nonempty. -/
theorem mem_dom_iff (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.dom ↔ (A x).Nonempty := by
  rfl

/-- A point belongs to the range exactly when it lies in the value set `A x` for some `x`. -/
theorem mem_range_iff (A : SetValuedOperator X Y) (y : Y) :
    y ∈ A.range ↔ ∃ x, y ∈ A x := by
  simp [range]

end SetValuedOperator

/-! ### Text_1_0_11 (from Chap01) -/
universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.11: The inverse of a set-valued operator is the operator obtained by reversing
its graph, equivalently by sending `u : Y` to the set of `x : X` such that `u ∈ A x`. -/
def inverse (A : SetValuedOperator X Y) : SetValuedOperator Y X := fun u ↦ { x | u ∈ A x }

/- Lean can use the standard inverse surface directly here, so the source-facing owner notation
for the inverse set-valued operator is `A⁻¹`. -/
scoped postfix:max "⁻¹" => SetValuedOperator.inverse

open scoped SetValuedOperator

/-- Membership in the inverse operator is equivalent to reversing the membership relation in
the original operator. -/
@[simp] theorem mem_inverse_iff (A : SetValuedOperator X Y) (u : Y) (x : X) :
    x ∈ A⁻¹ u ↔ u ∈ A x := by
  rfl

/-- The zero set of a set-valued operator consists of the points mapped to a set containing
`0`. -/
def zeros [Zero Y] (A : SetValuedOperator X Y) : Set X := A⁻¹ 0

/-- Membership in the zero set means that `0` belongs to the corresponding value set. -/
@[simp] theorem mem_zeros_iff [Zero Y] (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.zeros ↔ (0 : Y) ∈ A x := by
  rfl

end SetValuedOperator

namespace Function

variable {X : Type u} {Y : Type v}

/-- Dot-notation bridge for the inverse of a set-valued operator presented as a function
`X → Set Y`. -/
abbrev inverse (A : X → Set Y) : SetValuedOperator Y X := SetValuedOperator.inverse A

/-- Dot-notation bridge for the zero set of a set-valued operator presented as a function
`X → Set Y`. -/
abbrev zeros [Zero Y] (A : X → Set Y) : Set X := SetValuedOperator.zeros A

end Function

/-! ### Text_1_0_12 (from Chap01) -/
universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.12 (1): the domain of the inverse of a set-valued operator is the range of the
original operator. -/
@[simp] theorem dom_inverse (A : SetValuedOperator X Y) :
    A.inverse.dom = A.range := by
  ext u
  rw [mem_dom_iff, mem_range_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_inverse_iff A u x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_inverse_iff A u x).mpr hx⟩

/-- Text 1.0.12 (2): the range of the inverse of a set-valued operator is the domain of the
original operator. -/
@[simp] theorem range_inverse (A : SetValuedOperator X Y) :
    A.inverse.range = A.dom := by
  ext x
  rw [mem_range_iff, mem_dom_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_inverse_iff A u x).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_inverse_iff A u x).mpr hu⟩

end SetValuedOperator

/-! ### Text_1_0_13 (from Chap01) -/
universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.13: a set-valued operator is at most single-valued when each value set has at most
one element, equivalently when every value over its domain is a singleton. -/
def IsAtMostSingleValued (A : SetValuedOperator X Y) : Prop :=
  ∀ x, (A x).Subsingleton

/-- Textbook reformulation of `IsAtMostSingleValued`: over the domain, every value set is a
singleton. -/
theorem isAtMostSingleValued_iff_forall_eq_singleton (A : SetValuedOperator X Y) :
    IsAtMostSingleValued A ↔ ∀ x ∈ A.dom, ∃ y, A x = ({y} : Set Y) := by
  constructor
  · intro hA x hx
    rcases (mem_dom_iff A x).mp hx with ⟨y, hy⟩
    exact ⟨y, (hA x).eq_singleton_of_mem hy⟩
  · intro hA x
    by_cases hx : x ∈ A.dom
    · rcases hA x hx with ⟨y, hy⟩
      rw [hy]
      exact Set.subsingleton_singleton
    · rw [mem_dom_iff] at hx
      rw [Set.not_nonempty_iff_eq_empty] at hx
      rw [hx]
      exact Set.subsingleton_empty

/-- The set-valued operator associated with a function `T : D → Y` sends points of `D` to the
corresponding singleton values and points outside `D` to the empty set. -/
def ofFunction (D : Set X) (T : D → Y) : SetValuedOperator X Y :=
  fun x ↦ { y | ∃ hx : x ∈ D, y = T ⟨x, hx⟩ }

/-- On points of the domain, the operator associated with a function takes the corresponding
singleton value. -/
theorem ofFunction_apply_of_mem (D : Set X) (T : D → Y) {x : X} (hx : x ∈ D) :
    ofFunction D T x = ({T ⟨x, hx⟩} : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx', rfl⟩
    have hsub : (⟨x, hx'⟩ : D) = ⟨x, hx⟩ := Subtype.ext <| by rfl
    rw [hsub]
    exact Set.mem_singleton _
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hx, rfl⟩

/-- Outside the domain, the operator associated with a function takes the empty value set. -/
theorem ofFunction_apply_of_not_mem (D : Set X) (T : D → Y) {x : X} (hx : x ∉ D) :
    ofFunction D T x = (∅ : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx', _⟩
    exact (hx hx').elim
  · intro hy
    exact False.elim <| Set.notMem_empty y hy

/-- The operator associated with a function on a subset is at most single-valued. -/
theorem isAtMostSingleValued_ofFunction (D : Set X) (T : D → Y) :
    IsAtMostSingleValued (ofFunction D T) := by
  intro x
  by_cases hx : x ∈ D
  · rw [ofFunction_apply_of_mem D T hx]
    exact Set.subsingleton_singleton
  · rw [ofFunction_apply_of_not_mem D T hx]
    exact Set.subsingleton_empty

end SetValuedOperator

namespace Function

variable {X : Type u} {Y : Type v}

/-- The singleton-valued set-valued operator associated with a single-valued map on the whole
space. This is the `Set.univ` specialization of `SetValuedOperator.ofFunction`. -/
abbrev toSetValuedOperator (T : X → Y) : SetValuedOperator X Y :=
  SetValuedOperator.ofFunction Set.univ (fun x : Set.univ ↦ T x)

/-- Evaluating `Function.toSetValuedOperator` recovers the corresponding singleton value set. -/
@[simp] theorem toSetValuedOperator_apply (T : X → Y) (x : X) :
    T.toSetValuedOperator x = ({T x} : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx, rfl⟩
    rw [Set.mem_singleton_iff]
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨by simp, rfl⟩

end Function

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NormedField 𝕜]
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- The singleton-valued set-valued operator associated with a bounded linear map. This is the
function-level owner `Function.toSetValuedOperator` viewed through the canonical coercion from
`ContinuousLinearMap` to functions. -/
abbrev toSetValuedOperator (T : X →L[𝕜] Y) : SetValuedOperator X Y :=
  Function.toSetValuedOperator T

end ContinuousLinearMap

/-! ### Text_1_0_14 (from Chap01) -/
universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

variable {A : SetValuedOperator X Y}

/-- Text 1.0.14: a selection of `A` is an operator `T : A.dom → Y` such that `T x ∈ A x`
for every `x ∈ A.dom`. -/
abbrev Selection (A : SetValuedOperator X Y) : Type (max u v) := ∀ x : A.dom, A x

/-- A selection takes each point of the domain of `A` to a point of the corresponding value
set. -/
@[simp] theorem selection_apply_mem (T : Selection A) (x : A.dom) :
    (T x : Y) ∈ A x :=
  (T x).property

end SetValuedOperator

/-! ### Text_1_0_15 (from Chap01) -/
universe u v

variable {X : Type u} {Y : Type v}

/-- Text 1.0.15: the image `T(C)` of a subset `C ⊆ X` under a single-valued map `T : X → Y`
is the canonical set-theoretic construction `Set.image T C`. -/
-- Proof sketch: this is definitional, since the notation `T '' C` expands to `Set.image T C`.
theorem image_eq_set_image (T : X → Y) (C : Set X) :
    T '' C = Set.image T C := rfl

/-- The preimage `T⁻¹(D)` of a subset `D ⊆ Y` under a map `T : X → Y` is the set
`Set.preimage T D`. -/
-- Proof sketch: this is definitional, since the notation `T ⁻¹' D` expands to
-- `Set.preimage T D`.
theorem preimage_eq_set_preimage (T : X → Y) (D : Set Y) :
    T ⁻¹' D = Set.preimage T D := rfl

/-! ### Text_1_0_16 (from Chap01) -/
open scoped Pointwise

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y]

/-- Text 1.0.16: for set-valued operators `A B : X → Set Y` and a real scalar `c`
(`λ` in the text), the linear combination `A + λ B` is the pointwise operator satisfying
`(A + c • B) x = A x + c • B x`. -/
@[simp] theorem add_smul_apply (A B : SetValuedOperator X Y) (c : ℝ) (x : X) :
    (A + c • B) x = A x + c • B x :=
  rfl

end SetValuedOperator

/-! ### Text_1_0_17 (from Chap01) -/
open scoped Pointwise

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y]

/-- Membership in `(A + r • B) x` means being representable as `u + r • v` with
`u ∈ A x` and `v ∈ B x`. -/
theorem mem_add_smul_iff (A B : SetValuedOperator X Y) (r : ℝ) (x : X) (w : Y) :
    w ∈ (A + r • B) x ↔ ∃ u ∈ A x, ∃ v ∈ B x, w = u + r • v := by
  constructor
  · intro hw
    -- Expand membership in the pointwise sum, then unpack the scalar-multiple witness.
    rw [add_smul_apply, Set.mem_add] at hw
    rcases hw with ⟨u, hu, z, hz, huz⟩
    rw [Set.mem_smul_set] at hz
    rcases hz with ⟨v, hv, hvz⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [hvz] using huz.symm
  · rintro ⟨u, hu, v, hv, rfl⟩
    -- Rebuild membership by choosing `u` from `A x` and `r • v` from `r • B x`.
    rw [add_smul_apply, Set.mem_add]
    refine ⟨u, hu, r • v, ?_, rfl⟩
    rw [Set.mem_smul_set]
    exact ⟨v, hv, rfl⟩

/-- Helper for Text 1.0.17: `(A + r • B) x` is nonempty exactly when both input value sets
are nonempty. -/
-- Proof sketch: convert nonemptiness to a witness in the linear combination, use
-- `mem_add_smul_iff` to extract witnesses in `A x` and `B x`, and reverse the argument
-- by building the element `u + r • v`.
private lemma add_smul_nonempty_iff
    (A B : SetValuedOperator X Y) (r : ℝ) (x : X) :
    ((A + r • B) x).Nonempty ↔ (A x).Nonempty ∧ (B x).Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    -- Any witness in the linear combination decomposes into witnesses from both source sets.
    rw [mem_add_smul_iff] at hw
    rcases hw with ⟨u, hu, v, hv, _⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    -- Given witnesses in both source sets, their linear combination is a witness upstairs.
    refine ⟨u + r • v, ?_⟩
    rw [mem_add_smul_iff]
    exact ⟨u, hu, v, hv, rfl⟩

/-- Text 1.0.17 (1): the graph of the pointwise linear combination `A + λ B` consists of the
pairs `(x, u + λ • v)` coming from matching graph points of `A` and `B`. -/
-- Proof sketch: use `Set.ext`, unfold `SetValuedOperator.graph`, apply
-- `mem_add_smul_iff`, and rewrite the resulting membership conditions using
-- `SetValuedOperator.mem_graph_iff`.
theorem graph_add_smul (A B : SetValuedOperator X Y) (r : ℝ) :
    (A + r • B).graph =
      { xw | ∃ u v, (xw.1, u) ∈ A.graph ∧ (xw.1, v) ∈ B.graph ∧ xw.2 = u + r • v } := by
  ext xw
  constructor
  · intro hxw
    -- A graph point is exactly a point whose second coordinate lies in the combined value set.
    rw [mem_graph_iff, mem_add_smul_iff] at hxw
    rcases hxw with ⟨u, hu, v, hv, hEq⟩
    exact ⟨u, v, (mem_graph_iff A xw.1 u).2 hu, (mem_graph_iff B xw.1 v).2 hv, hEq⟩
  · intro hxw
    -- Conversely, the witness description gives membership in the value set, hence in the graph.
    rcases hxw with ⟨u, v, hu, hv, hEq⟩
    rw [mem_graph_iff, mem_add_smul_iff]
    exact ⟨u, (mem_graph_iff A xw.1 u).1 hu, v, (mem_graph_iff B xw.1 v).1 hv, hEq⟩

/-- Text 1.0.17 (2): the domain of the pointwise linear combination `A + λ B` is
`A.dom ∩ B.dom`. -/
@[simp] theorem dom_add_smul (A B : SetValuedOperator X Y) (r : ℝ) :
    (A + r • B).dom = A.dom ∩ B.dom := by
  ext x
  rw [Set.mem_inter_iff, mem_dom_iff, mem_dom_iff, mem_dom_iff]
  rw [add_smul_nonempty_iff]

end SetValuedOperator

/-! ### Text_1_0_18 (from Chap01) -/
universe u v

namespace EReal

/-- The canonical real scalar action on `EReal` is multiplication by the coerced real. -/
noncomputable instance : SMul ℝ EReal where
  smul a x := (a : EReal) * x

@[simp] theorem real_smul_def (a : ℝ) (x : EReal) : a • x = (a : EReal) * x :=
  rfl

end EReal

/-- Text 1.0.18: an operator between real scalar-action spaces is positively homogeneous when it
commutes with scalar multiplication by every positive real scalar. -/
def PositivelyHomogeneous {X : Type u} {Y : Type v} [SMul ℝ X] [SMul ℝ Y] (T : X → Y) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : X, T (a • x) = a • T x

namespace PositivelyHomogeneous

variable {X : Type u} {Y : Type v} [SMul ℝ X] [SMul ℝ Y] {T : X → Y}

/-- A positively homogeneous operator maps a positive scalar multiple to the corresponding
scalar multiple of the image. -/
theorem map_smul_of_pos (hT : PositivelyHomogeneous T) {a : ℝ} (ha : 0 < a) (x : X) :
    T (a • x) = a • T x :=
  hT ha x

end PositivelyHomogeneous

/-! ### Text_1_0_19 (from Chap01) -/
universe u v

/-- Text 1.0.19: affine mappings between real vector spaces are the canonical affine maps
`X →ᵃ[ℝ] Y`. -/
theorem affineMap_notation_eq (X : Type u) (Y : Type v) [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] :
    (X →ᵃ[ℝ] Y) = AffineMap ℝ X Y :=
  rfl

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace AffineMap

/-- An affine map between real vector spaces preserves binary affine combinations. -/
theorem map_affine_combination (T : X →ᵃ[ℝ] Y) (x y : X) (a : ℝ) :
    T (a • x + (1 - a) • y) = a • T x + (1 - a) • T y := by
  simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
    T.apply_lineMap y x a

end AffineMap

/-! ### Text_1_0_20 (from Chap01) -/
universe u v

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

private lemma centered_map_smul_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x : X) (μ : ℝ) :
    T (μ • x) - T 0 = μ • (T x - T 0) := by
  have hAffine : T (μ • x) = μ • T x + (1 - μ) • T 0 := by
    simpa using hT x 0 (1 - μ)
  have hShift : (1 - μ) • T 0 = -(μ • T 0) + T 0 := by
    rw [sub_eq_add_neg, add_smul, one_smul, neg_smul]
    abel
  rw [sub_eq_iff_eq_add]
  calc
    T (μ • x) = μ • T x + (1 - μ) • T 0 := hAffine
    _ = μ • T x + (-(μ • T 0) + T 0) := by rw [hShift]
    _ = μ • (T x - T 0) + T 0 := by
      rw [smul_sub, sub_eq_add_neg]
      abel

private lemma centered_map_half_sum_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x y : X) :
    T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0 =
      (1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0)) := by
  have hMidpoint :
      T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) = (1 / 2 : ℝ) • T x + (1 / 2 : ℝ) • T y := by
    have h := hT x y (1 / 2 : ℝ)
    norm_num at h
    exact h
  have hHalf : ((1 / 2 : ℝ) • T 0) + (1 / 2 : ℝ) • T 0 = T 0 := by
    rw [← add_smul]
    norm_num
  calc
    T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0
        = ((1 / 2 : ℝ) • T x + (1 / 2 : ℝ) • T y) -
            (((1 / 2 : ℝ) • T 0) + (1 / 2 : ℝ) • T 0) := by
              rw [hMidpoint, hHalf]
    _ = (1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0)) := by
      rw [smul_add, smul_sub, smul_sub]
      abel

private lemma centered_map_add_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x y : X) :
    T (x + y) - T 0 = (T x - T 0) + (T y - T 0) := by
  have hScale :=
    centered_map_smul_of_affine_combination T hT
      (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) (2 : ℝ)
  have hx : (2 : ℝ) • ((1 / 2 : ℝ) • x) = x := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • x) = ((2 : ℝ) * (1 / 2 : ℝ)) • x := by
        simp
      _ = x := by norm_num
  have hy : (2 : ℝ) • ((1 / 2 : ℝ) • y) = y := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • y) = ((2 : ℝ) * (1 / 2 : ℝ)) • y := by
        simp
      _ = y := by norm_num
  have hArg : (2 : ℝ) • (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) = x + y := by
    rw [smul_add, hx, hy]
  have hCentered :
      (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) =
        (T x - T 0) + (T y - T 0) := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) =
          ((2 : ℝ) * (1 / 2 : ℝ)) • ((T x - T 0) + (T y - T 0)) := by
            simp
      _ = (T x - T 0) + (T y - T 0) := by norm_num
  calc
    T (x + y) - T 0
        = T ((2 : ℝ) • (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y)) - T 0 := by rw [hArg]
    _ = (2 : ℝ) • (T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0) := hScale
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) := by
          rw [centered_map_half_sum_of_affine_combination T hT x y]
    _ = (T x - T 0) + (T y - T 0) := hCentered

/-- Companion bridge for Text 1.0.20: the textbook affine-combination formula for a map `T`
is equivalent to the existence of a bundled affine map with underlying function `T`. -/
theorem affine_combination_iff_exists_affineMap (T : X → Y) :
    (∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y) ↔
      ∃ A : X →ᵃ[ℝ] Y, (A : X → Y) = T := by
  constructor
  · intro hT
    let L : X →ₗ[ℝ] Y := IsLinearMap.mk' (fun x : X ↦ T x - T 0)
      { map_add := fun x y ↦ centered_map_add_of_affine_combination T hT x y
        map_smul := fun t x ↦ centered_map_smul_of_affine_combination T hT x t }
    refine ⟨AffineMap.mk' T L 0 ?_, rfl⟩
    intro x
    simp [L, sub_eq_add_neg, add_assoc]
  · rintro ⟨A, rfl⟩ x y t
    simpa [AffineMap.lineMap_apply_module] using A.apply_lineMap x y t

/-- Text 1.0.20: a map between real vector spaces is affine, in the canonical sense of arising
from an element of `X →ᵃ[ℝ] Y`, exactly when its translate through the origin,
`x ↦ T x - T 0`, is linear. -/
theorem affine_iff_isLinearMap_sub_apply_zero (T : X → Y) :
    (∃ A : X →ᵃ[ℝ] Y, (A : X → Y) = T) ↔
      IsLinearMap ℝ (fun x : X ↦ T x - T 0) := by
  constructor
  · rintro ⟨A, rfl⟩
    have hCentered : (fun x : X ↦ A x - A 0) = A.linear := by
      funext x
      simpa using (congrArg (fun f : X → Y ↦ f x) A.decomp').symm
    rw [hCentered]
    exact A.linear.isLinear
  · intro hL
    let L : X →ₗ[ℝ] Y := IsLinearMap.mk' (fun x : X ↦ T x - T 0) hL
    refine ⟨AffineMap.mk' T L 0 ?_, rfl⟩
    intro x
    simp [L, sub_eq_add_neg, add_assoc]

/-! ### Text_1_0_21 (from Chap01) -/
universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddGroup X]

/-- Text 1.0.21: The translation of a set-valued operator `A` by `y` sends `x` to the value
of `A` at `x - y`. -/
def translate (A : SetValuedOperator X Y) (y : X) : SetValuedOperator X Y :=
  fun x ↦ A (x - y)

/-- Applying the translation of `A` by `y` at `x` evaluates `A` at `x - y`. -/
@[simp] theorem translate_apply (A : SetValuedOperator X Y) (y x : X) :
    translate A y x = A (x - y) :=
  rfl

/-- Membership in the translation of a set-valued operator is equivalent to membership in the
original operator after translating the input by `-y`. -/
@[simp]
theorem mem_translate_iff (A : SetValuedOperator X Y) (y x : X) (u : Y) :
    u ∈ translate A y x ↔ u ∈ A (x - y) :=
  Iff.rfl

/-- The reversal of a set-valued operator sends `x` to the value of `A` at `-x`. -/
def reverse (A : SetValuedOperator X Y) : SetValuedOperator X Y :=
  fun x ↦ A (-x)

/- Lean cannot use the textbook ASCII surface `A^∨` here. We therefore use the postfix vee token
`Aᵛ` as the direct Lean surface for operator reversal. -/
scoped postfix:max "ᵛ" => SetValuedOperator.reverse

/-- Applying the reversal of `A` at `x` evaluates `A` at `-x`. -/
@[simp] theorem reverse_apply (A : SetValuedOperator X Y) (x : X) :
    reverse A x = A (-x) :=
  rfl

/-- Membership in the reversal of a set-valued operator is equivalent to membership in the
original operator at the negated input. -/
@[simp]
theorem mem_reverse_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    u ∈ reverse A x ↔ u ∈ A (-x) :=
  Iff.rfl

end SetValuedOperator

/-! ### Text_1_0_22 (from Chap01) -/
universe u

/- Reflexive relations are formalized by the canonical predicate `Std.Refl`. -/
recall Std.Refl

/- Transitive relations are formalized by the canonical predicate `IsTrans`. -/
recall IsTrans

/- Preorder relations are formalized by the canonical predicate `IsPreorder α r`. -/
recall IsPreorder

/- Antisymmetric relations are formalized by the canonical predicate `Std.Antisymm`. -/
recall Std.Antisymm

/- Total relations are formalized by the canonical predicate `Std.Total`. -/
recall Std.Total

/- A partially ordered set in the textbook sense is formalized by `IsPartialOrder α r`. -/
recall IsPartialOrder

/- A totally ordered set in the textbook sense is formalized by `IsLinearOrder α r`. -/
recall IsLinearOrder

/- A chain in a relation is formalized by the canonical predicate `IsChain`. -/
recall IsChain

/- Directed relations are formalized by the canonical predicate `IsDirected α r`. -/
recall IsDirected

/- The textbook converse relation is the canonical `Function.swap`. -/
recall Function.swap

/- Relation-theoretic upper bounds are formalized by the canonical upper polar `upperPolar r s`. -/
recall upperPolar {α β : Type*} (r : α → β → Prop) (s : Set α) : Set β

/- Companion recall: membership in `upperPolar r s` means that every element of `s` is `r`-below
the given point. -/
recall mem_upperPolar_iff {α β : Type*} {r : α → β → Prop} {s : Set α} {b : β} :
    b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b

/- For `≤`, the upper polar is exactly the canonical set of upper bounds `upperBounds s`. -/
recall upperPolar_le {α : Type*} {s : Set α} [LE α] :
    upperPolar (· ≤ ·) s = upperBounds s

/- Relation-theoretic lower bounds are formalized by the canonical lower polar `lowerPolar r t`. -/
recall lowerPolar {α β : Type*} (r : α → β → Prop) (t : Set β) : Set α

/- Companion recall: membership in `lowerPolar r t` means that the given point is `r`-below every
element of `t`. -/
recall mem_lowerPolar_iff {α β : Type*} {r : α → β → Prop} {t : Set β} {a : α} :
    a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b

/- For `≤`, the lower polar is exactly the canonical set of lower bounds `lowerBounds s`. -/
recall lowerPolar_le {α : Type*} {s : Set α} [LE α] :
    lowerPolar (· ≤ ·) s = lowerBounds s

/- A least element of a set in an ordered type is formalized by the canonical predicate
`IsLeast s a`. -/
recall IsLeast {α : Type*} [LE α] (s : Set α) (a : α) : Prop

/- A maximal element of an ordered type is formalized by the canonical predicate `IsMax a`. -/
recall IsMax {α : Type*} [LE α] (a : α) : Prop

/-- Text 1.0.22: the textbook notion of a directed set is exactly a nonempty type equipped with a
reflexive, transitive, and directed relation, equivalently a nonempty type with a directed
preorder relation. -/
theorem isDirectedSet_iff {α : Type u} {r : α → α → Prop} :
    (Nonempty α ∧ Std.Refl r ∧ IsTrans α r ∧ IsDirected α r) ↔
      Nonempty α ∧ IsPreorder α r ∧ IsDirected α r := by
  constructor
  · rintro ⟨hα, hrefl, htrans, hdir⟩
    exact ⟨hα, @IsPreorder.mk α r hrefl htrans, hdir⟩
  · rintro ⟨hα, hpre, hdir⟩
    exact ⟨hα, hpre.toRefl, hpre.toIsTrans, hdir⟩

/-- The textbook converse relation satisfies `Function.swap r a b` exactly when `r b a` holds. -/
theorem converseRelation_iff {α : Type u} {r : α → α → Prop} {a b : α} :
    Function.swap r a b ↔ r b a :=
  Iff.rfl

/-- Text 1.0.22: in a partial order, the textbook strict-order relation `a ≤ b ∧ a ≠ b` is the
canonical relation `<`. -/
theorem strictOrder {α : Type u} [PartialOrder α] :
    (fun a b : α ↦ a ≤ b ∧ a ≠ b) = (· < ·) := by
  funext a b
  exact propext lt_iff_le_and_ne.symm

/-- Companion bridge: the textbook strict-order condition is equivalent to the canonical relation
`a < b`. -/
theorem strictOrder_iff {α : Type u} [PartialOrder α] {a b : α} :
    (a ≤ b ∧ a ≠ b) ↔ a < b :=
  lt_iff_le_and_ne.symm

/-! ### Text_1_0_23 (from Chap01) -/
universe u v

variable (A : Type u) (X : Type v)

/- Text 1.0.23: once the directed-set structure on the index type is fixed in the ambient
context, a net in `X` indexed by `A` is formalized by the canonical function type `A → X`. The
textbook's nonemptiness assumption on `X` does not affect this underlying data. -/
#check A → X

/-! ### Text_1_0_24 (from Chap01) -/
universe u v

namespace Net

variable {A : Type u} {X : Type v} [Preorder A] [IsDirectedOrder A] [Nonempty A]

/-- A net is eventually in `Y` exactly when all sufficiently large indices map into `Y`. -/
theorem eventuallyIn_iff_exists_forall_ge_mem (x : A → X) (Y : Set X) :
    (∀ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∃ a : A, ∀ b ≥ a, x b ∈ Y := by
  exact
    (Filter.eventually_atTop : (∀ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∃ a : A, ∀ b ≥ a, x b ∈ Y)

/-- A net is frequently in `Y` exactly when every tail contains an index whose value lies in
`Y`. -/
theorem frequentlyIn_iff_forall_exists_ge_mem (x : A → X) (Y : Set X) :
    (∃ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∀ a : A, ∃ b ≥ a, x b ∈ Y := by
  exact
    (Filter.frequently_atTop : (∃ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∀ a : A, ∃ b ≥ a, x b ∈ Y)

end Net

/-! ### Text_1_0_25 (from Chap01) -/
open Filter

universe u v w

namespace Net

variable {X : Type u} {A : Type v} {B : Type w}

/-- Text 1.0.25: a net `y` is a subnet of a net `x` via `k` exactly when the textbook
reindexing-and-cofinality condition holds, equivalently when `y = x ∘ k` and `k` tends to
`atTop`. -/
theorem isSubnetOfVia_iff [Preorder A] [Preorder B] [IsDirectedOrder A] [IsDirectedOrder B]
    [Nonempty B] {x : A → X} {y : B → X} {k : B → A} :
    (y = x ∘ k ∧ ∀ a : A, ∃ d : B, ∀ b : B, d ≤ b → a ≤ k b) ↔
      y = x ∘ k ∧ Tendsto k atTop atTop := by
  rw [tendsto_atTop_atTop]

end Net

/-! ### Text_1_0_26 (from Chap01) -/
/- Text 1.0.26: the extended real line is formalized by the canonical type `EReal` of real
numbers with adjoined bottom and top elements `⊥` and `⊤`, equipped with the extended order;
the textbook's conventions about indeterminate arithmetic expressions are handled separately when
needed. -/
recall EReal : Type

namespace EReal

/-- Every real number lies strictly between `-∞` and `+∞` in the extended real line. -/
theorem real_strictly_between_infinities (ξ : ℝ) :
    (⊥ : EReal) < (ξ : EReal) ∧ (ξ : EReal) < ⊤ := by
  exact ⟨bot_lt_coe ξ, coe_lt_top ξ⟩

end EReal

/-! ### Text_1_0_27 (from Chap01) -/
open Set

namespace EReal

/-- Text 1.0.27: the extended interval `]ξ, +∞]` is the usual real interval `]ξ, +∞[`,
embedded into `EReal`, with the point `+∞` adjoined. -/
theorem openClosedUpperInfiniteInterval_eq_image_Ioi_union_top (ξ : ℝ) :
    Ioi (ξ : EReal) = Real.toEReal '' Ioi ξ ∪ ({(⊤ : EReal)} : Set EReal) := by
  rw [image_coe_Ioi]
  ext x
  simp [lt_top_iff_ne_top]

end EReal

/-! ### Text_1_0_28 (from Chap01) -/
/- Text 1.0.28: for a set `S` of extended reals, the canonical complete-lattice infimum `sInf S`
is its infimum, i.e. the greatest lower bound of `S`; this is exactly the `EReal` specialization
of the standard theorem `isGLB_sInf`. -/
recall isGLB_sInf {α : Type*} [CompleteSemilatticeInf α] (s : Set α) : IsGLB s (sInf s)

/- For `EReal`, the infimum of the empty set is `⊤`; this is the `EReal` specialization of the
canonical complete-lattice theorem `sInf_empty`. -/
recall sInf_empty {α : Type*} [CompleteLattice α] : sInf (∅ : Set α) = (⊤ : α)

/- For `EReal`, the supremum of the empty set is `⊥`; this is the `EReal` specialization of the
canonical complete-lattice theorem `sSup_empty`. -/
recall sSup_empty {α : Type*} [CompleteLattice α] : sSup (∅ : Set α) = (⊥ : α)

namespace EReal

/-- The supremum of a set of extended reals is the negative of the infimum of its negated image. -/
theorem sSup_eq_neg_sInf_image_neg (S : Set EReal) :
    sSup S = -sInf ((-·) '' S) := by
  apply neg_injective
  rw [neg_neg]
  change (negOrderIso (sSup S) : ERealᵒᵈ) = sSup (negOrderIso '' S)
  exact (negOrderIso.isLUB_image'.2 (isLUB_sSup S)).unique (isLUB_sSup _)

end EReal

/-! ### Text_1_0_29 (from Chap01) -/
open Filter

universe u

namespace Net

variable {A : Type u} [Preorder A] [IsDirectedOrder A]

/-- The limit inferior of a net is the supremum of the infima of its tails. -/
-- Proof sketch: unfold `Net.liminf`, rewrite `Filter.liminf` with
-- `Filter.liminf_eq_sSup_sInf`, and specialize `Filter.mem_atTop_sets` to identify the sets in
-- `atTop` with the tails `Set.Ici a`.
theorem liminf_eq_sSup_tail_sInf [Nonempty A] (ξ : A → EReal) :
    Filter.liminf ξ atTop = sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) := by
  refine le_antisymm ?_ ?_
  · calc
      Filter.liminf ξ atTop
          = sSup ((fun I ↦ sInf (ξ '' I)) '' (atTop : Filter A).sets) := by
              simpa using (Filter.liminf_eq_sSup_sInf (atTop : Filter A) ξ)
      _ ≤ sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) := by
            refine sSup_le ?_
            intro r hr
            rcases hr with ⟨I, hI, rfl⟩
            rcases mem_atTop_sets.mp hI with ⟨a, ha⟩
            exact le_trans (sInf_le_sInf (Set.image_mono ha)) (le_sSup ⟨a, rfl⟩)
  · calc
      sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a))
          ≤ sSup ((fun I ↦ sInf (ξ '' I)) '' (atTop : Filter A).sets) := by
            refine sSup_le ?_
            intro r hr
            rcases hr with ⟨a, rfl⟩
            exact le_sSup ⟨Set.Ici a, mem_atTop_sets.mpr ⟨a, fun _ hb ↦ hb⟩, rfl⟩
      _ = Filter.liminf ξ atTop := by
            simpa using (Filter.liminf_eq_sSup_sInf (atTop : Filter A) ξ).symm

/-- The limit superior of a net is the infimum of the suprema of its tails. -/
-- Proof sketch: unfold `Net.limsup`, rewrite `Filter.limsup` with
-- `Filter.limsup_eq_sInf_sSup`, and use `Filter.mem_atTop_sets` to replace sets in `atTop` by the
-- tails `Set.Ici a`.
theorem limsup_eq_sInf_tail_sSup [Nonempty A] (ξ : A → EReal) :
    Filter.limsup ξ atTop = sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
  refine le_antisymm ?_ ?_
  · calc
      Filter.limsup ξ atTop
          = sInf ((fun I ↦ sSup (ξ '' I)) '' (atTop : Filter A).sets) := by
              simpa using (Filter.limsup_eq_sInf_sSup (atTop : Filter A) ξ)
      _ ≤ sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
            refine le_sInf ?_
            intro r hr
            rcases hr with ⟨a, rfl⟩
            exact sInf_le_of_le
              ⟨Set.Ici a, mem_atTop_sets.mpr ⟨a, fun _ hb ↦ hb⟩, rfl⟩ le_rfl
  · calc
      sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a))
          ≤ sInf ((fun I ↦ sSup (ξ '' I)) '' (atTop : Filter A).sets) := by
            refine le_sInf ?_
            intro r hr
            rcases hr with ⟨I, hI, rfl⟩
            rcases mem_atTop_sets.mp hI with ⟨a, ha⟩
            exact sInf_le_of_le ⟨a, rfl⟩ (sSup_le_sSup (Set.image_mono ha))
      _ = Filter.limsup ξ atTop := by
            simpa using (Filter.limsup_eq_sInf_sSup (atTop : Filter A) ξ).symm

/-- Text 1.0.29: for an extended-real-valued net indexed by a nonempty directed set, the limit
inferior is the supremum of the infima of the tails and the limit superior is the infimum of the
suprema of the tails. -/
-- Proof sketch: combine `Net.liminf_eq_sSup_tail_sInf` and `Net.limsup_eq_sInf_tail_sSup`.
theorem tail_liminf_limsup_formulas [Nonempty A] (ξ : A → EReal) :
    Filter.liminf ξ atTop = sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) ∧
      Filter.limsup ξ atTop = sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
  exact ⟨liminf_eq_sSup_tail_sInf ξ, limsup_eq_sInf_tail_sSup ξ⟩

end Net

/-! ### Text_1_0_30 (from Chap01) -/
open Filter

universe u

namespace Net

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]

/-- Text 1.0.30: for an `EReal`-valued net on a nonempty directed index set, the lower limit is
bounded above by the upper limit. -/
theorem liminf_le_limsup (ξ : A → EReal) :
    liminf ξ atTop ≤ limsup ξ atTop := by
  simpa using (Filter.liminf_le_limsup : liminf ξ atTop ≤ limsup ξ atTop)

end Net

/-! ### Text_1_0_31 (from Chap01) -/
universe u

namespace ERealFunction

variable {X : Type u}

/-- Text 1.0.31: the effective domain of an extended-real-valued function is the set of points
at which the function takes a finite value. Equivalently, it is the preimage of the open interval
`Ioo ⊥ ⊤`, i.e. the points where the value is neither `+∞` nor `-∞`. -/
def effectiveDom (f : X → EReal) : Set X :=
  f ⁻¹' Set.Ioo (⊥ : EReal) ⊤

/-- A point lies in the effective domain exactly when the function value there is finite, i.e. it
is neither `+∞` nor `-∞`. -/
@[simp] theorem mem_effectiveDom_iff (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ↔ f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  rw [effectiveDom, Set.mem_preimage, Set.mem_Ioo, bot_lt_iff_ne_bot, lt_top_iff_ne_top]
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/-- A point lies in the effective domain exactly when the function value there comes from a real
number via the canonical coercion `ℝ → EReal`. -/
theorem mem_effectiveDom_iff_exists_real (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ↔ ∃ r : ℝ, f x = (r : EReal) := by
  constructor
  · intro hx
    rcases (mem_effectiveDom_iff f x).1 hx with ⟨h_top, h_bot⟩
    exact ⟨(f x).toReal, (EReal.coe_toReal h_top h_bot).symm⟩
  · rintro ⟨r, hr⟩
    simp [mem_effectiveDom_iff, hr]

/-- The effective domain is the part of the ordinary domain where the function also avoids
`-∞`. -/
theorem effectiveDom_eq_dom_inter_neBot (f : X → EReal) :
    effectiveDom f = dom f ∩ {x | f x ≠ ⊥} := by
  ext x
  rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_iff, mem_dom_iff, lt_top_iff_ne_top]

end ERealFunction

/-! ### Text_1_0_32 (from Chap01) -/
universe u

noncomputable section

namespace EReal

variable {X : Type u}

/-- Text 1.0.32: addition on `EReal` with the textbook convention that the indeterminate sums
`+∞ + -∞` and `-∞ + +∞` are assigned the value `+∞`. -/
def sumWithTopBotAsTop : EReal → EReal → EReal
  | ⊤, ⊥ => ⊤
  | ⊥, ⊤ => ⊤
  | x, y => x + y

/-- Text 1.0.32: the textbook pointwise sum of two extended-real-valued functions is obtained by
applying the textbook extended-real addition convention pointwise. -/
abbrev pointwiseSum (f g : X → EReal) : X → EReal :=
  fun x ↦ sumWithTopBotAsTop (f x) (g x)

/-- Evaluating the textbook pointwise sum amounts to applying the textbook extended-real
addition convention at the chosen point. -/
@[simp] theorem pointwiseSum_apply (f g : X → EReal) (x : X) :
    pointwiseSum f g x = sumWithTopBotAsTop (f x) (g x) :=
  rfl

/-- The textbook addition convention is finite exactly when both inputs are finite real values. -/
theorem exists_real_eq_sumWithTopBotAsTop_iff {a b : EReal} :
    (∃ r : ℝ, sumWithTopBotAsTop a b = (r : EReal)) ↔
      (∃ s : ℝ, a = (s : EReal)) ∧ ∃ t : ℝ, b = (t : EReal) := by
  cases a <;> cases b
  case bot.bot =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case bot.coe b =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    simp
  case bot.top =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp
  case coe.bot a =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case coe.coe a b =>
    change (∃ r : ℝ, (a : EReal) + (b : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    constructor
    · intro _
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    · intro _
      refine ⟨a + b, ?_⟩
      exact (EReal.coe_add a b).symm
  case coe.top a =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp
  case top.bot =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case top.coe b =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    simp
  case top.top =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp

end EReal

/-! ### Text_1_0_33 (from Chap01) -/
universe u

open EReal

namespace ERealFunction

variable {X : Type u}

/-- A point belongs to the effective domain of the textbook pointwise sum exactly when it belongs
to the effective domains of both summands. -/
lemma mem_effectiveDom_pointwiseSum_iff (f g : X → EReal) (x : X) :
    x ∈ effectiveDom (pointwiseSum f g) ↔ x ∈ effectiveDom f ∧ x ∈ effectiveDom g := by
  rw [mem_effectiveDom_iff_exists_real, pointwiseSum_apply, exists_real_eq_sumWithTopBotAsTop_iff,
    mem_effectiveDom_iff_exists_real, mem_effectiveDom_iff_exists_real]

/-- Text 1.0.33: the effective domain of the textbook pointwise sum of two extended-real-valued
functions is the intersection of their effective domains. -/
theorem effectiveDom_pointwiseSum_eq_inter (f g : X → EReal) :
    effectiveDom (pointwiseSum f g) = effectiveDom f ∩ effectiveDom g := by
  ext x
  rw [Set.mem_inter_iff, mem_effectiveDom_pointwiseSum_iff]

end ERealFunction

/-! ### Text_1_0_34 (from Chap01) -/
universe u

/- Text 1.0.34: a topology on a type `X` is the canonical structure `TopologicalSpace X`,
encoding the empty set, the whole space, arbitrary unions, and finite intersections of open
sets; a topological space is therefore a type equipped with an instance of `TopologicalSpace X`,
and the associated notions of open and closed sets are `IsOpen` and `IsClosed`. -/
recall TopologicalSpace (X : Type u) : Type u

/- Open sets of a topological space are formalized by the predicate `IsOpen`. -/
recall IsOpen {X : Type u} [TopologicalSpace X] (s : Set X) : Prop

/- Closed sets of a topological space are formalized by the predicate `IsClosed`. -/
recall IsClosed {X : Type u} [TopologicalSpace X] (s : Set X) : Prop

/-! ### Text_1_0_35 (from Chap01) -/
universe u

/- Text 1.0.35: for a topological space `X` and a point `x : X`, the family `𝓥(x)` of
neighborhoods of `x` is formalized by the neighborhood filter `nhds x`. -/
recall nhds {X : Type u} [TopologicalSpace X] (x : X) : Filter X

/-- A set belongs to the neighborhood filter of `x` exactly when it contains an open set
containing `x`. -/
-- Proof sketch: this is a direct restatement of `mem_nhds_iff`, rearranging the existential
-- witnesses into the textbook order `IsOpen U ∧ x ∈ U ∧ U ⊆ V`.
theorem mem_nhds_iff_exists_open_subset {X : Type u} [TopologicalSpace X] {x : X} {V : Set X} :
    V ∈ nhds x ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V := by
  simpa [and_assoc, and_left_comm, and_comm] using
    (mem_nhds_iff : V ∈ nhds x ↔ ∃ U ⊆ V, IsOpen U ∧ x ∈ U)

/-! ### Text_1_0_36 (from Chap01) -/
universe u

/- Text 1.0.36: a base of a topology on `X` is formalized by the canonical predicate
`TopologicalSpace.IsTopologicalBasis B`, expressing that `B` is a family of open sets whose
members locally refine every neighborhood. -/
recall TopologicalSpace.IsTopologicalBasis {X : Type u} [TopologicalSpace X] (B : Set (Set X)) :
    Prop

/-! ### Text_1_0_37 (from Chap01) -/
universe u

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-
Text 1.0.37: if `B` is a basis for the topology on `X`, then every open set is the union of the
basis sets contained in it. This is the canonical theorem
`TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`.
-/
recall IsTopologicalBasis.open_eq_sUnion'

/-- Text 1.0.37 in the textbook's unpacked basis hypotheses. -/
theorem open_eq_sUnion_basis_subsets {B : Set (Set X)} (hB_open : ∀ V ∈ B, IsOpen V)
    (hB_basis : ∀ x (U : Set X), x ∈ U → IsOpen U → ∃ V ∈ B, x ∈ V ∧ V ⊆ U)
    {U : Set X} (hU : IsOpen U) :
    U = ⋃₀ {V ∈ B | V ⊆ U} := by
  simpa using (isTopologicalBasis_of_isOpen_of_nhds hB_open hB_basis).open_eq_sUnion' hU

end TopologicalSpace

/-! ### Text_1_0_38 (from Chap01) -/
open Filter Topology

universe u

/- The canonical interior operator in a topological space is `interior`. -/
recall interior {X : Type u} [TopologicalSpace X] (C : Set X) : Set X

/- A point belongs to `interior C` exactly when `C` is a neighborhood of that point. -/
#check mem_interior_iff_mem_nhds

/-- Text 1.0.38: equivalently, a point lies in `interior C` exactly when `C` contains a
neighborhood of that point. -/
theorem mem_interior_iff_exists_mem_nhds_subset {X : Type u} [TopologicalSpace X] {x : X}
    {C : Set X} : x ∈ interior C ↔ ∃ V : Set X, V ∈ 𝓝 x ∧ V ⊆ C := by
  rw [mem_interior_iff_mem_nhds]
  constructor
  · intro hC
    exact ⟨C, hC, fun _ hx ↦ hx⟩
  · rintro ⟨V, hV, hVC⟩
    exact Filter.mem_of_superset hV hVC

/-! ### Text_1_0_39 (from Chap01) -/
universe u

/- Text 1.0.39: for a subset `C` of a topological space, the closure of `C` is the canonical set
`closure C`, namely the smallest closed set containing `C`. -/
recall closure {X : Type u} [TopologicalSpace X] (C : Set X) : Set X

/- Every set is contained in its closure. -/
#check subset_closure

/- The closure of a set is closed. -/
#check isClosed_closure

/- The closure is the smallest closed set containing the original set. -/
#check closure_minimal

/- The textbook notion that `C` is dense in `X` is the canonical predicate `Dense C`. -/
recall Dense {X : Type u} [TopologicalSpace X] (C : Set X) : Prop

/- A subset is dense exactly when its closure is the whole space. -/
#check dense_iff_closure_eq

/- A point belongs to the closure of `C` exactly when every neighborhood of that point meets
the set `C`. -/
#check mem_closure_iff_nhds

/-! ### Text_1_0_40 (from Chap01) -/
universe u

/- Text 1.0.40: the boundary `bdry C` of a subset `C` of a topological space is formalized by
the canonical set `frontier C`. -/
recall frontier {X : Type u} [TopologicalSpace X] (C : Set X) : Set X

/- Its defining equation in mathlib is the canonical theorem `closure_diff_interior`. -/
recall closure_diff_interior {X : Type u} [TopologicalSpace X] (C : Set X) :
    closure C \ interior C = frontier C

/-! ### Text_1_0_41 (from Chap01) -/
universe u v

namespace TopologicalSpace

variable {X₁ : Type u} [TopologicalSpace X₁]
variable {X₂ : Type v} [TopologicalSpace X₂]

/-- Text 1.0.41: if `B₁` and `B₂` are bases for the given topologies on `X₁` and `X₂`, then the
family of rectangles `U ×ˢ V` with `U ∈ B₁` and `V ∈ B₂` is a basis for the product topology on
`X₁ × X₂`. This is the textbook set-builder form of the canonical theorem
`TopologicalSpace.IsTopologicalBasis.prod`. -/
theorem IsTopologicalBasis.rectangles {B₁ : Set (Set X₁)} {B₂ : Set (Set X₂)}
    (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) :
    IsTopologicalBasis {s : Set (X₁ × X₂) | ∃ U ∈ B₁, ∃ V ∈ B₂, s = U ×ˢ V} := by
  have hrect :
      Set.image2 (· ×ˢ ·) B₁ B₂ =
        {s : Set (X₁ × X₂) | ∃ U ∈ B₁, ∃ V ∈ B₂, s = U ×ˢ V} := by
    ext s
    simp [Set.mem_image2, eq_comm]
  rw [← hrect]
  exact h₁.prod h₂

end TopologicalSpace
