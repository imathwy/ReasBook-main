import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import StacksProject_2024.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {U : C}

namespace SemiRepresentableFamily
namespace Over

/-- A fixed-target family lies in `B` if every source object of one of its arrows belongs to `B`.
-/
def objectsIn (𝒰 : SR(C, U)) (B : Set C) : Prop :=
  ∀ i : 𝒰.index, (𝒰.obj i).left ∈ B

/-- Unfolding `objectsIn` says exactly that each source object of the family belongs to `B`. -/
@[simp] theorem objectsIn_iff (𝒰 : SR(C, U)) (B : Set C) :
    𝒰.objectsIn B ↔ ∀ i : 𝒰.index, (𝒰.obj i).left ∈ B :=
  Iff.rfl

/-- The owner-level predicate `objectsIn` on `SR(C, U)` recovers the textbook indexed-arrow
formulation via `ofArrows`. -/
@[simp] theorem ofArrows_objectsIn_iff
    (B : Set C) {I : Type w} (X : I → C) (f : ∀ i : I, X i ⟶ U) :
    (ofArrows X f).objectsIn B ↔ ∀ i : I, X i ∈ B :=
  Iff.rfl

/-- 25.12.2.1: a fixed-target family of arrows into `U` is a basis covering family for `K` and
`B` when it is covering for the precoverage `K` and every source object of one of its arrows lies
in the designated basis `B`. -/
def IsBasisCovering
    (K : Precoverage C) (B : Set C) (𝒰 : SR(C, U)) : Prop :=
  IsCovering K 𝒰 ∧ 𝒰.objectsIn B

/-- Unfolding `IsBasisCovering` recovers the canonical conjunction of the covering condition and
the basis-membership predicate on the source objects. -/
@[simp] theorem isBasisCovering_iff
    (K : Precoverage C) (B : Set C) (𝒰 : SR(C, U)) :
    𝒰.IsBasisCovering K B ↔ IsCovering K 𝒰 ∧ 𝒰.objectsIn B :=
  Iff.rfl

/-- For a Grothendieck topology, a basis covering family is equivalently a family whose generated
sieve is covering and whose source objects all lie in the designated basis. -/
@[simp] theorem isBasisCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (B : Set C) (𝒰 : SR(C, U)) :
    𝒰.IsBasisCovering J.toPrecoverage B ↔ 𝒰.toSieve ∈ J U ∧ 𝒰.objectsIn B := by
  rw [isBasisCovering_iff, IsCovering, GrothendieckTopology.mem_toPrecoverage_iff]

/-- A basis covering family is covering for the underlying precoverage. -/
theorem IsBasisCovering.isCovering
    {K : Precoverage C} {B : Set C} {𝒰 : SR(C, U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) :
    IsCovering K 𝒰 :=
  h𝒰.1

/-- Every source object of a basis covering family lies in the designated basis. -/
theorem IsBasisCovering.mem_basis
    {K : Precoverage C} {B : Set C} {𝒰 : SR(C, U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) (i : 𝒰.index) :
    (𝒰.obj i).left ∈ B :=
  h𝒰.2 i

/-- A basis covering family lies in the designated basis. -/
theorem IsBasisCovering.objectsIn
    {K : Precoverage C} {B : Set C} {𝒰 : SR(C, U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) :
    𝒰.objectsIn B :=
  h𝒰.2

/-- The owner-level predicate `IsBasisCovering` on `SR(C, U)` recovers the textbook indexed-arrow
formulation via `ofArrows`. -/
@[simp] theorem ofArrows_isBasisCovering_iff
    (K : Precoverage C) (B : Set C) {I : Type w} (X : I → C) (f : ∀ i : I, X i ⟶ U) :
    (ofArrows X f).IsBasisCovering K B ↔
      IsCovering K (ofArrows X f) ∧ ∀ i : I, X i ∈ B :=
  Iff.rfl

/-- For a Grothendieck topology, the indexed-arrow formulation of `IsBasisCovering` is exactly
that the generated sieve is covering and each source object lies in the designated basis. -/
@[simp] theorem ofArrows_isBasisCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (B : Set C) {I : Type w} (X : I → C) (f : ∀ i : I, X i ⟶ U) :
    (ofArrows X f).IsBasisCovering J.toPrecoverage B ↔
      Sieve.ofArrows X f ∈ J U ∧ ∀ i : I, X i ∈ B := by
  rw [isBasisCovering_toPrecoverage_iff, ofArrows_objectsIn_iff]
  rfl

end Over
end SemiRepresentableFamily

end CategoryTheory
