import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

/- Definition 10.86.1: for an inverse system of sets over a directed preorder, the canonical owner
predicate is mathlib's `CategoryTheory.Functor.IsMittagLeffler` on functors `OrderDual I ⥤ Type`.
-/
recall CategoryTheory.Functor.IsMittagLeffler

/- Companion recall: mathlib packages the stabilization condition by saying that the eventual
range at each stage is attained. -/
recall CategoryTheory.Functor.isMittagLeffler_iff_eventualRange

/- Companion recall: over a cofiltered index category, the owner theorem
`Functor.isMittagLeffler_iff_subset_range_comp` is the canonical bridge from
`Functor.IsMittagLeffler` to stagewise range stabilization. -/
recall CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp

namespace CategoryTheory.Functor

variable {D : Type*} [Category D]

/-- For an additive cofiltered system, the eventual range at a fixed index is canonically an
additive subgroup of the target object. This is the additive bridge from the owner
`Functor.eventualRange` to additive downstream APIs. -/
def eventualRangeAddSubgroup (F : D ⥤ AddCommGrpCat) (j : D) : AddSubgroup (F.obj j) :=
  { carrier := (F ⋙ forget AddCommGrpCat).eventualRange j
    zero_mem' := by
      rw [Functor.eventualRange]
      refine Set.mem_iInter.2 fun i ↦ ?_
      refine Set.mem_iInter.2 fun f ↦ ?_
      refine ⟨0, ?_⟩
      change (F.map f).hom 0 = 0
      exact (F.map f).hom.map_zero
    add_mem' := by
      intro x y hx hy
      change x ∈ (F ⋙ forget AddCommGrpCat).eventualRange j at hx
      change y ∈ (F ⋙ forget AddCommGrpCat).eventualRange j at hy
      change x + y ∈ (F ⋙ forget AddCommGrpCat).eventualRange j
      rw [Functor.eventualRange] at hx hy ⊢
      refine Set.mem_iInter.2 fun i ↦ ?_
      refine Set.mem_iInter.2 fun f ↦ ?_
      rcases Set.mem_iInter.1 (Set.mem_iInter.1 hx i) f with ⟨x, rfl⟩
      rcases Set.mem_iInter.1 (Set.mem_iInter.1 hy i) f with ⟨y, rfl⟩
      refine ⟨x + y, ?_⟩
      change (F.map f).hom (x + y) = (F.map f).hom x + (F.map f).hom y
      exact (F.map f).hom.map_add x y
    neg_mem' := by
      intro x hx
      change x ∈ (F ⋙ forget AddCommGrpCat).eventualRange j at hx
      change -x ∈ (F ⋙ forget AddCommGrpCat).eventualRange j
      rw [Functor.eventualRange] at hx ⊢
      refine Set.mem_iInter.2 fun i ↦ ?_
      refine Set.mem_iInter.2 fun f ↦ ?_
      rcases Set.mem_iInter.1 (Set.mem_iInter.1 hx i) f with ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      change (F.map f).hom (-x) = -((F.map f).hom x)
      exact (F.map f).hom.map_neg x }

@[simp] theorem coe_eventualRangeAddSubgroup (F : D ⥤ AddCommGrpCat) (j : D) :
    ((F.eventualRangeAddSubgroup j : AddSubgroup (F.obj j)) : Set (F.obj j)) =
      (F ⋙ forget AddCommGrpCat).eventualRange j :=
  rfl

variable {J : Type u} [Category J]
variable {R : Type v} [Ring R]
variable (A : J ⥤ ModuleCat R)

/-- The stable image at a stage of a module-valued inverse system:
`A'_i = ⋂_{j ≥ i} im(A_j → A_i)`. This is the `ModuleCat` realization of the owner notion
`Functor.eventualRange`. -/
def stableImage (i : J) : Submodule R (A.obj i) :=
  ⨅ (j : J) (_f : j ⟶ i), LinearMap.range (A.map _f).hom

/-- Membership in `A.stableImage i` is equivalent to membership in the eventual range at `i` for
the underlying `Type`-valued inverse system. -/
theorem mem_stableImage_iff {i : J} {x : A.obj i} :
    x ∈ A.stableImage i ↔ x ∈ (A ⋙ forget (ModuleCat R)).eventualRange i := by
  change x ∈ (⨅ (j : J) (f : j ⟶ i), LinearMap.range (A.map f).hom) ↔
      x ∈ ⋂ (j : J) (f : j ⟶ i), Set.range (A.map f)
  simp

end CategoryTheory.Functor
