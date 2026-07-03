import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [HasColimitsOfShape WalkingParallelPair A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace CategoryTheory.Functor

/-
Source/core/bridge triage for Lemma 12.29.6:
- source-facing: the Stacks hypothesis that an object property `P` generates `B` by quotients,
  together with corepresentability of `Hom_B(P₀, u(-))` for `P₀ ∈ P`;
- core/canonical: the Chapter 12 owner `ObjectProperty.HasEpiCover`, the owner predicate
  `u.leftAdjointObjIsDefined`, and the adjointness criterion
  `Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top`;
- bridge/view: the quotient presentation of an arbitrary `Y : B` by two objects of `P`, used to
  promote the source-facing hypothesis `P ≤ u.leftAdjointObjIsDefined` to
  `u.leftAdjointObjIsDefined = ⊤`.

Primitive data here are only the functor `u`, the object property `P`, the canonical
quotient-generating owner `[P.HasEpiCover]`, and the owner predicate on `P`. The cokernel
presentation of an arbitrary object is derived bridge data, so it should stay internal to the
proof of the owner equality rather than becoming a parallel public wrapper. -/

/-- If an object property `P` on `B` has epi covers and every object of `P` lies in the domain of
definition of the partial left adjoint of `u`, then the owner predicate
`u.leftAdjointObjIsDefined` is all of `B`. -/
theorem leftAdjointObjIsDefined_eq_top_of_hasEpiCover
    (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
    (hdefined : P ≤ u.leftAdjointObjIsDefined) :
    u.leftAdjointObjIsDefined = ⊤ := by
  ext Y
  constructor
  · intro _
    trivial
  · intro _
    have hcover : P.HasEpiCover := inferInstance
    obtain ⟨P₁, hP₁, f, hf⟩ := hcover.exists_epi Y
    haveI : Epi f := hf
    obtain ⟨P₂, hP₂, e, he⟩ := hcover.exists_epi (Limits.kernel f)
    haveI : Epi e := he
    let g : P₂ ⟶ P₁ := e ≫ Limits.kernel.ι f
    have hg : g ≫ f = 0 := by
      dsimp [g]
      simp
    have hc : IsColimit (CokernelCofork.ofπ f hg) := by
      refine CokernelCofork.IsColimit.ofπ' f hg ?_
      intro Z k hk
      have hkernel : Limits.kernel.ι f ≫ k = 0 := by
        apply (cancel_epi e).1
        simpa [g, Category.assoc] using hk
      exact ⟨Abelian.epiDesc f k hkernel, Abelian.comp_epiDesc f k hkernel⟩
    exact u.leftAdjointObjIsDefined_of_isColimit hc
      (fun j ↦ by
        cases j with
        | zero => exact hdefined _ hP₂
        | one => exact hdefined _ hP₁)

/-- Lemma 12.29.6: if an object property `P` on `B` generates `B` by quotients and the functors
`Hom_B(P₀, u(-))` are corepresentable for all objects `P₀` satisfying `P`, then `u` admits a
left adjoint. -/
theorem isRightAdjoint_of_quotient_generating_set_and_leftAdjointObjIsDefined
    (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
    (hdefined : P ≤ u.leftAdjointObjIsDefined) :
    u.IsRightAdjoint := by
  exact isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (leftAdjointObjIsDefined_eq_top_of_hasEpiCover u P hdefined)

end CategoryTheory.Functor
