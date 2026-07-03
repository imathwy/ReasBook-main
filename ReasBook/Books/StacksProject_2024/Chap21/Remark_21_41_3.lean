import Mathlib
import Mathlib.CategoryTheory.Triangulated.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w x y z

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {DA : Type w} [Category.{w} DA]
variable {Dπ𝒪 : Type x} [Category.{x} Dπ𝒪]
variable {D𝒪 : Type y} [Category.{y} D𝒪]
variable {DAb : Type z} [Category.{z} DAb]

variable
  (augmentationQuasiIso :
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (A ⟶ 𝒪) → Prop)
variable
  (derivedLowerShriekToAb :
    SimplicialObject (Sheaf J CommRingCat.{max u v}) → DA ⥤ DAb)
variable
  (derivedTensorAlongAugmentation :
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (A ⟶ 𝒪) → DA ⥤ Dπ𝒪)
variable
  (projectionDerivedLowerShriek :
    SimplicialObject (Sheaf J CommRingCat.{max u v}) → Dπ𝒪 ⥤ D𝒪)
variable (targetForget : D𝒪 ⥤ DAb)
variable
  (forgetComparison :
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} →
      (ε : A ⟶ 𝒪) → augmentationQuasiIso ε →
        ∀ K : DA,
          IsIsomorphic
            ((derivedLowerShriekToAb A).obj K)
            (targetForget.obj
              ((projectionDerivedLowerShriek 𝒪).obj
                ((derivedTensorAlongAugmentation ε).obj K))))

/-- The `D(\mathcal O)`-valued derived lower shriek attached to an augmentation
`ε : \mathcal A_\bullet \to \mathcal O`, defined by first derived tensoring with `\mathcal O` and
then applying the target-side derived lower shriek `L\pi_!`. -/
abbrev augmentationDerivedLowerShriek
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪) :
    DA ⥤ D𝒪 :=
  derivedTensorAlongAugmentation ε ⋙ projectionDerivedLowerShriek 𝒪

-- Proof sketch: this is exactly the canonical comparison supplied by Lemma `21.41.2`, rewritten
-- using the definition of `augmentationDerivedLowerShriek` as tensoring with `\mathcal O` followed
-- by the target-side `L\pi_!` from Remark `21.38.6`.
/-- Remark 21.41.3: if an augmentation `ε : \mathcal A_\bullet \to \mathcal O` induces a
quasi-isomorphism `s(\mathcal A_\bullet) \to \mathcal O`, then for every
`K ∈ D(\mathcal A_\bullet)` the underlying abelian derived lower shriek `L\pi_!(K)` is
canonically isomorphic to the underlying abelian sheaf of the `D(\mathcal O)`-valued object
obtained by first tensoring `K` with `\mathcal O` over `\mathcal A_\bullet` and then applying the
target-side derived lower shriek. This is the functorial identification that gives `L\pi_!(K)` its
`\mathcal O`-module structure. -/
theorem augmentationDerivedLowerShriek_forget_obj_iso
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪)
    (hε : augmentationQuasiIso ε) (K : DA) :
    IsIsomorphic
      ((derivedLowerShriekToAb A).obj K)
      (targetForget.obj
        ((augmentationDerivedLowerShriek
            derivedTensorAlongAugmentation projectionDerivedLowerShriek ε).obj K)) := sorry

section Triangulated

variable [HasShift DA ℤ] [HasShift Dπ𝒪 ℤ] [HasShift D𝒪 ℤ]
variable [Limits.HasZeroObject DA] [Limits.HasZeroObject Dπ𝒪] [Limits.HasZeroObject D𝒪]
variable [Preadditive DA] [Preadditive Dπ𝒪] [Preadditive D𝒪]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor Dπ𝒪 n).Additive]
variable [∀ n : ℤ, (shiftFunctor D𝒪 n).Additive]
variable [Pretriangulated DA] [Pretriangulated Dπ𝒪] [Pretriangulated D𝒪]

/-- If the derived tensor functor along the augmentation and the target-side derived lower shriek
commute with triangulated shifts, then their composite does as well. -/
instance augmentationDerivedLowerShriek_commShift
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪)
    [(derivedTensorAlongAugmentation ε).CommShift ℤ]
    [(projectionDerivedLowerShriek 𝒪).CommShift ℤ] :
    (augmentationDerivedLowerShriek
        derivedTensorAlongAugmentation projectionDerivedLowerShriek ε).CommShift ℤ :=
  Functor.CommShift.comp
    (derivedTensorAlongAugmentation ε)
    (projectionDerivedLowerShriek 𝒪)

-- Proof sketch: the functor is the composite of the derived tensor functor along the augmentation
-- with the target-side derived lower shriek. Exact functors of triangulated categories are closed
-- under composition, so the composite is triangulated once both factors are.
/-- The augmentation-derived lower shriek is exact in the triangulated sense whenever both of its
factor functors are exact. -/
theorem augmentationDerivedLowerShriek_isTriangulated
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪)
    [(derivedTensorAlongAugmentation ε).CommShift ℤ]
    [(projectionDerivedLowerShriek 𝒪).CommShift ℤ]
    [(derivedTensorAlongAugmentation ε).IsTriangulated]
    [(projectionDerivedLowerShriek 𝒪).IsTriangulated] :
    (augmentationDerivedLowerShriek
      derivedTensorAlongAugmentation projectionDerivedLowerShriek ε).IsTriangulated := sorry

end Triangulated

end

end CategoryTheory
