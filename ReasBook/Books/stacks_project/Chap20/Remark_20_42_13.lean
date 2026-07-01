import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
/-- The derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
private abbrev DMod (X : RingedSpace.{u}) :=
  DerivedCategory (SheafOfModules (ringCatSheaf X))

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_X)`, written in the Stacks Project order
`A ⊗ B`. -/
private abbrev ringedSpaceDerivedInternalHomAdjunction
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (A B C : DMod X) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K \to L`
in `D(\mathcal O_X)`. -/
private abbrev ringedSpaceDerivedInternalHomEvaluation
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (K L : DMod X) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ringedSpaceDerivedInternalHomAdjunction X ((ihom K).obj L) K L (𝟙 ((ihom K).obj L))

section

variable {X Y : RingedSpace.{u}}

variable (leftDerivedPullback : DMod Y ⥤ DMod X)

variable [MonoidalCategory (DMod X)]
variable [BraidedCategory (DMod X)]
variable [MonoidalClosed (DMod X)]
variable [MonoidalCategory (DMod Y)]
variable [BraidedCategory (DMod Y)]
variable [MonoidalClosed (DMod Y)]

/-- Remark 20.42.13: after choosing a derived pullback functor `Lh^* : D(\mathcal O_Y) ⥤
D(\mathcal O_X)` and the pullback-tensor comparison isomorphism of Lemma `20.27.3`, there is a
canonical morphism
`Lh^* R\mathcal H\!\mathit{om}(K, L) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)`. -/
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    leftDerivedPullback.obj ((ihom K).obj L) ⟶
      (ihom (leftDerivedPullback.obj K)).obj (leftDerivedPullback.obj L) :=
  (ringedSpaceDerivedInternalHomAdjunction X
      (leftDerivedPullback.obj ((ihom K).obj L))
      (leftDerivedPullback.obj K)
      (leftDerivedPullback.obj L)).symm
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison
-- `Lh^*(R\mathcal H\!\mathit{om}(K, L) ⊗^{\mathbf L} K) ≅
--   Lh^*R\mathcal H\!\mathit{om}(K, L) ⊗^{\mathbf L} Lh^*K`.
/-- Applying the tensor-internal-Hom adjunction to the pullback comparison recovers the pullback
of the evaluation morphism after transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    ringedSpaceDerivedInternalHomAdjunction X
        (leftDerivedPullback.obj ((ihom K).obj L))
        (leftDerivedPullback.obj K)
        (leftDerivedPullback.obj L)
        (pullbackDerivedInternalHomComparison leftDerivedPullback pullbackTensorIso K L) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L) := sorry

end

end AlgebraicGeometry.RingedSpace
