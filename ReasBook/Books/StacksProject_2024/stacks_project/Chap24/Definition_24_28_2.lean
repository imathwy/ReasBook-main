import StacksProject_2024.stacks_project.Chap24.«24_28_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA vA uB vB uP vP

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable [CategoryWithHomology DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB] [Abelian DGModB]
variable [CategoryWithHomology DGModB]
variable {DGModPullbackB : Type uP} [Category.{vP} DGModPullbackB]
variable [Preadditive DGModPullbackB]

-- Semantic search note: `lean_leansearch` recalled the canonical
-- `Functor.HasLeftDerivedFunctor` and `Functor.totalLeftDerived` owners. Local Chapter 24
-- precedent now owns the concrete homotopy-to-derived functor in `24_28_0_1`, and Definition
-- 24.28.2 builds the total left derived functors directly from that canonical owner
-- `pullbackTensorToDerived`, so the names below expose that total left derived functor directly.

/-- Definition 24.28.2 (1): for a ringed site `(\mathcal C, \mathcal O)`, differential graded
`\mathcal O`-algebras `\mathcal A` and `\mathcal B`, and a differential graded
`(\mathcal A, \mathcal B)`-bimodule `\mathcal N`, the derived tensor product
`- \otimes_{\mathcal A}^{\mathbf L} \mathcal N : D(\mathcal A, d) ⥤ D(\mathcal B, d)` is the
total left derived functor of the fixed-right-factor tensor functor.  The underived tensor functor
is represented here by the additive functor `tensorWithBimodule`. -/
@[stacks 0FTG]
abbrev derivedTensorProduct
    (tensorWithBimodule : DGModA ⥤ DGModB) [tensorWithBimodule.Additive]
    [Functor.HasLeftDerivedFunctor
      (pullbackTensorToDerived (𝟭 DGModA) tensorWithBimodule)
      (HomotopyCategory.quasiIso DGModA (up ℤ))] :
    DerivedCategory DGModA ⥤ DerivedCategory DGModB :=
  (pullbackTensorToDerived (𝟭 DGModA) tensorWithBimodule).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory DGModA (up ℤ) ⥤ DerivedCategory DGModA)
    (HomotopyCategory.quasiIso DGModA (up ℤ))

/-- Unfolding the source-facing derived tensor product gives the canonical total left derived
functor of the fixed-right-factor tensor construction from Lemma 24.28.1. -/
theorem derivedTensorProduct_def
    (tensorWithBimodule : DGModA ⥤ DGModB) [tensorWithBimodule.Additive]
    [Functor.HasLeftDerivedFunctor
      (pullbackTensorToDerived (𝟭 DGModA) tensorWithBimodule)
      (HomotopyCategory.quasiIso DGModA (up ℤ))] :
    derivedTensorProduct tensorWithBimodule =
      (pullbackTensorToDerived (𝟭 DGModA) tensorWithBimodule).totalLeftDerived
        (DerivedCategory.Qh : HomotopyCategory DGModA (up ℤ) ⥤ DerivedCategory DGModA)
        (HomotopyCategory.quasiIso DGModA (up ℤ)) := sorry

/-- Definition 24.28.2 (2): for a morphism of ringed topoi together with a homomorphism of
differential graded algebras `\varphi : \mathcal B \to f_*\mathcal A`, the derived pullback
`Lf^* : D(\mathcal B, d) ⥤ D(\mathcal A, d)` is the total left derived functor of the
pullback-then-tensor construction from Lemma 24.28.1.  The chosen underived pullback and the
subsequent tensoring with the target algebra are represented by the additive functors `pullback`
and `tensorWithTargetAlgebra`. -/
@[stacks 0FTG]
abbrev derivedPullback
    (pullback : DGModB ⥤ DGModPullbackB) [pullback.Additive]
    (tensorWithTargetAlgebra : DGModPullbackB ⥤ DGModA) [tensorWithTargetAlgebra.Additive]
    [Functor.HasLeftDerivedFunctor
      (pullbackTensorToDerived pullback tensorWithTargetAlgebra)
      (HomotopyCategory.quasiIso DGModB (up ℤ))] :
    DerivedCategory DGModB ⥤ DerivedCategory DGModA :=
  (pullbackTensorToDerived pullback tensorWithTargetAlgebra).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory DGModB (up ℤ) ⥤ DerivedCategory DGModB)
    (HomotopyCategory.quasiIso DGModB (up ℤ))

/-- Unfolding the source-facing derived pullback gives the canonical total left derived functor of
the pullback-then-tensor construction from Lemma 24.28.1. -/
theorem derivedPullback_def
    (pullback : DGModB ⥤ DGModPullbackB) [pullback.Additive]
    (tensorWithTargetAlgebra : DGModPullbackB ⥤ DGModA) [tensorWithTargetAlgebra.Additive]
    [Functor.HasLeftDerivedFunctor
      (pullbackTensorToDerived pullback tensorWithTargetAlgebra)
      (HomotopyCategory.quasiIso DGModB (up ℤ))] :
    derivedPullback pullback tensorWithTargetAlgebra =
      (pullbackTensorToDerived pullback tensorWithTargetAlgebra).totalLeftDerived
        (DerivedCategory.Qh : HomotopyCategory DGModB (up ℤ) ⥤ DerivedCategory DGModB)
        (HomotopyCategory.quasiIso DGModB (up ℤ)) := sorry

end

end DifferentialGradedModule
