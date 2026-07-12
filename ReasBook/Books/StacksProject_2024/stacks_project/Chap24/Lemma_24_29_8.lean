import StacksProject_2024.Chap24.Lemma_24_29_6

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA vA uB vB uC vC uD vD

-- Semantic search note: `lean_leansearch` recalled `CategoryTheory.CatCommSq` as the canonical
-- owner for a commuting square of functors; the local API choice was then checked against the
-- nearby categorical square usage in `Chap07/Lemma_7_28_5.lean` and the Chapter 24
-- derived-pushforward owners `Definition_24_29_2` and `Lemma_24_29_6`.

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB] [Abelian DGModB]
variable {ModC : Type uC} [Category.{vC} ModC] [Abelian ModC]
variable {ModD : Type uD} [Category.{vD} ModD] [Abelian ModD]

/-- Lemma 24.29.8: for a morphism of ringed topoi together with a homomorphism
`\varphi : \mathcal B \to f_*\mathcal A` of differential graded algebras, the resulting derived
pushforward on differential graded modules commutes with the exact forgetful functors to the
underlying derived categories of `\mathcal O_\mathcal C`- and `\mathcal O_\mathcal D`-modules.

In this source-faithful categorical packaging, `pushforward` is the underived pushforward on
differential graded modules, `modulePushforward` is the underived pushforward on the underlying
module categories, `forgetA` and `forgetB` are the exact forgetful functors, and `hcomm`
identifies the underived square `pushforward ⋙ forgetB = forgetA ⋙ modulePushforward`. -/
instance derivedPushforwardForget_square
    (pushforward : DGModA ⥤ DGModB)
    (modulePushforward : ModC ⥤ ModD)
    (forgetA : DGModA ⥤ ModC)
    (forgetB : DGModB ⥤ ModD)
    [pushforward.Additive] [modulePushforward.Additive]
    [forgetA.Additive] [forgetB.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits forgetA]
    [CategoryTheory.Limits.PreservesFiniteColimits forgetA]
    [CategoryTheory.Limits.PreservesFiniteLimits forgetB]
    [CategoryTheory.Limits.PreservesFiniteColimits forgetB]
    [Functor.HasRightDerivedFunctor
      (pushforward.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (modulePushforward.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso ModC (up ℤ))]
    (hcomm : pushforward ⋙ forgetB = forgetA ⋙ modulePushforward) :
    CatCommSq
      forgetA.mapDerivedCategory
      (derivedPushforward pushforward)
      (derivedPushforward modulePushforward)
      forgetB.mapDerivedCategory where
  iso := sorry

/-- The comparison isomorphism carried by `derivedPushforwardForget_square`. -/
noncomputable abbrev derivedPushforwardForgetIso
    (pushforward : DGModA ⥤ DGModB)
    (modulePushforward : ModC ⥤ ModD)
    (forgetA : DGModA ⥤ ModC)
    (forgetB : DGModB ⥤ ModD)
    [pushforward.Additive] [modulePushforward.Additive]
    [forgetA.Additive] [forgetB.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits forgetA]
    [CategoryTheory.Limits.PreservesFiniteColimits forgetA]
    [CategoryTheory.Limits.PreservesFiniteLimits forgetB]
    [CategoryTheory.Limits.PreservesFiniteColimits forgetB]
    [Functor.HasRightDerivedFunctor
      (pushforward.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (modulePushforward.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso ModC (up ℤ))]
    (hcomm : pushforward ⋙ forgetB = forgetA ⋙ modulePushforward) :
    forgetA.mapDerivedCategory ⋙ derivedPushforward modulePushforward ≅
      derivedPushforward pushforward ⋙ forgetB.mapDerivedCategory := by
  let _ := derivedPushforwardForget_square pushforward modulePushforward forgetA forgetB hcomm
  simpa using
    (CatCommSq.iso
      forgetA.mapDerivedCategory
      (derivedPushforward pushforward)
      (derivedPushforward modulePushforward)
      forgetB.mapDerivedCategory)

end

end DifferentialGradedModule
