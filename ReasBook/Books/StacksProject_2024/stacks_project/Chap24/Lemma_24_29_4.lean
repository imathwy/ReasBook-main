import StacksProject_2024.Chap13.Lemma_13_30_3
import StacksProject_2024.Chap24.Definition_24_29_2
import StacksProject_2024.Chap24.Lemma_24_28_4

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA uB vA vB

-- Semantic search note: the `lean_leansearch` tool is unavailable in this runner; the owner/API
-- choice was checked against the local differential graded predecessors `Lemma_24_18_1`,
-- `Definition_24_29_2`, `Lemma_24_28_4`, and the generic derived-adjunction owner
-- `Chap13/Lemma_13_30_3.lean`.

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable [CategoryWithHomology DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB] [Abelian DGModB]
variable [CategoryWithHomology DGModB]

/-- Lemma 24.29.4: for the chosen pushforward functor on differential graded `\mathcal A`-modules
attached to a morphism of ringed topoi together with a differential graded algebra map
`\varphi : \mathcal B \to f_*\mathcal A`, the derived pushforward
`Rf_* : D(\mathcal A, \mathrm d) ⥤ D(\mathcal B, \mathrm d)` is right adjoint to the left derived
pullback `Lf^* : D(\mathcal B, \mathrm d) ⥤ D(\mathcal A, \mathrm d)`. -/
noncomputable abbrev leftDerivedPullback_pushforward_adjunction
    (fPush : DGModA ⥤ DGModB)
    (fPull : DGModB ⥤ DGModA)
    [fPush.Additive] [fPull.Additive]
    (hAdj : fPull ⊣ fPush)
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived fPull) (HomotopyCategory.quasiIso DGModB (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (fPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))] :
    leftDerivedPullback fPull ⊣ derivedPushforward fPush := sorry

/-- The Hom-set equivalence attached to `leftDerivedPullback_pushforward_adjunction`. -/
noncomputable abbrev leftDerivedPullbackPushforwardHomEquiv
    (fPush : DGModA ⥤ DGModB)
    (fPull : DGModB ⥤ DGModA)
    [fPush.Additive] [fPull.Additive]
    (hAdj : fPull ⊣ fPush)
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived fPull) (HomotopyCategory.quasiIso DGModB (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (fPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    (𝒩 : DerivedCategory DGModB) (ℳ : DerivedCategory DGModA) :
    (𝒩 ⟶ (derivedPushforward fPush).obj ℳ) ≃
      ((leftDerivedPullback fPull).obj 𝒩 ⟶ ℳ) := sorry

/-- Applying `leftDerivedPullbackPushforwardHomEquiv` is definitionally the Hom-equivalence of the
chosen derived adjunction. -/
theorem leftDerivedPullbackPushforwardHomEquiv_apply
    (fPush : DGModA ⥤ DGModB)
    (fPull : DGModB ⥤ DGModA)
    [fPush.Additive] [fPull.Additive]
    (hAdj : fPull ⊣ fPush)
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived fPull) (HomotopyCategory.quasiIso DGModB (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (fPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    (𝒩 : DerivedCategory DGModB) (ℳ : DerivedCategory DGModA)
    (φ : 𝒩 ⟶ (derivedPushforward fPush).obj ℳ) :
    leftDerivedPullbackPushforwardHomEquiv fPush fPull hAdj 𝒩 ℳ φ =
      ((leftDerivedPullback_pushforward_adjunction fPush fPull hAdj).homEquiv 𝒩 ℳ).symm φ := sorry

end

end DifferentialGradedModule
