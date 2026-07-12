import StacksProject_2024.Chap13.Lemma_13_30_3
import StacksProject_2024.Chap24.Definition_24_29_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA uB vA vB

-- Semantic search note: `lean_leansearch` surfaced only the generic derived-adjunction owners
-- `CategoryTheory.Adjunction.derived` and `CategoryTheory.Adjunction.ofIsRightAdjoint`, so the
-- source-facing owner/API choice here was checked against the local specializations
-- `Chap13/Lemma_13_30_3.lean`, `Chap24/Definition_24_29_2.lean`, and
-- `Chap24/Lemma_24_29_4.lean`.

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable {DGModB : Type uB} [Category.{vB} DGModB] [Abelian DGModB]

/-- The composite of the canonical left derived tensor functor with the chosen derived internal-Hom
carries the left-derived structure required to form the derived adjunction. -/
private theorem leftDerivedTensor_comp_derivedInternalHom_isLeftDerivedFunctor
    (tensorWithBimodule : DGModA ⥤ DGModB)
    (internalHomBimodule : DGModB ⥤ DGModA)
    [tensorWithBimodule.Additive] [internalHomBimodule.Additive]
    [Functor.HasLeftDerivedFunctor
      (tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (internalHomBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModB (up ℤ))] :
    (((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerived
          (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
          (HomologicalComplex.quasiIso DGModA (up ℤ))) ⋙
        derivedInternalHom internalHomBimodule).IsLeftDerivedFunctor
      (((Functor.associator
            (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
            ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerived
              (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
              (HomologicalComplex.quasiIso DGModA (up ℤ)))
            (derivedInternalHom internalHomBimodule)).inv) ≫
        Functor.whiskerRight
          ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerivedCounit
            (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
            (HomologicalComplex.quasiIso DGModA (up ℤ)))
          (derivedInternalHom internalHomBimodule))
      (HomologicalComplex.quasiIso DGModA (up ℤ)) := sorry

attribute [local instance] leftDerivedTensor_comp_derivedInternalHom_isLeftDerivedFunctor

/-- The composite of the chosen derived internal-Hom with the canonical left derived tensor functor
carries the right-derived structure required to form the derived adjunction. -/
private theorem derivedInternalHom_comp_leftDerivedTensor_isRightDerivedFunctor
    (tensorWithBimodule : DGModA ⥤ DGModB)
    (internalHomBimodule : DGModB ⥤ DGModA)
    [tensorWithBimodule.Additive] [internalHomBimodule.Additive]
    [Functor.HasLeftDerivedFunctor
      (tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (internalHomBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModB (up ℤ))] :
    ((derivedInternalHom internalHomBimodule) ⋙
        ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerived
          (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
          (HomologicalComplex.quasiIso DGModA (up ℤ)))).IsRightDerivedFunctor
      ((Functor.whiskerRight
          (derivedInternalHomUnit internalHomBimodule)
          ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerived
            (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
            (HomologicalComplex.quasiIso DGModA (up ℤ)))) ≫
        (Functor.associator
          (DerivedCategory.Q : CochainComplex DGModB ℤ ⥤ DerivedCategory DGModB)
          (derivedInternalHom internalHomBimodule)
          ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerived
            (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
            (HomologicalComplex.quasiIso DGModA (up ℤ)))).hom)
      (HomologicalComplex.quasiIso DGModB (up ℤ)) := sorry

attribute [local instance] derivedInternalHom_comp_leftDerivedTensor_isRightDerivedFunctor

/-- Lemma 24.29.3: let `(\mathcal C, \mathcal O)` be a ringed site, let `\mathcal A` and
`\mathcal B` be differential graded `\mathcal O`-algebras, and let `\mathcal N` be a
differential graded `(\mathcal A, \mathcal B)`-bimodule. For the chosen underived functors
`\mathcal M ↦ \mathcal M \otimes_{\mathcal A} \mathcal N` and
`\mathcal L ↦ \mathcal H\!\mathit{om}^{dg}_{\mathcal B}(\mathcal N, \mathcal L)` on the
corresponding categories of differential graded modules, if these functors are adjoint and their
canonical total left/right derived functors exist, then
`R\mathcal{H}\!\mathit{om}_{\mathcal B}(\mathcal N, -)` is right adjoint to
`- \otimes^{\mathbf L}_{\mathcal A} \mathcal N`. -/
noncomputable abbrev leftDerivedTensor_derivedInternalHom_adjunction
    (tensorWithBimodule : DGModA ⥤ DGModB)
    (internalHomBimodule : DGModB ⥤ DGModA)
    [tensorWithBimodule.Additive] [internalHomBimodule.Additive]
    (hAdj : tensorWithBimodule ⊣ internalHomBimodule)
    [Functor.HasLeftDerivedFunctor
      (tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (internalHomBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModB (up ℤ))] :
    (tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerived
        (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
        (HomologicalComplex.quasiIso DGModA (up ℤ))
      ⊣
        derivedInternalHom internalHomBimodule :=
  Adjunction.derived
    (hAdj.mapHomologicalComplex (up ℤ))
    (HomologicalComplex.quasiIso DGModA (up ℤ))
    (HomologicalComplex.quasiIso DGModB (up ℤ))
    ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerivedCounit
      (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
      (HomologicalComplex.quasiIso DGModA (up ℤ)))
    (derivedInternalHomUnit internalHomBimodule)

/-- Unfolding `leftDerivedTensor_derivedInternalHom_adjunction` identifies it with the canonical
derived adjunction obtained from the chosen underived tensor/Hom adjunction. -/
theorem leftDerivedTensor_derivedInternalHom_adjunction_def
    (tensorWithBimodule : DGModA ⥤ DGModB)
    (internalHomBimodule : DGModB ⥤ DGModA)
    [tensorWithBimodule.Additive] [internalHomBimodule.Additive]
    (hAdj : tensorWithBimodule ⊣ internalHomBimodule)
    [Functor.HasLeftDerivedFunctor
      (tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (internalHomBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModB (up ℤ))] :
    leftDerivedTensor_derivedInternalHom_adjunction tensorWithBimodule internalHomBimodule hAdj =
      Adjunction.derived
        (hAdj.mapHomologicalComplex (up ℤ))
        (HomologicalComplex.quasiIso DGModA (up ℤ))
        (HomologicalComplex.quasiIso DGModB (up ℤ))
        ((tensorWithBimodule.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).totalLeftDerivedCounit
          (DerivedCategory.Q : CochainComplex DGModA ℤ ⥤ DerivedCategory DGModA)
          (HomologicalComplex.quasiIso DGModA (up ℤ)))
        (derivedInternalHomUnit internalHomBimodule) := sorry

end

end DifferentialGradedModule
