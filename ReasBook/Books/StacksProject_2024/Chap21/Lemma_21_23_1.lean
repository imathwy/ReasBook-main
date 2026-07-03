import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category `\mathrm{Ab}(\mathcal C)` of sheaves of abelian groups on the site
`(\mathcal C, J)`. -/
abbrev SiteAbelianSheaf :=
  Sheaf J AddCommGrpCat.{max u v}

/-- The category of sequential inverse systems of abelian sheaves on the site `(\mathcal C, J)`.
-/
abbrev SiteAbelianSheafInverseSystem :=
  ℕᵒᵖ ⥤ SiteAbelianSheaf J

/-- The ordinary inverse-limit functor on sequential inverse systems of abelian sheaves on the
site `(\mathcal C, J)`. -/
abbrev siteAbelianSheafInverseLimitFunctor :
    SiteAbelianSheafInverseSystem J ⥤ SiteAbelianSheaf J :=
  lim

-- Proof sketch: limits in the sheaf category are computed objectwise from the ambient
-- presheaf category, so the inverse-limit functor preserves zero morphisms and addition
-- componentwise.
/-- The inverse-limit functor on sequential inverse systems of abelian sheaves is additive. -/
local instance siteAbelianSheafInverseLimitFunctor_additive :
    (siteAbelianSheafInverseLimitFunctor J).Additive := sorry

/-- The cochain-level inverse-limit functor from inverse systems of abelian sheaves on the site
to the derived category of abelian sheaves on the site. -/
abbrev siteAbelianSheafInverseLimitFunctorToDerived :
    CochainComplex (SiteAbelianSheafInverseSystem J) ℤ ⥤
      DerivedCategory (SiteAbelianSheaf J) :=
  (siteAbelianSheafInverseLimitFunctor J).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

-- Proof sketch: choose K-injective representatives in the abelian category of inverse systems
-- of abelian sheaves and apply inverse limit termwise; this computes the total right derived
-- functor of the cochain-level inverse-limit functor.
/-- The cochain-level inverse-limit functor on sequential inverse systems of abelian sheaves
admits a chosen right derived functor. -/
local instance siteAbelianSheafInverseLimitFunctorToDerived_hasRightDerivedFunctor :
    (siteAbelianSheafInverseLimitFunctorToDerived J).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ)) := sorry

/-- The chosen derived inverse-limit functor
`R lim : D(\mathcal C \times \mathbf N) ⥤ D(\mathcal C)`, modeled here by inverse systems of
abelian sheaves on the site. -/
abbrev siteAbelianSheafDerivedInverseLimitFunctor :
    DerivedCategory (SiteAbelianSheafInverseSystem J) ⥤
      DerivedCategory (SiteAbelianSheaf J) :=
  (siteAbelianSheafInverseLimitFunctorToDerived J).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ))

/-- The exact evaluation functor at the `n`th stage of a sequential inverse system of abelian
sheaves on the site. This is the site-theoretic restriction functor `i_n^{-1}` from the textbook
notation. -/
abbrev siteAbelianSheafEvaluation (n : ℕ) :
    SiteAbelianSheafInverseSystem J ⥤ SiteAbelianSheaf J :=
  (evaluation ℕᵒᵖ (SiteAbelianSheaf J)).obj (op n)

/-- The `n`th stage functor on derived categories obtained by applying the restriction
`i_n^{-1}` stagewise. -/
abbrev siteAbelianSheafDerivedEvaluation (n : ℕ) :
    DerivedCategory (SiteAbelianSheafInverseSystem J) ⥤
      DerivedCategory (SiteAbelianSheaf J) :=
  (siteAbelianSheafEvaluation J n).mapDerivedCategory

/-- Stagewise evaluation on derived categories is the right derived functor of stagewise
evaluation on cochain complexes. -/
local instance siteAbelianSheafDerivedEvaluation_isRightDerivedFunctor (n : ℕ) :
    (siteAbelianSheafDerivedEvaluation J n).IsRightDerivedFunctor
      ((siteAbelianSheafEvaluation J n).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ)) := sorry

/-- The transition natural transformation from stage `n + 1` to stage `n` on sequential inverse
systems of abelian sheaves on the site. -/
abbrev siteAbelianSheafEvaluationStep (n : ℕ) :
    siteAbelianSheafEvaluation J (n + 1) ⟶ siteAbelianSheafEvaluation J n :=
  (evaluation ℕᵒᵖ (SiteAbelianSheaf J)).map ((homOfLE (Nat.le_succ n)).op)

/-- The induced transition natural transformation between the stagewise restriction functors on
derived categories. -/
abbrev siteAbelianSheafDerivedEvaluationStep (n : ℕ) :
    siteAbelianSheafDerivedEvaluation J (n + 1) ⟶
      siteAbelianSheafDerivedEvaluation J n :=
  Functor.rightDerivedNatTrans
    (siteAbelianSheafDerivedEvaluation J (n + 1))
    (siteAbelianSheafDerivedEvaluation J n)
    ((siteAbelianSheafEvaluation J (n + 1)).mapDerivedCategoryFactors.inv)
    ((siteAbelianSheafEvaluation J n).mapDerivedCategoryFactors.inv)
    (HomologicalComplex.quasiIso (SiteAbelianSheafInverseSystem J) (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (siteAbelianSheafEvaluationStep J n)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The tower `(K_n)_n` in `D(\mathcal C)` attached to
`K ∈ D(\mathcal C \times \mathbf N)`, modeled here by stagewise restriction of an inverse-system
object in `D(ℕᵒᵖ ⥤ \mathrm{Ab}(\mathcal C))`. -/
abbrev siteAbelianSheafDerivedInverseLimitTower
    (K : DerivedCategory (SiteAbelianSheafInverseSystem J)) :
    ℕᵒᵖ ⥤ DerivedCategory (SiteAbelianSheaf J) :=
  @Functor.ofOpSequence (DerivedCategory (SiteAbelianSheaf J)) _
    (fun n ↦ (siteAbelianSheafDerivedEvaluation J n).obj K)
    (fun n ↦ (siteAbelianSheafDerivedEvaluationStep J n).app K)

-- Proof sketch: choose a representing inverse system of cochain complexes of abelian sheaves for
-- `K`, restrict it stagewise along the embeddings `i_n`, and compare the chosen derived
-- inverse-limit functor with the Milnor distinguished triangle defining `R lim_n K_n`.
/-- Lemma 21.23.1: let `(\mathcal C, J)` be a site and let `K` be an object of
`D(\mathcal C \times \mathbf N)`, modeled here as an object of
`D(ℕᵒᵖ ⥤ \mathrm{Ab}(\mathcal C))`. If `K_n = i_n^{-1}K` denotes the stagewise restriction to
`\mathcal C`, then the chosen object `R lim(K)` is a derived limit of the tower `(K_n)_n`.
Equivalently, `R lim(K) ≅ R lim_n K_n` in `D(\mathcal C)`. -/
theorem siteAbelianSheafDerivedInverseLimit_isDerivedLimit_of_stagewiseRestriction
    (K : DerivedCategory (SiteAbelianSheafInverseSystem J)) :
    CategoryTheory.IsDerivedLimit (siteAbelianSheafDerivedInverseLimitTower J K)
      ((siteAbelianSheafDerivedInverseLimitFunctor J).obj K) := sorry

end

end CategoryTheory
