import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopCat.Sheaf
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the source-facing scheme statement below is a specialization of the canonical
-- higher-direct-image filtered-colimit comparison owner `colimit.post` for abelian sheaves, so
-- the public surface stays directly on that comparison morphism.

variable {X S : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]

/-- Lemma 30.6.1: for a quasi-compact and quasi-separated morphism of schemes `f : X ⟶ S`, every
filtered colimit of abelian sheaves `\mathcal F = \operatorname{colim}_i \mathcal F_i` on `X`,
and every `p \geq 0`, the canonical map
`\operatorname{colim}_i R^p f_* \mathcal F_i \to R^p f_* (\operatorname{colim}_i \mathcal F_i)`
is an isomorphism. This is the canonical comparison-map formulation of the textbook equality
`R^p f_* \mathcal F = \operatorname{colim}_i R^p f_* \mathcal F_i`. -/
theorem higherDirectImageAbelianSheafColimitComparison_isIso_of_quasiCompact_quasiSeparated
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (X.Sheaf AddCommGrpCat.{u})]
    [HasColimitsOfShape I (S.Sheaf AddCommGrpCat.{u})]
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).Additive]
    (ℱ : I ⥤ X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso
      (colimit.post ℱ
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived p)) := sorry

end AlgebraicGeometry.Scheme
