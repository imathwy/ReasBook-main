import Mathlib
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall note: the source-facing owner is `IsLocallyPrincipalClosedSubscheme`, while the
-- canonical pullback morphism is `pullback.fst`. The class packages local generator data, so this
-- file keeps the pullback-stability result as a theorem rather than as a public instance.

variable {S S' Z : Scheme.{u}}

/-- Companion to Lemma 31.13.11: the ideal sheaf of the pullback closed immersion
`pullback.fst f i : S' ×[S] Z ⟶ S'` is generated near each point by one section whenever the ideal
sheaf of `i : Z ⟶ S` is. This is the source-facing neighborhood form used to repackage local
principality. -/
theorem pullback_fst_exists_isGeneratedBy_one_closedImmersionIdealSheaf_over
    (f : S' ⟶ S) (i : Z ⟶ S) [IsLocallyPrincipalClosedSubscheme i] :
    ∀ x : S', ∃ U : S'.Opens, x ∈ U ∧
      SheafOfModules.IsGeneratedBy
        ((RingedSpace.closedImmersionIdealSheaf (pullback.fst f i).toShHom).over U) 1 := by
  intro x
  sorry

/-- Lemma 31.13.11: if `i : Z ⟶ S` is a locally principal closed subscheme of `S`, then its
inverse image along any morphism `f : S' ⟶ S` is a locally principal closed subscheme of `S'`. -/
theorem isLocallyPrincipalClosedSubscheme_pullback_fst
    (f : S' ⟶ S) (i : Z ⟶ S) [IsLocallyPrincipalClosedSubscheme i] :
    IsLocallyPrincipalClosedSubscheme (pullback.fst f i) := by
  exact
    { toIsClosedImmersion := inferInstance
      idealSheaf_isGeneratedBy_one :=
        pullback_fst_exists_isGeneratedBy_one_closedImmersionIdealSheaf_over f i }

end AlgebraicGeometry
