import Mathlib
import StacksProject_2024.Chap21.Definition_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category C]
variable {C' : Type u} [Category C']
variable {D : Type v} [Category D]
variable {D' : Type v} [Category D']
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (𝒪' : C'ᵒᵖ ⥤ CommRingCat.{u})
variable (u : C' ⥤ C)
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable (RGamma' : ∀ U' : C', D' ⥤ DerivedCategory (ModuleCat (𝒪'.obj (op U'))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict' :
    ∀ {U' V' : C'},
      (U' ⟶ V') →
      DerivedCategory (ModuleCat (𝒪'.obj (op V'))) ⥤
        DerivedCategory (ModuleCat (𝒪'.obj (op U'))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable
  (comparison' :
    ∀ {U' V' : C'} (f' : U' ⟶ V'),
      RGamma' V' ⋙ derivedRestrict' f' ⟶ RGamma' U')
variable (leftDerivedPullback : D ⥤ D')

-- Proof sketch: for each arrow `f' : U' ⟶ V'`, the sectionwise base-change description of
-- `Lg^*` identifies the target comparison morphism for `leftDerivedPullback.obj K` with the
-- image of the source comparison morphism for `u.map f'`. Thus every isomorphism required by the
-- source `QC` condition transports to the corresponding isomorphism in the target.
/-- Lemma 21.43.10: if the comparison morphisms defining quasi-coherence on the target category
are obtained from those on the source category after applying the derived pullback `Lg^*`, then
`Lg^* : D(\mathcal O) ⥤ D(\mathcal O')` maps `QC(\mathcal O)` into `QC(\mathcal O')`. -/
theorem qc_le_inverseImage_leftDerivedPullback
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K))) :
    isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ≤
      (isQuasiCoherent 𝒪' RGamma' derivedRestrict' comparison').inverseImage
        leftDerivedPullback := sorry

/-- The derived pullback functor `Lg^*` restricted to the full subcategories cut out by the
sectionwise derived base-change condition. -/
abbrev leftDerivedPullbackToDerivedBaseChangeQC
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K))) :
    QC 𝒪 RGamma derivedRestrict comparison ⥤
      QC 𝒪' RGamma' derivedRestrict' comparison' :=
  ObjectProperty.lift
    (isQuasiCoherent 𝒪' RGamma' derivedRestrict' comparison')
    ((isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).ι ⋙ leftDerivedPullback)
    (fun K ↦
      (qc_le_inverseImage_leftDerivedPullback
        𝒪 𝒪' u RGamma RGamma' derivedRestrict derivedRestrict'
        comparison comparison' leftDerivedPullback hLg) K.obj K.property)

end

end CategoryTheory.ModulesOnCategory
