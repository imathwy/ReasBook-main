import Mathlib
import StacksProject_2024.Chap21.Lemma_21_43_5
import StacksProject_2024.Chap21.Lemma_21_43_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v w w'

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable {D : C → Type w} [∀ U : C, Category (D U)]
variable {Dτ : C → Type w'} [∀ U : C, Category (Dτ U)]
variable {DU : C → Type w} [∀ U : C, Category (DU U)]

variable (QC : ∀ U : C, ObjectProperty (D U))
variable (RGamma : ∀ U : C, D U ⥤ DU U)
variable (Lf : ∀ U : C, DU U ⥤ D U)
variable (sectionsAdj : ∀ U : C, Lf U ⊣ RGamma U)
variable (epsilonPullback : ∀ U : C, D U ⥤ Dτ U)
variable (rEpsilonPushforward : ∀ U : C, Dτ U ⥤ D U)
variable (epsilonAdj : ∀ U : C, epsilonPullback U ⊣ rEpsilonPushforward U)
variable (RGammaTau : ∀ U : C, Dτ U ⥤ DU U)
variable (leray : ∀ U : C, RGammaTau U ≅ rEpsilonPushforward U ⋙ RGamma U)

/-- Lemma 21.43.13: for each object `U` of `\mathcal C`, if `K|_U` is quasi-coherent on the
localized chaotic site and `M|_U` is any object on the localized `τ`-site, then the local
adjunction `ε^* ⊣ Rε_*`, the quasi-coherent Hom computation of Lemma `21.43.5`, and the Leray
identification combine to identify morphisms `ε^*(K|_U) ⟶ M|_U` with morphisms
`R\Gamma(U, K) ⟶ R\Gamma(U, M)`. -/
noncomputable abbrev epsilonPullback_homEquiv_sections
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U)
    [IsIso ((sectionsAdj U).counit.app K.obj)] :
    ((epsilonPullback U).obj K.obj ⟶ M) ≃
      ((RGamma U).obj K.obj ⟶ (RGammaTau U).obj M) :=
  ((epsilonAdj U).homEquiv K.obj M).trans
    ((quasiCoherent_homEquiv_sections (QC U) (RGamma U) (Lf U) (sectionsAdj U) K
        ((rEpsilonPushforward U).obj M)).trans
      (Iso.homCongr (Iso.refl ((RGamma U).obj K.obj)) ((leray U).app M).symm))

-- Proof sketch: first apply the local adjunction `ε^* ⊣ Rε_*` to replace morphisms
-- `ε^*(K|_U) ⟶ M|_U` by morphisms `K|_U ⟶ Rε_* M|_U`. Then use Lemma `21.43.5` for the
-- quasi-coherent object `K|_U`, and finally transport the target along the Leray isomorphism
-- `R\Gamma(U, M) ≅ R\Gamma(U, Rε_* M)`.
/-- The equivalence `epsilonPullback_homEquiv_sections` is the composite of the local adjunction,
the quasi-coherent sections equivalence, and the Leray comparison isomorphism. -/
theorem epsilonPullback_homEquiv_sections_def
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U)
    [IsIso ((sectionsAdj U).counit.app K.obj)] :
    epsilonPullback_homEquiv_sections QC RGamma Lf sectionsAdj epsilonPullback
        rEpsilonPushforward epsilonAdj RGammaTau leray U K M =
      ((epsilonAdj U).homEquiv K.obj M).trans
        ((quasiCoherent_homEquiv_sections (QC U) (RGamma U) (Lf U) (sectionsAdj U) K
            ((rEpsilonPushforward U).obj M)).trans
          (Iso.homCongr (Iso.refl ((RGamma U).obj K.obj)) ((leray U).app M).symm)) := sorry

end

end CategoryTheory.ModulesOnCategory
