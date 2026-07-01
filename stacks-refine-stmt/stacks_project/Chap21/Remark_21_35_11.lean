import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes_\mathcal O^{\mathbf L} K \to L`
in `D(\mathcal O)`. -/
private abbrev ringedSiteDerivedInternalHomEvaluation
    (K L : RingedSiteDerived J 𝒪) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ((((ihom.adjunction K).homEquiv ((ihom K).obj L) L).symm.trans
      ((β_ ((ihom K).obj L) K).symm.homCongr (Iso.refl L))) :
    (((ihom K).obj L ⟶ (ihom K).obj L) ≃ ((ihom K).obj L ⊗ K ⟶ L)))
    (𝟙 ((ihom K).obj L))

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
variable [J'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪' : Sheaf J' CommRingCat.{max u v}}
variable [Abelian (RingedSiteModules J' 𝒪')]
variable (leftDerivedPullback : RingedSiteDerived J' 𝒪' ⥤ RingedSiteDerived J 𝒪)
variable [MonoidalCategory (RingedSiteDerived J' 𝒪')]
variable [BraidedCategory (RingedSiteDerived J' 𝒪')]
variable [MonoidalClosed (RingedSiteDerived J' 𝒪')]

/-- Remark 21.35.11: for a morphism of ringed topoi, represented here by a chosen derived
pullback functor `Lh^* : D(\mathcal O') ⥤ D(\mathcal O)`, the pullback-tensor comparison of
Lemma `21.18.4` and the tensor-internal-Hom adjunction `21.35.0.1` induce the canonical morphism
`Lh^* R\mathcal H\!\mathit{om}(K, L) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)` in `D(\mathcal O)`. -/
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorIso :
      ∀ (A B : RingedSiteDerived J' 𝒪'),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : RingedSiteDerived J' 𝒪') :
    leftDerivedPullback.obj ((ihom K).obj L) ⟶
      (ihom (leftDerivedPullback.obj K)).obj (leftDerivedPullback.obj L) :=
  (((((ihom.adjunction (leftDerivedPullback.obj K)).homEquiv
        (leftDerivedPullback.obj ((ihom K).obj L))
        (leftDerivedPullback.obj L)).symm.trans
          ((β_ (leftDerivedPullback.obj ((ihom K).obj L))
              (leftDerivedPullback.obj K)).symm.homCongr
            (Iso.refl (leftDerivedPullback.obj L))))).symm)
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      leftDerivedPullback.map (ringedSiteDerivedInternalHomEvaluation K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison
-- `Lh^*(R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K) ≅
--   Lh^*R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} Lh^*K`.
/-- Applying the target-side tensor-internal-Hom adjunction to
`pullbackDerivedInternalHomComparison` recovers the pulled-back evaluation morphism after
transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ (A B : RingedSiteDerived J' 𝒪'),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : RingedSiteDerived J' 𝒪') :
    ((((ihom.adjunction (leftDerivedPullback.obj K)).homEquiv
          (leftDerivedPullback.obj ((ihom K).obj L))
          (leftDerivedPullback.obj L)).symm.trans
        ((β_ (leftDerivedPullback.obj ((ihom K).obj L))
            (leftDerivedPullback.obj K)).symm.homCongr
          (Iso.refl (leftDerivedPullback.obj L))))
      (pullbackDerivedInternalHomComparison leftDerivedPullback pullbackTensorIso K L)) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        leftDerivedPullback.map (ringedSiteDerivedInternalHomEvaluation K L) := sorry

end

end SheafOfModules.RingedSite
