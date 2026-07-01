import stacks_project.Chap21.«21_35_9_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪

-- Proof sketch: both postcomposition with `ringedSiteDerivedEvaluationHom L M` and the
-- closed-monoidal uncurrying map are additive on morphisms, and precomposition with the fixed
-- right-unitor inverse `(ρ_ L).inv` preserves addition.
/- The map induced on degree-zero global sections by the evaluation morphism is additive. -/
private theorem ringedSiteDerivedEvaluationH0ToHom_add
    (L M : D) (s t : 𝟙_ D ⟶ M ⊗ L^∨) :
    (ρ_ L).inv ≫
        uncurry
          ((s + t) ≫ ringedSiteDerivedEvaluationHom L M) =
      ((ρ_ L).inv ≫
          uncurry
            (s ≫ ringedSiteDerivedEvaluationHom L M)) +
        ((ρ_ L).inv ≫
          uncurry
            (t ≫ ringedSiteDerivedEvaluationHom L M)) := sorry

/-- Lemma 21.35.9: the canonical morphism
`M \otimes_\mathcal O^{\mathbf L} L^\vee \to R\mathcal H\!\mathit{om}(L, M)`
induces a canonical map
`H^0(\mathcal C, M \otimes_\mathcal O^{\mathbf L} L^\vee) \to
\operatorname{Hom}_{D(\mathcal O)}(L, M)`,
formalized here as the additive map from morphisms
`\mathcal O \to M \otimes_\mathcal O^{\mathbf L} L^\vee` out of the monoidal unit of
`D(\mathcal O)` to morphisms `L ⟶ M`. -/
noncomputable def ringedSiteDerivedEvaluationH0ToHom
    (L M : D) :
    AddMonoidHom (𝟙_ D ⟶ M ⊗ L^∨) (L ⟶ M) :=
  AddMonoidHom.mk'
    (fun s ↦
      (ρ_ L).inv ≫
        uncurry
          (s ≫ ringedSiteDerivedEvaluationHom L M))
    (ringedSiteDerivedEvaluationH0ToHom_add L M)

-- Proof sketch: on the source, functoriality in `M` is postcomposition with
-- `f ⊗ 𝟙_{L^\vee}`. Expand the definition and use functoriality of
-- `MonoidalClosed.uncurry` and the right unitor.
/-- The induced map on degree-zero global sections is functorial in the variable `M`. -/
theorem ringedSiteDerivedEvaluationH0ToHom_natural
    {L M₁ M₂ : D} (f : M₁ ⟶ M₂)
    (s : 𝟙_ D ⟶ M₁ ⊗ L^∨) :
    ringedSiteDerivedEvaluationH0ToHom L M₂
        (s ≫ (f ⊗ₘ 𝟙 (L^∨))) =
      ringedSiteDerivedEvaluationH0ToHom L M₁ s ≫ f := sorry

end

end SheafOfModules.RingedSite
