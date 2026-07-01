import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

/-- The presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q` obtained by tensoring the underlying
presheaf of the constant sheaf of `M` with the fixed module `Q`. -/
abbrev constantModuleTensorSectionsPresheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) :
    Cᵒᵖ ⥤ ModuleCat.{u} Λ :=
  ((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight Q

/-- The canonical natural transformation from the constant presheaf with value `M ⊗ Q` to the
presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q`. -/
abbrev constantModuleTensorComparisonNatTrans
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) :
    ((Functor.const Cᵒᵖ).obj (M ⊗ Q)) ⟶
      constantModuleTensorSectionsPresheaf J M Q :=
  (Functor.constComp Cᵒᵖ M (tensorRight Q)).inv ≫
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (tensorRight Q)

-- Proof sketch: choose a finite presentation of `Q`, tensor the resulting right exact sequence
-- with the constant sheaf of `M`, and use exactness of the constant abelian-sheaf functor together
-- with preservation of finite direct sums by evaluation on `U` to identify the resulting cokernel
-- presheaf with `U ↦ \underline{M}(U) \otimes_\Lambda Q`.
/-- The presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q` is a sheaf when `Q` is finitely
presented. -/
theorem constantModuleTensorSectionsPresheaf_isSheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    Presheaf.IsSheaf J (constantModuleTensorSectionsPresheaf J M Q) := sorry

/-- The sheaf whose sections over `U` are `\underline{M}(U) \otimes_\Lambda Q`. -/
abbrev constantModuleTensorSectionsSheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    Sheaf J (ModuleCat.{u} Λ) :=
  ⟨constantModuleTensorSectionsPresheaf J M Q,
    constantModuleTensorSectionsPresheaf_isSheaf J M Q⟩

/-- The canonical comparison morphism from the constant sheaf of `M ⊗_\Lambda Q` to the sheaf
`U ↦ \underline{M}(U) \otimes_\Lambda Q`. -/
abbrev constantModuleTensorComparison
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    (constantSheaf J (ModuleCat.{u} Λ)).obj (M ⊗ Q) ⟶
      constantModuleTensorSectionsSheaf J M Q :=
  ObjectProperty.homMk <|
    sheafifyLift J
      (constantModuleTensorComparisonNatTrans J M Q)
      (constantModuleTensorSectionsPresheaf_isSheaf J M Q)

-- Proof sketch: the previous theorem makes `U ↦ \underline{M}(U) \otimes_\Lambda Q` into a sheaf,
-- so the canonical map from the constant presheaf with value `M ⊗ Q` factors uniquely through its
-- sheafification `\underline{M \otimes_\Lambda Q}`. The finite-presentation argument shows this
-- factorization is an isomorphism on every section object.
/-- Lemma 18.42.2: if `Q` is a finitely presented `\Lambda`-module, then for every `U : C` the
canonical comparison
`\underline{M \otimes_\Lambda Q}(U) \to \underline{M}(U) \otimes_\Lambda Q` is an isomorphism. -/
theorem constantModuleTensorComparison_app_isIso
    (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] (U : C) :
    IsIso ((constantModuleTensorComparison J M Q).hom.app (op U)) := sorry

end CategoryTheory
