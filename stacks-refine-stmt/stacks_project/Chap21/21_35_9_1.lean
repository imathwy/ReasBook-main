import Mathlib
import stacks_project.Chap21.Lemma_21_35_7

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

/- Domain-style sampling for 21.35.9.1:
- primary domain: the braided closed monoidal structure on the derived category
  `RingedSiteDerived J 𝒪` of modules on a ringed site;
- sampled owner declarations:
  `RingedSiteDerived`,
  `ringedSiteDerivedTensorInternalHomComparison`,
  `ihom`,
  `CategoryTheory.MonoidalCategory.rightUnitorNatIso`;
- best owner abstraction: the ambient owner is the chapter category `RingedSiteDerived J 𝒪`, and
  the source-facing evaluation map is the tensor-unit specialization of the canonical comparison
  morphism `ringedSiteDerivedTensorInternalHomComparison`, followed by the right-unitor on the
  target of the internal Hom;
- primitive data: the chapter owner category `RingedSiteDerived J 𝒪` together with its braided
  monoidal closed structure;
- derived API: the source-facing dual notation `L^∨` and the evaluation map
  `M ⊗ L^∨ ⟶ R\mathcal H\!\mathit{om}(L, M)`.

Source/core/bridge triage:
- `source-facing`: `ringedSiteDerivedDual` and `ringedSiteDerivedEvaluationHom`;
- `core/canonical`: `RingedSiteDerived J 𝒪`, `ihom`, and
  `ringedSiteDerivedTensorInternalHomComparison`;
- `bridge/view`: the specialization to the tensor unit and the right-unitor map
  `(ihom L).map (ρ_ M).hom`. -/

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪

/-- The derived dual `L^\vee = R\mathcal H\!\mathit{om}(L, \mathcal O)` on the derived category
of modules over a ringed site, realized as internal Hom into the monoidal unit. -/
noncomputable abbrev ringedSiteDerivedDual (L : D) : D :=
  (ihom L).obj (𝟙_ D)

@[inherit_doc ringedSiteDerivedDual]
notation:max L:max "^∨" => ringedSiteDerivedDual L

/-- 21.35.9.1: for objects `M` and `L` of `D(\mathcal O)` on a ringed site, there is a canonical
morphism
`M \otimes_\mathcal O^{\mathbf L} L^\vee \to R\mathcal H\!\mathit{om}(L, M)`.
Here `L^\vee` is the derived dual `R\mathcal H\!\mathit{om}(L, \mathcal O)`. The morphism is
the tensor-unit specialization of the canonical tensor-internal-Hom comparison, followed by the
right-unitor identification `M \otimes \mathbf 1 ≅ M` inside the target internal Hom. -/
noncomputable abbrev ringedSiteDerivedEvaluationHom
    (L M : D) :
    M ⊗ L^∨ ⟶ (ihom L).obj M :=
  ringedSiteDerivedTensorInternalHomComparison M (𝟙_ D) L ≫
    (ihom L).map (ρ_ M).hom

end

end SheafOfModules.RingedSite
