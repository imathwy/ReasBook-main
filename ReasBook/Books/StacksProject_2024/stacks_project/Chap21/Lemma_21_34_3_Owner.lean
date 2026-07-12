import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B

/- Domain-style sampling for the owner layer of Lemma 21.34.3:
- primary domain: tensor-internal-Hom comparison in the closed braided monoidal category of
  cochain complexes of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry`,
  `(ihom.ev M).app L`,
  the canonical internal-Hom notation `A ⟶[CpxO] B`;
- best owner abstraction:
  the source-facing comparison morphism is the curried braiding/evaluation composite in the
  ambient complex category `CpxO`, with `ringedSiteModuleCategory J 𝒪` as the canonical owner
  for the ringed-site module category;
- primitive data:
  the complexes `K`, `L`, and `M`;
- derived API:
  the tensor-internal-Hom comparison together with its `uncurry` specification.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.3;
- `core/canonical`: `MonoidalClosed.curry`, `MonoidalClosed.uncurry`, and `(ihom.ev M).app L`;
- `bridge/view`: the ringed-site specialization of the ambient complex category `CpxO`. -/

/-- Lemma 21.34.3: for a ringed site `(𝒞, 𝒪)` and cochain complexes `K`, `L`, `M : CpxO`,
there is a canonical morphism
`K ⊗ (M ⟶[CpxO] L) ⟶ (M ⟶[CpxO] (K ⊗ L))`,
formalizing the source map
`Tot (𝒦^• ⊗_𝒪 Hom^•(𝓜^•, 𝓛^•)) ⟶ Hom^•(𝓜^•, Tot (𝒦^• ⊗_𝒪 𝓛^•))`.
In the canonical owner, this is the transpose of the braiding/evaluation composite above. -/
@[stacks 0BYT]
noncomputable def ringedSiteModuleComplexTensorInternalHomComparison
    (K L M : CpxO) :
    K ⊗ (M ⟶[CpxO] L) ⟶ (M ⟶[CpxO] (K ⊗ L)) :=
  curry
    ((α_ M K (M ⟶[CpxO] L)).inv ≫
      (β_ M K).hom ▷ (M ⟶[CpxO] L) ≫
      (α_ K M (M ⟶[CpxO] L)).hom ≫
      K ◁ (ihom.ev M).app L)

/- Uncurrying the ringed-site tensor-Hom comparison recovers its defining braiding/evaluation
composite. -/
@[simp]
theorem ringedSiteModuleComplexTensorInternalHomComparison_uncurry
    (K L M : CpxO) :
    uncurry (ringedSiteModuleComplexTensorInternalHomComparison K L M) =
      (α_ M K (M ⟶[CpxO] L)).inv ≫
        (β_ M K).hom ▷ (M ⟶[CpxO] L) ≫
        (α_ K M (M ⟶[CpxO] L)).hom ≫
        K ◁ (ihom.ev M).app L := by
  simp [ringedSiteModuleComplexTensorInternalHomComparison]

end

end SheafOfModules.RingedSite
