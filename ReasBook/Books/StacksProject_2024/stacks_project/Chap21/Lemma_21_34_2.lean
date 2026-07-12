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
notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.34.2:
- primary domain: internal-Hom composition in the braided closed monoidal category of cochain
  complexes of `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `MonoidalClosed.comp`,
  `MonoidalClosed.internalHomTensorIso`,
  `MonoidalClosed.braidedHomEquiv`,
  `A ⟶[CpxO] B`;
- best owner abstraction: the ambient closed-monoidal composition morphism `comp K L M` on `CpxO`;
  the Stacks Project source order is obtained by braiding the two internal-Hom factors into the
  owner order expected by `comp`;
- primitive data: the ambient braided monoidal closed structure on `CpxO` and the three complexes
  `K`, `L`, `M`;
- derived API: the source-order comparison morphism below.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.2;
- `core/canonical`: `comp K L M` and the ambient internal-Hom owner `A ⟶[CpxO] B`;
- `bridge/view`: the braiding that swaps the Stacks source order into the canonical owner order.

This file therefore stays at the `bridge/view` layer. It keeps the source-facing morphism but
builds it directly from the canonical owner instead of spelling a parallel entrywise construction.
-/

/-- Lemma 21.34.2: for a ringed site `(𝒞, 𝒪)` and cochain complexes `K`, `L`, `M` of
`𝒪`-modules, there is a canonical morphism
`((L ⟶[CpxO] M) ⊗ (K ⟶[CpxO] L)) ⟶ (K ⟶[CpxO] M)`,
formalizing the source composition map
`Tot(ℋom(L, M) ⊗ ℋom(K, L)) ⟶ ℋom(K, M)`.
In the canonical closed-monoidal owner, this is the braided source-order transport of
`MonoidalClosed.comp K L M`. -/
@[stacks 0A91]
noncomputable def internalHomComplexComposition
    (K L M : CpxO) :
    ((L ⟶[CpxO] M) ⊗ (K ⟶[CpxO] L)) ⟶ (K ⟶[CpxO] M) :=
  (β_ (L ⟶[CpxO] M) (K ⟶[CpxO] L)).hom ≫ MonoidalClosed.comp K L M

end

end SheafOfModules.RingedSite
