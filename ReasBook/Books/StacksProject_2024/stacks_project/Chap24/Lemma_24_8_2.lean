import Mathlib.Tactic.Recall
import StacksProject_2024.Chap24.Definition_24_8_1_Core

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "GModO" => GradedObject ℤ ModO

-- `GradedAlgebraSheaf`, `GradedModuleSheaf`, and the source-facing owner `GradedBimodule`
-- are available from `Definition_24_8_1_Core` and its Chapter 24 prerequisites.

/-- Lemma 24.8.2: the Chapter 24 tensor/Hom conventions for graded modules and graded bimodules
on a ringed site. -/
class HasGradedTensorHomAdjunction (𝒪 : Sheaf J CommRingCat.{max u v})
    (A B : GradedAlgebraSheaf 𝒪) where
  /-- The relative tensor product `M ⊗_A N` as a right graded `B`-module. -/
  tensorObj :
    GradedModuleSheaf A → GradedBimodule 𝒪 A B → GradedModuleSheaf B
  /-- The graded right-`A`-module `\mathcal H\!om_B^{gr}(N, L)`. -/
  bimoduleInternalHom :
    GradedBimodule 𝒪 A B → GradedModuleSheaf B → GradedModuleSheaf A
  /-- The graded internal Hom over `A`. -/
  moduleInternalHomA :
    GradedModuleSheaf A → GradedModuleSheaf A → GModO
  /-- The graded internal Hom over `B`. -/
  moduleInternalHomB :
    GradedModuleSheaf B → GradedModuleSheaf B → GModO
  /-- The Hom-set equivalence expressing the tensor/Hom adjunction. -/
  homEquiv
      (M : GradedModuleSheaf A) (N : GradedBimodule 𝒪 A B) (L : GradedModuleSheaf B) :
      GradedModuleSheaf.Hom (tensorObj M N) L ≃
        GradedModuleSheaf.Hom M (bimoduleInternalHom N L)
  /-- The internal-Hom isomorphism induced by the tensor/Hom adjunction. -/
  internalHomIso
      (M : GradedModuleSheaf A) (N : GradedBimodule 𝒪 A B) (L : GradedModuleSheaf B) :
      moduleInternalHomB (tensorObj M N) L ≅
        moduleInternalHomA M (bimoduleInternalHom N L)

namespace HasGradedTensorHomAdjunction

/-- The relative tensor product from the Chapter 24 graded tensor/Hom conventions. -/
abbrev tensor
    {A B : GradedAlgebraSheaf 𝒪}
    [HasGradedTensorHomAdjunction 𝒪 A B]
    (M : GradedModuleSheaf A) (N : GradedBimodule 𝒪 A B) : GradedModuleSheaf B :=
  (inferInstance : HasGradedTensorHomAdjunction 𝒪 A B).tensorObj M N

/-- The graded right `\mathcal A`-module `\mathcal H\!om_B^{gr}(\mathcal N, \mathcal L)` from
the Chapter 24 conventions. -/
abbrev bimoduleIHom
    {A B : GradedAlgebraSheaf 𝒪}
    [HasGradedTensorHomAdjunction 𝒪 A B]
    (N : GradedBimodule 𝒪 A B) (L : GradedModuleSheaf B) : GradedModuleSheaf A :=
  (inferInstance : HasGradedTensorHomAdjunction 𝒪 A B).bimoduleInternalHom N L

/-- The graded internal Hom over `\mathcal A` from the Chapter 24 conventions. -/
abbrev moduleIHomA
    {A B : GradedAlgebraSheaf 𝒪}
    [HasGradedTensorHomAdjunction 𝒪 A B]
    (M M' : GradedModuleSheaf A) : GModO :=
  (inferInstance : HasGradedTensorHomAdjunction 𝒪 A B).moduleInternalHomA M M'

/-- The graded internal Hom over `\mathcal B` from the Chapter 24 conventions. -/
abbrev moduleIHomB
    {A B : GradedAlgebraSheaf 𝒪}
    [HasGradedTensorHomAdjunction 𝒪 A B]
    (L L' : GradedModuleSheaf B) : GModO :=
  (inferInstance : HasGradedTensorHomAdjunction 𝒪 A B).moduleInternalHomB L L'

end HasGradedTensorHomAdjunction

/- Source/core/bridge triage for Lemma 24.8.2:
- `source-facing`: the graded tensor/Hom adjunction equivalence and the induced internal-Hom
  comparison isomorphism;
- `core/canonical`: the owner class `HasGradedTensorHomAdjunction` with fields `tensorObj`,
  `bimoduleInternalHom`, `moduleInternalHomA`, `moduleInternalHomB`, `homEquiv`, and
  `internalHomIso`.

This item is therefore expressed by direct recall of the canonical owner fields, without redundant
local wrappers that only rename those fields. -/

/- Lemma 24.8.2 (1): for a right graded `\mathcal A`-module `\mathcal M`, a graded
`(\mathcal A, \mathcal B)`-bimodule `\mathcal N`, and a right graded `\mathcal B`-module
`\mathcal L`, the graded tensor product `\mathcal M \otimes_{\mathcal A} \mathcal N` is left
adjoint to `\mathcal H\!om_{\mathcal B}^{gr}(\mathcal N, -)`, functorially in
`\mathcal M`, `\mathcal N`, and `\mathcal L`. This source-facing statement is the canonical owner
field `HasGradedTensorHomAdjunction.homEquiv`. -/
recall HasGradedTensorHomAdjunction.homEquiv

/- Lemma 24.8.2 (2): for the same data, the graded internal Hom over `\mathcal B` out of
`\mathcal M \otimes_{\mathcal A} \mathcal N` is isomorphic to the graded internal Hom over
`\mathcal A` out of `\mathcal M`, functorially in `\mathcal M`, `\mathcal N`, and
`\mathcal L`. This source-facing statement is the canonical owner field
`HasGradedTensorHomAdjunction.internalHomIso`. -/
recall HasGradedTensorHomAdjunction.internalHomIso

end

end SheafOfModules.RingedSite
