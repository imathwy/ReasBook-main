import Mathlib
import StacksProject_2024.Chap18.Example_18_29_1
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.4:
- primary domain: invertible objects and duality in the symmetric monoidal closed category
  `ringedSiteModuleCategory J 𝒪`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `ringedSiteModuleDual`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.nonempty_iso_ringedSiteModuleDual_of_tensor_inverse`;
- best owner abstraction:
  `IsInvertible` on `ringedSiteModuleCategory J 𝒪`, with the tensor product `ℒ ⊗ 𝒩`,
  `ringedSiteModuleDual`, and the closed-structure evaluation at the tensor unit as derived API;
- primitive data:
  invertible modules `ℒ` and `𝒩`;
- derived API:
  invertibility of `ℒ ⊗ 𝒩`, invertibility of `ringedSiteModuleDual ℒ`, and the `IsIso`
  statement for the evaluation map at `SheafOfModules.unit (ringSheaf J 𝒪)`.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 18.32.4;
- `core/canonical`: `IsInvertible`, `ringedSiteModuleDual`, and
  `(ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))`;
- `bridge/view`: the tensor-inverse and dual-comparison theorems from Lemma 18.32.2.
-/

section Tensor

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: right tensoring by `\mathcal L \otimes_{\mathcal O} \mathcal N` is the composite
-- of right tensoring by `\mathcal L` and by `\mathcal N`, so it is an equivalence when each
-- factor is.
/-- Lemma 18.32.4 (1): if `\mathcal L` and `\mathcal N` are invertible `\mathcal O`-modules on a
ringed site, then their tensor product `\mathcal L \otimes_{\mathcal O} \mathcal N` is
invertible. -/
theorem isInvertible_tensor_of_isInvertible
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] [IsInvertible 𝒩] :
    IsInvertible (ℒ ⊗ 𝒩) := sorry

instance instIsInvertibleTensor
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] [IsInvertible 𝒩] :
    IsInvertible (ℒ ⊗ 𝒩) :=
  isInvertible_tensor_of_isInvertible ℒ 𝒩

end Tensor

section Duality

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: by Lemma `18.32.2 (1)`, choose a tensor inverse `𝒩` for `ℒ`; then Lemma
-- `18.32.2 (5)` identifies `𝒩` with `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L,
-- \mathcal O)`, so the internal Hom inherits invertibility from the tensor inverse.
/-- Lemma 18.32.4 (2): if `\mathcal L` is an invertible `\mathcal O`-module on a ringed site,
then `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)` is invertible. -/
theorem isInvertible_internalHom_unit_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsInvertible (ringedSiteModuleDual ℒ) := sorry

instance instIsInvertibleRingedSiteModuleDual
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsInvertible (ringedSiteModuleDual ℒ) :=
  isInvertible_internalHom_unit_of_isInvertible ℒ

-- Proof sketch: identify `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)` with a
-- tensor inverse of `ℒ` via Lemma `18.32.2 (5)`. Under this identification, the evaluation map
-- becomes the chosen trivialization `\mathcal L \otimes_{\mathcal O} \mathcal L^\vee \cong
-- \mathcal O`, hence it is an isomorphism.
/-- Lemma 18.32.4 (3): for an invertible `\mathcal O`-module `\mathcal L` on a ringed site, the
evaluation map
`\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)
\to \mathcal O` is an isomorphism. -/
theorem isIso_internalHom_unit_evaluation_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) := sorry

instance instIsIsoInternalHomUnitEvaluation
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) :=
  isIso_internalHom_unit_evaluation_of_isInvertible ℒ

end Duality

end SheafOfModules.RingedSite
