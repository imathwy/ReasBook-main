import Mathlib
import StacksProject_2024.Chap18.«18_19_2_1»
import StacksProject_2024.Chap18.Lemma_18_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.30.4:
- primary domain: sheaves of modules on a ringed site, the standard summands
  `j_{U!}\mathcal O_U`, and preservation of direct sums by the represented additive Hom-functor;
- sampled owner declarations:
  `localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_homEquiv`,
  `quasiCompactObject_module_evaluation_preserves_direct_sums`,
  `preadditiveCoyoneda.obj`;
- best owner abstraction: the chapter owner
  `localizedStructureModuleExtensionByZero 𝒪 U = j_{U!}\mathcal O_U`, with the source-facing
  sections comparison carried by
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`;
- primitive-vs-derived split: the primitive data are only the ringed site `(C, J, 𝒪)`, the object
  `U`, the quasi-compactness hypothesis on `U`, and the index type `ι`; the represented additive
  Hom-functor and its sections comparison are derived from the owner
  `localizedStructureModuleExtensionByZero 𝒪 U` and the bridge
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that `Hom_\mathcal O(j_{U!}\mathcal O_U, -)` preserves
  direct sums for quasi-compact `U`;
- `core/canonical`: the chapter owner `localizedStructureModuleExtensionByZero 𝒪 U` together with
  the evaluation-preserves-direct-sums theorem
  `quasiCompactObject_module_evaluation_preserves_direct_sums`;
- `bridge/view`: the comparison
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`.

This file should therefore state the lemma directly on
`preadditiveCoyoneda.obj (op (localizedStructureModuleExtensionByZero 𝒪 U))`, deriving the
sections comparison through `localizedStructureModuleExtensionByZero_homEquiv` instead of exposing
the raw pullback/unit implementation term in the public statement. -/

-- Proof sketch: identify `Hom_\mathcal O(j_{U!}\mathcal O_U, -)` with the sections functor
-- `\mathcal F ↦ \mathcal F(U)` via `localizedStructureModuleExtensionByZero_homEquiv`, then apply
-- the quasi-compact direct-sum preservation statement for sections from Lemma `18.30.3`.
/-- Lemma 18.30.4: if `U` is quasi-compact in a ringed site `(\mathcal C, \mathcal O)`, then the
additive Hom-functor represented by `j_{U!}\mathcal O_U` preserves direct sums. -/
theorem localizedStructureModuleExtensionByZero_hom_preserves_directSums
    (hU : J.QuasiCompactObject U) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op (localizedStructureModuleExtensionByZero 𝒪 U))) := sorry

end SheafOfModules.RingedSite
