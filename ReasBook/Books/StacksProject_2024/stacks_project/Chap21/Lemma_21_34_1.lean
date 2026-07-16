import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_6
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

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
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.34.1:
- primary domain: the braided closed monoidal structure on cochain complexes of `𝒪`-modules
  on a ringed site;
- sampled owner declarations:
  `MonoidalClosed.braidedHomEquiv`,
  `MonoidalClosed.internalHomTensorIso`,
  `ihom.adjunction`,
  `Adjunction.rightAdjointUniq`;
- best owner abstraction: the canonical owner is the generic braided closed-monoidal currying
  isomorphism `MonoidalClosed.internalHomTensorIso`, specialized here to the complex category
  `CpxO`;
- primitive data: only the ambient braided monoidal closed structure on `CpxO` and the three
  complexes `K`, `L`, `M`;
- derived API: the ringed-site specialization
  `K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.1 for complexes of `𝒪`-modules on a ringed site;
- `core/canonical`: `MonoidalClosed.internalHomTensorIso`;
- `bridge/view`: the specialization from the generic braided closed-monoidal owner to `CpxO`.

This file therefore remains at the `bridge/view` layer and directly reuses the owner theorem
instead of rebuilding a parallel ringed-site-specific right-adjoint-uniqueness bridge. -/

/- Lemma 21.34.1: for cochain complexes `K`, `L`, and `M` of `𝒪`-modules on a ringed site,
there is a canonical isomorphism
`K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M`.
In the project API this is exactly `MonoidalClosed.internalHomTensorIso`, specialized to `CpxO`.
-/
recall CategoryTheory.MonoidalClosed.internalHomTensorIso

/- Specialized check for Lemma 21.34.1 on cochain complexes of `𝒪`-modules. -/
#check
  (internalHomTensorIso : ∀ K L M : CpxO, K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M)

end

end SheafOfModules.RingedSite
