import Mathlib
import stacks_proof.stacks_project.Chap18.Lemma_18_33_8

open CategoryTheory

universe u

noncomputable section

namespace SheafOfModules.RingedSite

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for 18.35.0.2:
- primary domain: the conormal morphism attached to the canonical presentation of an
  `\mathcal A`-algebra sheaf `\mathcal B`;
- sampled owner declarations:
  `conormalMap`;
- best owner abstraction: the canonical presentation data lives in
  `Chap17.Definition_17_31_6`, while the conormal morphism itself is the site-level owner
  `conormalMap` from Lemma `18.33.8`;
- primitive data: a sheaf of commutative rings `𝒜`, an `𝒜`-algebra sheaf `𝒝 : Under 𝒜`, the
  canonical presentation morphisms `presentationBase 𝒜 𝒝 : 𝒜 ⟶ 𝒜[𝒝]` and
  `presentationMap 𝒜 𝒝 : 𝒜[𝒝] ⟶ 𝒝.right`;
- derived API: only the specialization of the generic conormal owner to that canonical
  presentation.

Source/core/bridge triage:
- `source-facing`: Equation `18.35.0.2`, the conormal morphism of the canonical presentation;
- `core/canonical`: `conormalMap`;
- `bridge/view`: the canonical presentation maps `presentationBase` and `presentationMap` from
  `Chap17.Definition_17_31_6`, used when specializing this owner.

This file remains recall-only: Equation `18.35.0.2` is the specialization of the chapter owner
`conormalMap` to the canonical presentation `presentationBase 𝒜 𝒝` and `presentationMap 𝒜 𝒝`. -/

/- 18.35.0.2: the canonical morphism
`\mathcal I/\mathcal I^2 \to \Omega_{\mathcal A[\mathcal B]/\mathcal A}
\otimes_{\mathcal A[\mathcal B]} \mathcal B`
is the specialization of the site-level conormal owner `conormalMap` to the canonical
presentation `presentationBase 𝒜 𝒝` and `presentationMap 𝒜 𝒝`. -/

end SheafOfModules.RingedSite
