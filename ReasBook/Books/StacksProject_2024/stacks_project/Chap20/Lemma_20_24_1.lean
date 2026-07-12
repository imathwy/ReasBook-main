import StacksProject_2024.Chap20.Open_cover_module_cech_core

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.24.1:
- primary domain: module-valued Čech resolutions on a ringed space, built from restriction to
  open subspaces, pushforward back to the ambient space, and the alternating Čech differential on
  tuple intersections;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `openCoverModuleCechComplex`,
  `openCoverModuleCechAugmentation`,
  `QuasiIso`;
- best owner abstraction: the source-facing module-valued Čech augmentation should be stated on the
  shared Chapter 20 canonical owners `openCoverModuleCechComplex` and
  `openCoverModuleCechAugmentation` from `Open_cover_module_cech_core`, which package the explicit
  term, differential, and degree-zero augmentation map into the repository's reusable owner layer.

Primitive data is only the ringed space `X`, the open family `𝒰`, and the module `ℱ`. The
module-valued Čech complex and its augmentation are imported reusable owner data; this file stays
source-facing only in asserting that the resulting canonical augmentation from `ℱ[0]` to the Čech
complex is a quasi-isomorphism.

Source/core/bridge triage:
- `source-facing`: `openCoverModuleCechAugmentation_quasiIso`;
- `core/canonical`: the imported Chapter 20 owners `openCoverModuleCechComplex` and
  `openCoverModuleCechAugmentation`;
- `bridge/view`: none; the source-facing theorem is stated directly on the imported augmentation
  owner. -/

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "ModX" => RingedSpace.Modules X

variable [Abelian ModX]
variable (𝒰 : ι → Opens X.carrier) (ℱ : ModX)

-- Proof sketch: the source-facing complex is the explicit module-valued Čech complex whose
-- degree-`p` term is the product over the pushed-forward restrictions from the tuple
-- intersections. The displayed augmentation is the usual degree-zero Čech augmentation. The usual
-- Čech-resolution argument for an open cover shows that this augmentation is a quasi-isomorphism.
/-- Lemma 20.24.1: for a ringed space `X`, an open cover `𝒰`, and an `𝒪_X`-module `ℱ`, the
canonical augmentation from `ℱ[0]` to the module-valued Čech complex with degree-`p` term
`∏_{i₀,…,iₚ}(j_{i₀ … iₚ})_* ℱ_{i₀ … iₚ}` is a
quasi-isomorphism. -/
@[stacks 02FU]
instance openCoverModuleCechAugmentation_quasiIso
    [Fact (IsOpenCover 𝒰)] :
    QuasiIso (openCoverModuleCechAugmentation 𝒰 ℱ) := by
  sorry

theorem openCoverModuleCechAugmentation_quasiIso_of_isOpenCover
    (h𝒰 : IsOpenCover 𝒰) :
    QuasiIso (openCoverModuleCechAugmentation 𝒰 ℱ) := by
  let _ : Fact (IsOpenCover 𝒰) := ⟨h𝒰⟩
  infer_instance

end AlgebraicGeometry.RingedSpace
