import Mathlib
import stacks_project.Chap15.Lemma_15_65_13
import stacks_project.Chap15.Lemma_15_67_14
import stacks_project.Chap15.Lemma_15_75_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Ext" => ModuleCat.extendScalars (algebraMap A B)

/- Domain-style sampling for Lemma 15.75.10:
- primary domain: perfect modules viewed in degree `0` inside derived module categories and then
  transported across flat scalar extension;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `ModuleCat.IsPseudoCoherent`,
  `ModuleHasTorDimensionLE`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `ModuleCat.exists_moduleHasTorDimensionLE_of_isPerfect`;
- best owner abstraction: this file is a `bridge/view`; the source-facing module statement should
  keep `ModuleCat.IsPerfect` as the owner, but derive the base-change statement from the canonical
  perfectness characterization by pseudo-coherence and finite tor dimension, together with the
  existing module-level flat base-change bridges for those two ingredients;
- primitive vs. derived:
  primitive data are the flat map `A → B`, the module `M`, and the owner hypothesis `M.IsPerfect`;
  the derived API used here is pseudo-coherence and finite tor dimension of `M[0]`, repackaged
  canonically as `M.IsPseudoCoherent` and `ModuleHasFiniteTorDimension M`, then transported across
  flat scalar extension and reassembled into perfectness;
- source/core/bridge triage:
  `source-facing`: perfectness is preserved by flat scalar extension for modules;
  `core/canonical`: `DerivedCategory.IsPerfect`, `ModuleCat.IsPerfect`,
    `ModuleCat.IsPseudoCoherent`, and `HasFiniteTorDimension`;
  `bridge/view`: the module-level flat base-change theorems for pseudo-coherence and tor
    dimension. -/

-- Proof sketch: decompose `hM : M.IsPerfect` into pseudo-coherence plus finite tor dimension
-- using the owner theorem `ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`.
-- Transport pseudo-coherence by Lemma `15.65.13` and a finite tor-dimension bound by
-- Lemma `15.67.14`, then reassemble perfectness over `B` with the same owner theorem.
/-- Lemma 15.75.10: for a flat ring map `A → B`, the base change of a perfect `A`-module is a
perfect `B`-module. This is the module-level bridge/view of Lemma `15.75.9`. -/
theorem isPerfect_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat.{u} A) (hM : M.IsPerfect) :
    ((Ext).obj M).IsPerfect := by
  have hpcA : M.IsPseudoCoherent :=
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension M).1 hM |>.1
  have hpcB : ((Ext).obj M).IsPseudoCoherent :=
    isPseudoCoherent_extendScalars hflat M hpcA
  rcases ModuleCat.exists_moduleHasTorDimensionLE_of_isPerfect M hM with ⟨d, hd⟩
  have htorB : ModuleHasFiniteTorDimension ((Ext).obj M) :=
    (moduleHasTorDimensionLE_extendScalars hflat M d hd).hasFiniteTorDimension
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension ((Ext).obj M)).2
      ⟨hpcB, htorB⟩

end

end CategoryTheory
