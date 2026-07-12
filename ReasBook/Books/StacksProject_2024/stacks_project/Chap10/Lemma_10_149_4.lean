import Mathlib
import StacksProject_2024.Chap10.Definition_10_149_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Algebra
open Algebra.Extension
open scoped TensorProduct

universe u v w x

namespace Algebra.Extension

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 10.149.4:
- primary domain: localization behavior of universal first-order thickenings and their conormal
  modules in the `Algebra.Extension` API;
- sampled owner declarations:
  `Extension.localization`,
  `Extension.toLocalization`,
  `Extension.Hom`,
  `Extension.Cotangent`,
  `Extension.Cotangent.map`;
- best owner abstraction: the ambient owner remains `Extension`; this file is a
  `source-facing` localization statement phrased on the canonical owner
  `Extension.localization`, and the canonical comparison map is the owner-level bridge
  `Extension.toLocalization`;
- primitive data vs. derived API:
  the primitive data are the extension `P` and the localization choices of the source or target
  algebra, while the comparison morphism `Extension.toLocalization` and the induced conormal-module
  maps are derived from the owner APIs `Extension.Hom` and `Extension.Cotangent.map`;
- source/core/bridge triage:
  `source-facing`: the two localization clauses of Lemma 10.149.4,
  `core/canonical`: `Extension.localization` and `Extension.Cotangent`,
  `bridge/view`: the canonical owner-level localization map `Extension.toLocalization`. -/

/-- The canonical hom from an extension to any localization of its target algebra. -/
noncomputable def toLocalization (P : Extension R S) (T : Submonoid S)
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [IsLocalization T S'] :
    P.Hom (P.localization T : Extension R S') where
  toRingHom := algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom x := congrArg (fun f : P.Ring →+* S' ↦ f x) (IsLocalization.map_comp le_rfl)

section

variable (P : Extension R S)

variable (M : Submonoid R)
variable {Sₘ : Type w} [CommRing Sₘ] [Algebra R Sₘ] [Algebra S Sₘ] [IsScalarTower R S Sₘ]
  [IsLocalization (M.map (algebraMap R S)) Sₘ]

variable (T : Submonoid S)
variable {Sₜ : Type x} [CommRing Sₜ] [Algebra R Sₜ] [Algebra S Sₜ] [IsScalarTower R S Sₜ]
  [IsLocalization T Sₜ]

local notation "Pₘ" => ((P.localization (M.map (algebraMap R S)) : Extension R Sₘ))
local notation "Pₜ" => ((P.localization T : Extension R Sₜ))

-- Proof sketch: for localization from the source, lift maps out of the localized square-zero
-- quotient by composing with `B → S⁻¹B`, use universality of `P`, and then localize the resulting
-- lift because the image of `M` becomes invertible. For localization from the target, apply the
-- same argument directly to the multiplicative subset of `B`; the inverse maps are obtained by the
-- defining universal properties on the localized targets.
/-- Lemma 10.149.4 (1): the canonical localization of a universal first-order thickening at the
image of a multiplicative subset of the source ring is again a universal first-order thickening. -/
theorem universalFirstOrderThickening_sourceLocalization
    (hP : P.IsUniversalFirstOrderThickening) :
    (Pₘ).IsUniversalFirstOrderThickening := sorry

/-- Lemma 10.149.4 (2): localizing a universal first-order thickening along a multiplicative
subset of the target ring again yields the universal first-order thickening of the corresponding
localized algebra. -/
theorem universalFirstOrderThickening_targetLocalization
    (hP : P.IsUniversalFirstOrderThickening) :
    (Pₜ).IsUniversalFirstOrderThickening := sorry

-- Proof sketch: identify the cotangent module of a localization with the localization of the
-- original cotangent module by localizing the kernel ideal and checking that the canonical
-- comparison map on cotangent modules satisfies the module-localization universal property.
/-- The canonical map on conormal modules for source localization realizes the localized conormal
module. -/
theorem conormalModule_sourceLocalization_isLocalizedModule :
    IsLocalizedModule (M.map (algebraMap R S))
      (Extension.Cotangent.map (P.toLocalization (M.map (algebraMap R S)) : P.Hom Pₘ)) := sorry

-- Proof sketch: localizing the extension at a multiplicative subset of the target localizes its
-- kernel ideal, so the canonical cotangent map is the localization map of the conormal module.
/-- The canonical map on conormal modules for target localization realizes the localized conormal
module. -/
theorem conormalModule_targetLocalization_isLocalizedModule :
    IsLocalizedModule T
      (Extension.Cotangent.map (P.toLocalization T : P.Hom Pₜ)) := sorry

end

end Algebra.Extension
