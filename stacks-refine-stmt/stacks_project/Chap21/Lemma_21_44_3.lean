import Mathlib
import stacks_project.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.3:
- primary domain: total tensor products of strictly perfect cochain complexes of `\mathcal O`-modules
  on a ringed site;
- sampled owner declarations:
  `RingedSiteModules`,
  `CochainComplex.IsStrictlyPerfect`,
  `HomologicalComplex.HasTensor`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the source-facing notion is still
  `CochainComplex.IsStrictlyPerfect`, but the tensor product complex itself should be the canonical
  total tensor object `HomologicalComplex.tensorObj K L`, not an arbitrary monoidal tensor on the
  whole complex category;
- primitive data: the ambient monoidal module category `RingedSiteModules J 𝒪`, the additive
  hypotheses needed for the total tensor construction, the complexes `K`, `L`, and the instance
  `[HomologicalComplex.HasTensor K L]`;
- derived API: this lemma is the ringed-site source-facing strict-perfectness statement for that
  canonical total tensor object.

Source/core/bridge triage:
- `source-facing`: strict perfectness of the tensor product complex on a ringed site;
- `core/canonical`: `HomologicalComplex.tensorObj`;
- `bridge/view`: this file is a thin source-facing specialization of the canonical total tensor
  owner to strict perfectness on `RingedSiteModules J 𝒪`. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [HasZeroObject (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteModules J 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules J 𝒪)]
variable [(curriedTensor (RingedSiteModules J 𝒪)).Additive]
variable [∀ M : RingedSiteModules J 𝒪,
  ((curriedTensor (RingedSiteModules J 𝒪)).obj M).Additive]

variable {K L : CochainComplex (RingedSiteModules J 𝒪) ℤ}
variable [HomologicalComplex.HasTensor K L]

-- Proof sketch: boundedness of the tensor total complex follows from boundedness of `K` and `L`.
-- In each degree, the total tensor term is assembled from finitely many tensor products of terms of
-- `K` and `L`; since retracts of finite free module sheaves are preserved under these finite
-- tensor/direct-sum constructions, each degree remains a retract of a finite free module sheaf.
/-- Lemma 21.44.3: the total complex associated to the tensor product of two strictly perfect
complexes of `\mathcal O`-modules on a ringed site is strictly perfect. In Lean, this total
complex is the canonical total tensor product `HomologicalComplex.tensorObj K L`. -/
theorem tensor_isStrictlyPerfect_of_isStrictlyPerfect
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (HomologicalComplex.tensorObj K L) := sorry

end

end SheafOfModules.RingedSite
