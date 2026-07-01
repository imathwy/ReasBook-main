import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w u v

/-
Domain-style sampling for Lemma 17.10.2:
- primary domain: quasi-coherent sheaves of modules and their binary direct sums/biproducts;
- inspected owner declarations:
  `SheafOfModules.isQuasicoherent`,
  `SheafOfModules.Presentation.of_isIso`,
  `CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan`,
  `CategoryTheory.Limits.BinaryBiproduct.isLimit`,
  `CategoryTheory.HasBinaryBiproduct.of_hasBinaryProduct`;
- best owner abstraction: the canonical object property `SheafOfModules.isQuasicoherent R`;
- primitive data: two quasi-coherent sheaves of modules `M` and `N`;
- derived API: the source-facing direct-sum statement, with the binary-product cone used only as
  an internal bridge to the canonical owner abstraction.

Source/core/bridge triage:
- `source-facing`: the binary direct sum of two quasi-coherent modules is quasi-coherent;
- `core/canonical`: the owner predicate `SheafOfModules.isQuasicoherent R`;
- `bridge/view`: `BinaryBiproduct.isLimit M N`, viewing the source-facing direct sum as the
  binary-product cone used by the owner API.
-/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Proof sketch: refine the local quasi-coherent presentations of the two summands to a common
-- cover, take the biproduct of the resulting local cokernel presentations, and then package that
-- local construction through the owner-level binary-product bridge.
/-- Lemma 17.10.2: the direct sum of two quasi-coherent `\mathcal O_X`-modules is
quasi-coherent. -/
theorem isQuasicoherent_biprod
    {M N : SheafOfModules.{w} R} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  letI : (SheafOfModules.isQuasicoherent R).IsClosedUnderBinaryProducts := by
    sorry
  simpa using (SheafOfModules.isQuasicoherent R).prop_of_isLimit_binaryFan
    (BinaryBiproduct.isLimit M N) inferInstance inferInstance

instance instIsQuasicoherentBiprod
    {M N : SheafOfModules.{w} R} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent :=
  isQuasicoherent_biprod

end SheafOfModules
