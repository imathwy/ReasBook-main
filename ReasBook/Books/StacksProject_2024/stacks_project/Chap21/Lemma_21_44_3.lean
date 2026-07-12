import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap20.Lemma_20_46_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.CochainComplex renaming
  tensorObj_isStrictlyPerfect_of_isStrictlyPerfect →
    ringedSpace_tensorObj_isStrictlyPerfect_of_isStrictlyPerfect

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.44.3:
- primary domain: total tensor products of strictly perfect cochain complexes of `𝒪`-modules
  on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsStrictlyPerfect`,
  `HomologicalComplex.tensorObj`,
  `AlgebraicGeometry.RingedSpace.CochainComplex.tensorObj_isStrictlyPerfect_of_isStrictlyPerfect`;
- best owner abstraction: the numbered item remains the source-facing owner theorem
  `SheafOfModules.RingedSite.CochainComplex.tensorObj_isStrictlyPerfect_of_isStrictlyPerfect`,
  stated directly on the canonical total tensor object `HomologicalComplex.tensorObj K L`; the
  Chapter 20 ringed-space theorem is only the opens-site specialization;
- primitive data: the complexes `K` and `L`, their strict-perfectness hypotheses, and the ambient
  total-tensor datum `[HomologicalComplex.HasTensor K L]`;
- derived API: none; the owner theorem itself is the source-facing item.

Source/core/bridge triage:
- `source-facing`: Lemma 21.44.3 for complexes of `𝒪`-modules on a ringed site;
- `core/canonical`: the owner theorem
  `SheafOfModules.RingedSite.CochainComplex.tensorObj_isStrictlyPerfect_of_isStrictlyPerfect`;
- `bridge/view`: none; the numbered item is the owner theorem itself, so no parallel wrapper
  theorem should remain. -/
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "ringedSpaceTensorObjIsStrictlyPerfect" =>
  @ringedSpace_tensorObj_isStrictlyPerfect_of_isStrictlyPerfect
    _ (ringSheaf J 𝒪) inferInstance inferInstance inferInstance inferInstance inferInstance

namespace CochainComplex

-- Proof sketch: boundedness of the total tensor complex follows from boundedness of the two
-- strictly perfect inputs. In each degree, the tensor term is built from finitely many tensor
-- products of finite-free retracts, hence is again a finite-free retract.
--
/-- Lemma 21.44.3: the canonical total tensor product of two strictly perfect complexes of
`𝒪`-modules on a commutative ringed site is strictly perfect. -/
@[stacks 09J8]
theorem tensorObj_isStrictlyPerfect_of_isStrictlyPerfect
    (K L : Cpx) [HomologicalComplex.HasTensor K L]
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (HomologicalComplex.tensorObj K L) := by
  rw [CochainComplex.isStrictlyPerfect_iff_ringedSpace] at hK hL
  simpa [CochainComplex.isStrictlyPerfect_iff_ringedSpace] using
    ringedSpaceTensorObjIsStrictlyPerfect K L hK hL

end CochainComplex

end

end SheafOfModules.RingedSite
