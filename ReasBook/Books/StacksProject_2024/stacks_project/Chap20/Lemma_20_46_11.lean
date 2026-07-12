import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap21.Lemma_21_44_10

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxX] " B:19 => (ihom A).obj B
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 20.46.11:
- primary domain: derived internal Hom for complexes of `𝒪_X`-modules on a ringed space,
  represented by the canonical internal-Hom complex under boundedness and termwise
  finite-free-retract hypotheses;
- inspected owner declarations:
  `ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract`;
- best owner abstraction:
  the Chapter 21 ringed-site theorem together with its explicit-bounds companion; this Chapter 20
  file is the corresponding ringed-space `bridge/view`, stated directly for
  `CochainComplex (RingedSpace.Modules X) ℤ`;
- primitive data: the ringed space `X`, the complexes `E` and `F`, the bounded-below hypothesis
  on `F`, the bounded-above hypothesis on `E`, and the explicit degreewise
  `SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf` hypothesis on `E`;
- derived API:
  the source-facing Chapter 20 bridge theorem below together with its explicit-bounds companion.

Source/core/bridge triage:
- `source-facing`: Lemma 20.46.11 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the Chapter 21 owner
  `ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract`;
- `bridge/view`: specialization to the canonical opens ringed site of `X`, while keeping the
  public theorem surface in `AlgebraicGeometry.RingedSpace`.
-/

/-- Lemma 20.46.11: for complexes `E` and `F` of `𝒪_X`-modules on a ringed space, if `F` is
bounded below, `E` is bounded above, and each term of `E` is a direct summand of a finite free
`𝒪_X`-module, then the derived internal Hom from `E` to `F` is represented by the canonical
internal-Hom complex `E ⟶[CpxX] F`. This is the ringed-space specialization of the canonical
Chapter 21 ringed-site owner theorem. -/
@[stacks 08I5]
theorem moduleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract
    (E F : CpxX)
    (hF_boundedBelow : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE_boundedAbove : ∃ b : ℤ, E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj (E ⟶[CpxX] F))
      (DerivedCategory.Q.obj E ⟹ DerivedCategory.Q.obj F) := by
  simpa using
    ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract
      E F hF_boundedBelow hE_boundedAbove hE_termwise_finiteFreeRetract

/-- Explicit-bounds companion to Lemma 20.46.11. It keeps the Chapter 20 ringed-space surface but
replaces the existential boundedness hypotheses by chosen bounds `a` and `b`. -/
theorem moduleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyGE_of_isStrictlyLE_of_termwise_finiteFreeRetract
    (E F : CpxX) {a b : ℤ}
    (hF_boundedBelow : F.IsStrictlyGE a)
    (hE_boundedAbove : E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj (E ⟶[CpxX] F))
      (DerivedCategory.Q.obj E ⟹ DerivedCategory.Q.obj F) := by
  simpa using
    ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyGE_of_isStrictlyLE_of_termwise_finiteFreeRetract
      E F hF_boundedBelow hE_boundedAbove hE_termwise_finiteFreeRetract

end

end AlgebraicGeometry.RingedSpace
