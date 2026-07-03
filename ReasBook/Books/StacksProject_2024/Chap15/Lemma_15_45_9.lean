import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_130_3
import StacksProject_2024.Chap10.Lemma_10_163_3
import StacksProject_2024.Chap15.Lemma_15_45_1
import StacksProject_2024.Chap15.Lemma_15_45_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

local notation "ClosedFiberH" => Ideal.Fiber (maximalIdeal R) Rh
local notation "ClosedFiberSh" => Ideal.Fiber (maximalIdeal R) Rsh

private noncomputable def closedFiberMaximalIdealQuotEquiv
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
  (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)).toRingEquiv.trans <|
    Ideal.quotEquivOfEq hmap

/-- A Noetherian local ring is Cohen-Macaulay if and only if any henselization is
Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_henselization :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay Rh Rh := by
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : Module.Flat R Rh := RingHom.flat_algebraMap_iff.mp
    henselizationMap_faithfullyFlat.flat
  let e : ClosedFiberH ≃+* Rh ⧸ maximalIdeal Rh :=
    closedFiberMaximalIdealQuotEquiv IsHenselizationOf.map_maximalIdeal
  letI : Field (Rh ⧸ maximalIdeal Rh) := Ideal.Quotient.field (maximalIdeal Rh)
  letI : Field ClosedFiberH := IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  have hiff :
      Module.CohenMacaulay Rh Rh ↔
        Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiberH ClosedFiberH :=
    cohenMacaulayRing_iff_source_and_closedFiber
  have hfiber : Module.CohenMacaulay ClosedFiberH ClosedFiberH :=
    self_cohenMacaulay_of_krullDimLE_zero ClosedFiberH
  constructor
  · intro hR
    exact hiff.2 ⟨hR, hfiber⟩
  · intro hRh
    exact (hiff.1 hRh).1

/-- A Noetherian local ring is Cohen-Macaulay if and only if any strict henselization is
Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_strictHenselization :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay Rsh Rsh := by
  letI : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : Module.Flat R Rsh := RingHom.flat_algebraMap_iff.mp
    strictHenselizationMap_faithfullyFlat.flat
  let e : ClosedFiberSh ≃+* Rsh ⧸ maximalIdeal Rsh :=
    closedFiberMaximalIdealQuotEquiv IsStrictHenselizationOf.map_maximalIdeal
  letI : Field (Rsh ⧸ maximalIdeal Rsh) := Ideal.Quotient.field (maximalIdeal Rsh)
  letI : Field ClosedFiberSh := IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  have hiff :
      Module.CohenMacaulay Rsh Rsh ↔
        Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiberSh ClosedFiberSh :=
    cohenMacaulayRing_iff_source_and_closedFiber
  have hfiber : Module.CohenMacaulay ClosedFiberSh ClosedFiberSh :=
    self_cohenMacaulay_of_krullDimLE_zero ClosedFiberSh
  constructor
  · intro hR
    exact hiff.2 ⟨hR, hfiber⟩
  · intro hRsh
    exact (hiff.1 hRsh).1

-- Proof sketch: specialize the flat-local Cohen-Macaulay criterion
-- `cohenMacaulayRing_iff_source_and_closedFiber` to the henselization and strict-henselization
-- maps. Lemma `15.45.3` supplies the canonical Noetherianity instances for the target rings, and
-- Lemma `15.45.1` gives faithful flatness. In both cases the closed fiber identifies with the
-- residue field of the target local ring via the maximal-ideal image equality, hence is a field
-- and therefore Cohen-Macaulay.
/-- Lemma 15.45.9: for a Noetherian local ring `R`, the following are equivalent:
`R` is Cohen-Macaulay, a chosen henselization `Rh` of `R` is Cohen-Macaulay, and a chosen strict
henselization `Rsh` of `R` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE
      [Module.CohenMacaulay R R, Module.CohenMacaulay Rh Rh, Module.CohenMacaulay Rsh Rsh] := by
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  letI : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  tfae_have 1 ↔ 2 := cohenMacaulayRing_iff_henselization
  tfae_have 1 ↔ 3 := cohenMacaulayRing_iff_strictHenselization
  tfae_finish

end
