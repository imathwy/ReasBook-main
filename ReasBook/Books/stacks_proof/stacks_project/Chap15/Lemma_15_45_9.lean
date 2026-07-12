import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_130_3
import StacksProject_2024.Chap10.Lemma_10_163_3
import StacksProject_2024.Chap15.Lemma_15_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Helper for Lemma 15.45.9: the canonical closed fiber of a local algebra map is local. -/
private theorem closedFiber_isLocalRing_aux
    {A B : Type u}
    [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    IsLocalRing (Ideal.Fiber (maximalIdeal A) B) := by
  let e :
      Ideal.Fiber (maximalIdeal A) B ≃ₐ[A]
        B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A) :=
    closedFiberQuotAlgEquiv
  letI : IsLocalRing (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) < (⊤ : Ideal B) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)
    have : Nontrivial (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
      Ideal.Quotient.nontrivial_iff.2 hmap.ne
    exact IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)))
      Ideal.Quotient.mk_surjective
  exact
    (e.toRingEquiv.symm :
      B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A) ≃+*
        Ideal.Fiber (maximalIdeal A) B).isLocalRing

/-- Helper for Lemma 15.45.9: if a local algebra has maximal ideal equal to the image of the base
maximal ideal, then its closed fiber is the residue field quotient and hence Cohen-Macaulay. -/
private theorem cohenMacaulay_closedFiber_of_map_maximalIdeal
    {A B : Type u}
    [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalRing (Ideal.Fiber (maximalIdeal A) B)]
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    Module.CohenMacaulay (Ideal.Fiber (maximalIdeal A) B) (Ideal.Fiber (maximalIdeal A) B) := by
  let e : Ideal.Fiber (maximalIdeal A) B ≃+* B ⧸ maximalIdeal B :=
    (closedFiberQuotAlgEquiv (R := A) (S := B)).toRingEquiv.trans <|
      Ideal.quotEquivOfEq hmap
  let _ : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal A) B) := e.symm.isLocalRing
  let _ : IsNoetherianRing (Ideal.Fiber (maximalIdeal A) B) :=
    isNoetherianRing_of_ringEquiv (B ⧸ maximalIdeal B) e.symm
  let _ : Field (Ideal.Fiber (maximalIdeal A) B) :=
    IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  let _ : Ring.KrullDimLE 0 (Ideal.Fiber (maximalIdeal A) B) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <|
      ringKrullDim_eq_zero_of_isField (Field.toIsField _)
  exact self_cohenMacaulay_of_krullDimLE_zero (Ideal.Fiber (maximalIdeal A) B)

section Henselization

variable [IsNoetherianRing Rh]

/-- A Noetherian local ring is Cohen-Macaulay if and only if any henselization is
Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_henselization :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay Rh Rh := by
  let _ : Module.Flat R Rh := RingHom.flat_algebraMap_iff.mp <|
    (algebraMap_faithfullyFlat_of_isHenselizationOf (R := R) (Rh := Rh)).flat
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal R) Rh) := closedFiber_isLocalRing_aux
  have hclosed :
      Module.CohenMacaulay (Ideal.Fiber (maximalIdeal R) Rh) (Ideal.Fiber (maximalIdeal R) Rh) :=
    cohenMacaulay_closedFiber_of_map_maximalIdeal
      (A := R) (B := Rh) IsHenselizationOf.map_maximalIdeal
  -- Apply the flat local criterion and use that the henselian closed fiber is a field.
  simpa [hclosed] using
    (cohenMacaulayRing_iff_source_and_closedFiber (R := R) (S := Rh)).symm

end Henselization

section StrictHenselization

variable [IsNoetherianRing Rsh]

/-- A Noetherian local ring is Cohen-Macaulay if and only if any strict henselization is
Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_strictHenselization :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay Rsh Rsh := by
  let _ : Module.Flat R Rsh := RingHom.flat_algebraMap_iff.mp <|
    (algebraMap_faithfullyFlat_of_isStrictHenselizationOf (R := R) (Rsh := Rsh)).flat
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal R) Rsh) := closedFiber_isLocalRing_aux
  have hclosed :
      Module.CohenMacaulay (Ideal.Fiber (maximalIdeal R) Rsh)
        (Ideal.Fiber (maximalIdeal R) Rsh) :=
    cohenMacaulay_closedFiber_of_map_maximalIdeal
      (A := R) (B := Rsh) IsStrictHenselizationOf.map_maximalIdeal
  -- The strict henselization has the same field-valued closed fiber.
  simpa [hclosed] using
    (cohenMacaulayRing_iff_source_and_closedFiber (R := R) (S := Rsh)).symm

end StrictHenselization

section TFAE

variable [IsNoetherianRing Rh] [IsNoetherianRing Rsh]

-- Proof sketch: apply the flat local Cohen-Macaulay criterion to `R → Rh` and `R → Rsh`. In both
-- cases the image of the maximal ideal is the maximal ideal of the target, so the closed fiber is
-- the residue field quotient and therefore Cohen-Macaulay.
/-- Lemma 15.45.9: for a Noetherian local ring `R`, the following are equivalent:
`R` is Cohen-Macaulay, a chosen henselization `Rh` of `R` is Cohen-Macaulay, and a chosen strict
henselization `Rsh` of `R` is Cohen-Macaulay. -/
@[stacks 06LM]
theorem cohenMacaulayRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE
      [Module.CohenMacaulay R R, Module.CohenMacaulay Rh Rh, Module.CohenMacaulay Rsh Rsh] := by
  -- The two source-proof equivalences give the TFAE edges from `R` to the two henselian targets.
  tfae_have 1 ↔ 2 := cohenMacaulayRing_iff_henselization
  tfae_have 1 ↔ 3 := cohenMacaulayRing_iff_strictHenselization
  tfae_finish

end TFAE

end
