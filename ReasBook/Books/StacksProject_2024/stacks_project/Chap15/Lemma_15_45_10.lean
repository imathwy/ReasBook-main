import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Lemma_10_110_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_112_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: regular local rings under henselization and strict henselization in local
  commutative algebra;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  `isRegularLocalRing_closedFiber_of_quotient`;
* best owner abstraction: the source-facing statement should stay directly on the canonical owner
  `IsRegularLocalRing`; the theorem should therefore quantify only over the local ring and the
  chosen henselization / strict-henselization owners, recovering flatness, target Noetherianity,
  and closed-fiber regularity internally instead of exposing parallel auxiliary hypotheses;
* primitive data: the local base ring `R` and the chosen henselization / strict henselization
  owners;
* derived API: faithful flatness of `R → Rh` and `R → Rsh`, Noetherianity of `Rh` and `Rsh`, and
  regularity of the closed fibers through their quotient-field presentations.

Source/core/bridge triage:
* `source-facing`: the three-way `List.TFAE` for `IsRegularLocalRing`;
* `core/canonical`: `IsRegularLocalRing`;
* `bridge/view`: the closed-fiber owner `Ideal.Fiber (maximalIdeal R) S` together with the
  maximal-ideal image equalities for henselization and strict henselization.
-/

-- Proof sketch: for the backward implications, apply the canonical flat-local descent theorem for
-- regular local rings to the faithfully flat henselization and strict-henselization maps. For the
-- forward implications, apply the flat-local ascent theorem with regular closed fiber; the closed
-- fiber is canonically a residue-field quotient because the maximal ideal extends to the maximal
-- ideal of the henselization / strict henselization, hence it is a field and therefore a regular
-- local ring.
/-- Helper for Lemma 15.45.10: the closed fiber of a henselization is regular local because it is
the quotient by the target maximal ideal. -/
lemma isRegularLocalRing_henselization_closedFiber :
    IsRegularLocalRing ((maximalIdeal R).Fiber Rh) := by
  let _ : Field (Rh ⧸ maximalIdeal Rh) := Ideal.Quotient.field (maximalIdeal Rh)
  let _ : IsRegularLocalRing (Rh ⧸ maximalIdeal Rh) := inferInstance
  let _ : IsRegularLocalRing (Rh ⧸ Ideal.map (algebraMap R Rh) (maximalIdeal R)) :=
    IsRegularLocalRing.of_ringEquiv
      (Ideal.quotEquivOfEq IsHenselizationOf.map_maximalIdeal).symm
  -- The closed fiber is the quotient by the image of the source maximal ideal.
  simpa using (isRegularLocalRing_closedFiber_of_quotient (R := R) (S := Rh))

/-- Helper for Lemma 15.45.10: the closed fiber of a strict henselization is regular local because
it is the quotient by the target maximal ideal. -/
lemma isRegularLocalRing_strictHenselization_closedFiber :
    IsRegularLocalRing ((maximalIdeal R).Fiber Rsh) := by
  let _ : Field (Rsh ⧸ maximalIdeal Rsh) := Ideal.Quotient.field (maximalIdeal Rsh)
  let _ : IsRegularLocalRing (Rsh ⧸ maximalIdeal Rsh) := inferInstance
  let _ : IsRegularLocalRing (Rsh ⧸ Ideal.map (algebraMap R Rsh) (maximalIdeal R)) :=
    IsRegularLocalRing.of_ringEquiv
      (Ideal.quotEquivOfEq IsStrictHenselizationOf.map_maximalIdeal).symm
  -- The closed fiber is again the quotient by the image of the source maximal ideal.
  simpa using (isRegularLocalRing_closedFiber_of_quotient (R := R) (S := Rsh))

/-- Helper for Lemma 15.45.10: regularity ascends from a Noetherian local ring to any chosen
henselization. -/
lemma isRegularLocalRing_henselization (hR : IsRegularLocalRing R) :
    IsRegularLocalRing Rh := by
  let _ : IsRegularLocalRing R := hR
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : Module.Flat R Rh :=
    RingHom.flat_algebraMap_iff.mp
      (algebraMap_faithfullyFlat_of_isHenselizationOf (R := R) (Rh := Rh)).flat
  -- Apply the flat local ascent criterion once the henselization target is known Noetherian.
  exact
    isRegularLocalRing_of_flat_localHom_of_regular_closedFiber
      isRegularLocalRing_henselization_closedFiber

/-- Helper for Lemma 15.45.10: regularity ascends from a Noetherian local ring to any chosen
strict henselization. -/
lemma isRegularLocalRing_strictHenselization (hR : IsRegularLocalRing R) :
    IsRegularLocalRing Rsh := by
  let _ : IsRegularLocalRing R := hR
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : Module.Flat R Rsh :=
    RingHom.flat_algebraMap_iff.mp
      (algebraMap_faithfullyFlat_of_isStrictHenselizationOf (R := R) (Rsh := Rsh)).flat
  -- The same flat local ascent argument applies to strict henselizations.
  exact
    isRegularLocalRing_of_flat_localHom_of_regular_closedFiber
      isRegularLocalRing_strictHenselization_closedFiber

/-- Lemma 15.45.10: for a local ring `R`, the following are equivalent: `R` is a
regular local ring, a chosen henselization `Rh` of `R` is a regular local ring, and a chosen
strict henselization `Rsh` of `R` is a regular local ring. -/
theorem isRegularLocalRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE [IsRegularLocalRing R, IsRegularLocalRing Rh, IsRegularLocalRing Rsh] := by
  tfae_have 1 → 2 := by
    -- Regularity ascends along the henselization map by the regular-closed-fiber criterion.
    intro hR
    exact isRegularLocalRing_henselization hR
  tfae_have 2 → 1 := by
    -- Regularity descends back to the base along the faithfully flat local henselization map.
    intro hRh
    let _ : IsRegularLocalRing Rh := hRh
    let _ : Module.Flat R Rh :=
      RingHom.flat_algebraMap_iff.mp
        (algebraMap_faithfullyFlat_of_isHenselizationOf (R := R) (Rh := Rh)).flat
    exact isRegularLocalRing_of_flat_localHom_of_regularTarget Rh
  tfae_have 1 → 3 := by
    -- The source-faithful ascent argument repeats verbatim for the strict henselization.
    intro hR
    exact isRegularLocalRing_strictHenselization hR
  tfae_have 3 → 1 := by
    -- Regularity also descends along the faithfully flat local strict-henselization map.
    intro hRsh
    let _ : IsRegularLocalRing Rsh := hRsh
    let _ : Module.Flat R Rsh :=
      RingHom.flat_algebraMap_iff.mp
        (algebraMap_faithfullyFlat_of_isStrictHenselizationOf (R := R) (Rsh := Rsh)).flat
    exact isRegularLocalRing_of_flat_localHom_of_regularTarget Rsh
  tfae_finish

end
