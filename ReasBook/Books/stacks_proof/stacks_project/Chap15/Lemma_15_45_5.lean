import Mathlib
import StacksProject_2024.Chap10.Lemma_10_32_3
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap10.Lemma_10_156_4
import StacksProject_2024.Chap15.Lemma_15_105_8
import StacksProject_2024.Chap15.Lemma_15_105_14.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open IsLocalRing

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
- primary domain: commutative algebra of nilradicals under henselization and strict
  henselization;
- sampled owner declarations:
  `Ideal.map_isLocallyNilpotent`,
  `Ideal.isRadical_iff_quotient_reduced`,
  `henselization_quotient_isHenselizationOf_quotient`,
  `strictHenselization_quotient_isStrictHenselizationOf_quotient`;
- best owner abstraction: the public statements should stay source-facing equalities of nilradicals,
  while the proof factors through the canonical owners `IsReduced`, `IsHenselizationOf`, and
  `IsStrictHenselizationOf` on the quotient rings;
- primitive data: only the local ring `R` and the chosen henselization / strict henselization;
  local nilpotence and reducedness of the quotient are derived API, not primitive fields.
-/

omit [IsLocalRing R] in
private theorem map_nilradical_eq_nilradical_of_isReduced_quotient
    {S : Type u} [CommRing S] [Algebra R S]
    (hReduced : IsReduced (S ⧸ Ideal.map (algebraMap R S) (nilradical R))) :
    Ideal.map (algebraMap R S) (nilradical R) = nilradical S := by
  apply le_antisymm
  · exact Ideal.map_isLocallyNilpotent (algebraMap R S) le_rfl
  · have hRadical : (Ideal.map (algebraMap R S) (nilradical R)).IsRadical :=
      (Ideal.isRadical_iff_quotient_reduced _).2 hReduced
    calc
      nilradical S = (⊥ : Ideal S).radical := rfl
      _ ≤ (Ideal.map (algebraMap R S) (nilradical R)).radical := Ideal.radical_mono bot_le
      _ = Ideal.map (algebraMap R S) (nilradical R) := Ideal.radical_eq_iff.mpr hRadical

private theorem nilradical_le_maximalIdeal : nilradical R ≤ maximalIdeal R := by
  simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
    (nilradical_le_jacobson R : nilradical R ≤ Ring.jacobson R)

private theorem nilradical_ne_top : nilradical R ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top nilradical_le_maximalIdeal

omit [IsLocalRing R] in
private theorem reduced_quotient_nilradical : IsReduced (R ⧸ nilradical R) := by
  exact (Ideal.isRadical_iff_quotient_reduced (nilradical R)).1 <| by
    simpa [nilradical] using (Ideal.radical_isRadical (⊥ : Ideal R))

-- Route correction: the source proof reduces to a reduced quotient and then applies the
-- "reduced base implies reduced henselization" bridge from Lemma `15.45.4`. Since that upstream
-- file is currently blocked, we use the same owner-level weakly-étale ascent step directly on
-- the quotient henselization here.
/-- Helper for Lemma 15.45.5: quotienting a henselization by the extended nilradical is reduced
because it is a henselization of the reduced quotient `R ⧸ nilradical R`. -/
private theorem reduced_henselization_quotient_map_nilradical :
    IsReduced (Rh ⧸ Ideal.map (algebraMap R Rh) (nilradical R)) := by
  let I : Ideal R := nilradical R
  let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I nilradical_ne_top
  let _ : IsHenselizationOf (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) :=
    henselization_quotient_isHenselizationOf_quotient I nilradical_ne_top
  have hReducedBase : IsReduced (R ⧸ I) := by
    -- The source invariant is that quotienting by the nilradical produces a reduced ring.
    simpa [I] using reduced_quotient_nilradical (R := R)
  let _ : IsReduced (R ⧸ I) := hReducedBase
  let hWeak :
      Algebra.IsWeaklyEtale (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) :=
    isWeaklyEtale_of_isFilteredColimitOfEtale IsHenselizationOf.isFilteredColimitOfEtale
  -- Reducedness now ascends along the weakly étale quotient henselization map.
  exact isReduced_of_isWeaklyEtale hWeak

/-- Helper for Lemma 15.45.5: quotienting a strict henselization by the extended nilradical is
reduced because it is a strict henselization of the reduced quotient `R ⧸ nilradical R`. -/
private theorem reduced_strictHenselization_quotient_map_nilradical :
    IsReduced (Rsh ⧸ Ideal.map (algebraMap R Rsh) (nilradical R)) := by
  let I : Ideal R := nilradical R
  let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I nilradical_ne_top
  let _ : IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) :=
    strictHenselization_quotient_isStrictHenselizationOf_quotient I nilradical_ne_top
  have hReducedBase : IsReduced (R ⧸ I) := by
    -- The same reduced quotient is the base of the strict henselization argument.
    simpa [I] using reduced_quotient_nilradical (R := R)
  let _ : IsReduced (R ⧸ I) := hReducedBase
  let hWeak :
      Algebra.IsWeaklyEtale (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) :=
    isWeaklyEtale_of_isFilteredColimitOfEtale IsStrictHenselizationOf.isFilteredColimitOfEtale
  -- Reducedness ascends along the weakly étale quotient strict henselization map as well.
  exact isReduced_of_isWeaklyEtale hWeak

-- Proof sketch: `nilradical R` is locally nilpotent by definition, so its extension to `Rh`
-- lies in `nilradical Rh` by `Ideal.map_isLocallyNilpotent`. The quotient
-- `Rh ⧸ Ideal.map (algebraMap R Rh) (nilradical R)` is a henselization of the reduced quotient
-- `R ⧸ nilradical R` by Lemma `10.156.2`, so weakly-étale reducedness ascent makes that quotient
-- reduced. The extended ideal is therefore radical, hence it must coincide with `nilradical Rh`.
/-- Lemma 15.45.5 (1): for a local ring `R`, the extension of the nilradical of `R` to a
henselization `Rh` is the nilradical of `Rh`. -/
@[stacks 0ASE]
theorem henselization_map_nilradical :
    Ideal.map (algebraMap R Rh) (nilradical R) = nilradical Rh := by
  let I : Ideal R := nilradical R
  -- The quotient side is reduced by the source-faithful quotient-henselization argument above.
  have hReducedQuotient : IsReduced (Rh ⧸ Ideal.map (algebraMap R Rh) I) := by
    simpa [I] using reduced_henselization_quotient_map_nilradical (R := R) (Rh := Rh)
  have hMap : Ideal.map (algebraMap R Rh) I = nilradical Rh :=
    map_nilradical_eq_nilradical_of_isReduced_quotient hReducedQuotient
  simpa [I] using hMap

-- Proof sketch: the strict quotient is a strict henselization of `R ⧸ nilradical R` by
-- Lemma `10.156.4`, and the same weakly-étale ascent argument makes that strict quotient
-- reduced.
/-- Lemma 15.45.5 (2): for a local ring `R`, the extension of the nilradical of `R` to a strict
henselization `Rsh` is the nilradical of `Rsh`. -/
@[stacks 0ASE]
theorem strictHenselization_map_nilradical :
    Ideal.map (algebraMap R Rsh) (nilradical R) = nilradical Rsh := by
  let I : Ideal R := nilradical R
  -- The strict quotient is reduced by the parallel quotient-strict-henselization argument.
  have hReducedQuotient : IsReduced (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) := by
    simpa [I] using
      reduced_strictHenselization_quotient_map_nilradical (R := R) (Rsh := Rsh)
  have hMap : Ideal.map (algebraMap R Rsh) I = nilradical Rsh :=
    map_nilradical_eq_nilradical_of_isReduced_quotient hReducedQuotient
  simpa [I] using hMap

end
