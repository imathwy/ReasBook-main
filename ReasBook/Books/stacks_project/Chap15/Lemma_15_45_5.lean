import Mathlib
import stacks_project.Chap10.Lemma_10_32_3
import stacks_project.Chap10.Lemma_10_156_2
import stacks_project.Chap10.Lemma_10_156_4
import stacks_project.Chap15.Lemma_15_45_4

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

-- Proof sketch: `nilradical R` is locally nilpotent by definition, so its extension to `Rh`
-- lies in `nilradical Rh` by `Ideal.map_isLocallyNilpotent`. The quotient
-- `Rh ⧸ Ideal.map (algebraMap R Rh) (nilradical R)` is a henselization of `R ⧸ nilradical R` by
-- Lemma `10.156.2`, and `R ⧸ nilradical R` is reduced because `nilradical R` is radical. Choose
-- any strict henselization of `R ⧸ nilradical R` via the owner-level existence theorem
-- `exists_strictHenselization`; then Lemma `15.45.4` makes the quotient of `Rh` reduced, so the
-- extended ideal is radical and hence equals `nilradical Rh`.
/-- Lemma 15.45.5 (1): for a local ring `R`, the extension of the nilradical of `R` to a
henselization `Rh` is the nilradical of `Rh`. -/
theorem henselization_map_nilradical :
    Ideal.map (algebraMap R Rh) (nilradical R) = nilradical Rh := by
  let I : Ideal R := nilradical R
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.quotient I nilradical_ne_top
  let _ : IsHenselizationOf (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) :=
    henselization_quotient_isHenselizationOf_quotient I nilradical_ne_top
  have hReducedBase : IsReduced (R ⧸ I) := by
    simpa [I] using reduced_quotient_nilradical
  have hReducedQuotient : IsReduced (Rh ⧸ Ideal.map (algebraMap R Rh) I) :=
    isReduced_iff_isReduced_henselization.mp hReducedBase
  have hMap : Ideal.map (algebraMap R Rh) I = nilradical Rh :=
    map_nilradical_eq_nilradical_of_isReduced_quotient hReducedQuotient
  simpa [I] using hMap

-- Proof sketch: the strict quotient is a strict henselization of `R ⧸ nilradical R` by
-- Lemma `10.156.4`; choosing any henselization of the same reduced quotient and applying the
-- `0 ↔ 2` implication from Lemma `15.45.4` makes the strict quotient reduced.
/-- Lemma 15.45.5 (2): for a local ring `R`, the extension of the nilradical of `R` to a strict
henselization `Rsh` is the nilradical of `Rsh`. -/
theorem strictHenselization_map_nilradical :
    Ideal.map (algebraMap R Rsh) (nilradical R) = nilradical Rsh := by
  let I : Ideal R := nilradical R
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.quotient I nilradical_ne_top
  let _ : IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) :=
    strictHenselization_quotient_isStrictHenselizationOf_quotient I nilradical_ne_top
  have hReducedBase : IsReduced (R ⧸ I) := by
    simpa [I] using reduced_quotient_nilradical
  have hReducedQuotient : IsReduced (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) :=
    isReduced_iff_isReduced_strictHenselization.mp hReducedBase
  have hMap : Ideal.map (algebraMap R Rsh) I = nilradical Rsh :=
    map_nilradical_eq_nilradical_of_isReduced_quotient hReducedQuotient
  simpa [I] using hMap

end
