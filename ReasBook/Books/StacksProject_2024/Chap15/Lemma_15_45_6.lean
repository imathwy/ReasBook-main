import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_37_11
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
* primary domain: normality for local rings under henselization and strict henselization;
* sampled owner-style declarations: `IsNormalRing`, `IsHenselizationOf`,
  `IsStrictHenselizationOf`, `isNormalRing_of_faithfullyFlat`,
  `isNormalRing_of_smooth`, and `isNormalRing_of_isColimit_filtered_system`;
* core/canonical owners: `IsNormalRing` for the property being compared, and
  `IsHenselizationOf` / `IsStrictHenselizationOf` for the chosen algebra objects;
* primitive vs. derived API: the primitive inputs are only the chosen henselization and strict
  henselization instances; faithful-flat descent via `isNormalRing_of_faithfullyFlat` and
  smooth/filtered-colimit ascent via `isNormalRing_of_smooth` and
  `isNormalRing_of_isColimit_filtered_system` are canonical derived chapter API and should not be
  repackaged locally;
* layer split: the three-way `List.TFAE` is the `source-facing` statement, and pairwise
  equivalences are derived canonically via `List.TFAE.out` rather than kept as parallel local
  wrappers.
-/
-- Proof sketch: the maps `R → Rh` and `R → Rsh` are faithfully flat local maps because
-- henselizations and strict henselizations are filtered colimits of étale algebras. Normality then
-- descends from `Rh` or `Rsh` to `R` by faithful flatness. Conversely, if `R` is normal, each
-- étale stage in the filtered-colimit presentations of `Rh` and `Rsh` is normal by smooth ascent,
-- and the directed colimit remains normal. For a local ring, `IsNormalRing` is equivalent to the
-- textbook phrase “normal domain”.
/-- Lemma 15.45.6: for a local ring `R`, the following are equivalent: `R` is a normal ring, a
henselization `Rh` of `R` is a normal ring, and a strict henselization `Rsh` of `R` is a normal
ring. For local rings this matches the textbook formulation in terms of normal domains. -/
theorem isNormalRing_tfae_henselization_strictHenselization :
    List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] := by
  sorry

end

section

variable {R Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- The `0 ↔ 1` implication extracted from the source-facing `TFAE`.
/-- A local ring is normal if and only if any henselization is normal. -/
theorem isNormalRing_iff_isNormalRing_henselization :
    IsNormalRing R ↔ IsNormalRing Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] :=
    isNormalRing_tfae_henselization_strictHenselization
  exact hTFAE.out 0 1

end

section

variable {R Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- The `0 ↔ 2` implication extracted from the source-facing `TFAE`.
/-- A local ring is normal if and only if any strict henselization is normal. -/
theorem isNormalRing_iff_isNormalRing_strictHenselization :
    IsNormalRing R ↔ IsNormalRing Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] :=
    isNormalRing_tfae_henselization_strictHenselization
  exact hTFAE.out 0 2

end
