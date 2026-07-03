import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Domain triage:
- primary domain: commutative algebra of reduced rings under henselization and strict
  henselization;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `isReduced_of_faithfullyFlat`,
  `isReduced_of_isWeaklyEtale`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`;
- best owner abstraction: the source-facing TFAE statement should be phrased directly in terms of
  the canonical reducedness owner `IsReduced` on the three rings, with henselization data carried
  only by the ambient owner classes; ascent should factor through the chapter owner
  `Algebra.IsWeaklyEtale`, not through a parallel local ind-etale wrapper;
- primitive data: the local ring `R` and the chosen henselization / strict henselization rings;
  faithful flatness and weakly-etale reducedness ascent are derived API, not extra public data;
- `source-facing`: the three-way `List.TFAE` from the Stacks lemma;
- `core/canonical`: `IsReduced`, `RingHom.FaithfullyFlat`, and `Algebra.IsWeaklyEtale`;
- `bridge/view`: the pairwise `↔` consequences extracted canonically from the source-facing TFAE.
-/

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- Proof sketch: reducedness descends from `Rh` to `R` by faithful flatness of flat local maps,
-- and descends from `Rsh` to `R` by the same faithfully-flat descent applied to the flat local
-- map `R → Rsh`. Conversely, the
-- filtered-colimit-of-etale presentations of `Rh` and `Rsh` upgrade to the chapter owner
-- `Algebra.IsWeaklyEtale`, so Lemma `15.105.8` ascends reducedness from `R` to both chosen
-- henselizations.
/-- Lemma 15.45.4: for a local ring `R`, the following are equivalent: `R` is reduced, a
henselization `Rh` of `R` is reduced, and a strict henselization `Rsh` of `R` is reduced. -/
theorem isReduced_tfae_henselization_strictHenselization :
    List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] := sorry

end

section

variable {R Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- The `0 ↔ 1` implication extracted from the source-facing `TFAE`.
/-- A local ring is reduced if and only if any henselization is reduced. -/
theorem isReduced_iff_isReduced_henselization :
    IsReduced R ↔ IsReduced Rh := by
  obtain ⟨Rsh, hRshComm, hRshAlg, hRsh⟩ := exists_strictHenselization R
  let _ : CommRing Rsh := hRshComm
  let _ : Algebra R Rsh := hRshAlg
  let _ : IsStrictHenselizationOf R Rsh := hRsh
  have hTfae : List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] :=
    isReduced_tfae_henselization_strictHenselization
  exact hTfae.out 0 1

end

section

variable {R Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- The `0 ↔ 2` implication extracted from the source-facing `TFAE`.
/-- A local ring is reduced if and only if any strict henselization is reduced. -/
theorem isReduced_iff_isReduced_strictHenselization :
    IsReduced R ↔ IsReduced Rsh := by
  obtain ⟨Rh, hRhComm, hRhAlg, hRh⟩ := exists_henselization R
  let _ : CommRing Rh := hRhComm
  let _ : Algebra R Rh := hRhAlg
  let _ : IsHenselizationOf R Rh := hRh
  have hTfae : List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] :=
    isReduced_tfae_henselization_strictHenselization
  exact hTfae.out 0 2

end
