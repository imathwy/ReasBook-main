import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, and
  Noetherianity;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `List.TFAE`,
  `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`,
  `henselizationMap_faithfullyFlat`;
- best owner abstraction: the source-facing content of this item is the `List.TFAE` statement for
  the canonical predicates `IsNoetherianRing R`, `IsNoetherianRing Rh`, and
  `IsNoetherianRing Rsh`;
- primitive data: the local ring `R` together with chosen henselization and strict henselization
  owners;
- derived API: completion comparison, flatness, and formal-smoothness facts already belong to
  their upstream owner files and should be reused directly rather than duplicated here.

Source/core/bridge triage:
- `source-facing`: the `List.TFAE` equivalence of Noetherianity for `R`, `Rh`, and `Rsh`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, and `IsNoetherianRing`;
- `bridge/view`: completion-comparison and faithful-flatness lemmas from the earlier chapter
  owners.
-/
-- Proof sketch: faithful flatness of the henselization and strict henselization maps gives the
-- implications from `Rh` or `Rsh` back to `R` by Noetherian descent. Conversely, when `R` is
-- Noetherian, both `Rh` and `Rsh` are filtered colimits of étale local `R`-algebras with maximal
-- ideal extended from `R`, so the Stacks proof shows their maximal-ideal completions are
-- Noetherian and then descends Noetherianity back to `Rh` and `Rsh`.
/-- Lemma 15.45.3: for a local ring `R`, the following are equivalent: `R` is Noetherian, a
henselization `Rh` of `R` is Noetherian, and a strict henselization `Rsh` of `R` is Noetherian.
-/
theorem isNoetherianRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] := sorry

end

section

/-- A henselization of a Noetherian local ring is Noetherian. -/
theorem isNoetherianRing_henselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    [IsNoetherianRing R] : IsNoetherianRing Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  exact (hTFAE.out 0 1).mp hR

end

section

/-- A strict henselization of a Noetherian local ring is Noetherian. -/
theorem isNoetherianRing_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Rsh : Type u) [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [IsNoetherianRing R] : IsNoetherianRing Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  exact (hTFAE.out 0 2).mp hR

end
