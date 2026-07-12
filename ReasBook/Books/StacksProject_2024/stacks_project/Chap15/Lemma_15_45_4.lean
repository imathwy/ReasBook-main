import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_164_2
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

/-- Helper for Lemma 15.45.4: the canonical map to a henselization is faithfully flat because a
henselization is a filtered colimit of étale algebras, hence weakly étale, and local flat maps
are faithfully flat. -/
lemma algebraMap_faithfullyFlat_of_isHenselizationOf :
    (algebraMap R Rh).FaithfullyFlat := by
  sorry

/-- Helper for Lemma 15.45.4: the canonical map to a strict henselization is faithfully flat by
the same weakly-étale local-map argument. -/
lemma algebraMap_faithfullyFlat_of_isStrictHenselizationOf :
    (algebraMap R Rsh).FaithfullyFlat := by
  sorry

-- Proof sketch: reducedness descends from `Rh` to `R` by faithful flatness of flat local maps,
-- and descends from `Rsh` to `R` by the same faithfully-flat descent applied to the flat local
-- map `R → Rsh`. Conversely, the
-- filtered-colimit-of-etale presentations of `Rh` and `Rsh` upgrade to the chapter owner
-- `Algebra.IsWeaklyEtale`, so Lemma `15.105.8` ascends reducedness from `R` to both chosen
-- henselizations.
/-- Helper for Lemma 15.45.4: reducedness descends from a reduced henselization to the base local
ring. -/
lemma reduced_base_of_reduced_henselization (hRh : IsReduced Rh) :
    IsReduced R := by
  -- Install reducedness on the henselization and descend along the faithfully flat structural map.
  let _ : IsReduced Rh := hRh
  exact isReduced_of_faithfullyFlat (algebraMap R Rh)
    algebraMap_faithfullyFlat_of_isHenselizationOf

/-- Helper for Lemma 15.45.4: a filtered colimit of étale algebras over a reduced base is reduced,
because the structural map is weakly étale and Lemma `15.105.8` applies. -/
private theorem reduced_target_of_filteredColimitOfEtale
    {S : Type u} [CommRing S] [Algebra R S]
    (hR : IsReduced R) (hcolim : (algebraMap R S).IsFilteredColimitOfEtale) :
    IsReduced S := by
  let _ : IsReduced R := hR
  let _ : (algebraMap R S).IsFilteredColimitOfEtale := hcolim
  sorry

/-- Helper for Lemma 15.45.4: reducedness ascends from a reduced local ring to any chosen
henselization. -/
lemma reduced_henselization_of_reduced_base (hR : IsReduced R) :
    IsReduced Rh := by
  -- This is the source-proof ascent step specialized to the henselization colimit presentation.
  exact
    reduced_target_of_filteredColimitOfEtale (R := R) (S := Rh) hR
      IsHenselizationOf.isFilteredColimitOfEtale

/-- Helper for Lemma 15.45.4: reducedness descends from a reduced strict henselization to the
base local ring. -/
lemma reduced_base_of_reduced_strictHenselization (hRsh : IsReduced Rsh) :
    IsReduced R := by
  -- Install reducedness on the strict henselization and descend along its faithfully flat map.
  let _ : IsReduced Rsh := hRsh
  exact isReduced_of_faithfullyFlat (algebraMap R Rsh)
    algebraMap_faithfullyFlat_of_isStrictHenselizationOf

/-- Helper for Lemma 15.45.4: reducedness ascends from a reduced local ring to any chosen strict
henselization. -/
lemma reduced_strictHenselization_of_reduced_base (hR : IsReduced R) :
    IsReduced Rsh := by
  -- The strict henselization case is the same source-proof bridge with its own colimit witness.
  exact
    reduced_target_of_filteredColimitOfEtale (R := R) (S := Rsh) hR
      IsStrictHenselizationOf.isFilteredColimitOfEtale

/-- Lemma 15.45.4: for a local ring `R`, the following are equivalent: `R` is reduced, a
henselization `Rh` of `R` is reduced, and a strict henselization `Rsh` of `R` is reduced. -/
theorem isReduced_tfae_henselization_strictHenselization :
    List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] := by
  -- The source proof is a two-map transfer argument: weakly-etale ascent and faithfully flat
  -- descent for the canonical maps `R → Rh` and `R → Rsh`.
  tfae_have 1 → 2 := by
    -- Reducedness ascends from the base ring to the henselization.
    intro hR
    exact reduced_henselization_of_reduced_base hR
  tfae_have 2 → 1 := by
    -- Reducedness descends back to the base ring from the henselization.
    intro hRh
    exact reduced_base_of_reduced_henselization hRh
  tfae_have 1 → 3 := by
    -- The same ascent argument applies to strict henselizations.
    intro hR
    exact reduced_strictHenselization_of_reduced_base hR
  tfae_have 3 → 1 := by
    -- The strict henselization map is also faithfully flat, so descent closes the cycle.
    intro hRsh
    exact reduced_base_of_reduced_strictHenselization hRsh
  tfae_finish

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
