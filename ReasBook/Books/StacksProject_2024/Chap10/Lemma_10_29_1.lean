import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommSemiring R] {U : Set (PrimeSpectrum R)}

/- Domain-style sampling for quasi-compact open subsets of `Spec(R)`:
- primary domain: prime spectrum topology, retrocompactness, and compact-open descriptions;
- same-domain declarations inspected:
  `QuasiSeparatedSpace.isRetrocompact_iff_isCompact`,
  `PrimeSpectrum.isCompact_isOpen_iff`,
  `PrimeSpectrum.isCompact_isOpen_iff_ideal`,
  `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`,
  `StacksProject_2024.Chap10.Definition_10_17_1`'s notation owners `D(-)` and `V(-)`;
- best owner abstraction: the core/canonical owners are the ambient predicates `IsRetrocompact`,
  `IsCompact`, and the spectrum-specific compact-open characterizations above;
- primitive data: an open subset `U ⊆ Spec(R)`;
- derived API: the finite-union-of-basic-opens and finitely-generated-ideal presentations of the
  same compact open subset.

Layer triage:
- `source-facing`: the four-way textbook equivalence for an open subset of `Spec(R)`;
- `core/canonical`: `QuasiSeparatedSpace.isRetrocompact_iff_isCompact`,
  `PrimeSpectrum.isCompact_isOpen_iff`, and `PrimeSpectrum.isCompact_isOpen_iff_ideal`;
- `bridge/view`: converting `(V(t))ᶜ` into a finite union of standard opens `D(f)`.
-/

private theorem compl_V_eq_iUnion_D (t : Finset R) :
    ((V(t) : Set (PrimeSpectrum R)))ᶜ = ⋃ f ∈ t, D(f) := by
  ext x
  simp [basicOpen_eq_zeroLocus_compl, mem_zeroLocus, Set.not_subset]

-- Proof sketch: identify retrocompactness with compactness for the open subset `U` using
-- quasi-separatedness of `Spec(R)`, then rewrite compactness through the compact-open owner
-- theorems for finite unions of standard opens and complements of zero loci of finitely generated
-- ideals.
/-- Lemma 10.29.1: for an open subset `U ⊆ Spec(R)`, the following are equivalent: `U` is
retrocompact in `Spec(R)`, `U` is quasi-compact, `U` is a finite union of standard opens `D(f)`,
and `U` is the complement of a closed subset `V(I)` for a finitely generated ideal `I`. -/
theorem primeSpectrum_open_tfae_retrocompact
    (hU : IsOpen U) :
    List.TFAE
      [ IsRetrocompact U
      , IsCompact U
      , ∃ t : Finset R, U = ⋃ f ∈ t, D(f)
      , ∃ I : Ideal R, I.FG ∧ U = (V(I))ᶜ ] := by
  have hcompact_basicOpen :
      IsCompact U ↔ ∃ t : Finset R, U = ⋃ f ∈ t, D(f) := by
    constructor
    · intro hCompact
      obtain ⟨t, ht⟩ := isCompact_isOpen_iff.mp ⟨hCompact, hU⟩
      exact ⟨t, ht.symm.trans (compl_V_eq_iUnion_D t)⟩
    · rintro ⟨t, rfl⟩
      exact (isCompact_isOpen_iff.mpr
        ⟨t, compl_V_eq_iUnion_D t⟩).1
  have hcompact_ideal :
      IsCompact U ↔ ∃ I : Ideal R, I.FG ∧ U = (V(I))ᶜ := by
    constructor
    · intro hCompact
      obtain ⟨I, hI, hIU⟩ := isCompact_isOpen_iff_ideal.mp ⟨hCompact, hU⟩
      exact ⟨I, hI, hIU.symm⟩
    · rintro ⟨I, hI, rfl⟩
      exact (isCompact_isOpen_iff_ideal.mpr ⟨I, hI, rfl⟩).1
  tfae_have 1 ↔ 2 := QuasiSeparatedSpace.isRetrocompact_iff_isCompact hU
  tfae_have 2 ↔ 3 := hcompact_basicOpen
  tfae_have 2 ↔ 4 := hcompact_ideal
  tfae_finish

end
