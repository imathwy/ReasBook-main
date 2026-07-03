import Mathlib
import StacksProject_2024.Chap12.Lemma_12_13_9
import StacksProject_2024.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-
Domain sampling pass:
* primary domain: K-flat resolutions of cochain complexes of `R`-modules;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` and `CochainComplex.IsTermwiseFlat` from
    `Definition_15_59_1`, the chapter owners for the two ambient properties carried by the
    resolving complex;
  - `cochainComplex_epi_iff_degreewise_epi` from `Lemma_12_13_9`, the source-facing bridge
    between the termwise epimorphism condition from the text and the canonical complex-level owner
    `Epi π`;
  - `CategoryTheory.IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn` and
    `CategoryTheory.UpperTruncationResolutionTower` from Chapter 13, the canonical owner
    abstractions for the bounded-above, termwise-epimorphic quasi-isomorphism data used in the
    truncation tower construction;
  - `Module.Flat R`, the canonical owner predicate for flat `R`-modules.

Source/core/bridge triage:
* `source-facing`: the existence of a termwise-epimorphic quasi-isomorphism from a K-flat complex
  with flat terms;
* `core/canonical`: the predicates `IsKFlat`, `IsTermwiseFlat`, `QuasiIso`, and the
  complex-level epimorphism owner `Epi π`;
* `bridge/view`: `cochainComplex_epi_iff_degreewise_epi` and the Chapter 13 upper-truncation
  resolution tower used to construct the witness.

Primitive data are only the resolving complex `K` and comparison morphism `π`. The four
properties above are derived API over existing owner abstractions, so they should not be bundled
into a parallel local wrapper class in this file.
-/

-- Proof sketch: choose the truncation-resolution tower from Derived Categories, Lemma `13.29.1`
-- with flat terms in each bounded-above stage. Each stage is K-flat by Lemma `15.59.7`, and the
-- sequential colimit is K-flat by Lemma `15.59.8`. Filtered colimits of flat modules are flat by
-- Algebra, Lemma `10.39.3`, and the induced map from the colimit complex to `M^•` is a
-- termwise-epimorphic quasi-isomorphism by the construction of the tower.
/-- Lemma 15.59.10: every cochain complex of `R`-modules admits a termwise-epimorphic
quasi-isomorphism from a K-flat cochain complex whose terms are flat `R`-modules. -/
lemma exists_termwiseEpi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (π : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ ∀ i : ℤ, Epi (π.f i) := sorry

-- The source-facing lemma above keeps the textbook termwise-epimorphism conclusion. This
-- companion re-expresses the same existence statement through the canonical complex-level owner
-- `Epi π`.
/-- Canonical owner-level form of Lemma 15.59.10: every cochain complex of `R`-modules admits a
quasi-isomorphism from a K-flat cochain complex with flat terms whose comparison morphism is
epimorphic. -/
lemma exists_epi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (π : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ Epi π := by
  obtain ⟨K, π, hKFlat, hTermwiseFlat, hπ, hEpi⟩ := exists_termwiseEpi_kFlatResolution M
  exact ⟨K, π, hKFlat, hTermwiseFlat, hπ,
    (cochainComplex_epi_iff_degreewise_epi π).2 hEpi⟩

end CochainComplex
