import Mathlib
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap15.Lemma_15_43_2

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing

universe u

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
private abbrev PuncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :=
  { p : PrimeSpectrum R // p.asIdeal ≠ maximalIdeal R }

/-
Domain-style sampling:
- primary domain: topological connectedness of punctured prime spectra for Noetherian local rings,
  compared across henselization and maximal-ideal completion;
- sampled owner declarations:
  `PrimeSpectrum`,
  `PreconnectedSpace`,
  `henselizationCompletionComparison`,
  `exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one`;
- best owner abstraction: the punctured spectrum should remain a direct subtype view on the
  canonical owner `PrimeSpectrum R`, while disconnectedness is expressed by the canonical
  topological predicate `¬ PreconnectedSpace _` rather than by a parallel wrapper notion;
- primitive data: the local Noetherian ring `A`, its chosen henselization `Ah`, and the punctured
  spectrum subtype on each local ring;
- derived API: the disconnectedness comparison between the punctured spectra of `Ah` and
  `ACompletion`.

Source/core/bridge triage:
- `source-facing`: the punctured-spectrum disconnectedness equivalence below;
- `core/canonical`: `PrimeSpectrum`, `PreconnectedSpace`, `AdicCompletion`, and `maximalIdeal`;
- `bridge/view`: the canonical henselization-to-completion comparison together with the
  algebraization descent from Lemmas `15.109.4` and `15.109.5`.
-/

-- Proof sketch: identify the completion of the henselization with the completion `ACompletion`,
-- so it suffices to compare the punctured spectra of a henselian local ring and its completion.
-- Faithful flatness of the completion map gives one implication by surjectivity on punctured
-- spectra, and the converse descends a disconnection of the punctured spectrum of `ACompletion`
-- to a disconnection of the punctured spectrum of `Ah` using the algebraization steps from
-- Lemmas `15.109.4` and `15.109.5`.
/-- Lemma 15.109.6: for a Noetherian local ring `A` and a chosen henselization `Ah` of `A`, the
punctured spectrum of the maximal-ideal completion `ACompletion = AdicCompletion (maximalIdeal A) A`
is disconnected if and only if the punctured spectrum of `Ah` is disconnected. Here
“disconnected” is formalized as failure of preconnectedness of the corresponding punctured
spectrum. -/
theorem puncturedSpectrum_completion_disconnected_iff_henselization_disconnected :
    ¬ PreconnectedSpace (PuncturedSpectrum ACompletion) ↔
      ¬ PreconnectedSpace (PuncturedSpectrum Ah) := sorry

end
