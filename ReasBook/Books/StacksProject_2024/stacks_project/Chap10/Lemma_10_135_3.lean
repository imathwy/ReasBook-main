import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_135_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Domain-style sampling in the local-complete-intersection / Cohen-Macaulay interface:
- primary domain: commutative algebra of local complete intersections over a field and the
  resulting global Cohen-Macaulay ring property;
- sampled owner declarations:
  `IsLocalCompleteIntersection`,
  `IsGlobalCompleteIntersection`,
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`;
- best owner abstraction: this file is a `bridge/view` from the source-facing field-algebra owner
  `IsLocalCompleteIntersection k S` to the chapter-global ring owner `CohenMacaulayRing S`;
- primitive data: only the owner hypothesis `hCI : IsLocalCompleteIntersection k S`;
- derived API: finite presentation and hence finite type of `S`, together with the primewise
  Cohen-Macaulay self-module statements packaged by `CohenMacaulayRing`.

Source/core/bridge triage:
* source-facing: Lemma `10.135.3`, asserting that a local complete intersection over a field is a
  Cohen-Macaulay ring;
* core/canonical: `IsLocalCompleteIntersection k S`, `Module.LocallyCohenMacaulay S S`, and
  `CohenMacaulayRing S`;
* bridge/view: passage to each localization `Localization.AtPrime q.asIdeal`, where the local
  complete-intersection hypothesis becomes a complete-intersection local ring and hence a
  Cohen-Macaulay self-module.

The public theorem should therefore take the source-level hypothesis explicitly and return the
global owner `CohenMacaulayRing S` directly, rather than hide the main input in an instance
argument.
-/
-- Proof sketch: for each prime `p` of `S`, localize at `p`. A local complete intersection over a
-- field stays a local complete intersection after localization, so `Sₚ` admits a presentation by
-- quotienting a regular local ring by a regular sequence. Regular local rings are
-- Cohen-Macaulay, and quotienting a Cohen-Macaulay local ring by a regular sequence remains
-- Cohen-Macaulay. Hence every prime localization of `S` is Cohen-Macaulay, which is exactly the
-- global `CohenMacaulayRing` condition. The theorem header does not repeat a separate finite-type
-- or Noetherian hypothesis, since that data is derived from `hCI`.
/-- Lemma 10.135.3: a finite type `k`-algebra that is a local complete intersection over `k` is a
Cohen-Macaulay ring. -/
theorem cohenMacaulayRing_of_isLocalCompleteIntersection
    (hCI : IsLocalCompleteIntersection k S) : CohenMacaulayRing S := by
  let _ : IsLocalCompleteIntersection k S := hCI
  sorry

end
