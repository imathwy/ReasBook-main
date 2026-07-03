import Mathlib.Tactic.Recall
import stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.37.5:
- primary domain: topological formal smoothness for adic topologies on commutative rings.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_iff`
  * `IsAdic`
  * `IsAdicComplete`
- owner abstraction: `RingHom.formally_smooth_for_adic`.
- source/core/bridge triage:
  * source-facing: the adic lifting theorem for a formally smooth-for-adic map, with a chosen
    ideal of definition `I` on the target.
  * core/canonical: `RingHom.FormallySmoothTopologically`.
  * bridge/view: the ambient-topology witnesses `hS : IsAdic 𝔫` and `hA : IsAdic I`.
- primitive data: the formally smooth-for-adic hypothesis `hf` and the target-side ideal-of-
  definition data `hA : IsAdic I`, together with the complete-separated owner
  `[IsAdicComplete I A]` and the eventual containment `∃ t : ℕ+, J ^ (t : ℕ) ≤ I`.
- derived API: ambient-topology continuity of the given quotient map `ψ` and of the resulting lift
  `φ`, recovered through the adic witnesses.
-/

/- Lemma 15.37.5: the adic lifting theorem is derived API for the owner
`RingHom.formally_smooth_for_adic`, so the theorem now lives in the owner file
`Definition_15_37_3`. -/
recall RingHom.exists_continuous_lift_of_formally_smooth_for_adic
