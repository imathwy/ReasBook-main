import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopCat TopCat.Sheaf

noncomputable section

/-
Domain-style sampling for Example 7.41.3:
- primary domain: pushforward of sheaves of sets along a fixed continuous map of spaces, together
  with the finite-colimit preservation predicates `PreservesColimitsOfShape WalkingParallelPair`
  and `PreservesColimitsOfShape WalkingSpan`;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.discrete.map`,
  `Functor.sheafPushforwardContinuous`,
  `MorphismOfTopoiIn.pushforward`;
- owner abstraction: the core owner is the canonical sheaf-pushforward functor
  `TopCat.Sheaf.pushforward`, specialized here to the collapse map from the discrete two-point
  space to the one-point space;
- primitive data: only the fixed continuous map `Fin 2 → PUnit`;
- derived API: the two non-preservation statements for coequalizers and pushouts.

Source/core/bridge triage:
- `source-facing`: the Stacks counterexample for the direct image along the two-point collapse map;
- `core/canonical`: the functor
  `pushforward Type (discrete.map (fun _ : Fin 2 ↦ PUnit.unit))`;
- `bridge/view`: the identification of this pushforward with binary product on pairs of sets used
  in the proof sketch.

There is no upstream chapter-local duplicate owner here: the correct public surface is the
canonical pushforward functor itself. Since the file only exports the two counterexample
statements, the right public surface is the explicit canonical owner term rather than a local alias
for the fixed collapse map or its pushforward.
-/

-- Proof sketch: identify sheaves on the discrete two-point space with pairs of sets, note that
-- the pushforward along the collapse map `Fin 2 → PUnit` acts as binary product, and use the
-- case `A₂ = ∅` from the Stacks example to see that this product functor does not preserve the
-- relevant coequalizer.
/-- Example 7.41.3 (1): for the collapse map from the discrete two-point space to the one-point
space, the direct-image functor on sheaves of sets does not preserve coequalizers. -/
theorem two_point_to_point_pushforward_not_preserves_coequalizers :
    ¬ PreservesColimitsOfShape WalkingParallelPair
      (pushforward Type (discrete.map (fun _ : Fin 2 ↦ PUnit.unit))) := sorry

-- Proof sketch: the same discrete-two-point computation provides a pushout diagram whose image
-- under the pushforward functor fails to remain a pushout, again because the functor acts as
-- binary product on the underlying pair of sets.
/-- Example 7.41.3 (2): for the same collapse map, the direct-image functor on sheaves of sets
does not preserve pushouts. -/
theorem two_point_to_point_pushforward_not_preserves_pushouts :
    ¬ PreservesColimitsOfShape WalkingSpan
      (pushforward Type (discrete.map (fun _ : Fin 2 ↦ PUnit.unit))) := sorry
