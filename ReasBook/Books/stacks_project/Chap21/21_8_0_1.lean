import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 21.8.0.1:
- primary domain: Čech cosimplicial objects in `FormalCoproduct C` and the induced alternating
  coface differential on the associated cochain complex;
- sampled owner API:
  `AlternatingCofaceMapComplex.objD`,
  `FormalCoproduct.mapPower_π`,
  `FormalCoproduct.cech`,
  `CategoryTheory.cechComplexFunctor`;
- best owner abstraction: `AlternatingCofaceMapComplex.objD` for the differential, with
  `FormalCoproduct.mapPower_π` as the bridge identifying each coface map with the corresponding
  restriction map on Čech powers.

Source/core/bridge triage:
- `source-facing`: the Čech differential is the alternating sum of the restriction maps obtained by
  forgetting one index;
- `core/canonical`: `AlternatingCofaceMapComplex.objD`;
- `bridge/view`: `FormalCoproduct.mapPower_π`.

Primitive data versus derived API:
- primitive data: the underlying formal coproduct/family defining the Čech object;
- derived API: the coface maps and their alternating sum, already owned upstream.

This item should therefore stay recall-only: it identifies the source statement with the canonical
owners instead of introducing a parallel local differential or restriction-map wrapper. -/
/- 21.8.0.1: in the Čech complex, the differential is the alternating sum of the coface maps;
for the Čech cosimplicial object these coface maps are the restriction maps to the higher fibre
products. This is exactly `AlternatingCofaceMapComplex.objD` specialized to the Čech cosimplicial
object. -/
recall AlternatingCofaceMapComplex.objD

/- Forgetting one index in the Čech power object induces the restriction map to the corresponding
higher intersection component; this is the formal-coproduct identity `mapPower_π`. -/
recall FormalCoproduct.mapPower_π
