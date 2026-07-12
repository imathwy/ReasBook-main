import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 28.5.4:
- primary domain: quasi-separatedness of schemes arising from local Noetherian hypotheses;
- sampled owner declarations:
  `IsLocallyNoetherian`,
  `IsLocallyNoetherian.quasiSeparatedSpace`,
  `quasiSeparatedSpace_iff_forall_affineOpens`;
- best owner abstraction: the source statement is exactly the canonical topological owner
  `QuasiSeparatedSpace X` for a scheme `X`, supplied by the instance
  `IsLocallyNoetherian.quasiSeparatedSpace`;
- source/core/bridge triage:
  `source-facing`: a locally Noetherian scheme is quasi-separated;
  `core/canonical`: `IsLocallyNoetherian.quasiSeparatedSpace`;
  `bridge/view`: none, since the canonical owner already matches the source semantics.

This item is therefore a pure canonical recall: adding a local wrapper theorem or duplicate
instance would only weaken the public API. -/

/- Lemma 28.5.4: a locally Noetherian scheme is quasi-separated. This is exactly the canonical
instance `IsLocallyNoetherian.quasiSeparatedSpace`. -/
recall IsLocallyNoetherian.quasiSeparatedSpace

end AlgebraicGeometry
