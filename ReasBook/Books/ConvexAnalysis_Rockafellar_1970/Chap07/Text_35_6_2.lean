import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_2

noncomputable section

open scoped Rockafellar

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.2 reuses the second partial subdifferential with source-facing
  no-parameter notation `∂₂ K(u, v)`.
- `core/canonical`: the chapter owner is `Bifunction.subdifferential2At`, i.e. the
  second-variable slice on the canonical pairing-level subgradient owner from Chapter 23.
- `bridge/view`: this file is recall-only and keeps both canonical surfaces coherent:
  pairing-level (`∂₂[Y]K(u, v)`) and strong-dual (`∂₂ K(u, v)`).

Domain-style sampling used here:
- `Bifunction.subdifferential2At` from `Chap07.Text_35_5_2`;
- `Bifunction.mem_subdifferential2At_pairing` from `Chap07.Text_35_5_2`;
- `Bifunction.subdifferential2AtDual` from `Chap07.Text_35_5_2`;
- `Bifunction.mem_subdifferential2At` from `Chap07.Text_35_5_2`;
- `_root_.subdifferentialAt` from Chapter 23 as the intrinsic upstream owner.

Primitive data vs derived API:
- primitive owner data already live upstream in `Bifunction.subdifferential2At`;
- derived API here: direct recall of the pairing-level owner, its companion membership theorem,
  and the intrinsic-owner equality bridges, plus direct recall of the source-facing strong-dual
  owner and membership theorem.

Layer target: owner-first pairing surface with a coherent no-parameter strong-dual bridge.
-/

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub V]

/- Text 35.6.2 pairing-level owner recall. -/
recall subdifferential2At

/- Pairing-level affine-support membership criterion companion recall. -/
recall mem_subdifferential2At_pairing

/- Intrinsic-owner equality bridge recall (`∂₂[Y]K(u, v)` as the slice owner). -/
recall subdifferential2At_eq_subdifferentialAt

/- Notation-surface intrinsic bridge recall (`∂₂[Y]K(u, v) = ∂[Y](K u)(v)`). -/
recall subdifferential2At_eq_subdifferentialAt_notation

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/- Strong-dual bridge owner recall, using plain source notation `∂₂ K(u, v)`. -/
recall subdifferential2AtDual

/- Strong-dual membership companion recall, using plain source notation `∂₂ K(u, v)`. -/
recall mem_subdifferential2At

end

end Bifunction
