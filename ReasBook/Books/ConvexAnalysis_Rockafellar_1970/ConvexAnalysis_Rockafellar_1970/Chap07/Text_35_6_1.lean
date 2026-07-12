import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_1

noncomputable section

open scoped Rockafellar

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.1 introduces the first partial subdifferential with respect to the
  first variable of a concave-convex bifunction `K`.
- `core/canonical`: the chapter owner is `Bifunction.subdifferential1At` with companion
  pairing-level membership theorem `Bifunction.mem_subdifferential1At_pairing`.
- `bridge/view`: the no-explicit-carrier source surface is the strong-dual notation bridge
  `∂₁ K(u, v)` with membership theorem `Bifunction.mem_subdifferential1At`.

Layer target: owner-first recall at both canonical surfaces:
- pairing-level (`∂₁[Y]K(u, v)`) for intrinsic dual-pairing reuse;
- strong-dual notation bridge (`∂₁ K(u, v)`) for source-facing no-parameter notation.
-/

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U]

/- Text 35.6.1 pairing-level owner recall. -/
recall subdifferential1At

/- Pairing-level affine-support membership criterion companion recall. -/
recall mem_subdifferential1At_pairing

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/- Strong-dual notation bridge recall, using plain source notation `∂₁ K(u, v)`. -/
recall subdifferential1At

/- Strong-dual membership companion recall, using plain source notation `∂₁ K(u, v)`. -/
recall mem_subdifferential1At

end

end Bifunction
