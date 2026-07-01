import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1

noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithTopBot 𝕜}
local notation "fStar" => (f⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.2 identifies the range of `∂f` with the conjugate-side
  subdifferential domain and places that range between `ri(dom f⋆)` and `dom(f⋆)`.
- `core/canonical`: the owner statements are intrinsic on `gph∂`, relation inversion
  `SetRel.inv`, the codomain-explicit conjugate-domain owner `dom∂[E](fStar)`, and the
  primal range owner `cod∂(f)`.
- `bridge/view`: the Euclidean self-dual graph view is downstream; this item keeps the canonical
  dual/primal owner surface.

Domain-style sampling used here:
- `gph∂[Y](·)` and `dom∂[Y](·)` from Definitions 5.24.3/5.24.1;
- relation-owner lemmas `SetRel.inv`, `SetRel.dom_inv`;
- `_root_.subdifferentialGraph_convexConjugate_eq_inv` from Text 26.0.1.

Primitive data vs derived API:
- primitive graph-level bridge input:
  `gph∂[E](fStar) = (gph∂(f)).inv`;
- primitive conjugate-side owner set: `dom∂[E](fStar)`, with codomain parameter explicit because
  it is not recoverable from `fStar`;
- derived source-facing bridge API: codomain/domain transport from `cod∂(f)`
  along graph inversion.

Layer target: `bridge/view`.
-/

/-- Relation-level bridge: if the conjugate-side intrinsic graph is the inverse of the primal
graph, then the canonical range owner `cod∂(f)` equals the conjugate-side domain owner
`dom∂[E](fStar)`. -/
theorem codSubdifferential_eq_domSubdifferential_convexConjugate_of_graph_eq_inv
    (hgraph : gph∂[E](fStar) = (gph∂(f)).inv) :
    cod∂(f) = dom∂[E](fStar) := by
  calc
    cod∂(f) = (gph∂[E](fStar)).dom := by
      simpa [SetRel.dom_inv] using congrArg SetRel.dom hgraph.symm
    _ = dom∂[E](fStar) := rfl

/-- The range of the intrinsic subdifferential graph equals the conjugate-side subdifferential
domain with explicit primal codomain parameter. -/
theorem codSubdifferential_eq_domSubdifferential_convexConjugate
    (hf : IsClosedProperConvex[𝕜] f) :
    cod∂(f) = dom∂[E](fStar) := by
  exact codSubdifferential_eq_domSubdifferential_convexConjugate_of_graph_eq_inv
    (_root_.subdifferentialGraph_convexConjugate_eq_inv hf)

-- Proof sketch: first identify `cod∂(f)` with `dom∂[E](fStar)`.
-- Then transport any already-available conjugate-side domain sandwich
-- `riDom[𝕜](fStar) ⊆ dom∂[E](fStar) ⊆ dom(fStar)` across that equality.
/-- Transport lemma at owner level: a conjugate-side sandwich on `dom∂[E](fStar)` transfers to
the primal range owner `cod∂(f)` once `cod∂(f) = dom∂[E](fStar)` is known. -/
theorem codSubdifferential_between_riDom_and_dom_convexConjugate_of_eq
    (hcod : cod∂(f) = dom∂[E](fStar))
    (hdom_conj : riDom[𝕜](fStar) ⊆ dom∂[E](fStar) ∧ dom∂[E](fStar) ⊆ dom(fStar)) :
    riDom[𝕜](fStar) ⊆ cod∂(f) ∧ cod∂(f) ⊆ dom(fStar) := by
  constructor
  · intro x hx
    exact hcod.symm ▸ hdom_conj.1 hx
  · intro x hx
    exact hdom_conj.2 (by rwa [hcod] at hx)

/-- Remark 5.24.2, intrinsic owner form: if the conjugate-side sandwich is available at codomain
`E`, then the range owner `cod∂(f)` lies between `riDom[𝕜](fStar)` and `dom(fStar)`. -/
theorem codSubdifferential_between_riDom_and_dom_convexConjugate
    (hf : IsClosedProperConvex[𝕜] f)
    (hdom_conj : riDom[𝕜](fStar) ⊆ dom∂[E](fStar) ∧ dom∂[E](fStar) ⊆ dom(fStar)) :
    riDom[𝕜](fStar) ⊆ cod∂(f) ∧ cod∂(f) ⊆ dom(fStar) := by
  exact codSubdifferential_between_riDom_and_dom_convexConjugate_of_eq
    (codSubdifferential_eq_domSubdifferential_convexConjugate hf) hdom_conj

end
