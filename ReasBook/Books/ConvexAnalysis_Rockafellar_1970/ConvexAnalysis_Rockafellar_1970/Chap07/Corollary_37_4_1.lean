import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_3_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type v} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [Sub U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {YU : Type u} {YV : Type v}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.4.1 says that equivalent saddle-functions have the same saddle
  subdifferential `∂K = ∂L`, and that their values agree on the common domain of that
  subdifferential.
- `core/canonical`: the equivalence owner is the Chapter 34 relation `K ∼ L` from `Defn_34_4`.
- `bridge/view`: the saddle subdifferential surface is the chapter owner
  `Bifunction.subdifferentialAt` from `Text_35_6_3`, while its canonical domain owner is
  `domd(K | YU, YV)` from `Definition_37_3_1`.

Domain-style sampling used here:
- `Bifunction.equivalent_iff` and the notation `K ∼ L` from `Defn_34_4`;
- `Bifunction.subdifferentialAt` and the notation `d(K ; u, v | YU, YV)` from `Text_35_6_3`;
- `domd(K | YU, YV)` and `mem_subdifferentialDom` from `Definition_37_3_1`.

Primitive data vs derived API:
- primitive source data: equivalent saddle-functions `K ∼ L`;
- primitive owner data used here: the pointwise saddle subdifferentials `d(K ; u, v)` and
  `d(L ; u, v)` on the canonical pairing layer;
- derived API recorded here: pointwise equality of those saddle subdifferentials, equality of the
  canonical domain owners `domd(K | YU, YV)` and `domd(L | YU, YV)`, the induced equivalence of
  the pointwise nonemptiness predicates, and value agreement on the common subdifferential domain.

Layer target: `source-facing`, stated directly on the chapter's canonical owner declarations.
-/

-- Proof sketch: fix `(u, v)` and a candidate pair `(uStar, vStar)`. Theorem 37.4 rewrites
-- `(uStar, vStar) ∈ d(K ; u, v)` as a saddle-point statement for the translated kernel obtained
-- by subtracting the two pairing terms from `K`. The same translation preserves equivalence, so
-- Theorem 36.4 gives the corresponding saddle-point statement for the translated kernel of `L`,
-- and translating back yields equality of the two saddle subdifferentials.
/-- Corollary 37.4.1 (1): equivalent saddle-functions have the same saddle subdifferential at
every point, i.e. `∂K = ∂L` as multivalued mappings. -/
theorem subdifferentialAt_eq_of_equivalent
    {K L : U → V → WithBotTop 𝕜} (hKL : K ∼ L) {u : U} {v : V} :
    d(K ; u, v | YU, YV) = d(L ; u, v | YU, YV) := sorry

-- Proof sketch: extensionality on `U × V`; membership in either side is exactly nonemptiness of
-- the corresponding fiber, and `subdifferentialAt_eq_of_equivalent hKL` identifies those fibers.
/-- Equivalent saddle-functions have the same saddle-subdifferential domain set. -/
theorem subdifferentialDomain_eq_of_equivalent
    {K L : U → V → WithBotTop 𝕜} (hKL : K ∼ L) :
    domd(K | YU, YV) = domd(L | YU, YV) := by
  ext p
  simp [subdifferentialAt_eq_of_equivalent hKL]

-- Proof sketch: evaluate the domain-set equality
-- `subdifferentialDomain_eq_of_equivalent hKL` at the point `(u, v)`.
/-- Equivalent saddle-functions have the same pointwise nonemptiness locus for the saddle
subdifferential. -/
theorem subdifferentialAt_ne_empty_iff_of_equivalent
    {K L : U → V → WithBotTop 𝕜} (hKL : K ∼ L) {u : U} {v : V} :
    d(K ; u, v | YU, YV) ≠ ∅ ↔ d(L ; u, v | YU, YV) ≠ ∅ := by
  simp [subdifferentialAt_eq_of_equivalent hKL]

-- Proof sketch: if `d(K ; u, v)` is nonempty, choose a saddle subgradient at `(u, v)`. Theorem
-- 37.4 converts that witness into a saddle-point of the corresponding translated kernel of `K`,
-- and Theorem 36.4 transfers that saddle-point to the translated kernel of `L`. Equivalent
-- saddle-functions have the same saddle value at such a point, which is exactly the equality
-- `K u v = L u v`. The preceding domain equality identifies the common domain.
/-- Corollary 37.4.1 (2): equivalent saddle-functions agree on the common domain
`domd(K | YU, YV) = domd(L | YU, YV)` of the saddle subdifferential. -/
theorem eqOn_subdifferentialDomain_of_equivalent
    {K L : U → V → WithBotTop 𝕜} (hKL : K ∼ L) :
    Set.EqOn (Function.uncurry K) (Function.uncurry L)
      domd(K | YU, YV) := sorry

end

end Bifunction
