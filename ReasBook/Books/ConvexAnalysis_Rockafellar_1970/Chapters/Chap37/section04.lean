import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_37_4_1 (from Chap07) -/
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

/-! ### Theorem_37_4 (from Chap07) -/
noncomputable section

open scoped Rockafellar

universe u u'

namespace Bifunction

section Pairing

variable {U : Type u} {V : Type}
variable {YU : Type u'} {YV : Type}
variable [Sub U]
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [HasPairing U YU ℝ] [HasPairing V YV ℝ]

/-- The saddle kernel obtained by subtracting the two pairing terms determined by `(uStar, vStar)`
from `K`. -/
def subPairingTranslate
    (K : U → V → WithBotTop ℝ) (uStar : YU) (vStar : YV) : U → V → WithBotTop ℝ :=
  fun u v ↦ K u v - ⟪u, uStar⟫ₚ - ⟪v, vStar⟫ₚ

-- Proof sketch: unfold `subPairingTranslate`.
/-- Evaluating `subPairingTranslate K uStar vStar` gives the defining affine-translation formula.
-/
@[simp] theorem subPairingTranslate_apply
    (K : U → V → WithBotTop ℝ) (uStar : YU) (vStar : YV) (u : U) (v : V) :
    subPairingTranslate K uStar vStar u v = K u v - ⟪u, uStar⟫ₚ - ⟪v, vStar⟫ₚ := sorry

-- Proof sketch: subtract the affine form determined by `(uStar, vStar)` from `K`. Membership
-- `(uStar, vStar) ∈ d(K ; u, v)` becomes the zero-subgradient condition for the translated
-- kernel, and Proposition 36.5.2 rewrites that zero-subgradient condition as the ambient
-- saddle-point predicate for the translated kernel.
/-- Theorem 37.4 (1): a pair `(uStar, vStar)` belongs to the saddle subdifferential `∂K(u, v)`
exactly when the translated kernel `K - ⟪·, uStar⟫ - ⟪·, vStar⟫`, rendered as
`subPairingTranslate K uStar vStar`, has `(u, v)` as a saddle-point. -/
theorem mem_subdifferentialAt_iff_isSaddlePointOn_univ_swap_subPairingTranslate
    {K : U → V → WithBotTop ℝ} {u : U} {v : V} {uStar : YU} {vStar : YV} :
    (uStar, vStar) ∈ d(K ; u, v | YU, YV) ↔
      IsSaddlePointOn (Set.univ : Set V) (Set.univ : Set U)
        (Function.swap (subPairingTranslate K uStar vStar)) v u := sorry

end Pairing

section Domain

variable {U : Type u} {V : Type}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

-- Proof sketch: write the relative interior of the product domain through
-- `ri[ℝ](dom K)`, then use the Chapter 35 partial-subdifferential nonemptiness
-- criteria on the two slices to obtain a witness in `d(K ; u, v)`.
/-- Theorem 37.4 (2): for a closed proper concave-convex saddle-function, every point of
`ri (dom K)` admits a saddle subgradient; rendered here as inclusion of
`ri[ℝ](dom K)` into the intrinsic strong-dual domain owner `dom∂ₛ K`. -/
theorem ri_dom_subset_subdifferentialDomDual_of_isClosedProperConcaveConvex
    {K : U → V → WithBotTop ℝ}
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hK_concaveConvex : SaddleFunction.IsConcaveConvex ℝ K) :
    ri[ℝ](SaddleFunction.dom K) ⊆ (dom∂ₛ K) := sorry

-- Proof sketch: if `(u, v)` admits a saddle subgradient, choose
-- `(uStar, vStar) ∈ d(K ; u, v)`. Clause (1) converts this to a saddle-point statement for the
-- corresponding translated kernel, and the Chapter 36 domain bridge places `(u, v)` in
-- `dom K`.
/-- Theorem 37.4 (3): for a closed proper concave-convex saddle-function, the domain of the
saddle subdifferential is contained in the product domain. -/
theorem subdifferentialDomDual_subset_dom_of_isClosedProperConcaveConvex
    {K : U → V → WithBotTop ℝ}
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hK_concaveConvex : SaddleFunction.IsConcaveConvex ℝ K) :
    (dom∂ₛ K) ⊆ SaddleFunction.dom K := sorry

end Domain

end Bifunction
