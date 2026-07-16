import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1

noncomputable section

universe u

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.3 studies the explicit saddle-function on `𝕜 × 𝕜` whose value is
  `+∞`, `0`, or `-∞` according to the sign of the product `uv`, together with its upper/lower
  closures and its finite-value locus.
- `core/canonical`: the Chapter 34 iterated closure owners `Bifunction.upperClosure` and
  `Bifunction.lowerClosure` from `Defn_34_1`, together with the chapter finite-value owner surface
  `dom(Function.uncurry K) ∩ dom(-Function.uncurry K)`.

Domain-style sampling used here:
- `Bifunction.upperClosure` and `Bifunction.lowerClosure` from `Defn_34_1`;
- `Function.uncurry` as the canonical owner bridge from a bifunction to an ordinary function;
- `dom(·)` from `Definition_4_4`, paired intrinsically as
  `dom(Function.uncurry K) ∩ dom(-Function.uncurry K)`;
- `Convex 𝕜` and the product-set notation `×ˢ` from mathlib.

Primitive data vs derived API:
- primitive source datum: the explicit bifunction `productSignSaddle`;
- derived API: the upper-closure and lower-closure formulas, the finite-value-locus description,
  and the non-product consequence for that locus.

Layer target: `source-facing`, written directly on the canonical iterated closure formulas and the
intrinsic finite-value owner.
-/

variable (𝕜 : Type u)

/-- The explicit saddle-function of Text 34.1.3, equal to `+∞`, `0`, or `-∞` according to the
sign of `uv`. -/
def productSignSaddle [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    𝕜 → 𝕜 → WithBotTop 𝕜 :=
  fun u v =>
    if 0 < u * v then ⊤ else if u * v = 0 then 0 else ⊥

-- Proof sketch: unfold `productSignSaddle`; this is the defining case split on the sign
-- of `u * v`.
/-- Evaluating `productSignSaddle` amounts to the defining sign-of-product case split. -/
@[simp] theorem productSignSaddle_apply [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (u v : 𝕜) :
    productSignSaddle 𝕜 u v =
      if 0 < u * v then ⊤ else if u * v = 0 then 0 else ⊥ := rfl

-- Proof sketch: first fix `u` and compute `cl₂` of the slice `v ↦ productSignSaddle u v`.
-- For `u ≠ 0`, that slice is `-∞` on an open half-line, so its convex closure collapses to `-∞`
-- everywhere; for `u = 0`, the slice is constantly `0`. Applying `cl₁` to the resulting spike in
-- the `u`-variable preserves `0` on the axis and `-∞` off it.
/-- Text 34.1.3 (1): the upper closure `K̅` of the product-sign saddle-function is `0` on the
axis `u = 0` and `-∞` away from that axis. -/
theorem upperClosure_productSignSaddle [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] :
    (productSignSaddle 𝕜)̅ =
      fun u _ ↦ if u = 0 then 0 else ⊥ := sorry

-- Proof sketch: first fix `v` and compute `cl₁` of the slice `u ↦ productSignSaddle u v`.
-- For `v ≠ 0`, that slice is `+∞` on an open half-line, so its concave closure collapses to `+∞`
-- everywhere; for `v = 0`, the slice is constantly `0`. Applying `cl₂` to the resulting spike in
-- the `v`-variable preserves `0` on the axis and `+∞` off it.
/-- The lower closure `K̲` of the product-sign saddle-function is `0` on the axis `v = 0` and
`+∞` away from that axis. -/
theorem lowerClosure_productSignSaddle [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] :
    (productSignSaddle 𝕜)̲ =
      fun _ v ↦ if v = 0 then 0 else ⊤ := sorry

-- Proof sketch: finite-valuedness is written as
-- `p ∈ dom(Function.uncurry (productSignSaddle 𝕜)) ∩
--   dom(-Function.uncurry (productSignSaddle 𝕜))`.
-- For `productSignSaddle`, this conjunction holds exactly in the middle branch of the defining
-- case split, so exactly when `u * v = 0`. In an ordered ring,
-- `u * v = 0` is equivalent to `u = 0 ∨ v = 0`, giving the union of the two coordinate axes.
/-- The finite-value locus of `productSignSaddle` is the union of the two coordinate axes. -/
theorem finiteValueLocus_productSignSaddle_eq_axes [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    dom(Function.uncurry (productSignSaddle 𝕜)) ∩
      dom(-Function.uncurry (productSignSaddle 𝕜)) =
      {p : 𝕜 × 𝕜 | p.1 = 0} ∪ {p : 𝕜 × 𝕜 | p.2 = 0} := sorry

-- Proof sketch: by the previous theorem, the finite-value locus is the union of the two axes. If
-- that locus were a product `A ×ˢ B` with `A` and `B` convex, then `(0, 0)`, `(1, 0)`, and
-- `(0, 1)` would lie in `A ×ˢ B`, forcing both `0` and `1` to lie in each factor. Hence `(1, 1)`
-- would also lie in `A ×ˢ B`, contradicting that `(1, 1)` is not on either axis.
/-- The finite-value locus of `productSignSaddle` is not a product of two convex subsets of `𝕜`.
-/
theorem finiteValueLocus_productSignSaddle_not_prod_of_convex_sets [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    ¬ ∃ A B : Set 𝕜, Convex 𝕜 A ∧ Convex 𝕜 B ∧
      dom(Function.uncurry (productSignSaddle 𝕜)) ∩
        dom(-Function.uncurry (productSignSaddle 𝕜)) = A ×ˢ B :=
  sorry

end Bifunction
