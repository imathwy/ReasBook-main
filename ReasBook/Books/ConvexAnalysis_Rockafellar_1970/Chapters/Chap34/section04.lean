import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_34_4_1 (from Chap07) -/
noncomputable section

universe u v

namespace SaddleFunction

section

variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: apply the Chapter 34 closed-slice characterization from Theorem 34.3 to the
-- closed proper concave-convex saddle-function `K`. Clause `(a)` gives
-- `dom (K u) = dom₂ K` for every `u ∈ ri[ℝ](dom₁ K)`, and clause `(d)` gives
-- `dom (fun u ↦ -K u v) = dom₁ K` for every `v ∈ ri[ℝ](dom₂ K)`. Each equality implies the
-- corresponding inclusion into the relevant closure, which is exactly the pair of fields of
-- `IsSimple ℝ K`.
/-- Text 34.4.1: every closed proper saddle-function is simple. In the Chapter 34 owner layer,
this is formalized for a closed proper concave-convex saddle-function `K` as the implication
from `IsConcaveConvex ℝ K`, `IsClosed K`, and `IsProper K` to `IsSimple ℝ K`. -/
theorem isSimple_of_isClosed_of_isProper
    {K : U → V → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hK_closed : IsClosed K)
    (hK_proper : IsProper K) :
    IsSimple ℝ K := sorry

end

end SaddleFunction

/-! ### Text_34_4_2 (from Chap07) -/
noncomputable section

universe u v

open scoped Rockafellar
open SaddleFunction

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: view `lowerPairing F` as the canonical Chapter 34 lower saddle representative
-- attached to `F`. The Chapter 33 slice-conjugate results give the required concave-convex and
-- slice-closed properties of that kernel, and the Chapter 34 simplicity criterion then applies
-- to this canonical representative.
/-- Text 34.4.2: convex-side clause of the source statement. If `F` is a convex bifunction, then
the saddle-function `K(u, x^*) = ⟪F u, x^*⟫ᶠ`, i.e. `lowerPairing F`, is simple. -/
theorem lowerPairing_isSimple_of_uncurry_isConvex
    {F : U → X → EReal}
    (hF_convex : (Function.uncurry F).IsConvex ℝ) :
    IsSimple ℝ (lowerPairing F) := sorry

end

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: apply the convex-side statement to the sign-dual/swapped kernel corresponding to
-- `G`, then rewrite the resulting lower-pairing representative as the concave slice-conjugate
-- kernel `fun u xStar ↦ concaveConjugate (G xStar) u`.
/-- Concave-side companion: if `G` is a concave bifunction, then the saddle kernel
`(u, x^*) ↦ concaveConjugate (G x^*) u` is simple. -/
theorem concaveConjugateKernel_isSimple_of_uncurry_isConcave
    {G : X → U → EReal}
    (hG_concave : (Function.uncurry G).IsConcave ℝ) :
    IsSimple ℝ (fun (u : U) (xStar : X) ↦ concaveConjugate (G xStar) u) := sorry

end

end Bifunction

/-! ### Text_34_4_3 (from Chap07) -/
noncomputable section

universe u v

namespace SaddleFunction

section

variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: the nonempty-interior hypothesis on `dom K = dom₁ K ×ˢ dom₂ K`
-- forces both coordinate domains to have nonempty interior. For a concave-convex saddle-function,
-- those coordinate domains are convex, so their relative interiors agree with their ordinary
-- interiors. The Chapter 34 slice-domain behavior over interior points then gives exactly the two
-- containment fields required by `IsSimple ℝ K`.
/-- Text 34.4.3: if the effective domain of a saddle-function `K` has nonempty interior, then `K`
is simple. In the chapter owner language, a concave-convex saddle-function whose effective domain
`dom K` has nonempty interior satisfies `IsSimple ℝ K`. -/
theorem isSimple_of_interior_nonempty_dom
    {K : U → V → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hdom_int : (interior (dom K)).Nonempty) :
    IsSimple ℝ K := sorry

end

end SaddleFunction

/-! ### Text_34_4_4 (from Chap07) -/
noncomputable section

open Bifunction (productSignSaddle)

namespace SaddleFunction

/-!
Source/core/bridge triage:

- `source-facing`: this item gives a concrete concave-convex saddle-function on `ℝ × ℝ` whose
  slice domains show that the Chapter 34 simplicity condition fails.
- `core/canonical`: the relevant owner predicates are `SaddleFunction.IsConcaveConvex ℝ` and
  `SaddleFunction.IsSimple ℝ`, together with the Chapter 34 domain owners used inside
  `IsSimple`.
- `bridge/view`: the explicit bifunction itself is already owned upstream by
  `Bifunction.productSignSaddle` in `Text_34_1_3`, so this file should reuse that owner rather
  than redefine it locally.

Primary mathematical domain:
- saddle-functions and simplicity in convex analysis.

Domain-style sampling used here:
- `Bifunction.productSignSaddle` from `Text_34_1_3`;
- `SaddleFunction.IsConcaveConvex` from `Definition33_0_1`;
- `SaddleFunction.IsSimple` from `Defn_34_5`;
- the Chapter 34 slice-domain owners `dom₁`, `dom₂`, and the one-variable effective-domain owner
  `dom`, which already sit behind `IsSimple`.

Primitive data vs derived API:
- primitive source data reused from upstream: `Bifunction.productSignSaddle`;
- derived API: its three branch formulas, the concave-convexity fact, and the failure of
  simplicity.

Layer target: `source-facing`.
-/

-- Proof sketch: unfold `productSignSaddle`; the first branch of the defining `if` is selected
-- directly by the hypothesis `0 < u * v`.
/-- On the region where `uv > 0`, `productSignSaddle` is `+∞`. -/
theorem productSignSaddle_apply_of_mul_pos
    {u v : ℝ} (h : 0 < u * v) :
    productSignSaddle ℝ u v = ⊤ := sorry

-- Proof sketch: unfold `productSignSaddle`; the second branch of the defining `if` is selected
-- because the first inequality fails and the product is exactly zero.
/-- On the zero set of the product, `productSignSaddle` is `0`. -/
theorem productSignSaddle_apply_of_mul_eq_zero
    {u v : ℝ} (h : u * v = 0) :
    productSignSaddle ℝ u v = 0 := sorry

-- Proof sketch: unfold `productSignSaddle`; a negative product rules out the positive and zero
-- branches, leaving the `-∞` branch.
/-- On the region where `uv < 0`, `productSignSaddle` is `-∞`. -/
theorem productSignSaddle_apply_of_mul_neg
    {u v : ℝ} (h : u * v < 0) :
    productSignSaddle ℝ u v = ⊥ := sorry

section

variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: fix one variable and split on the sign of the other. Each row is constant `0`
-- when `u = 0`, identically `+∞` on one open half-line and `-∞` on the other when `u ≠ 0`, and
-- the same description holds symmetrically for columns. These slice descriptions yield concavity
-- in the first variable and convexity in the second variable.
/-- `productSignSaddle` is a concave-convex saddle-function on `ℝ × ℝ`. -/
theorem isConcaveConvex_productSignSaddle :
    IsConcaveConvex ℝ (productSignSaddle ℝ) := sorry

end

-- Proof sketch: compute `dom₁ (productSignSaddle ℝ) = {0}` and
-- `dom₂ (productSignSaddle ℝ) = {0}`.
-- Their relative interiors and closures are therefore both `{0}`. At `u = 0`, however, the slice
-- `productSignSaddle ℝ 0` is identically `0`, so `dom (productSignSaddle ℝ 0) = Set.univ`,
-- which is not contained in `closure (dom₂ (productSignSaddle ℝ)) = {0}`. This violates the first
-- field of
-- `SaddleFunction.IsSimple ℝ (productSignSaddle ℝ)`.
/-- Text 34.4.4: the concave-convex saddle-function `productSignSaddle` on `ℝ × ℝ`, defined by
`K(u, v) = +∞` for `uv > 0`, `K(u, v) = 0` for `uv = 0`, and `K(u, v) = -∞` for `uv < 0`, is
not simple. -/
theorem not_isSimple_productSignSaddle :
    ¬ IsSimple ℝ (productSignSaddle ℝ) := sorry

end SaddleFunction

/-! ### Theorem_34_4 (from Chap07) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section SameKernel

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.4 compares the Chapter 34 equivalence relation with having the same
  kernel.
- `core/canonical`: the owner layer is the existing Chapter 34 equivalence relation `K ∼ L`
  together with the Chapter 34 product domain `dom K` and its relative interior `ri[ℝ](dom K)`.
- `bridge/view`: literal equality of the restricted kernels is ill-typed because the restriction
  domains depend on the bifunction, so the canonical source-facing formulation is equality of the
  product domains together with equality of values on their common relative interior.

Primary mathematical domain:
- closed proper concave-convex saddle-functions and their Chapter 34 equivalence classes.

Domain-style sampling used here:
- `Bifunction.equivalence` and `Bifunction.equivalent_iff` from `Defn_34_4`;
- `SaddleFunction.IsClosed` from `Defn_34_2`;
- the Chapter 34 notation `dom K` from `Defn_34_3`;
- `ri[ℝ](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source data: two saddle-functions `K, L : U → X → EReal`;
- primitive owner data already present upstream: `K ∼ L`, `SaddleFunction.IsClosed`,
  `dom ·`, and `ri[ℝ](·)`;
- derived bridge API introduced here: the predicate `SameKernel K L`.

Layer target: `bridge/view`.
-/

/-- Two saddle-functions have the same Chapter 34 kernel when they have the same effective domain
and their uncurried graph functions agree on the relative interior of that domain. -/
def SameKernel (K L : U → X → EReal) : Prop :=
  dom K = dom L ∧
    Set.EqOn (Function.uncurry K) (Function.uncurry L) (ri[ℝ](dom K))

-- Proof sketch: unfold `SameKernel`; the relation is definitionally the conjunction of common
-- effective domain and equality of the two uncurried graph functions on the common relative
-- interior.
/-- Unfolded criterion for two saddle-functions to have the same Chapter 34 kernel. -/
theorem sameKernel_iff (K L : U → X → EReal) :
    SameKernel K L ↔
      dom K = dom L ∧
        Set.EqOn (Function.uncurry K) (Function.uncurry L) (ri[ℝ](dom K)) :=
  Iff.rfl

end SameKernel

section

open Bifunction

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: for `→`, use Corollary 34.2.1 to transport the effective domain and the
-- relative-interior values across the Chapter 34 equivalence relation. For `←`, Theorem 34.3
-- identifies a closed proper concave-convex saddle-function by its closed slices on the relative
-- interiors of the coordinate domains, so common kernel data forces equivalence.
/-- Theorem 34.4: two closed proper concave-convex saddle-functions are equivalent if and only if
they have the same kernel, i.e. the same effective domain and the same values on its relative
interior. -/
theorem equivalent_iff_sameKernel_of_isConcaveConvex_of_isClosed_of_isProper
    {K L : U → X → EReal}
    (hK_shape : IsConcaveConvex ℝ K)
    (hL_shape : IsConcaveConvex ℝ L)
    (hK_closed : IsClosed K)
    (hL_closed : IsClosed L)
    (hK_proper : IsProper K)
    (hL_proper : IsProper L) :
    K ∼ L ↔ SameKernel K L := sorry

end

end SaddleFunction
