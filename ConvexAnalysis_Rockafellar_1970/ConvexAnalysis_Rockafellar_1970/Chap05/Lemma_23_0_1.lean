import Mathlib.Analysis.Convex.Slope
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/-- The directional difference quotient of `f` at `x` in the direction `d`. -/
def directionalDifferenceQuotientAt (f : E → WithTopBot 𝕜) (x d : E) (t : 𝕜) : WithTopBot 𝕜 :=
  ((f (x + t • d) - f x) : WithTopBot 𝕜) / (t : WithTopBot 𝕜)

section

open Filter
open scoped Topology

variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]

/-- `HasDirectionalDerivativeAt f x d L` says that the right directional difference quotient of
`f` at `x` along `d` converges to `L`. This is the source-facing owner for Rockafellar's
directional derivative `f'(x; d)`. -/
def HasDirectionalDerivativeAt (f : E → WithTopBot 𝕜) (x d : E) (L : WithTopBot 𝕜) : Prop :=
  Tendsto (directionalDifferenceQuotientAt f x d) (𝓝[>] (0 : 𝕜)) (𝓝 L)

/-- The directional derivative `f'(x; d)` is the right limit of the directional difference
quotient, represented by the canonical filter-limit owner `limUnder`. -/
def directionalDerivativeAt (f : E → WithTopBot 𝕜) (x d : E) : WithTopBot 𝕜 :=
  limUnder (𝓝[>] (0 : 𝕜)) (directionalDifferenceQuotientAt f x d)

end

end Function

section

open Filter
open scoped Rockafellar Topology

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [SupSet (WithTopBot 𝕜)]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.1 identifies the right directional derivative of a convex
  extended-real-valued function at a finite point with the support of its nonempty
  subdifferential in the chosen direction.
- `core/canonical`: the owner abstractions already present in the project are `Function.IsConvex`,
  `dom(·)`, `_root_.subdifferentialAt`, and the support-function owner `δᵛ(· | ·)`. This file adds
  only the Chapter 23 directional-derivative owners
  `Function.directionalDifferenceQuotientAt`, `Function.HasDirectionalDerivativeAt`, and
  `Function.directionalDerivativeAt`.
- `bridge/view`: Rockafellar's `sInf`-`sSup` upper formula is retained only as a companion bridge
  theorem for the limit-based owner, while the support term on the theorem surface is written
  directly with the canonical pairing-level owner as `δᵛ(d | ∂[Y]f(x))`.

Domain-style sampling used here:
- `Function.IsConvex` from the chapter owner layer;
- `supportFunction` / `δᵛ(· | ·)` from `Chap01/Defintion_4_8_2`;
- `ConvexOn.secant_mono` and `ConvexOn.monotoneOn_slope_gt` from mathlib's one-variable convex
  slope API, which provide the canonical owner abstraction behind the monotone difference-quotient
  proof route used later in this section;
- mathlib's filter-limit owner `limUnder` together with `Filter.Tendsto.limUnder_eq`, which give
  the canonical value-level API once right-hand convergence is available;
- `_root_.subdifferentialAt` / `∂[Y]f(x)` from `Chap05/Definition_23_0_6`.

Primitive data vs derived API:
- primitive source data: the convex function `f`, the finite base point `x`, the already-owned
  subdifferential `∂[Y]f(x)`, the finite-value guard `f x ≠ ⊥`, and the
  direction `d`;
- primitive owner definitions: the directional difference quotient, the predicate
  `HasDirectionalDerivativeAt`, and the limit-valued owner `directionalDerivativeAt`;
- derived API: the support-function formula for the directional derivative and the bridge theorem
  that recovers Rockafellar's `sInf`-`sSup` upper presentation from the canonical limit owner.

Layer target: `source-facing`.

Ambient-assumption minimization:
- the directional-difference owners only use addition and scalar multiplication on the ambient
  space, so they are stated at `[AddCommMonoid E] [SMul 𝕜 E]`;
- the support/subdifferential theorem is stated directly on `_root_.subdifferentialAt`, so it
  uses only the canonical pairing layer `[HasPairing E Y 𝕜]`;
- the source-facing finite-point hypothesis must remain explicit as `x ∈ dom(f)` together with
  `f x ≠ ⊥`: nonemptiness of `∂[Y]f(x)` alone does not exclude `f x = ⊥`.

Notation evaluation:
- the source notation `f'(x; d)` does not have a stable Lean parser surface in this chapter, so
  the owner remains `directionalDerivativeAt f x d`;
- the support term already has the chapter notation
  `δᵛ(d | ∂[Y]f(x))`, so no parallel local wrapper is introduced.

Codomain/scalar canonicalization:
- the source-function layer is surfaced on `WithTopBot 𝕜` (`f : E → WithTopBot 𝕜`) instead of being
  hard-wired to the alias `EReal`;
- the directional-difference/limit owners are surfaced directly in the chapter codomain
  `WithTopBot 𝕜`, avoiding concrete `EReal` theorem surfaces;
- the scalar layer is shared with the upstream owner
  `_root_.subdifferentialAt : (E → WithTopBot 𝕜) → E → Set Y` and with right-ray limits
  `𝓝[>] (0 : 𝕜)`.
-/

namespace Function

variable {f : E → WithTopBot 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

-- Proof sketch: the subgradient inequality gives an affine lower support at `x`, so every
-- directional difference quotient is bounded below by the corresponding support value. The
-- one-variable convex restriction along `t ↦ x + t • d` and the secant-slope monotonicity owner
-- show that the right difference quotient has a limit, and nonemptiness of the subdifferential
-- identifies that limit with the support function of `∂[Y]f(x)`.
/-- Lemma 23.0.1, owner form: for a convex function and a finite point `x` with nonempty
subdifferential, the directional derivative `f'(x; d)` exists and equals the support of `∂f(x)` in
the direction `d`. The theorem surface reuses the chapter support-function owner directly, so no
parallel “subdifferential support” wrapper is introduced. -/
theorem hasDirectionalDerivativeAt_supportFunction_subdifferentialAt
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    (d : E) :
    HasDirectionalDerivativeAt f x d (δᵛ(d | ∂[Y]f(x))) := sorry

section

variable [T2Space (WithTopBot 𝕜)]
variable [NeBot (𝓝[>] (0 : 𝕜))]

-- Proof sketch: evaluate the limit-valued owner `directionalDerivativeAt` at the canonical limit
-- furnished by the preceding theorem.
/-- Lemma 23.0.1, value form: for a convex function and a finite point `x` with nonempty
subdifferential, the directional derivative equals the support of `∂f(x)` evaluated on the
direction `d`. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    (d : E) :
    directionalDerivativeAt f x d = δᵛ(d | ∂[Y]f(x)) := by
  simpa [HasDirectionalDerivativeAt, directionalDerivativeAt] using
    (hasDirectionalDerivativeAt_supportFunction_subdifferentialAt
      hf_convex hx hx_bot hsub d).limUnder_eq

-- Proof sketch: the value identity above is pointwise in `d`; function extensionality upgrades it
-- to the owner-level equality of maps on directions.
/-- Function-valued owner form of Lemma 23.0.1:
`directionalDerivativeAt f x` is exactly the support function of `∂[Y]f(x)`. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty) :
    directionalDerivativeAt f x = (δᵛ(· | ∂[Y]f(x)) : E → WithTopBot 𝕜) := by
  funext d
  exact directionalDerivativeAt_eq_supportFunction_subdifferentialAt hf_convex hx hx_bot hsub d

end

-- Proof sketch: once the right directional derivative is known to exist, Rockafellar's
-- `sInf`-`sSup` upper formula recovers the same value.
/-- Rockafellar's `sInf`-`sSup` upper presentation is a bridge to the canonical
filter-limit directional-derivative owner. -/
theorem directionalDerivativeAt_eq_sInf_iSup_directionalDifferenceQuotientAt
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    [InfSet (WithTopBot 𝕜)]
    (d : E) :
    directionalDerivativeAt f x d =
      sInf ((Set.Ioi (0 : 𝕜)).image fun a : 𝕜 ↦
        sSup (directionalDifferenceQuotientAt f x d '' Set.Ioo (0 : 𝕜) a)) := sorry

end Function

end
