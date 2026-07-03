import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_23_0_1 (from Chap05) -/
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

/-! ### Lemma_23_0_2 (from Chap05) -/
noncomputable section

universe u v

section

open scoped Rockafellar
open Filter

variable {𝕜 : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [T2Space (WithTopBot 𝕜)]
variable [NeBot (𝓝[>] (0 : 𝕜))]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.2 packages the direction-side regularity of
  `y ↦ directionalDerivativeAt f x y` (convexity, positive homogeneity, and subadditivity) at a
  fixed base point `x` of a convex function `f`.
- `core/canonical`: the owner abstractions are already upstream:
  `Function.directionalDerivativeAt` from `Lemma_23_0_1`,
  `Function.IsConvex` from `Theorem_4_2`, and
  `Function.PositivelyHomogeneous` from `Definition_4_8`.
- `bridge/view`: the source wording “`f'(x; ·)` is sublinear” is represented by the canonical
  owner predicates plus the explicit two-point inequality
  `directionalDerivativeAt f x (d₁ + d₂) ≤ ...`.

Primitive data vs derived API:
- primitive data: a convex function `f`, a finite base point `x ∈ dom(f)` with `f x ≠ ⊥`, and a
  nonempty subdifferential `∂[Y]f(x)`;
- primitive owner reused from upstream: `directionalDerivativeAt f x`;
- derived API: convexity, positive homogeneity, and subadditivity of that owner in the direction
  variable.

Layer target: `source-facing` on the canonical chapter owner surface.

Ambient-assumption minimization:
- this file keeps exactly the additive-topological module layer needed by the upstream owners
  `directionalDerivativeAt` and `∂[Y]f(x)`, and no norm, inner-product, completeness, or
  finite-dimensional assumptions are exposed.

Codomain normalization:
- theorem surfaces use the chapter canonical codomain layer `WithTopBot 𝕜`,
  and now consume that codomain directly from the upstream owner in `Lemma_23_0_1` with no local
  concrete-codomain scalar-action glue.
- the support-function scaling bridge is consumed from the generic pairing owner theorem
  `supportFunction_smul_left_of_nonempty_apply`, and the support-function subadditivity bridge is
  consumed from `supportFunction_add_le`, both at the same ordered-field pairing layer.
-/

-- Proof sketch: identify `directionalDerivativeAt f x` with the support-function owner
-- `δᵛ(· | ∂[Y]f(x))` from Lemma 23.0.1, then reuse the canonical owner theorem
-- `Function.isConvex_supportFunction`.
/-- Lemma 23.0.2, convexity form: for convex `f` finite at `x`, the map
`d ↦ directionalDerivativeAt f x d` is convex. -/
theorem isConvex_directionalDerivativeAt
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty) :
    (directionalDerivativeAt f x).IsConvex 𝕜 := by
  have hEq := directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    hf_convex hx hx_bot hsub
  simpa [hEq] using isConvex_supportFunction (∂[Y]f(x))

-- Proof sketch: the same direction-side owner is positively homogeneous in the direction
-- variable because it is identified with the support-function owner.
/-- Lemma 23.0.2, homogeneity form: for convex `f` finite at `x`,
`d ↦ directionalDerivativeAt f x d` is positively homogeneous. -/
theorem positivelyHomogeneous_directionalDerivativeAt
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty) :
    (directionalDerivativeAt f x).PositivelyHomogeneous 𝕜 := by
  have hsupport :
      (δᵛ(· | ∂[Y]f(x)) : E → WithTopBot 𝕜).PositivelyHomogeneous 𝕜 := by
    intro c d
    simpa [smul_eq_mul] using
      supportFunction_smul_left_of_nonempty_apply
        (∂[Y]f(x)) hsub (le_of_lt c.2) d
  have hEq := directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    hf_convex hx hx_bot hsub
  simpa [hEq] using hsupport

/-- Positive-scalar owner form of
`positivelyHomogeneous_directionalDerivativeAt`. -/
theorem directionalDerivativeAt_smul_pos
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    (c : PositiveScalars 𝕜) (d : E) :
    directionalDerivativeAt f x (c • d) = c • directionalDerivativeAt f x d := by
  exact
    (positivelyHomogeneous_directionalDerivativeAt hf_convex hx hx_bot hsub).map_smul_pos c d

/-- Positive-scalar evaluation form of
`positivelyHomogeneous_directionalDerivativeAt`. -/
theorem directionalDerivativeAt_smul
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    {c : 𝕜} (hc : 0 < c) (d : E) :
    directionalDerivativeAt f x (c • d) = c • directionalDerivativeAt f x d := by
  simpa using directionalDerivativeAt_smul_pos hf_convex hx hx_bot hsub ⟨c, hc⟩ d

-- Proof sketch: rewrite the directional derivative by Lemma 23.0.1 as the support-function owner
-- of the subdifferential and apply the canonical support-function subadditivity theorem from
-- Text 13.2.3.
/-- Lemma 23.0.2, subadditivity form: for convex `f` finite at `x`, the directional-derivative
map in the direction variable satisfies
`directionalDerivativeAt f x (d₁ + d₂) ≤ directionalDerivativeAt f x d₁ +
  directionalDerivativeAt f x d₂`.
-/
theorem directionalDerivativeAt_add_le
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    (d₁ d₂ : E) :
    directionalDerivativeAt f x (d₁ + d₂) ≤
      directionalDerivativeAt f x d₁ + directionalDerivativeAt f x d₂ := by
  have hEq := directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    hf_convex hx hx_bot hsub
  simpa [hEq] using supportFunction_add_le (∂[Y]f(x)) d₁ d₂

end Function

end

/-! ### Lemma_23_0_3 (from Chap05) -/
noncomputable section

universe u v

section

open Filter
open scoped Topology

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/-- `HasBilateralDirectionalDerivativeAt f x d L` says that the directional difference quotient of
`f` at `x` along `d` converges to `L` on the punctured neighborhood of `0`. -/
def HasBilateralDirectionalDerivativeAt
    (f : E → WithTopBot 𝕜) (x d : E) (L : WithTopBot 𝕜) : Prop :=
  Tendsto (directionalDifferenceQuotientAt f x d) (𝓝[≠] (0 : 𝕜)) (𝓝 L)

end Function

end

section

open Filter
open scoped Topology

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [DistribSMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.3 states the left/right symmetry of directional difference
  quotients under the direction change `d ↦ -d`, and reformulates existence of a bilateral
  directional derivative through the two right-hand limits in directions `d` and `-d`.
- `core/canonical`: the only one-sided owner remains
  `Function.HasDirectionalDerivativeAt` from Lemma 23.0.1; the only new owner introduced here is
  the punctured-neighborhood bilateral companion `Function.HasBilateralDirectionalDerivativeAt`.
- `bridge/view`: the source's left directional derivative along `d` is expressed directly as the
  left-limit theorem for `Function.directionalDifferenceQuotientAt`, proved equivalent to the
  reflected right-hand owner along `-d`; no parallel left-sided owner is introduced.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt` from
  `Items/Chap05/Lemma_23_0_1.lean`;
- `Function.HasDirectionalDerivativeAt` from `Items/Chap05/Lemma_23_0_1.lean`,
  which is the chapter's one-sided directional-derivative owner;
- `Function.hasDirectionalDerivativeAt_supportFunction_subdifferentialAt` from
  `Items/Chap05/Lemma_23_0_1.lean`,
  which fixes the right-hand `Tendsto` owner for directional difference quotients in this chapter;
- `Function.tendsto_directionalDifferenceQuotientAt_toWithBotTop_bilateral_of_hasGradientAt` from
  `Items/Chap05/Lemma_23_0_4.lean`,
  which uses the punctured-neighborhood owner shape `Tendsto ... (𝓝[≠] (0 : 𝕜)) ...`;
- mathlib's filter-level owner `Filter.Tendsto` together with
  `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin`.

Primitive data vs derived API:
- primitive data: the function `f`, the base point `x`, and the direction `d`;
- primitive owners reused from upstream: `Function.directionalDifferenceQuotientAt` and
  `Function.HasDirectionalDerivativeAt`;
- derived API: the reflected left-directional view, the bilateral/right owner equivalence, and the
  existential bilateral companion.

Layer target: `source-facing`.

Ambient-assumption minimization:
- the punctured-neighborhood owner `Function.HasBilateralDirectionalDerivativeAt` itself only uses
  the directional-difference quotient owner and is therefore stated at the primitive
  `AddCommMonoid`/`SMul` layer;
- the symmetry theorems below use direction negation `d ↦ -d`, so they are stated at
  `AddCommGroup`/`DistribSMul`, still far below the stronger finite-dimensional inner-product-space
  layer.
- this bridge file still presents the bilateral/left-right filter decomposition over `𝕜`
  (`𝓝[>] (0 : 𝕜)`, `𝓝[<] (0 : 𝕜)`, `𝓝[≠] (0 : 𝕜)`), and adds no stronger ambient structure than
  needed for that directional-negation comparison: the scalar side uses order-topology control on
  left/right neighborhoods around `0`, while the codomain side only asks for continuity of `Neg`
  to express reflected limits.
-/

namespace Function

/-- Changing the direction from `d` to `-d` turns the directional difference quotient at time `t`
into the negative of the quotient in direction `d` at time `-t`. -/
theorem directionalDifferenceQuotientAt_neg_direction
    (f : E → WithTopBot 𝕜) (x d : E) (t : 𝕜) :
    directionalDifferenceQuotientAt f x (-d) t = -directionalDifferenceQuotientAt f x d (-t) := by
  sorry

variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]

-- Proof sketch: substitute `t = -s` in the left quotient. The numerator becomes the same
-- difference quotient evaluated at the reflected direction `-d`, and the denominator changes sign,
-- so the limit value is negated. Bilateral existence is then exactly the conjunction of the right
-- limit in direction `d` with the reflected right limit in direction `-d`.
/-- Lemma 23.0.3, left-limit form: the source left directional derivative along `d` equals `L`
exactly when the chapter's right directional-derivative owner along `-d` equals `-L`. -/
theorem tendsto_directionalDifferenceQuotientAt_left_iff_hasDirectionalDerivativeAt_neg
    [OrderTopology 𝕜] [ContinuousNeg (WithTopBot 𝕜)]
    {f : E → WithTopBot 𝕜} {x d : E} {L : WithTopBot 𝕜} :
    Tendsto (directionalDifferenceQuotientAt f x d) (𝓝[<] (0 : 𝕜)) (𝓝 L) ↔
      HasDirectionalDerivativeAt f x (-d) (-L) := by
  sorry

/-- Lemma 23.0.3, bilateral owner form: bilateral convergence along `d` is equivalent to the two
right directional-derivative owners in directions `d` and `-d`, with reflected limit `-L`. -/
theorem hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg
    [OrderTopology 𝕜] [ContinuousNeg (WithTopBot 𝕜)]
    {f : E → WithTopBot 𝕜} {x d : E} {L : WithTopBot 𝕜} :
    HasBilateralDirectionalDerivativeAt f x d L ↔
      HasDirectionalDerivativeAt f x d L ∧
        HasDirectionalDerivativeAt f x (-d) (-L) := by
  rw [HasBilateralDirectionalDerivativeAt, punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, tendsto_sup]
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact ⟨by simpa [HasDirectionalDerivativeAt] using hRight,
      tendsto_directionalDifferenceQuotientAt_left_iff_hasDirectionalDerivativeAt_neg.1 hLeft⟩
  · rintro ⟨hRight, hLeft⟩
    exact ⟨tendsto_directionalDifferenceQuotientAt_left_iff_hasDirectionalDerivativeAt_neg.2 hLeft,
      by simpa [HasDirectionalDerivativeAt] using hRight⟩

/-- Lemma 23.0.3, existential owner companion: a bilateral directional derivative along `d` exists
exactly when the right directional derivatives in directions `d` and `-d` exist with opposite
values. -/
theorem exists_hasBilateralDirectionalDerivativeAt_iff_exists_hasDirectionalDerivativeAt_and_neg
    [OrderTopology 𝕜] [ContinuousNeg (WithTopBot 𝕜)]
    {f : E → WithTopBot 𝕜} {x d : E} :
    (∃ L : WithTopBot 𝕜, HasBilateralDirectionalDerivativeAt f x d L) ↔
      ∃ L : WithTopBot 𝕜,
        HasDirectionalDerivativeAt f x d L ∧
          HasDirectionalDerivativeAt f x (-d) (-L) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, (hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg.1 hL)⟩
  · rintro ⟨L, hL⟩
    exact ⟨L, (hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg.2 hL)⟩

end Function

end

/-! ### Lemma_23_0_4 (from Chap05) -/
noncomputable section

universe u v

section

open Filter

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.4 says that differentiability at `x` forces the directional
  derivative in every direction to be finite and bilateral. In real inner-product spaces this
  value is the gradient pairing.
- `core/canonical`: the ambient owner abstractions already exist upstream: mathlib's
  `HasFDerivAt`, together with the Chapter 23 owners
  `Function.directionalDifferenceQuotientAt`, `Function.HasDirectionalDerivativeAt`,
  `Function.HasBilateralDirectionalDerivativeAt`, and `Function.directionalDerivativeAt`.
- `bridge/view`: this file is only the bridge from the scalar-valued differentiability owner to
  the chapter directional-derivative owner on `WithTopBot 𝕜` via the codomain lift
  `Function.toWithTopBot`; it should not introduce a second directional-derivative package.
  The gradient-facing statements are downstream real inner-product specializations of this
  Fréchet-derivative bridge.

Domain-style sampling used here:
- mathlib's derivative owners `HasFDerivAt`, `HasLineDerivAt`, and
  `HasLineDerivAt.tendsto_slope_zero_right`;
- the gradient specialization bridge `HasGradientAt.hasFDerivAt` and
  `InnerProductSpace.toDual_apply`;
- the project Chapter 23 owners `Function.directionalDifferenceQuotientAt`,
  `Function.HasDirectionalDerivativeAt`, `Function.HasBilateralDirectionalDerivativeAt`, and
  `Function.directionalDerivativeAt` from
  `ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1`.

Primitive data vs derived API:
- primitive owner-side input: `HasFDerivAt f f' x`;
- primitive owner-side output:
  `HasDirectionalDerivativeAt f.toWithTopBot x y ((f' y : 𝕜) : WithTopBot 𝕜)`;
- derived owner-side companions: the bilateral owner view
  `HasBilateralDirectionalDerivativeAt f.toWithTopBot x y ((f' y : 𝕜) : WithTopBot 𝕜)` and the
  value formula for `directionalDerivativeAt`;
- derived source-facing input: `HasGradientAt f g x` and then `DifferentiableAt ℝ f x`, which
  canonically recover the source gradient pairing `⟪g, y⟫ = (f' y)`.

Layer target: `bridge/view`. The source statement adds no new owner object; it identifies the
existing directional-derivative owner with the canonical gradient pairing under a stronger smooth
hypothesis. The owner theorem here should therefore land first on
`HasDirectionalDerivativeAt` at the primitive Fréchet-derivative layer, with gradient and
bilateral source forms exposed only as companion views.

Ambient-assumption minimization:
- the Chapter 23 directional-difference owner only uses the additive/module structure already
  provided in `Lemma_23_0_1`;
- the Fréchet-derivative bridge needs only `[SeminormedAddCommGroup E] [NormedSpace 𝕜 E]`;
- the inner-pairing bridge (`⟪g, y⟫`) needs only `[InnerProductSpace ℝ E]`;
- the `HasGradientAt` source view needs only the inner-product structure, while the
  `DifferentiableAt`/`∇` source view remains in the complete real inner-product specialization.
-/

namespace Function

/-- Owner-side primitive bridge for Lemma 23.0.4: if `f` has Fréchet derivative `f'` at `x`, then
the Chapter 23 right directional-derivative owner for `f.toWithTopBot` in direction `y` exists and
is the finite value `f' y`. -/
theorem hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt
    {f : E → 𝕜} {x y : E} {f' : E →L[𝕜] 𝕜} (hf : HasFDerivAt f f' x) :
    HasDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot 𝕜) := by
  sorry

section

variable [OrderTopology 𝕜] [OrderTopology (WithTopBot 𝕜)]

/-- Bilateral owner companion at the primitive derivative layer: Fréchet differentiability gives
the punctured-neighborhood directional-derivative owner with value `f' y`. -/
theorem hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt
    {f : E → 𝕜} {x y : E} {f' : E →L[𝕜] 𝕜} (hf : HasFDerivAt f f' x) :
    HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot 𝕜) := by
  refine hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg.2 ?_
  refine ⟨?_, ?_⟩
  · exact hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
  · have hneg :
        HasDirectionalDerivativeAt f.toWithTopBot x (-y) (f' (-y) : WithTopBot 𝕜) :=
      hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
    simpa [map_neg] using hneg

end

section

variable [T2Space (WithTopBot 𝕜)]

/-- Owner-side value form at the primitive derivative layer: Fréchet derivative evaluation gives
the Chapter 23 directional-derivative owner value on `f.toWithTopBot`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt
    {f : E → 𝕜} {x y : E} {f' : E →L[𝕜] 𝕜} (hf : HasFDerivAt f f' x) :
    directionalDerivativeAt f.toWithTopBot x y = (f' y : WithTopBot 𝕜) := by
  simpa [HasDirectionalDerivativeAt, directionalDerivativeAt] using
    (hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf).limUnder_eq

end

end Function

end

section

open Filter
open scoped RealInnerProductSpace

variable {E : Type u} [InnerProductSpace ℝ E]

namespace Function

/-- Pairing-level bridge at the primitive derivative layer: if the Fréchet derivative at `x`
evaluates as `⟪g, ·⟫`, then the Chapter 23 right directional derivative of `f.toWithTopBot` in
direction `y` exists with value `⟪g, y⟫`. -/
theorem hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    HasDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  have hFDeriv :
      HasDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot ℝ) :=
    hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
  simpa [hinner y] using hFDeriv

/-- Pairing-level bilateral companion at the primitive derivative layer: if the Fréchet
derivative at `x` evaluates as `⟪g, ·⟫`, then the punctured-neighborhood directional-derivative
owner exists with value `⟪g, y⟫`. -/
theorem hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  have hFDeriv :
      HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot ℝ) :=
    hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
  simpa [hinner y] using hFDeriv

/-- Pairing-level bilateral-limit view: if the Fréchet derivative at `x` evaluates as `⟪g, ·⟫`,
then the directional difference quotient of `f.toWithTopBot` converges on the punctured
neighborhood of `0` to `⟪g, y⟫`. -/
theorem tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    Tendsto (directionalDifferenceQuotientAt f.toWithTopBot x y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (⟪g, y⟫ : WithTopBot ℝ)) := by
  simpa [HasBilateralDirectionalDerivativeAt] using
    hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner hf hinner

/-- Pairing-level value form at the primitive derivative layer: if the Fréchet derivative at `x`
evaluates as `⟪g, ·⟫`, then `directionalDerivativeAt f.toWithTopBot x y = ⟪g, y⟫`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_inner_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    directionalDerivativeAt f.toWithTopBot x y = (⟪g, y⟫ : WithTopBot ℝ) := by
  have hFDeriv :
      directionalDerivativeAt f.toWithTopBot x y = (f' y : WithTopBot ℝ) :=
    directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt hf
  simpa [hinner y] using hFDeriv

end Function

end

section

open Filter
open scoped Gradient RealInnerProductSpace

variable {E : Type u} [InnerProductSpace ℝ E]

namespace Function

/-- Owner-side gradient specialization for Lemma 23.0.4: if `f` has gradient `g` at `x`, then the
Chapter 23 right directional derivative of `f.toWithTopBot` in direction `y` is `⟪g, y⟫`. -/
theorem hasDirectionalDerivativeAt_toWithTopBot_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    HasDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  exact
    hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

/-- Bilateral owner specialization for a prescribed gradient: the punctured-neighborhood owner
form follows from the primitive derivative-layer bridge. -/
theorem hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  exact
    hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

/-- Lemma 23.0.4, bilateral companion for a prescribed gradient: the source's bilateral-limit
wording is the punctured-neighborhood view of the Chapter 23 directional-derivative owner, so it
is derived from the owner theorem together with the left/right symmetry from Lemma 23.0.3. -/
theorem tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    Tendsto (directionalDifferenceQuotientAt f.toWithTopBot x y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (⟪g, y⟫ : WithTopBot ℝ)) := by
  exact
    tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasFDerivAt_inner
      hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

/-- Owner-side value form for Lemma 23.0.4: a prescribed gradient `g` at `x` evaluates the
Chapter 23 directional-derivative owner on `f.toWithTopBot`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_inner_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    directionalDerivativeAt f.toWithTopBot x y = (⟪g, y⟫ : WithTopBot ℝ) := by
  exact
    directionalDerivativeAt_toWithTopBot_eq_inner_of_hasFDerivAt_inner hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

section

variable [CompleteSpace E]

/-- Lemma 23.0.4, bilateral-limit form: if `f` is differentiable at `x`, then the directional
difference quotient of `f.toWithTopBot` has a finite bilateral limit, namely the gradient pairing
with the direction `y`. -/
theorem tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_differentiableAt
    {f : E → ℝ} {x y : E} (hf : DifferentiableAt ℝ f x) :
    Tendsto (directionalDifferenceQuotientAt f.toWithTopBot x y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (⟪∇ f x, y⟫ : WithTopBot ℝ)) := by
  simpa using
    tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasGradientAt hf.hasGradientAt

/-- Lemma 23.0.4, owner form: if `f` is differentiable at `x`, then the Chapter 23 directional
derivative of `f.toWithTopBot` in the direction `y` is the finite value `⟪∇ f x, y⟫`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_inner_gradient
    {f : E → ℝ} {x y : E} (hf : DifferentiableAt ℝ f x) :
    directionalDerivativeAt f.toWithTopBot x y = (⟪∇ f x, y⟫ : WithTopBot ℝ) := by
  simpa using
    directionalDerivativeAt_toWithTopBot_eq_inner_of_hasGradientAt hf.hasGradientAt

end

end Function

end

/-! ### Definition_23_0_5 (from Chap05) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.0.5 introduces the terminology that a dual-side element
  `xStar` is a subgradient of an extended-valued function `f` at `x` when it satisfies the
  global supporting-affine inequality.
- `core/canonical`: the chapter owner for this notion is `_root_.subdifferentialAt`, written on
  the theorem surface as `∂[Y]f(x)`.
- `bridge/view`: the source inequality is already the exact membership criterion
  `_root_.mem_subdifferentialAt_pairing`.

Domain-style sampling:
- `_root_.subdifferentialAt` from `Definition_23_0_6`, the intrinsic pairing-valued owner;
- `_root_.mem_subdifferentialAt_pairing` from the same file, the intrinsic
  supporting-inequality characterization;
- `_root_.mem_subdifferentialAt` from the same file, the default-`StrongDual` specialization;
- `Function.mem_subdifferentialAt` from the same file, the Euclidean inner-product bridge view.

Primitive data vs derived API:
- primitive owner data already exist upstream as `_root_.subdifferentialAt f x Y`;
- derived source-facing API here is only the terminology that a subgradient at `x` is exactly
  membership in that owner set, equivalently the supporting-affine inequality.

Layer target: `source-facing` recall of the existing pairing-level membership theorem. Introducing
an `IsSubgradientAt` alias here would duplicate the canonical chapter owner without adding new
mathematics.
-/

/- Definition 23.0.5: for a pairing-based Chapter 23 subdifferential owner, an element `xStar`
is a subgradient of `f` at `x` exactly when it belongs to `∂[Y]f(x)`, equivalently when it
satisfies the global supporting-affine inequality. -/
recall _root_.mem_subdifferentialAt_pairing

/-! ### Definition_23_0_6 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.0.6 introduces the subdifferential of an extended-valued
  function at a point: the set of continuous linear functionals whose affine support inequality
  holds everywhere.
- `core/canonical`: there is no upstream project or mathlib owner for this exact notion in the
  current chapter graph, so this file owns the declaration `subdifferentialAt`. The primitive
  mathematical data are only the function `f`, the base point `x`, and the supporting inequality
  for a dual-side element of a pairing.
- `bridge/view`: the membership theorem below is the derived pointwise characterization of being a
  subgradient at `x`.

Domain-style sampling used here:
- the chapter owner `convexConjugate` from `Chap03.Defn_12_2`,
  which also lives on the canonical extended codomain `WithTopBot 𝕜` and uses Rockafellar scoped
  notation;
- the chapter owner `indicatorFunction` with notation `δ(· | C)` from
  `Chap01.Defintion_4_8_1`,
  showing the project convention of a direct owner plus thin notation/specification API;
- the chapter effective-domain owner `dom(·)` from `Chap01.Definition_4_4`,
  which downstream Chapter 23 theorems use alongside subdifferentials;
- the project pairing owner `HasPairing`, which keeps the source-facing definition intrinsic and
  lets the strong-dual model `StrongDual 𝕜 E` remain a canonical default specialization.

Primitive data vs derived API:
- primitive owner: `subdifferentialAt f x`;
- derived API: the membership characterization `xStar ∈ subdifferentialAt f x`.

Layer target: `source-facing`. The definition itself only uses the affine support inequality
through a pairing, so the owner is pairing-intrinsic with the continuous-dual model kept as the
default specialization.
-/

/-- Definition 23.0.6: the subdifferential of an extended-valued function at `x` is the set
of dual-side elements that support `f` at `x`. -/
def subdifferentialAt (f : E → WithTopBot 𝕜) (x : E)
    {Y : Type*} [HasPairing E Y 𝕜] : Set Y :=
  {xStar | ∀ z, f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)}

scoped[Rockafellar] notation "∂[" Y "]" f "(" x ")" => subdifferentialAt (Y := Y) f x

/-- Pairing-level membership form of `subdifferentialAt`. -/
@[simp] theorem mem_subdifferentialAt_pairing
    {f : E → WithTopBot 𝕜} {x : E} {Y : Type*} [HasPairing E Y 𝕜]
    {xStar : Y} :
    xStar ∈ (∂[Y]f(x)) ↔
      ∀ z, f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

/-- Pairing transport API for `subdifferentialAt`: if two pairing instances on `(E, Y, 𝕜)` are
pointwise equal, they define the same subdifferential set at every base point. -/
theorem subdifferentialAt_eq_of_pairing_eq
    {f : E → WithTopBot 𝕜} {x : E} {Y : Type*}
    {pairing₁ pairing₂ : HasPairing E Y 𝕜}
    (hpair : ∀ z : E, ∀ xStar : Y,
      @HasPairing.pairing E Y 𝕜 pairing₁ z xStar =
        @HasPairing.pairing E Y 𝕜 pairing₂ z xStar) :
    (letI : HasPairing E Y 𝕜 := pairing₁; _root_.subdifferentialAt (Y := Y) f x) =
      (letI : HasPairing E Y 𝕜 := pairing₂; _root_.subdifferentialAt (Y := Y) f x) := by
  ext xStar
  constructor <;> intro hx
  · rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₂ xStar]
    rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₁ xStar] at hx
    intro z
    simpa [hpair (z - x) xStar] using hx z
  · rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₁ xStar]
    rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₂ xStar] at hx
    intro z
    simpa [hpair (z - x) xStar] using hx z

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

scoped[Rockafellar] notation "∂ " f " at " x =>
  (_root_.subdifferentialAt (Y := StrongDual _ _) f x)

/-- Pairing-level membership form on the default dual codomain `StrongDual 𝕜 E`. This keeps the
default subdifferential surface `∂ f at x` on the intrinsic pairing owner layer; the concrete
evaluation form is provided below as a bridge specialization. -/
theorem mem_subdifferentialAt_default_pairing
    {f : E → WithTopBot 𝕜} {x : E}
    {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂ f at x) ↔
      ∀ z, f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A functional belongs to the subdifferential at `x` exactly when it satisfies the global
supporting-affine inequality. -/
@[simp] theorem mem_subdifferentialAt
    {f : E → WithTopBot 𝕜} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂ f at x) ↔ ∀ z, f z ≥ f x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜) := by
  rw [mem_subdifferentialAt_default_pairing (f := f) (x := x) (xStar := xStar)]
  change
      (∀ z, f z ≥ f x + (((HasLinearPairing.pairingLinear (z - x)) xStar : 𝕜) :
        WithTopBot 𝕜)) ↔
      ∀ z, f z ≥ f x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜)
  rfl

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.0.6 introduces the subdifferential `∂f(x)` through the
  supporting-affine inequality.
- `core/canonical`: the primitive owner remains the dual-valued declaration
  `_root_.subdifferentialAt`.
- `bridge/view`: later Chapter 23 statements pair subdifferentials with directions using the
  chapter support-function owner on `Set E`. The canonical dual-pairing map
  `InnerProductSpace.toDualMap 𝕜 E` sends vectors to continuous dual vectors, so
  `Function.subdifferentialAt` below is a thin vector-valued bridge, not a second root
  definition.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsProper` and `dom(·)` from `Chap01.Definition_4_6`;
- `supportFunction` from `Chap01.Defintion_4_8_2`;
- mathlib's canonical dual-pairing bridge `InnerProductSpace.toDualMap`, which gives the chapter's
  standard vector-to-dual map in ordered inner-product spaces.

Primitive data vs derived API:
- primitive owner: `_root_.subdifferentialAt f x`;
- derived API: the vector-valued bridge `Function.subdifferentialAt f x`,
  obtained by pulling back the owner along `InnerProductSpace.toDualMap 𝕜 E`,
  and its pointwise membership simplification.

Layer target: `bridge/view`.

Notation evaluation:
- the pointwise source notation is exposed as `∂ f at x`, with `∂[Y]f(x)` available when the
  dual codomain must be explicit. This keeps the textbook symbol while avoiding a parser collision
  with the established image notation `∂f(S)`.
-/

namespace Function

/-- In an ordered inner-product space, the vector-valued subdifferential used later in this
chapter is the pullback of the dual-valued owner `_root_.subdifferentialAt` along
`InnerProductSpace.toDualMap`. -/
abbrev subdifferentialAt (f : E → WithTopBot 𝕜) (x : E) : Set E :=
  (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (_root_.subdifferentialAt f x)

scoped[Rockafellar] notation "∂ᵥ" f "(" x ")" => Function.subdifferentialAt f x

@[simp] theorem mem_subdifferentialAt {f : E → WithTopBot 𝕜} {x g : E} :
    g ∈ (∂ᵥf(x)) ↔ ∀ z, f z ≥ f x + ((inner 𝕜 g (z - x) : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end Function

end

/-! ### Example_23_0_7 (from Chap05) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace Rockafellar

universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 23.0.7 records explicit subdifferentials for four standard convex
  examples: the Euclidean norm, the coordinate `ℓ∞` norm, the closed-unit-ball square-root
  barrier, and the indicator of a convex set.
- `core/canonical`: the owner abstractions already present in the project are
  `_root_.subdifferentialAt` (dual-valued) and `Function.subdifferentialAt` (Euclidean bridge)
  from `Chap05.Definition_23_0_6`,
  `normalCone` from `Chap01.Definition_2_7_10`, and the coordinate owners
  `linftyNorm` and `coordinateL1Ball` from `Chap01.Text_5_5_0_5`.
- `bridge/view`: for indicator functions, this file states the canonical dual-owner formulas first
  and then keeps the Euclidean vector-valued formulas as Fréchet-Riesz transport bridges, instead
  of introducing any parallel local “subgradient vector” owner.

Domain-style sampling used here:
- `Function.subdifferentialAt` and `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `normalCone` and `mem_normalCone_iff_sub_nonpos` from `Chap01.Definition_2_7_10`;
- `linftyNorm` and `coordinateL1Ball` from `Chap01.Text_5_5_0_5`;
- `Metric.closedBall` as the canonical owner for the Euclidean unit ball.

Primitive data vs derived API:
- primitive concrete data introduced here: the square-root barrier on the closed unit ball;
- derived API: the explicit subdifferential formulas for the norm, coordinate `ℓ∞` norm, and
  indicator examples, with the active-coordinate presentation of the `ℓ∞` case kept inline rather
  than packaged as a second public owner.

Layer target: `source-facing`, stated on the existing canonical owners.
-/

section Norm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Function

local notation "normGauge" => Function.toWithTopBot (fun x : E ↦ ‖x‖)

-- Proof sketch: combine the Chapter 23 supporting-hyperplane characterization with the sharp
-- Cauchy--Schwarz bound `⟪g, z⟫ ≤ ‖g‖ * ‖z‖`; at the origin this shows that the supporting
-- inequality is equivalent to `‖g‖ ≤ 1`, i.e. membership in the closed unit ball.
/-- Example 23.0.7 (1): in a real inner-product space, the subdifferential of the norm at
the origin is the closed unit ball. -/
theorem subdifferentialAt_norm_zero :
    ∂ᵥnormGauge((0 : E)) =
      Metric.closedBall (0 : E) 1 := sorry

-- Proof sketch: at `x ≠ 0`, differentiability of the norm identifies the unique supporting
-- functional with the Fréchet-Riesz vector `‖x‖⁻¹ • x`, and strict convexity of the Euclidean norm
-- forces the subdifferential to be a singleton.
/-- Example 23.0.7 (2): away from the origin, the subdifferential of the norm is the singleton
containing the normalized base point. -/
theorem subdifferentialAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    ∂ᵥnormGauge(x) = ({‖x‖⁻¹ • x} : Set E) := sorry

end Function

end Norm

section Linfty

variable {ι : Type*} [Fintype ι]

section Generic

variable {𝕜 : Type v} [Ring 𝕜] [LinearOrder 𝕜]
local notation "X" => ι → 𝕜
local notation "linftyGauge" => Function.toWithTopBot (fun x : X ↦ linftyNorm x)
local instance instHasPairingLinfty : HasPairing X X 𝕜 where
  pairing x y := ∑ i, x i * y i

namespace Function

-- Proof sketch: at the origin, the Chapter 23 support inequality for `linftyGauge` is equivalent
-- to the coordinate estimate `∑ j |g j| ≤ 1`, i.e. membership in the canonical coordinate owner
-- `coordinateL1Ball` on the function-space model.
/-- Example 23.0.7 (3): at the origin, the pairing-owner subdifferential of the coordinate `ℓ∞`
norm on `ι → 𝕜` is the coordinate `ℓ¹` unit ball. -/
theorem subdifferentialAt_linftyNorm_zero :
    ∂[X]linftyGauge((0 : X)) = (coordinateL1Ball : Set X) := sorry

end Function

end Generic

section Real

local notation "X" => ι → ℝ
local notation "linftyGauge" => Function.toWithTopBot (fun x : X ↦ linftyNorm x)

namespace Function

-- Proof sketch: for `x ≠ 0`, use the Chapter 23 support characterization together with the
-- coordinate support-function computation for the `ℓ¹` ball. The active supporting points are the
-- signed basis vectors indexed by the coordinates where `|x j| = linftyNorm x`, and the
-- subdifferential is their convex hull.
/-- Example 23.0.7 (4): away from the origin, for real coordinates the pairing-owner
subdifferential of `linftyNorm` is the convex hull of the signed coordinate basis vectors indexed
by the active coordinates. -/
theorem subdifferentialAt_linftyNorm_of_ne_zero [DecidableEq ι] {x : ι → ℝ} (hx : x ≠ 0) :
    ∂[X]linftyGauge(x) =
      convexHull ℝ
        ((fun j : ι ↦ Pi.single j (Real.sign (x j))) ''
          {j : ι | |x j| = linftyNorm x}) := sorry

end Function

end Real

end Linfty

section Barrier

variable {E : Type u} [SeminormedAddCommGroup E]

/-- The closed-unit-ball barrier example `x ↦ -sqrt(1 - ‖x‖^2)` on `‖x‖ ≤ 1`, with value `+∞`
outside the closed unit ball. -/
def unitBallSqrtBarrier : E → WithTopBot ℝ :=
  Function.toWithTopBotOn (fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ 2))
    (Metric.closedBall (0 : E) 1)

-- Proof sketch: unfold `unitBallSqrtBarrier` and simplify the `if` branch using `hx`.
/-- On the closed unit ball, `unitBallSqrtBarrier` is given by the negative square-root branch. -/
theorem unitBallSqrtBarrier_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) :
    unitBallSqrtBarrier x = ((-Real.sqrt (1 - ‖x‖ ^ 2) : ℝ) : WithTopBot ℝ) := by
  have hmem : x ∈ Metric.closedBall (0 : E) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  simpa [unitBallSqrtBarrier] using
    Function.toWithTopBotOn_of_mem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      (Metric.closedBall (0 : E) 1)
      hmem

-- Proof sketch: unfold `unitBallSqrtBarrier`; the hypothesis `1 < ‖x‖` forces the outside branch.
/-- Outside the closed unit ball, `unitBallSqrtBarrier` takes the value `+∞`. -/
theorem unitBallSqrtBarrier_of_one_lt_norm {x : E} (hx : 1 < ‖x‖) :
    unitBallSqrtBarrier x = (⊤ : WithTopBot ℝ) := by
  have hnotmem : x ∉ Metric.closedBall (0 : E) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  simpa [unitBallSqrtBarrier] using
    Function.toWithTopBotOn_of_notMem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      (Metric.closedBall (0 : E) 1)
      hnotmem

end Barrier

section BarrierSubdifferential

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Function

-- Proof sketch: on `‖x‖ < 1`, the barrier example is finite and differentiable, so its
-- subdifferential is nonempty by the Chapter 23 bridge from differentiability to singleton
-- subdifferentials.
/-- Example 23.0.7 (5): inside the open unit ball, the square-root barrier example is
subdifferentiable. -/
theorem subdifferentialAt_unitBallSqrtBarrier_nonempty_of_norm_lt_one {x : E} (hx : ‖x‖ < 1) :
    (∂ᵥunitBallSqrtBarrier(x)).Nonempty := sorry

-- Proof sketch: when `‖x‖ ≥ 1`, either the function is already `+∞` off the closed ball or the
-- boundary supporting inequality has no continuous supporting vector, so the Chapter 23 owner set
-- is empty.
/-- Example 23.0.7 (6): on and outside the unit sphere, the square-root barrier example has empty
subdifferential. -/
theorem subdifferentialAt_unitBallSqrtBarrier_eq_empty_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    ∂ᵥunitBallSqrtBarrier(x) = (∅ : Set E) := sorry

end Function

end BarrierSubdifferential

section IndicatorDual

variable {𝕜 : Type v} [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E]
variable {N : Type (max u v)}

-- Proof sketch: unfold the indicator branches in the dual-valued Chapter 23 owner
-- `∂[N](·)(·)`; on `z ∈ C` the value is `0` and off `C` it is `+∞`, so the support
-- inequality is equivalent to the feasibility condition and nonpositivity on displacements.
/-- Example 23.0.7 (7), canonical dual-owner form: membership in the subdifferential of the
indicator function is exactly the normal-inequality condition on the underlying set. -/
theorem mem_subdifferentialAt_indicatorFunction_iff {C : Set E} {x : E}
    {xStar : N} [AddMonoid 𝕜] [HasPairing E N 𝕜] :
    xStar ∈ (∂[N] (δ[𝕜](· | C))(x)) ↔
      x ∈ C ∧ ∀ z ∈ C, (⟪z - x, xStar⟫ₚ : 𝕜) ≤ 0 := sorry

section NormalCone

variable [CommRing 𝕜] [Module 𝕜 E]
variable [AddLeftMono 𝕜]
variable [AddCommMonoid N] [Module 𝕜 N] [HasLinearPairing E N 𝕜]

-- Proof sketch: extensionality on membership, then combine the previous canonical indicator
-- criterion with `mem_normalCone_iff_sub_nonpos` specialized to the canonical pairing with
-- the chosen dual-side linear pairing codomain `N`.
/-- Example 23.0.7 (8), canonical dual-owner form: the subdifferential of the indicator function
of a set is the normal cone at the base point. -/
theorem subdifferentialAt_indicatorFunction_eq_normalCone (C : Set E) (x : E) :
    ∂[N] (δ[𝕜](· | C))(x) = N[𝕜, N](x | C) := sorry

end NormalCone

end IndicatorDual

section Indicator

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Function

-- Proof sketch: this is the Euclidean bridge of the canonical dual-owner theorem above along
-- `InnerProductSpace.toDualMap`; it rewrites the dual inequality as an inner-product inequality.
/-- Example 23.0.7 (7), Euclidean bridge form: membership in the subdifferential of the indicator
function is the normal-inequality condition written with inner products. -/
theorem mem_subdifferentialAt_indicatorFunction_iff {C : Set E} {x xStar : E} :
    xStar ∈ ∂ᵥ(δ[ℝ](· | C))(x) ↔
      x ∈ C ∧ ∀ z ∈ C, ⟪xStar, z - x⟫ ≤ 0 := sorry

-- Proof sketch: transport the canonical dual-owner normal-cone identity above through the
-- Fréchet-Riesz bridge to get the vector-valued Euclidean statement.
/-- Example 23.0.7 (8), Euclidean bridge form: the subdifferential of the indicator function of a
set is the normal cone at the base point. -/
theorem subdifferentialAt_indicatorFunction_eq_normalCone (C : Set E) (x : E) :
    ∂ᵥ(δ[ℝ](· | C))(x) = N[ℝ](x | C) := sorry

end Function

end Indicator
