import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_35_6_1 (from Chap07) -/
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

/-! ### Text_35_6_2 (from Chap07) -/
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

/-! ### Text_35_6_3 (from Chap07) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.3 defines the saddle subdifferential `∂K(u, v)` of a
  concave-convex bifunction at `(u, v)` as the product of the first and second partial
  subdifferentials.
- `core/canonical`: the owner abstraction in this chapter is the pointwise set-valued map
  `Bifunction.subdifferentialAt`, together with its coordinate-membership theorem
  `Bifunction.mem_subdifferentialAt`.
- `bridge/view`: the notation `d(K ; u, v)` is the source-facing surface notation for that owner;
  the explicit-carrier form `d(K ; u, v | YU, YV)` is the thin ambient-parameter bridge when
  inference needs help.

Primary mathematical domain:
- convex analysis of saddle bifunctions and their partial subdifferentials.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Text_35_5_2`;
- the one-variable owner pattern `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- the one-variable concave owner pattern `_root_.concaveSubdifferentialAt` from
  `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive source data: the two already-owned partial subdifferentials
  `subdifferential1At K u v` and `subdifferential2At K u v`;
- primitive owner defined here: their product `subdifferentialAt K u v`;
- derived API: the pairing-level notation `d(K ; u, v)` (with inferred pairings), its explicit
  carrier form `d(K ; u, v | YU, YV)`, the canonical strong-dual bridge
  `subdifferentialAtDual` with notation `∂ₛ K(u, v)`, and the coordinate membership theorems
  `mem_subdifferentialAt` / `mem_subdifferentialAtDual`.

Layer target: `source-facing`.

Notation evaluation:
- the source-facing pairing-level notation is `d(K ; u, v)` and infers carriers from context;
- the pairing-parametric owner remains available as `d(K ; u, v | YU, YV)` when needed;
- the strong-dual theorem surface needs its own inference-stable notation, parallel to
  `∂₁ K(u, v)` and `∂₂ K(u, v)`, so this file exposes the canonical bridge as `∂ₛ K(u, v)`.
-/

/-- Text 35.6.3: the saddle subdifferential of a concave-convex bifunction `K` at `(u, v)` is
the product of the already-owned first and second partial subdifferentials. -/
def subdifferentialAt (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (YU : Type*) [HasPairing U YU 𝕜]
    (YV : Type*) [HasPairing V YV 𝕜] : Set (YU × YV) :=
  ∂₁[YU]K(u, v) ×ˢ ∂₂[YV]K(u, v)

/- Explicit dual-carrier variant of the Rockafellar saddle-subdifferential notation. -/
scoped[Rockafellar] notation "d(" k " ; " u ", " v " | " yu ", " yv ")" =>
  Bifunction.subdifferentialAt k u v yu yv

/- Source-facing notation with inferred pairing carriers. -/
scoped[Rockafellar] notation "d(" k " ; " u ", " v ")" =>
  Bifunction.subdifferentialAt k u v _ _

/-- Coordinate membership form of the saddle subdifferential product owner. -/
@[simp] theorem mem_subdifferentialAt
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {YU : Type*} [HasPairing U YU 𝕜]
    {YV : Type*} [HasPairing V YV 𝕜]
    {p : YU × YV} :
    p ∈ d(K ; u, v) ↔
      p.1 ∈ ∂₁[YU]K(u, v) ∧ p.2 ∈ ∂₂[YV]K(u, v) :=
  Iff.rfl

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Canonical strong-dual bridge for Text 35.6.3. The notation `∂ₛ K(u, v)` uses the intrinsic
continuous-dual product, while `d(K ; u, v | YU, YV)` remains the explicit pairing-level view
when type inference needs help. -/
abbrev subdifferentialAtDual (K : U → V → WithTopBot 𝕜) (u : U) (v : V) :
    Set (StrongDual 𝕜 U × StrongDual 𝕜 V) :=
  subdifferentialAt K u v (StrongDual 𝕜 U) (StrongDual 𝕜 V)

scoped[Rockafellar] notation "∂ₛ" K "(" u ", " v ")" =>
  Bifunction.subdifferentialAtDual K u v

/-- Strong-dual membership form of the saddle subdifferential product owner. -/
@[simp] theorem mem_subdifferentialAtDual
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {p : StrongDual 𝕜 U × StrongDual 𝕜 V} :
    p ∈ ∂ₛ K(u, v) ↔ p.1 ∈ ∂₁ K(u, v) ∧ p.2 ∈ ∂₂ K(u, v) :=
  Iff.rfl

end

end Bifunction

/-! ### Text_35_6_4 (from Chap07) -/
noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.4 names the set-valued mapping `(u, v) ↦ ∂K(u, v)` with no extra
  ambient carrier parameters.
- `core/canonical`: the primitive owner remains the pairing-level product owner
  `Bifunction.subdifferentialAt` from `Text_35_6_3`.
- `bridge/view`: `Bifunction.subdifferentialAtDual` is the canonical strong-dual bridge of that
  primitive owner, and this file keeps both surfaces coherent in recall form.

Primary mathematical domain:
- convex analysis of saddle bifunctions and their saddle subdifferentials.

Domain-style sampling:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Text_35_5_2`;
- `Bifunction.subdifferentialAt` from `Text_35_6_3`;
- `Bifunction.mem_subdifferentialAt` from `Text_35_6_3`;
- `Bifunction.subdifferentialAtDual` and `Bifunction.mem_subdifferentialAtDual` from
  `Text_35_6_3`.

Primitive data vs derived API:
- primitive owner data already exist upstream in the chapter at `Text_35_6_3`;
- derived API here: recall of the owner and companion theorem at the pairing layer, together with
  recall of the no-parameter strong-dual bridge surface used in source-facing notation.

Layer target: owner-first pairing surface with coherent strong-dual bridge recall.
This file intentionally avoids rebinding local scalar/ambient assumptions; those abstractions are
owned upstream by the recalled declarations.
-/

namespace Bifunction

/- Text 35.6.4 pairing-level owner recall. -/
recall subdifferentialAt

/- Pairing-level coordinate membership companion recall. -/
recall mem_subdifferentialAt

/- Strong-dual bridge owner recall, using plain source notation `∂ₛ K(u, v)`. -/
recall subdifferentialAtDual

/- Strong-dual coordinate membership companion recall. -/
recall mem_subdifferentialAtDual

end Bifunction

/-! ### Text_35_6_5 (from Chap07) -/
noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type*} [NormedField 𝕜] [PartialOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.5 states that for each base point `(u, v)`, the saddle
  subdifferential `∂K(u, v)` is a possibly empty closed convex subset of the product space.
- `core/canonical`: the chapter already owns this set as `Bifunction.subdifferentialAt`.
- `bridge/view`: the canonical carrier for this regularity statement is the strong-dual product
  `StrongDual 𝕜 U × StrongDual 𝕜 V`; the Euclidean vector-valued bridge is downstream-only and
  should not be the main theorem surface here.

Primary mathematical domain:
- convex analysis of saddle bifunctions and their canonical dual-valued subdifferentials.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Text_35_5_2`;
- `Bifunction.subdifferentialAt` and `Bifunction.mem_subdifferentialAt` from `Text_35_6_3`;
- product lemmas for `IsClosed` and `Convex` on set products.

Primitive data vs derived API:
- primitive owner data already exist upstream: the two partial strong-dual subdifferentials and
  their product owner `∂ₛ K(u, v)`;
- derived API here: the closedness and convexity regularity statement for that canonical product
  owner.

Layer target: `source-facing`.

Ambient-assumption minimization:
- the source is written on `ℝ^m × ℝ^n`, but the regularity argument only needs the normed-space
  structure required by the chapter's canonical strong-dual subdifferential owners;
- inner-product, completeness, and finite-dimensional assumptions belong only to the Euclidean
  bridge files, not to this owner-level theorem.
-/

-- Proof sketch: write the saddle subdifferential as the product of the already-owned first and
-- second partial strong-dual subdifferentials, and combine the two partial regularity hypotheses
-- with the product lemmas for closed and convex sets.
/-- Text 35.6.5: for every base point `(u, v)`, the saddle subdifferential is a possibly empty
closed convex subset of the canonical dual product `StrongDual 𝕜 U × StrongDual 𝕜 V`. -/
theorem isClosed_and_convex_subdifferentialAt
    (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (h₁_isClosed : IsClosed (∂₁K(u, v))) (h₂_isClosed : IsClosed (∂₂K(u, v)))
    (h₁_convex : Convex 𝕜 (∂₁K(u, v))) (h₂_convex : Convex 𝕜 (∂₂K(u, v))) :
    IsClosed (∂ₛ K(u, v)) ∧ Convex 𝕜 (∂ₛ K(u, v)) := by
  simpa [subdifferentialAtDual, subdifferentialAt] using
    (show
        IsClosed (∂₁K(u, v) ×ˢ ∂₂K(u, v)) ∧
          Convex 𝕜 (∂₁K(u, v) ×ˢ ∂₂K(u, v)) from
      ⟨h₁_isClosed.prod h₂_isClosed, h₁_convex.prod h₂_convex⟩)

theorem subdifferentialAt_isClosed
    (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (h₁_isClosed : IsClosed (∂₁K(u, v))) (h₂_isClosed : IsClosed (∂₂K(u, v))) :
    IsClosed (∂ₛ K(u, v)) :=
  by
    simpa [subdifferentialAtDual, subdifferentialAt] using h₁_isClosed.prod h₂_isClosed

theorem subdifferentialAt_convex
    (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (h₁_convex : Convex 𝕜 (∂₁K(u, v))) (h₂_convex : Convex 𝕜 (∂₂K(u, v))) :
    Convex 𝕜 (∂ₛ K(u, v)) :=
  by
    simpa [subdifferentialAtDual, subdifferentialAt] using h₁_convex.prod h₂_convex

end

end Bifunction

/-! ### Text_35_6_6 (from Chap07) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommGroup U] [SMul 𝕜 U]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.6 fixes a first-variable slice `K · v` and studies the
  reflected first partial directional-derivative profile `u' ↦ -K'(u, v; -u', 0)`.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.directionalDerivativeAt` for one-variable slices and `Bifunction.subdifferential1At`
  for the first partial subdifferential.
- `bridge/view`: the displayed source profile is exactly the reflected slice owner
  `u' ↦ -directionalDerivativeAt (fun u'' ↦ K u'' v) u (-u')`; the uncurried bridge
  `Function.directionalDerivativeAt_uncurry_first_eq` remains upstream and no second public owner
  is introduced here.

Domain-style sampling used here:
- `Function.IsConcave` from `Chap06.Definition_6_30_2` as the canonical whole-space owner for the
  fixed first slice `K · v`, definitionally replacing `ConcaveOn 𝕜 Set.univ`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `Function.isConvex_directionalDerivativeAt_of_finite_point` from `Chap05.Theorem_23_1`;
- `Function.directionalDerivativeAt_uncurry_first_eq` from `Chap07.Text_35_5_3`;
- `Bifunction.subdifferential1At` from `Chap07.Text_35_5_1`.

Primitive data vs derived API:
- primitive inputs: a fixed slice `K · v`, its canonical whole-space concavity owner,
  and finiteness of `K u v`;
- derived API: convexity of the reflected first-direction profile below.

Layer target: `source-facing`, stated directly on the canonical slice directional-derivative
owner.

Ambient-assumption minimization:
- the first-variable directional-derivative owner and its finite-point convexity theorem from
  Chapter 23 live on the scalar-action layer of `U`, while the reflected source direction `-u'`
  requires additive inverses on `U`;
- the second variable is a fixed parameter here, so no algebraic structure on `V` enters the
  public API.
-/

-- Proof sketch: apply the Chapter 23 convexity theorem to the convex function
-- `fun u'' ↦ -K u'' v` at the finite point `u`, then read the resulting direction profile in the
-- reflected source form `u' ↦ -K'(u, v; -u', 0)`.
/-- Text 35.6.6 (1): if the first-variable slice `K · v` is concave and `u` belongs to
its effective domain with finite value, then the reflected first partial directional-derivative
profile `u' ↦ -K'(u, v; -u', 0)`, rendered here as
`u' ↦ -directionalDerivativeAt (K · v) u (-u')`, is convex. -/
theorem isConvex_neg_directionalDerivativeAt_first
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    (hK_concave : (K · v).IsConcave 𝕜)
    (huv : u ∈ dom((K · v))) (huv_bot : K u v ≠ ⊥) :
    (fun u' : U ↦ -directionalDerivativeAt (K · v) u (-u')).IsConvex 𝕜 := sorry

end

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [SMul 𝕜 U]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.6 also identifies the lower-semicontinuous hull of the same
  reflected first partial directional-derivative profile with the support function of the first
  partial subdifferential.
- `core/canonical`: the owner abstractions are the lower-semicontinuous hull `cl(·)`, the support
  function `δᵛ(· | ·)`, the slice directional derivative `Function.directionalDerivativeAt`, and
  the canonical first-partial owner `Bifunction.subdifferential1At` on the pairing-level surface
  `∂₁[Y]K(u, v)`.
- `bridge/view`: the source notation `-K'(u, v; -u', 0)` is kept on the theorem surface only
  through the reflected slice owner, while the first partial subdifferential is surfaced on the
  intrinsic pairing owner layer as `∂₁[Y]K(u, v)`.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Chap07.Text_35_5_1`;
- `Function.IsConcave` from `Chap06.Definition_6_30_2` as the canonical whole-space owner for the
  fixed first slice `K · v`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- the intrinsic dual-pairing owner `HasPairing U Y 𝕜`;
- the chapter support-function notation `δᵛ(· | ·)`;
- the chapter lower-semicontinuous-hull owner `cl(·)`.

Primitive data vs derived API:
- primitive inputs: the same fixed-slice whole-space concavity owner as in part (1), together
  with the pairing-level first partial owner `∂₁[Y]K(u, v)`;
- derived API: the lower-semicontinuous-hull/support-function identity below.

Layer target: `source-facing`.

Ambient-assumption minimization:
- this clause uses only the pairing-level first-partial owner `∂₁[Y]K(u, v)`, so it stays at the
  scalar-action/additive-group layer of `U` needed for reflected directions `-u'`;
- the second variable is again a fixed parameter, so no algebraic or topological structure on `V`
  enters the public API.
-/

-- Proof sketch: apply the Chapter 23 support-function description of the lower-semicontinuous
-- hull of directional derivatives to the convex function `fun u'' ↦ -K u'' v` at `u`, then
-- rewrite the resulting subdifferential through the first partial owner `∂₁[Y]K(u, v)`
-- and express the profile in the reflected source form.
/-- Text 35.6.6 (2): under the same concavity and finiteness hypotheses, the lower-semicontinuous
closure of the reflected first partial directional-derivative profile is the support function of
the first partial subdifferential `∂₁[Y]K(u, v)`. -/
theorem
    lowerSemicontinuousHull_neg_directionalDerivativeAt_first_eq_supportFunction_subdifferential1At
    {Y : Type*} [HasPairing U Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    (hK_concave : (K · v).IsConcave 𝕜)
    (huv : u ∈ dom((K · v))) (huv_bot : K u v ≠ ⊥) :
    cl(fun u' : U ↦ -directionalDerivativeAt (K · v) u (-u')) =
      (δᵛ(· | ∂₁[Y]K(u, v))) := sorry

end

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Strong-dual specialization of Text 35.6.6 (2): on the canonical dual bridge, the same
lower-semicontinuous-hull identity is written with plain notation `∂₁ K(u, v)`. -/
theorem
    lscHull_neg_directionalDerivativeAt_first_eq_supportFunction_subdifferential1At_dual
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    (hK_concave : (K · v).IsConcave 𝕜)
    (huv : u ∈ dom((K · v))) (huv_bot : K u v ≠ ⊥) :
    cl(fun u' : U ↦ -directionalDerivativeAt (K · v) u (-u')) =
      (δᵛ(· | ∂₁ K(u, v))) := sorry

end

end Bifunction

/-! ### Theorem_35_6 (from Chap07) -/
noncomputable section

universe u v

open Function Set

namespace Bifunction

section

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommMonoid U] [SMul 𝕜 U]
variable [TopologicalSpace V] [AddCommMonoid V] [SMul 𝕜 V]

local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) := WithBotTop.instSMul

variable {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
variable {u : U} {v : V}

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 35.6 says that at every interior point of a product domain where
  an extended-valued bifunction is concave in the first variable and convex in the second, the mixed
  directional derivative exists, is finite, is positively homogeneous and concave-convex as a
  function of the direction pair, and splits as the sum of the two partial directional
  derivatives.
- `core/canonical`: the directional-derivative owners are already
  `Function.HasDirectionalDerivativeAt` and `Function.directionalDerivativeAt`.
- `bridge/view`: the theorem is stated directly on `uncurry K`, so no separate
  mixed-direction derivative package is introduced.

Domain-style sampling used here:
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- product-topology interior on `C ×ˢ D` together with the additive/scalar-action layer on `U`, `V`
  needed to form the directional rays `u + t • u'` and `v + t • v'`;
- `Bifunction.isConvex_neg_directionalDerivativeAt_first`;
- `Bifunction.isConvex_directionalDerivativeAt_second`;
- `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point`;
- `Bifunction.IsConcaveConvex`.

Primitive data vs derived API:
- primitive source data: the bifunction `K : U → V → WithTopBot 𝕜`, the domain sets `C`, `D`,
  the slice-wise concavity/convexity hypotheses, and the interior base-point condition
  `(u, v) ∈ interior (C ×ˢ D)`, and the direction pair `(u', v')`;
- primitive owner conclusion: existence of the mixed directional derivative with the additive
  partial-derivative formula;
- derived API: the value-level equality, pointwise finiteness, positive homogeneity, and
  concave-convexity of the direction map.

Layer target: `source-facing`, expressed through the existing Chapter 23 directional-derivative
owners and the Chapter 33 concave-convex owner.

Scalar/codomain boundary:
- this file is surfaced at the same generic codomain/scalar layer already used by the Chapter 23
  directional-derivative owners:
  `K : U → V → WithTopBot 𝕜` with right-ray limits along `𝓝[>] (0 : 𝕜)`;
- no local `ℝ`-specific codomain bridge (`toWithTopBot`) remains on theorem surfaces.

Ambient-owner canonicalization:
- the theorem surface keeps the same product-interior source semantics at the minimal topological
  scalar-action layer (`[TopologicalSpace] [AddCommMonoid] [SMul 𝕜 ·]`) needed for directional-ray
  expressions and product-domain interior;
- the directional-derivative owner itself remains `Function.HasDirectionalDerivativeAt` /
  `Function.directionalDerivativeAt`, so no new mixed-direction owner is introduced;
- no norm, inner product, or finite-dimensional structure appears in the primitive data or the
  derived owner conclusions below, so those stronger assumptions are removed from the public API;
- the source's Euclidean spaces are represented here by arbitrary topological `𝕜`-scalar-action
  spaces rather
  than by a coordinate model.
-/

-- Proof sketch: localize around `(u, v)` using the interior-point hypothesis in `C ×ˢ D`,
-- decompose the mixed difference quotient into the first partial quotient plus the shifted second
-- partial quotient, and compare the second term with the second partial directional derivative via
-- convexity in the second variable. Repeating with upper/lower roles exchanged gives the matching
-- bound, hence existence and the additive formula.
/-- Theorem 35.6: at every interior point `(u, v)` of a product domain on which `K` is
concave in the first variable and convex in the second, the mixed directional derivative of
`uncurry K` exists and is the sum of the two intrinsic slice-directional derivatives
`(K · v)'(u; u')` and `(K u)'(v; v')`, rendered by the chapter owner
`Function.directionalDerivativeAt`. -/
theorem hasDirectionalDerivativeAt_uncurry_eq_add_partial
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    HasDirectionalDerivativeAt (uncurry K) (u, v) (u', v')
      (directionalDerivativeAt (K · v) u u' +
        directionalDerivativeAt (K u) v v') := sorry

-- Proof sketch: evaluate the canonical limit-valued owner `directionalDerivativeAt` at the limit
-- supplied by `hasDirectionalDerivativeAt_uncurry_eq_add_partial`.
/-- The mixed directional derivative at an interior saddle point equals the sum of the two
partial directional derivatives. -/
theorem directionalDerivativeAt_uncurry_eq_add_partial
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry K) (u, v) (u', v') =
      directionalDerivativeAt (K · v) u u' +
        directionalDerivativeAt (K u) v v' := sorry

-- Proof sketch: combine the additive formula with the one-variable Chapter 23 finiteness results
-- for the concave first-variable slice derivative `directionalDerivativeAt (K · v) u` and convex
-- second-variable slice derivative `directionalDerivativeAt (K u) v`; each partial directional
-- derivative is finite, hence so is their sum.
/-- At an interior saddle point, the mixed directional derivative is finite in every direction. -/
theorem directionalDerivativeAt_uncurry_ne_bot_ne_top
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    (u' : U) (v' : V) :
    directionalDerivativeAt (uncurry K) (u, v) (u', v') ≠ ⊥ ∧
      directionalDerivativeAt (uncurry K) (u, v) (u', v') ≠ ⊤ := sorry

-- Proof sketch: use the additive formula together with positive homogeneity of the two intrinsic
-- slice directional-derivative maps `directionalDerivativeAt (K · v) u` and
-- `directionalDerivativeAt (K u) v` from the one-variable Chapter 23 theory, then rewrite the
-- common scalar action on `(u', v')` as simultaneous scaling of the two summands.
/-- At an interior saddle point, the mixed directional-derivative map is positively homogeneous in
the direction pair. -/
theorem positivelyHomogeneous_directionalDerivativeAt_uncurry
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    :
    (directionalDerivativeAt (uncurry K) (u, v)).PositivelyHomogeneous 𝕜 := sorry

-- Proof sketch: for fixed `v'`, the additive formula reduces the first-variable slice of the
-- mixed-direction map to the intrinsic first slice derivative
-- `u' ↦ directionalDerivativeAt (K · v) u u'` plus a constant, so it is concave by the
-- one-variable concave analogue of Chapter 23. For fixed `u'`, the second-variable slice
-- similarly reduces to `v' ↦ directionalDerivativeAt (K u) v v'` plus a constant, hence is convex
-- by Theorem 23.1. These two slice statements are exactly the Chapter 33 whole-space
-- concave-convex owner.
/-- At an interior saddle point, the mixed directional-derivative map is concave-convex in the
direction variables. -/
theorem isConcaveConvex_directionalDerivativeAt_uncurry
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (huv : (u, v) ∈ interior (C ×ˢ D))
    :
    IsConcaveConvex 𝕜
      (fun u' v' ↦ directionalDerivativeAt (uncurry K) (u, v) (u', v')) := sorry

end

end Bifunction

/-! ### Text_35_6_7 (from Chap07) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommMonoid V] [SMul 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.7 fixes a second-variable slice `K u`, a finite point `v`, and the
  second partial directional-derivative profile `v' ↦ K'(u, v; 0, v')`.
- `core/canonical`: the owner abstractions are the convex slice predicate `(K u).IsConvex 𝕜` and
  the Chapter 23 directional-derivative owner `Function.directionalDerivativeAt`.
- `bridge/view`: the source notation `K'(u, v; 0, v')` is rendered directly by the slice owner
  `directionalDerivativeAt (K u) v`.

Domain-style sampling used here:
- `Function.IsConvex 𝕜` from `Chap01/Theorem_4_2`;
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Function.isConvex_directionalDerivativeAt_of_finite_point` from `Chap05/Theorem_23_1`.

Primitive data vs derived API:
- primitive inputs: the slice `K u`, the fixed point `v`, convexity of that slice, and finiteness
  of `K u v`;
- derived API: convexity of the second partial directional-derivative profile.

Layer target: `source-facing`, stated directly on the canonical chapter owners.

Ambient-assumption minimization:
- the first variable is only a parameter indexing the slice `K u`, so no algebraic structure on
  `U` belongs in the public API;
- the second variable here needs the scalar-action layer used by the Chapter 23 finite-point
  convexity theorem for directional derivatives.
-/

-- Proof sketch: fix `u` and set `f := K u`. The convex-slice hypothesis applies directly to `f`.
-- The source profile `v' ↦ K'(u, v; 0, v')` is the Chapter 23 directional
-- derivative `v' ↦ directionalDerivativeAt f v v'`, and directional derivatives of a convex slice
-- at a finite point are convex in the direction variable.
/-- Text 35.6.7 (1): if the second-variable slice `K u` is convex and `K u v` is finite, then the
second partial directional-derivative profile `v' ↦ K'(u, v; 0, v')`, rendered here by the slice
owner `directionalDerivativeAt (K u) v`, is a convex function on the second variable space. -/
theorem isConvex_directionalDerivativeAt_second
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    {v : V} (hv : v ∈ dom(K u)) (hv_bot : K u v ≠ ⊥) :
    (directionalDerivativeAt (K u) v).IsConvex 𝕜 := by
  simpa using
    Function.isConvex_directionalDerivativeAt_of_finite_point hKu_convex hv hv_bot

end

section

variable {𝕜 : Type w}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.7 also identifies the lower-semicontinuous hull of the same second
  partial directional-derivative profile with the support function of the second partial
  subdifferential.
- `core/canonical`: the owner abstractions are the convex slice predicate `(K u).IsConvex 𝕜`,
  the lower-semicontinuous hull `cl(·)`, the support function `δᵛ(· | ·)`, and the chapter
  bifunction owner `Bifunction.subdifferential2At`.
- `bridge/view`: the source-facing `∂₂ K(u, v)` is the thin chapter bridge to the upstream slice
  owner `_root_.subdifferentialAt (K u) v` on the canonical dual `StrongDual 𝕜 V`.

Domain-style sampling used here:
- `Function.IsConvex 𝕜` from `Chap01/Theorem_4_2`;
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Bifunction.subdifferential2At` from `Chap07/Text_35_5_2`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`, as the upstream owner reused by
  `subdifferential2At`;
- chapter owners `cl(·)` and `δᵛ(· | ·)`.

Primitive data vs derived API:
- primitive inputs: the slice `K u`, convexity/properness of that slice, and a base point in the
  intrinsic relative interior `v ∈ riDom[𝕜](K u)`;
- derived API: the lower-semicontinuous-hull/support-function identity for the second partial
  directional-derivative profile.

Layer target: `source-facing`, with the second partial subdifferential surfaced through the
chapter's canonical bifunction owner `∂₂ K(u, v)`.

Ambient-assumption minimization:
- the first variable again only indexes the slice `K u`, so no algebraic structure on `U` enters
  this theorem surface;
- this clause is rebased to the existing Chapter 23 `riDom` owner theorem for support-function
  representation, so its order-topology and properness hypotheses are retained explicitly.
-/

-- Proof sketch: set `f := K u`. The Chapter 23 `riDom` theorem gives
-- `directionalDerivativeAt f v = δᵛ(· | ∂ f at v)` and `IsClosedProperConvex` for the same
-- directional-derivative profile. Closedness yields `cl(directionalDerivativeAt f v) =
-- directionalDerivativeAt f v`, and the chapter bridge `∂₂ K(u, v)` identifies the slice
-- subdifferential term on the source-facing theorem surface.
/-- Text 35.6.7, support-owner bridge: for a convex proper second-variable slice `K u` and
`v ∈ riDom[𝕜](K u)`, the second partial directional-derivative profile is exactly the support
function of the second partial subdifferential. -/
theorem directionalDerivativeAt_second_eq_supportFunction_subdifferential2At_of_mem_riDom
    {Y : Type*} [HasPairing V Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    directionalDerivativeAt (K u) v =
      (δᵛ(· | ∂₂[Y]K(u, v)) : V → WithTopBot 𝕜) := by
  have hdirRoot :
      directionalDerivativeAt (K u) v =
        (δᵛ(· | _root_.subdifferentialAt (Y := Y) (K u) v) : V → WithTopBot 𝕜) :=
    _root_.directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom
      (f := K u) (x := v) (Y := Y) hKu_convex hKu_proper hv
  simpa [Bifunction.subdifferential2At_eq_subdifferentialAt] using hdirRoot

/-- Text 35.6.7 (2): if the second-variable slice `K u` is convex proper and
`v ∈ riDom[𝕜](K u)`, then the lower-semicontinuous hull of the second partial directional
derivative profile equals the support function of the second partial subdifferential
`∂₂[Y] K(u, v)`. -/
theorem lowerSemicontinuousHull_directionalDerivativeAt_second_eq_supportFunction_subdifferential2At
    {Y : Type*} [HasPairing V Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    cl(directionalDerivativeAt (K u) v) =
      (δᵛ(· | ∂₂[Y]K(u, v))) := by
  have hclosed :
      Function.IsClosedProperConvex (𝕜 := 𝕜) (directionalDerivativeAt (K u) v) :=
    _root_.isClosedProperConvex_directionalDerivativeAt_of_mem_riDom
      (f := K u) (x := v) hKu_convex hKu_proper hv
  have hdir :
      directionalDerivativeAt (K u) v =
        (δᵛ(· | ∂₂[Y]K(u, v)) : V → WithTopBot 𝕜) :=
    directionalDerivativeAt_second_eq_supportFunction_subdifferential2At_of_mem_riDom
      (Y := Y) hKu_convex hKu_proper hv
  calc
    cl(directionalDerivativeAt (K u) v) = directionalDerivativeAt (K u) v := by
      simpa using
        lowerSemicontinuousHull_eq_self (f := directionalDerivativeAt (K u) v) hclosed.closed
    _ = (δᵛ(· | ∂₂[Y]K(u, v)) : V → WithTopBot 𝕜) := hdir

/-- Strong-dual specialization of Text 35.6.7 support-owner bridge: with the canonical dual
surface `∂₂ K(u, v)`, the second partial directional-derivative profile equals the
support function of the second partial subdifferential. -/
theorem directionalDerivativeAt_second_eq_supportFunction_subdifferential2AtDual_of_mem_riDom
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    directionalDerivativeAt (K u) v =
      (δᵛ(· | ∂₂ K(u, v)) : V → WithTopBot 𝕜) := by
  simpa using
    directionalDerivativeAt_second_eq_supportFunction_subdifferential2At_of_mem_riDom
      (Y := StrongDual 𝕜 V) hKu_convex hKu_proper hv

/-- Strong-dual specialization of Text 35.6.7 (2): with the canonical dual surface
`∂₂ K(u, v)`, the lower-semicontinuous hull of the second partial directional
derivative profile equals the support function of the second partial subdifferential. -/
theorem
    lowerSemicontinuousHull_directionalDerivativeAt_second_eq_supportFunction_subdifferential2AtDual
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    cl(directionalDerivativeAt (K u) v) =
      (δᵛ(· | ∂₂ K(u, v))) := by
  simpa using
    lowerSemicontinuousHull_directionalDerivativeAt_second_eq_supportFunction_subdifferential2At
      (Y := StrongDual 𝕜 V) hKu_convex hKu_proper hv

end

end Bifunction

/-! ### Text_35_6_8 (from Chap07) -/
universe u v

namespace SaddleFunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace U] [LT α] [Top α]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.8 concludes that an interior point of `dom K` yields interior
  membership in the effective domains of the first- and second-variable slices.
- `core/canonical`: the owner abstractions already exist upstream as `SaddleFunction.dom₂ K` and
  the one-variable slice-domain owner `dom(·)`, together with the primitive slice-domain bridges
  `dom_firstSlice_eq_univ` and `dom₂_subset_dom_secondSlice`.
- `bridge/view`: the first-slice clause first factors through the primitive owner fact
  `v ∈ dom₂ K`, because `dom_firstSlice_eq_univ` already upgrades that to full slice domain; a
  source-facing bridge then reuses this at `v ∈ interior (dom₂ K)`. The second-slice clause is
  the genuine interior bridge from `v ∈ interior (dom₂ K)`.

Domain-style sampling used here:
- `SaddleFunction.dom₂` and the slice-domain bridges
  `dom_firstSlice_eq_univ` / `dom₂_subset_dom_secondSlice` from `Chap07.Defn_34_3`;
- `SaddleFunction.mem_interior_dom` from `Chap07.Text_35_5_5`;
- `dom(·)` from `Chap01.Definition_4_4`;
- `interior_mono` from mathlib.

Primitive data vs derived API:
- primitive owner data already exist upstream: `dom₂ K` and the slice-domain bridges
  `dom_firstSlice_eq_univ` and `dom₂_subset_dom_secondSlice`;
- derived API here: the first-slice interior conclusion both from `v ∈ dom₂ K` and from
  `v ∈ interior (dom₂ K)`, and the second-slice interior conclusion from
  `v ∈ interior (dom₂ K)`.

Codomain owner level:
- the slice-domain owners above are already stated for a generic codomain carrying only `⊤` and
  `<`, so this file should stay on that same owner layer rather than specialize to
  `WithBotTop α`.

Layer target: `bridge/view`.

Redundant-source-assumption elimination:
- the textbook hypothesis `(u, v) ∈ interior (dom K)` is not kept in the main declarations,
  because `mem_interior_dom` isolates the second-coordinate owner information;
- the first-slice owner theorem does not keep the stronger interior hypothesis on `dom₂ K`,
  because `dom_firstSlice_eq_univ` already yields the full slice domain from plain
  `v ∈ dom₂ K`; a separate source-facing bridge recovers the interior-hypothesis form;
- the second-slice clause keeps the interior hypothesis `v ∈ interior (dom₂ K)`.
-/

/-- Text 35.6.8, owner form: if `v` lies in the second-coordinate domain of `K`, then every
first-variable slice `K(·, v)` has full effective domain, so any `u` lies in its
interior domain. -/
theorem interior_dom_firstSlice_eq_univ_of_mem_dom₂
    (K : U → X → α) {v : X} (hv : v ∈ dom₂ K) :
    interior (dom(K(·, v))) = Set.univ := by
  simp [dom_firstSlice_eq_univ K hv]

/-- Text 35.6.8, pointwise bridge: if `v` lies in the second-coordinate domain of `K`, then every
first-variable slice `K(·, v)` has full interior domain. -/
theorem mem_interior_dom_firstSlice_of_mem_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ dom₂ K) :
    u ∈ interior (dom(K(·, v))) := by
  simp [interior_dom_firstSlice_eq_univ_of_mem_dom₂ K hv]

end

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace U] [TopologicalSpace X] [LT α] [Top α]

/-- Text 35.6.8, source-facing bridge for the first slice: interior membership in `dom₂ K`
implies interior membership in the effective domain of every first-variable slice. -/
theorem mem_interior_dom_firstSlice_of_mem_interior_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ interior (dom₂ K)) :
    u ∈ interior (dom(K(·, v))) :=
  mem_interior_dom_firstSlice_of_mem_dom₂ (interior_subset hv)

end

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace X] [LT α] [Top α]

/-- Text 35.6.8, owner form: for each fixed `u`, the interior of the second-coordinate domain
`dom₂ K` is contained in the interior of the effective domain of the second-variable slice `K u`. -/
theorem interior_dom₂_subset_interior_dom_secondSlice
    (K : U → X → α) (u : U) :
    interior (dom₂ K) ⊆ interior (dom(K u)) :=
  interior_mono (dom₂_subset_dom_secondSlice (K := K) (u := u))

/-- Text 35.6.8, pointwise bridge: interior points of `dom₂ K` remain interior points in the
effective domain of each second-variable slice `K u`. -/
theorem mem_interior_dom_secondSlice_of_mem_interior_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ interior (dom₂ K)) :
    v ∈ interior (dom(K u)) :=
  interior_dom₂_subset_interior_dom_secondSlice K u hv

end

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {X : Type v} {EV : Type*} {α : Type*}
variable [TopologicalSpace X]
variable [AddCommGroup EV] [Module 𝕜 EV] [AddTorsor EV X]
variable [LT α] [Top α]

/-- Intrinsic bridge for Text 35.6.8 on the textbook owner surface `riDom`: interior points of
`dom₂ K` lie in the intrinsic interior domain of each second-variable slice `K u`. -/
theorem interior_dom₂_subset_riDom_secondSlice
    (K : U → X → α) (u : U) :
    interior (dom₂ K) ⊆ riDom[𝕜](K u) := by
  intro v hv
  exact interior_subset_intrinsicInterior
    (interior_dom₂_subset_interior_dom_secondSlice K u hv)

/-- Pointwise intrinsic bridge for Text 35.6.8. -/
theorem mem_riDom_secondSlice_of_mem_interior_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ interior (dom₂ K)) :
    v ∈ riDom[𝕜](K u) :=
  interior_dom₂_subset_riDom_secondSlice K u hv

end

end SaddleFunction

/-! ### Text_35_6_9 (from Chap07) -/
noncomputable section

universe u v

open Set
open SaddleFunction
open scoped Rockafellar

namespace Bifunction

section FirstPartial

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

variable {K : U → V → WithTopBot ℝ} {u : U} {v : V}

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.9 states that at an interior point of the effective domain of a
  saddle-function, the two partial subdifferentials are nonempty, closed, bounded, and convex.
- `core/canonical`: the chapter owner declarations are `Bifunction.subdifferential1At`,
  `Bifunction.subdifferential2At`, the Chapter 34 domain owner `dom K`, and the slice-domain
  interior bridges from `Text_35_6_8`.
- `bridge/view`: this section states the first-partial conclusions directly on the intrinsic
  first-partial owner with the canonical strong-dual notation `∂₁ K(u, v)`.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `SaddleFunction.mem_interior_dom_firstSlice_of_mem_interior_dom₂` and
  `SaddleFunction.mem_interior_dom_secondSlice_of_mem_interior_dom₂` from
  `Text_35_6_8`;
- `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom` and the finite convex
  subdifferential regularity statements of `Corollary_23_4_1`, which are the one-variable owners
  behind the two partial conclusions.

Primitive data vs derived API:

- primitive owner data: first-slice concavity of `fun u' ↦ K u' v` and coordinate-domain
  memberships `u ∈ dom₁ K`, `v ∈ dom₂ K`;
- derived API: the first-partial regularity properties at `(u, v)`.
- source-facing bridge: the same conclusion under the textbook hypothesis
  `(u, v) ∈ interior (dom K)`, obtained by reducing to the coordinate-domain owner layer.

Layer target: `source-facing`.

Scalar/codomain boundary:
- this item remains on the real branch because the upstream finite-dimensional nonempty/bounded
  owner route reused here is currently available on `StrongDual ℝ` / `WithTopBot ℝ`; scalar
  weakening of this boundedness layer should be repaired upstream first.

Redundant-source-assumption elimination:

- the primitive owner theorem below does not keep the stronger interior-domain product hypothesis,
  because the first-partial nonempty/bounded clause only needs first-slice concavity and the
  coordinate-domain owners `u ∈ dom₁ K`, `v ∈ dom₂ K`;
- the textbook adjective “proper” is omitted from both owner and bridge theorem surfaces.
-/

-- Proof sketch: `v ∈ dom₂ K` gives the no-`⊤` side on the first slice, while `u ∈ dom₁ K`
-- gives a finite-point witness for that slice; together these supply properness of the convex
-- negated first slice. Then apply Theorem 23.4 and translate through the sign-change bridge to
-- `∂₁ K(u,v)`.
/-- Text 35.6.9 (1), owner form: if the first-variable slice `fun u' ↦ K u' v` is concave on the
whole space and `(u, v)` lies in the coordinate-domain owner layer
`u ∈ dom₁ K`, `v ∈ dom₂ K`, then the first partial subdifferential is nonempty and bounded. -/
theorem subdifferential1At_nonempty_and_bounded_of_isConcave_firstSlice_of_mem_dom₂
    (hK_concave : ConcaveOn ℝ Set.univ (fun u' ↦ K u' v))
    (hu : u ∈ dom₁ K)
    (hv : v ∈ dom₂ K) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) := sorry

variable [AddCommMonoid V] [SMul ℝ V]

/-- Concave-convex bridge for Text 35.6.9 (1) on the coordinate-domain owner
`u ∈ dom₁ K`, `v ∈ dom₂ K`. -/
theorem subdifferential1At_nonempty_and_bounded_of_mem_dom₂
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hu : u ∈ dom₁ K)
    (hv : v ∈ dom₂ K) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) := by
  rcases (SaddleFunction.isConcaveConvex_iff (𝕜 := ℝ) K).1 hK_shape with ⟨hConcave, _⟩
  exact subdifferential1At_nonempty_and_bounded_of_isConcave_firstSlice_of_mem_dom₂
    (hK_concave := hConcave v) hu hv

variable [TopologicalSpace V]

/-- Source-facing interior-`dom₂` bridge for Text 35.6.9 (1). -/
theorem subdifferential1At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hu : u ∈ dom₁ K)
    (hv : v ∈ interior (dom₂ K)) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) :=
  subdifferential1At_nonempty_and_bounded_of_mem_dom₂
    (hK_shape := hK_shape) hu (interior_subset hv)

-- Proof sketch: project `(u, v) ∈ interior (dom K)` to `v ∈ interior (dom₂ K)` using
-- `SaddleFunction.mem_interior_dom`, then apply the interior-`dom₂` bridge above.
/-- Text 35.6.9 (1), source-facing bridge: at an interior point of `dom K` of a concave-convex
saddle-function, the first partial subdifferential is nonempty and bounded. -/
theorem subdifferential1At_nonempty_and_bounded_of_mem_interior_dom
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (huv : (u, v) ∈ interior (dom K)) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) := by
  have hmem : u ∈ interior (SaddleFunction.dom₁ K) :=
    (SaddleFunction.mem_interior_dom.mp huv).1
  have hu : u ∈ dom₁ K := interior_subset hmem
  exact subdifferential1At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape := hK_shape) hu ((SaddleFunction.mem_interior_dom.mp huv).2)

end FirstPartial

/- Text 35.6.9 (2): the first partial subdifferential clause is a direct owner recall.
For every slice `fun u' ↦ K u' v`, the intrinsic owner
`_root_.concaveSubdifferentialAt (fun u' ↦ K u' v) u` is already closed and convex upstream, and
`∂₁ K(u, v)` is definitionally that owner. -/
recall _root_.concaveSubdifferentialAt_isClosed
recall _root_.concaveSubdifferentialAt_convex

section SecondPartial

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {K : U → V → WithTopBot ℝ} {u : U} {v : V}

-- Proof sketch: from `u ∈ dom₁ K`, the second slice `K u` is nowhere `⊥`. Together with
-- `v ∈ interior (dom₂ K)`, we get `v ∈ dom₂ K`, hence `K u v < ⊤` and therefore a finite point of
-- `K u`; this yields properness of the slice. Then place `v` in the interior of `dom(K u)` and
-- apply Theorem 23.4 to the convex proper second slice `K u`.
/-- Text 35.6.9 (3), owner form: if the second-variable slice `K u` is convex on the whole space
and `(u, v)` lies in the coordinate-domain owner layer
`u ∈ dom₁ K`, `v ∈ interior (dom₂ K)`, then the second partial subdifferential is nonempty and
bounded. -/
theorem subdifferential2At_nonempty_and_bounded_of_isConvex_secondSlice_of_mem_interior_dom₂
    (hKu_convex : ConvexOn ℝ Set.univ (K u))
    (hu : u ∈ dom₁ K)
    (hv : v ∈ interior (dom₂ K)) :
    (∂₂ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₂ K(u, v)) := sorry

variable [AddCommMonoid U] [SMul ℝ U]

/-- Concave-convex bridge for Text 35.6.9 (3) on the coordinate-domain owner
`u ∈ dom₁ K`, `v ∈ interior (dom₂ K)`. -/
theorem subdifferential2At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hu : u ∈ dom₁ K)
    (hv : v ∈ interior (dom₂ K)) :
    (∂₂ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₂ K(u, v)) := by
  rcases (SaddleFunction.isConcaveConvex_iff (𝕜 := ℝ) K).1 hK_shape with ⟨_, hConvex⟩
  exact subdifferential2At_nonempty_and_bounded_of_isConvex_secondSlice_of_mem_interior_dom₂
    (hKu_convex := hConvex u) hu hv

variable [TopologicalSpace U]

-- Proof sketch: project `(u, v) ∈ interior (dom K)` to `v ∈ interior (dom₂ K)` using
-- `SaddleFunction.mem_interior_dom`, then apply the interior-`dom₂` bridge above.
/-- Text 35.6.9 (3), source-facing bridge: at an interior point of `dom K` of a concave-convex
saddle-function, the second partial subdifferential is nonempty and bounded. -/
theorem subdifferential2At_nonempty_and_bounded_of_mem_interior_dom
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (huv : (u, v) ∈ interior (dom K)) :
    (∂₂ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₂ K(u, v)) := by
  have hmem : u ∈ interior (SaddleFunction.dom₁ K) :=
    (SaddleFunction.mem_interior_dom.mp huv).1
  have hu : u ∈ dom₁ K := interior_subset hmem
  exact subdifferential2At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape := hK_shape) hu ((SaddleFunction.mem_interior_dom.mp huv).2)

end SecondPartial

end Bifunction

/-! ### Text_35_6_10 (from Chap07) -/
noncomputable section

universe u v

open Function
open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommGroup U] [SMul 𝕜 U]
variable {Y : Type*} [HasPairing U Y 𝕜]

variable {K : U → V → WithTopBot 𝕜} {u : U} {v : V}

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.10 identifies the first partial directional derivative with the
  infimum of pairings against the first partial subdifferential of the first-variable slice.
- `core/canonical`: the primary owner layer is the first-variable slice
  `Function.directionalDerivativeAt (fun u'' ↦ K u'' v) u u'`, together with the Chapter 35
  first-partial owner `Bifunction.subdifferential1At`, used here on the pairing-level surface
  `∂₁[Y]K(u, v)`.
- `bridge/view`: the uncurried source notation `K'(u, v; u', 0)` is retained below through
  `Function.directionalDerivativeAt_uncurry_first_eq`.

Primary mathematical domain:
- convex analysis of first-slice concavity and first partial subdifferentials.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` and
  `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom` from
  Chapter 23;
- `Function.IsConcave` from `Chap06.Definition_6_30_2`, which is the chapter's canonical
  whole-space owner for the fixed first slice `fun u'' ↦ K u'' v`;
- `Bifunction.subdifferential1At` and the notation `∂₁[...]K(u, v)` from `Chap07.Text_35_5_1`;
- `Function.directionalDerivativeAt_uncurry_first_eq` from `Chap07.Text_35_5_3`;
- `neg_supportFunction_neg_eq_sInf_image_pairing` from `Chap03.Text_13_0_2`, which rewrites the
  Chapter 23 support-function identity into the textbook infimum formula.

Primitive data vs derived API:
- primitive source data: whole-space concavity of the fixed first-variable slice
  `(fun u'' ↦ K u'' v).IsConcave 𝕜`, a finite first-slice base point encoded by
  `u ∈ dom(fun u'' ↦ -K u'' v)` together with `K u v ≠ ⊤`, first-partial
  subdifferential nonemptiness, and a first-direction vector `u'`;
- primitive owner data already exist upstream as `Function.directionalDerivativeAt` and the
  first-partial owner `Bifunction.subdifferential1At` on the pairing-level surface
  `∂₁[Y]K(u, v)`;
- derived API here: the first-direction infimum formula on that owner notation, together with the
  uncurried-direction bridge corollary.

Layer target: `source-facing` on the intrinsic pairing-level owner.

Demotion note:
- Inner-product vector bridges (`subdifferential1AtVec`) are intentionally not surfaced in this
  source item; they belong to downstream bridge files.
-/

-- Proof sketch: transport first-partial nonemptiness through the Chapter 6 sign bridge to a
-- nonempty Chapter 23 subdifferential of the convex negated slice `fun u'' ↦ -K u'' v`. The
-- finite-point hypotheses `u ∈ dom(fun u'' ↦ -K u'' v)` and `K u v ≠ ⊤` give both side
-- finiteness conditions for `-K(·, v)` at `u`, which are needed to recover properness from that
-- nonempty subdifferential. Apply the one-variable
-- support-function formula to `-K(·, v)`, then rewrite the resulting support term by the Chapter
-- 13 pairing/infimum bridge and the first-partial owner `∂₁[Y]K(u, v)`.
/-- Text 35.6.10, owner form: if the first-variable slice `u'' ↦ K u'' v` is concave on the whole
space, `u` is a finite point of the negated slice `-K(·, v)` in the sense that
`u ∈ dom(fun u'' ↦ -K u'' v)` and `K u v ≠ ⊤`, and the first partial
subdifferential `∂₁[Y]K(u, v)` is nonempty, then the first directional derivative
equals the infimum of pairings against that first partial subdifferential. -/
theorem directionalDerivativeAt_firstSlice_eq_iInf_subdifferential1At
    (hK_concave : (K · v).IsConcave 𝕜)
    (hu : u ∈ dom(fun u'' ↦ -K u'' v))
    (hu_top : K u v ≠ ⊤)
    (hsub : (∂₁[Y]K(u, v)).Nonempty)
    (u' : U) :
    directionalDerivativeAt (K · v) u u' =
      ⨅ uStar : ∂₁[Y]K(u, v),
        ((⟪u', (uStar : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) := sorry

section

variable [AddCommMonoid V] [SMulZeroClass 𝕜 V]

-- Proof sketch: rewrite the source notation `K'(u, v; u', 0)` as the directional derivative of
-- the first slice by `Function.directionalDerivativeAt_uncurry_first_eq`, then apply the
-- canonical first-slice theorem above.
/-- Text 35.6.10, uncurried source-facing form: under the same whole-space first-slice concavity,
the finite-point hypotheses `u ∈ dom(fun u'' ↦ -K u'' v)` and `K u v ≠ ⊤`, and the
first-partial-subdifferential hypothesis, the first partial directional derivative
`K'(u, v; u', 0)` equals the infimum of pairings over `∂₁[Y]K(u, v)`. -/
theorem directionalDerivativeAt_uncurry_first_eq_iInf_subdifferential1At
    (hK_concave : (K · v).IsConcave 𝕜)
    (hu : u ∈ dom(fun u'' ↦ -K u'' v))
    (hu_top : K u v ≠ ⊤)
    (hsub : (∂₁[Y]K(u, v)).Nonempty)
    (u' : U) :
    directionalDerivativeAt (uncurry K) (u, v) (u', 0) =
      ⨅ uStar : ∂₁[Y]K(u, v),
        ((⟪u', (uStar : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
  rw [directionalDerivativeAt_uncurry_first_eq K u v u']
  exact directionalDerivativeAt_firstSlice_eq_iInf_subdifferential1At
    hK_concave hu hu_top hsub u'

end

end

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable {Y : Type*} [HasPairing U Y 𝕜]

variable {K : U → V → WithTopBot 𝕜} {u : U} {v : V}

-- Proof sketch: apply Theorem 23.4 directly to the proper convex negated slice `-K(·, v)` at the
-- `riDom` base point `u`; the additional guard `K u v ≠ ⊤` keeps the base value of `-K(·, v)`
-- away from `⊥`, so the slice is finite there. Then rewrite the support term through the
-- sign-change bridge and Chapter 13 pairing/infimum formula exactly as in the intrinsic owner
-- theorem above.
/-- `riDom` companion to Text 35.6.10 at the pairing owner layer: the Chapter 23
relative-interior qualification on `-K(·, v)`, together with the lower-side finiteness guard
`K u v ≠ ⊤`, yields the same first-slice infimum formula over `∂₁[Y]K(u, v)`. -/
theorem directionalDerivativeAt_firstSlice_eq_iInf_subdifferential1At_of_mem_riDom_neg
    (hK_concave : (K · v).IsConcave 𝕜)
    (hu : u ∈ riDom[𝕜](fun u'' ↦ -K u'' v))
    (hu_top : K u v ≠ ⊤)
    (u' : U) :
    directionalDerivativeAt (K · v) u u' =
      ⨅ uStar : ∂₁[Y]K(u, v),
        ((⟪u', (uStar : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) := sorry

end

end Bifunction

/-! ### Text_35_6_11 (from Chap07) -/
noncomputable section

open Function
open scoped Rockafellar Topology

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [T2Space (WithTopBot 𝕜)]
variable [SupSet (WithTopBot 𝕜)]
variable [Filter.NeBot (𝓝[>] (0 : 𝕜))]
variable {U : Type u} {V : Type v}
variable [AddCommMonoid U] [SMulZeroClass 𝕜 U]
variable [AddCommGroup V] [Module 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.11 identifies the second partial directional derivative
  `K'(u, v; 0, v')` with the support function of the second partial subdifferential
  `∂₂ K(u, v)`.
- `core/canonical`: the owner formula already lives upstream as the one-variable Chapter 23
  theorem for the second slice `K u`, namely
  `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt`.
- `bridge/view`: this file contributes only the uncurried partial-derivative bridge via
  `Function.directionalDerivativeAt_uncurry_second_eq` and the chapter bridge
  `Bifunction.subdifferential2At`.

Primary mathematical domain:
- convex analysis of concave-convex saddle bifunctions and their second partial subdifferentials.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `Function.directionalDerivativeAt_uncurry_second_eq` from `Chap07.Text_35_5_3` as the slice
  bridge behind the displayed source notation;
- `Bifunction.subdifferential2At` from `Chap07.Text_35_5_2`;
- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from
  `Chap05.Lemma_23_0_1`, whose slice specialization is the intended proof route.

Primitive data vs derived API:
- primitive inputs for the owner theorem: convexity of the second-variable slice `K u`, a finite
  point `v`, nonemptiness of `subdifferential2At K u v`, and a second-variable direction `v'`;
- derived API here: only the source-facing uncurried-partial formula for the same fixed second
  slice.

Layer target:
- `bridge/view`.

Finite-value convention:
- the project encodes scalar finiteness of `K(u, v)` as `v ∈ dom(K u)` together with
  `K u v ≠ ⊥`, i.e. the value
  is neither `⊤` nor `⊥`.
-/

-- Proof sketch: fix `u` and apply the Chapter 23 support-function formula to the convex
-- second-variable slice `f := K u` at the finite point `v`. The second partial subdifferential
-- `∂₂[Y] K(u, v)` is exactly the Chapter 23 subdifferential of that slice, and the
-- source notation `K'(u, v; 0, v')` is the directional derivative of `uncurry K` in direction
-- `(0, v')`, which matches the slice derivative by the existing Chapter 35 bridge.
/-- Text 35.6.11, source-facing bridge form: for a fixed second slice `K u`, once that slice is
convex and its second partial subdifferential at `(u, v)` is known to be nonempty, the second
partial directional derivative `K'(u, v; 0, v')` is the support function of `∂₂ K(u, v)`. -/
theorem directionalDerivativeAt_uncurry_second_eq_supportFunction_subdifferential2At
    {Y : Type (max v w)} [HasPairing V Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    {v : V} (hv : v ∈ dom(K u)) (hv_bot : K u v ≠ ⊥)
    (hsub : (∂₂[Y]K(u, v)).Nonempty)
    (v' : V) :
    directionalDerivativeAt (uncurry K) (u, v) (0, v') =
      δᵛ(v' | ∂₂[Y]K(u, v)) := by
  rw [Function.directionalDerivativeAt_uncurry_second_eq K u v v']
  simpa using
    (Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt
      (f := K u) (x := v) hKu_convex hv hv_bot hsub v')

end

end Bifunction
