import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_35_5_1 (from Chap07) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.1 introduces the first partial subdifferential of a bifunction,
  namely the concave subgradients of the first-variable slice `fun u' ↦ K u' v` at `u`.
- `core/canonical`: the owner abstraction already present upstream is
  `_root_.concaveSubdifferentialAt`, together with its pointwise characterization
  `_root_.mem_concaveSubdifferentialAt`.
- `bridge/view`: this file's chapter owner is exactly that canonical owner specialized to a fixed
  second-variable slice.

Domain-style sampling used here:
- `_root_.concaveSubdifferentialAt` from `Chap06.Definition_6_30_5`;
- `_root_.mem_concaveSubdifferentialAt` from the same file.

Primitive data vs derived API:
- primitive owner data: the canonical dual-valued slice owner
  `_root_.concaveSubdifferentialAt (fun u' ↦ K u' v) u`;
- derived API: the chapter bridge owner `subdifferential1At` and its pointwise membership
  theorem.

Layer target: `bridge/view` on the intrinsic dual-pairing owner. The vector-valued first partial
subdifferential is intentionally demoted to a downstream inner-product bridge module.

Notation evaluation:
- the first partial owner recurs throughout Chapter 35, so this file keeps the explicit-codomain
  bridge form `∂₁[Y]K(u, v)` for the pairing-level view and keeps the plain surface
  `∂₁ K(u, v)` as notation-level specialization to the strong-dual carrier.
-/

/-- Text 35.5.1: the first partial subdifferential of a bifunction `K` at `(u, v)` is the
concave subdifferential of the first-variable slice `fun u' ↦ K u' v` at `u`, on the canonical
pairing owner layer. -/
abbrev subdifferential1At (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (Y : Type*) [HasPairing U Y 𝕜] : Set Y :=
  (∂⁺[Y] (fun u' ↦ K u' v)(u))

scoped[Rockafellar] notation "∂₁[" Y "]" K "(" u ", " v ")" =>
  Bifunction.subdifferential1At K u v Y

/-- Pairing-level membership form of the first partial subdifferential. -/
@[simp] theorem mem_subdifferential1At_pairing
    {K : U → V → WithTopBot 𝕜} {u : U} {Y : Type*} [HasPairing U Y 𝕜] {uStar : Y} {v : V} :
    uStar ∈ (∂₁[Y]K(u, v)) ↔
      ∀ u', K u' v ≤ K u v + ((⟪u' - u, uStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  by
    simpa only [Bifunction.subdifferential1At] using
      (_root_.mem_concaveSubdifferentialAt_pairing
        (g := fun u' ↦ K u' v) (x := u) (xStar := uStar) (Y := Y))

end

section

variable {𝕜 : Type*} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/- Canonical strong-dual bridge for Text 35.5.1. The plain notation `∂₁ K(u, v)` uses this
strong-dual carrier, while `∂₁[Y]K(u, v)` remains the explicit pairing-level view. -/

/-- Canonical strong-dual bridge for Text 35.5.1. -/
abbrev subdifferential1AtDual (K : U → V → WithTopBot 𝕜) (u : U) (v : V) :
    Set (StrongDual 𝕜 U) :=
  subdifferential1At K u v (StrongDual 𝕜 U)

scoped[Rockafellar] notation "∂₁" K "(" u ", " v ")" =>
  Bifunction.subdifferential1AtDual K u v

/-- A continuous functional belongs to the first partial subdifferential of `K` at `(u, v)`
exactly when it gives the source affine-support inequality for the first-variable slice. -/
@[simp] theorem mem_subdifferential1At
    {K : U → V → WithTopBot 𝕜} {u : U} {uStar : StrongDual 𝕜 U} {v : V} :
    uStar ∈ (∂₁ K(u, v)) ↔
      ∀ u', K u' v ≤ K u v + ((uStar (u' - u) : 𝕜) : WithTopBot 𝕜) := by
  simpa only [Bifunction.subdifferential1AtDual, Bifunction.subdifferential1At] using
    (_root_.mem_concaveSubdifferentialAt
      (g := fun u' ↦ K u' v) (x := u) (xStar := uStar))

end

end Bifunction

/-! ### Text_35_5_1_InnerProductBridge (from Chap07) -/
noncomputable section

universe u v

open scoped RealInnerProductSpace Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*} [RCLike 𝕜] [Preorder 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [InnerProductSpace 𝕜 U]

/-- Downstream inner-product Fréchet-Riesz bridge for Text 35.5.1:
vector-valued first partial subdifferential. -/
abbrev subdifferential1AtVec (K : U → V → WithBotTop 𝕜) (u : U) (v : V) : Set U :=
  Function.concaveSubdifferentialAt (fun u' ↦ K u' v) u

/-- Pointwise inner-product characterization of the vector-valued first partial subdifferential. -/
@[simp] theorem mem_subdifferential1AtVec
    {K : U → V → WithBotTop 𝕜} {u uStar : U} {v : V} :
    uStar ∈ subdifferential1AtVec K u v ↔
      ∀ u', K u' v ≤ K u v + ((inner 𝕜 uStar (u' - u) : 𝕜) : WithBotTop 𝕜) := by
  change uStar ∈ Function.concaveSubdifferentialAt (fun u' ↦ K u' v) u ↔
      ∀ u', K u' v ≤ K u v + ((inner 𝕜 uStar (u' - u) : 𝕜) : WithBotTop 𝕜)
  exact Function.mem_concaveSubdifferentialAt

end

section

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Euclidean downstream bridge: the pairing-valued first partial subdifferential over the ambient
space itself agrees with the vector-valued Fréchet-Riesz bridge `subdifferential1AtVec`. -/
theorem subdifferential1At_eq_subdifferential1AtVec
    (K : U → V → WithBotTop ℝ) (u : U) (v : V) :
    subdifferential1At K u v U = subdifferential1AtVec K u v := by
  ext uStar
  rw [mem_subdifferential1At_pairing, mem_subdifferential1AtVec]
  constructor
  · intro h u'
    have hInner :
        ((HasLinearPairing.pairingLinear u') uStar - (HasLinearPairing.pairingLinear u) uStar :
            ℝ) =
          inner ℝ uStar (u' - u) := by
      simp [HasLinearPairing.pairingLinear, innerₗ_apply_apply, inner_sub_right,
        real_inner_comm]
    simpa [hInner] using h u'
  · intro h u'
    have hInner :
        ((HasLinearPairing.pairingLinear u') uStar - (HasLinearPairing.pairingLinear u) uStar :
            ℝ) =
          inner ℝ uStar (u' - u) := by
      simp [HasLinearPairing.pairingLinear, innerₗ_apply_apply, inner_sub_right,
        real_inner_comm]
    simpa [hInner] using h u'

end

end Bifunction

/-! ### Text_35_5_2 (from Chap07) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.2 introduces the second partial subdifferential `d₂ K(u, v)`,
  i.e. the subgradients in the second variable of a bifunction.
- `core/canonical`: the owner abstraction already exists upstream as
  `_root_.subdifferentialAt`, together with its pointwise characterization
  `_root_.mem_subdifferentialAt`.
- `bridge/view`: the source notion is exactly the Chapter 23 owner applied to the second-variable
  slice `K u`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `_root_.mem_subdifferentialAt_pairing` and `_root_.mem_subdifferentialAt` from the same file.

Primitive data vs derived API:
- primitive data: a bifunction `K : U → V → WithTopBot 𝕜` and a base point `(u, v)`;
- primitive owner: the canonical one-variable owner `_root_.subdifferentialAt` on the
  second-variable slice `K u` at `v`;
- derived API: the source-facing bridge name `subdifferential2At` and its pointwise membership
  theorem.

Layer target: `bridge/view`. This file owns the chapter-level bifunction bridge, not a second
primitive subgradient object.

Scalar/codomain boundary:
- this bridge is stated directly at the primitive pairing layer (`Add` + `LE`) and keeps
  strong-dual specialization as a downstream view.

Notation evaluation:
- the second partial owner recurs throughout Chapter 35, so this file exposes the source-facing
  surface `∂₂ K(u, v)` and the explicit-codomain form `∂₂[Y]K(u, v)` instead of forcing later
  theorem surfaces to spell the raw bridge name.
-/

/-- Text 35.5.2: the second partial subdifferential of a bifunction `K` at `(u, v)` is the
subdifferential of the second-variable slice `K(u, ·)` at `v`, on the canonical pairing
owner layer. -/
abbrev subdifferential2At (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (Y : Type*) [HasPairing V Y 𝕜] : Set Y :=
  (_root_.subdifferentialAt (Y := Y) (K u) v : Set Y)

scoped[Rockafellar] notation "∂₂[" Y "]" K "(" u ", " v ")" =>
  Bifunction.subdifferential2At K u v Y

/-- Pairing-level membership form of the second partial subdifferential. -/
@[simp] theorem mem_subdifferential2At_pairing
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {Y : Type*} [HasPairing V Y 𝕜] {vStar : Y} :
    vStar ∈ ∂₂[Y]K(u, v) ↔
      ∀ v', K u v' ≥ K u v + ((⟪v' - v, vStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  by
    change vStar ∈ (_root_.subdifferentialAt (Y := Y) (K u) v) ↔
        ∀ v', K u v' ≥ K u v + ((⟪v' - v, vStar⟫ₚ : 𝕜) : WithTopBot 𝕜)
    exact _root_.mem_subdifferentialAt_pairing (f := K u) (x := v) (Y := Y) (xStar := vStar)

/-- Under the primitive owner layer, `∂₂[Y]K(u, v)` is definitionally the one-variable
subdifferential owner of the second-variable slice `K u` at `v`. -/
@[simp] theorem subdifferential2At_eq_subdifferentialAt
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {Y : Type*} [HasPairing V Y 𝕜] :
    (∂₂[Y]K(u, v)) = (_root_.subdifferentialAt (Y := Y) (K u) v) :=
  rfl

/-- Notation-surface variant of `subdifferential2At_eq_subdifferentialAt`, keeping the bridge on
the short canonical owner notation used in chapter statements. -/
@[simp] theorem subdifferential2At_eq_subdifferentialAt_notation
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {Y : Type*} [HasPairing V Y 𝕜] :
    (∂₂[Y]K(u, v)) = (∂[Y](K u)(v)) :=
  rfl

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Canonical strong-dual bridge for Text 35.5.2. The plain notation `∂₂ K(u, v)` uses this
strong-dual carrier, while `∂₂[Y]K(u, v)` remains the explicit pairing-level view. -/
abbrev subdifferential2AtDual (K : U → V → WithTopBot 𝕜) (u : U) (v : V) :
    Set (StrongDual 𝕜 V) :=
  subdifferential2At K u v (StrongDual 𝕜 V)

scoped[Rockafellar] notation "∂₂" K "(" u ", " v ")" =>
  Bifunction.subdifferential2AtDual K u v

/-- A continuous linear functional belongs to the second partial subdifferential of `K` at
`(u, v)` exactly when it gives the source affine-support inequality for the second-variable
slice. -/
@[simp] theorem mem_subdifferential2At
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {vStar : StrongDual 𝕜 V} :
    vStar ∈ ∂₂ K(u, v) ↔
      ∀ v', K u v' ≥ K u v + ((vStar (v' - v) : 𝕜) : WithTopBot 𝕜) :=
  by
    change vStar ∈ (_root_.subdifferentialAt (Y := StrongDual 𝕜 V) (K u) v) ↔
        ∀ v', K u v' ≥ K u v + ((vStar (v' - v) : 𝕜) : WithTopBot 𝕜)
    exact _root_.mem_subdifferentialAt (f := K u) (x := v) (xStar := vStar)

end

end Bifunction

/-! ### Text_35_5_3 (from Chap07) -/
noncomputable section

open Filter
open scoped Topology

universe u v

section

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
variable {U : Type u} {X : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.3 singles out the partial directional derivatives
  `K'(u, v; u', 0)` and `K'(u, v; 0, v')` of a saddle-function.
- `core/canonical`: the chapter owner for directional derivatives is already
  `Function.HasDirectionalDerivativeAt` / `Function.directionalDerivativeAt` from
  `Chap05.Lemma_23_0_1`.
- `bridge/view`: the first- and second-variable partial derivatives are exactly the directional
  derivatives of the uncurried bifunction in directions `(u', 0)` and `(0, v')`, equivalently the
  directional derivatives of the corresponding slices.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt`;
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- the earlier Chapter 7 slice-bridge pattern from `Chap07.Text_35_5_1`, where the first-variable
  partial owner is likewise obtained by specializing an existing one-variable owner to a fixed
  slice.

Primitive data vs derived API:
- primitive owner data: the existing directional-derivative owners on functions;
- derived API: the slice-identification lemmas below for the two partial directions.

Layer target: `bridge/view`.
-/

/- Text 35.5.3 uses the existing Chapter 23 owner for directional derivatives, specialized to the
uncurried bifunction `Function.uncurry K`; no separate saddle-directional-derivative owner should
be introduced here. -/
recall Function.HasDirectionalDerivativeAt

/- The proof route also uses the Chapter 23 directional-difference-quotient owner directly. -/
recall Function.directionalDifferenceQuotientAt

/- The value-level owner is likewise the existing Chapter 23 directional derivative. -/
recall Function.directionalDerivativeAt

namespace Function

/-- Text 35.5.3, first-variable quotient bridge:
the mixed-direction quotient in direction `(u', 0)` is exactly the quotient of the first-variable
slice `K · v` in direction `u'`. -/
@[simp] theorem directionalDifferenceQuotientAt_uncurry_first_eq
    [AddCommMonoid U] [SMul 𝕜 U]
    [AddCommMonoid X] [SMulZeroClass 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (u' : U) :
    directionalDifferenceQuotientAt (uncurry K) (u, v) (u', 0) =
      directionalDifferenceQuotientAt (K · v) u u' := by
  funext t
  simp [directionalDifferenceQuotientAt, uncurry]

/-- Text 35.5.3, second-variable quotient bridge:
the mixed-direction quotient in direction `(0, v')` is exactly the quotient of the second-variable
slice `K u` in direction `v'`. -/
@[simp] theorem directionalDifferenceQuotientAt_uncurry_second_eq
    [AddCommMonoid U] [SMulZeroClass 𝕜 U]
    [AddCommMonoid X] [SMul 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (v' : X) :
    directionalDifferenceQuotientAt (uncurry K) (u, v) (0, v') =
      directionalDifferenceQuotientAt (K u) v v' := by
  funext t
  simp [directionalDifferenceQuotientAt, uncurry]

section Topology

variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]

/-- Text 35.5.3, first-variable owner bridge:
existence of `K'(u, v; u', 0)` is exactly existence of the directional derivative of `K · v` at
`u` in direction `u'`. -/
@[simp] theorem hasDirectionalDerivativeAt_uncurry_first_iff
    [AddCommMonoid U] [SMul 𝕜 U]
    [AddCommMonoid X] [SMulZeroClass 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (u' : U) (L : WithTopBot 𝕜) :
    HasDirectionalDerivativeAt (uncurry K) (u, v) (u', 0) L ↔
      HasDirectionalDerivativeAt (K · v) u u' L := by
  simp [HasDirectionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_first_eq]

/-- Text 35.5.3, second-variable owner bridge:
existence of `K'(u, v; 0, v')` is exactly existence of the directional derivative of `K u` at `v`
in direction `v'`. -/
@[simp] theorem hasDirectionalDerivativeAt_uncurry_second_iff
    [AddCommMonoid U] [SMulZeroClass 𝕜 U]
    [AddCommMonoid X] [SMul 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (v' : X) (L : WithTopBot 𝕜) :
    HasDirectionalDerivativeAt (uncurry K) (u, v) (0, v') L ↔
      HasDirectionalDerivativeAt (K u) v v' L := by
  simp [HasDirectionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_second_eq]

/-- Text 35.5.3, first-variable slice form: the partial directional derivative
`K'(u, v; u', 0)` is exactly the directional derivative of the slice `fun u'' ↦ K u'' v`
at `u` in the direction `u'`. -/
@[simp] theorem directionalDerivativeAt_uncurry_first_eq
    [AddCommMonoid U] [SMul 𝕜 U]
    [AddCommMonoid X] [SMulZeroClass 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (u' : U) :
    directionalDerivativeAt (uncurry K) (u, v) (u', 0) =
      directionalDerivativeAt (K · v) u u' := by
  simp [directionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_first_eq]

/-- Text 35.5.3, second-variable slice form: the partial directional derivative
`K'(u, v; 0, v')` is exactly the directional derivative of the slice `K u`
at `v` in the direction `v'`. -/
@[simp] theorem directionalDerivativeAt_uncurry_second_eq
    [AddCommMonoid U] [SMulZeroClass 𝕜 U]
    [AddCommMonoid X] [SMul 𝕜 X]
    (K : U → X → WithTopBot 𝕜) (u : U) (v : X) (v' : X) :
    directionalDerivativeAt (uncurry K) (u, v) (0, v') =
      directionalDerivativeAt (K u) v v' := by
  simp [directionalDerivativeAt, directionalDifferenceQuotientAt_uncurry_second_eq]

end Topology

end Function

end

/-! ### Text_35_5_4 (from Chap07) -/
noncomputable section

section

open Function

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]

local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) := WithBotTop.instSMul

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.4 is a pure existence statement: some saddle-function on `𝕜 × 𝕜`
  has a finite product point where a nonzero mixed-direction directional derivative fails to
  exist.
- `core/canonical`: the project already owns the relevant notions as
  `Bifunction.IsSaddle 𝕜 K`, the effective-domain owner `dom(uncurry K)` together with
  the finite-value guard `(uncurry K) p ≠ ⊥`, and `Function.HasDirectionalDerivativeAt` for
  existence of a directional derivative.
- `bridge/view`: finiteness and directional differentiability are both surfaced directly on the
  canonical product-space owner `uncurry K`, avoiding a split slice-vs-product statement surface.

Domain-style sampling used here:
- `Bifunction.IsSaddle` from `Chap07.Definition33_0_1`;
- `dom(·)` / `mem_effectiveDomain` from `Chap01.Definition_4_4`;
- `Function.HasDirectionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- the nearby Chapter 35 finite-point theorem surfaces
  `Bifunction.isConvex_directionalDerivativeAt_second` and
  `Bifunction.directionalDerivativeAt_uncurry_second_eq_supportFunction_subdifferential2At`,
  which likewise record finiteness of `K u v` by `v ∈ dom(K u)` together with `K u v ≠ ⊥`.
- Layer target: `source-facing`, stated directly on canonical chapter owners without introducing a
  local counterexample package wrapper.
-/

-- Proof sketch: instantiate Rockafellar's counterexample by choosing a saddle bifunction on
-- `𝕜 × 𝕜` whose one-variable slices have the required saddle shape but whose mixed difference
-- quotient along some nonzero direction has no right limit at a finite product point.
/-- Text 35.5.4: there exists a saddle-function on `𝕜 × 𝕜` with a finite value at some point
where a nonzero mixed-direction directional derivative fails to exist.

Abstraction-layer decision audit for this theorem surface:
- Scalar/codomain layer: `K` is exposed at the chapter codomain owner `WithTopBot 𝕜` (not `EReal`)
  and keeps the chapter directional-derivative owner layer (`Field` + `LinearOrder`) required by
  `Function.HasDirectionalDerivativeAt`.
  The textbook real statement is recovered by specialization `𝕜 := ℝ`.
- Owner surface: finiteness and directional-derivative failure are both phrased on the same
  product-space owner `uncurry K`, using a single base point `p : 𝕜 × 𝕜` rather than separate
  coordinates.
- Topology layer: this item is not an ambient `closure`/`interior` theorem, but the
  nonexistence claim lives on the Chapter 23 filter-limit owner and must avoid vacuous
  non-Hausdorff/degenerate topologies. The theorem therefore keeps the primitive topological
  owners together with order-compatibility at both source and codomain:
  `TopologicalSpace 𝕜` + `OrderTopology 𝕜` and
  `TopologicalSpace (WithTopBot 𝕜)` + `OrderTopology (WithTopBot 𝕜)`.
-/
theorem exists_saddleFunction_finite_point_no_mixedDirectionalDerivative :
    ∃ K : 𝕜 → 𝕜 → WithTopBot 𝕜,
      Bifunction.IsSaddle 𝕜 K ∧
        ∃ p d : 𝕜 × 𝕜,
          p ∈ dom(uncurry K) ∧
            (uncurry K) p ≠ ⊥ ∧
            d ≠ 0 ∧
              ¬ ∃ L, HasDirectionalDerivativeAt (uncurry K) p d L :=
  sorry

end

/-! ### Text_35_5_5 (from Chap07) -/
open Set
open scoped Rockafellar

universe u v

namespace SaddleFunction

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace U] [TopologicalSpace X] [LT α] [Bot α] [Top α]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.5 restricts the later discussion to interior points of `dom K`.
- `core/canonical`: Chapter 34 already owns the product domain as `SaddleFunction.dom K`, and
  mathlib already owns ordinary product interiors through `interior_prod_eq`.
- `bridge/view`: this file specializes those existing owners to the Chapter 34 domain and also
  records the ambient-to-intrinsic interior bridge at the same owner surface `dom K`.

Domain-style sampling used here:
- `SaddleFunction.dom₁` from `Chap07.Defn_34_3`;
- `SaddleFunction.dom₂` from `Chap07.Defn_34_3`;
- the Chapter 34 owner/notation `dom K` from `Chap07.Defn_34_3`;
- `interior_prod_eq` and `interior_subset_intrinsicInterior` from mathlib.

Primitive data vs derived API:
- primitive owner data already exist upstream: `dom₁ K`, `dom₂ K`, and `dom K`;
- derived API here: the ordinary-interior product description and ambient-to-intrinsic bridge for
  the existing owner `dom K`.

Layer target: `bridge/view`.
-/

/- Text 35.5.5 uses the already existing Chapter 34 owner `dom K`, while ordinary interior on a
product is the canonical mathlib theorem `interior_prod_eq`. -/
recall interior_prod_eq

@[simp] theorem interior_dom (K : U → X → α) :
    interior (dom K) = interior (dom₁ K) ×ˢ interior (dom₂ K) := by
  simpa [SaddleFunction.dom] using interior_prod_eq (s := dom₁ K) (t := dom₂ K)

@[simp] theorem mem_interior_dom {K : U → X → α} {p : U × X} :
    p ∈ interior (dom K) ↔
      p.1 ∈ interior (dom₁ K) ∧ p.2 ∈ interior (dom₂ K) := by
  simp [interior_dom]

@[simp] theorem mem_interior_dom_mk {K : U → X → α} {u : U} {v : X} :
    (u, v) ∈ interior (dom K) ↔
      u ∈ interior (dom₁ K) ∧ v ∈ interior (dom₂ K) := by
  exact mem_interior_dom (K := K) (p := (u, v))

end

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {X : Type v} {E : Type*} {α : Type*}
variable [TopologicalSpace (U × X)]
variable [AddCommGroup E] [Module 𝕜 E] [AddTorsor E (U × X)]
variable [LT α] [Bot α] [Top α]

/-- Ambient interior of `dom K` sits inside the intrinsic interior of the same owner. -/
theorem interior_dom_subset_ri_dom {K : U → X → α} :
    interior (dom K) ⊆ ri[𝕜](dom K) :=
  interior_subset_intrinsicInterior

/-- Pointwise form of `interior_dom_subset_ri_dom`. -/
theorem mem_ri_dom_of_mem_interior_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ interior (dom K)) :
    p ∈ ri[𝕜](dom K) :=
  interior_dom_subset_ri_dom hp

end

end SaddleFunction

/-! ### Theorem_35_5 (from Chap07) -/
section

universe u v w

open scoped Topology
open Function Set Filter SaddleFunction

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 X]

variable (KSeq : ℕ → U → X → 𝕜)
variable {C C' : Set U} {D D' : Set X}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.5 starts with a sequence of finite concave-convex functions on
  `C × D`, assumes pointwise boundedness on a dense product subset `C' × D' ⊆ C × D`, and
  concludes existence of a subsequence converging uniformly on each closed bounded subset of
  `C × D` to a finite concave-convex limit.
- `core/canonical`: the shape owner is `IsConcaveConvexOn 𝕜 C D`, the boundedness owner is
  `PointwiseBoundedOn (fun i ↦ uncurry (KSeq i))` on `C' ×ˢ D'`, the subsequence is canonically
  represented, as elsewhere in Chapter 10, by a reindexing map `φ : ℕ → ℕ` together with
  `StrictMono φ`, and the convergence owner is `TendstoLocallyUniformlyOn` on `C ×ˢ D` for the
  reindexed product-view family `fun i ↦ uncurry (KSeq (φ i))`.
- `bridge/view`: Theorem 35.4 upgrades dense-subset pointwise convergence of a saddle sequence to
  a concave-convex locally uniform limit, so Theorem 35.5 should only add the subsequence
  extraction layer and then feed the reindexed sequence into that owner theorem, not introduce a
  second product-family wrapper.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvexOn` from `Definition33_0_1`;
- `PointwiseBoundedOn` on the owner family `fun i ↦ uncurry (KSeq i)`;
- `TendstoLocallyUniformlyOn` as the canonical convergence owner on `C ×ˢ D`;
- `exists_subsequence_tendstoLocallyUniformlyOn_of_convexOn_of_pointwise_bounded` from
  `Theorem_10_9` for the chapter-standard diagonal Bolzano-Weierstrass ambient layer on the scalar
  field;
- `exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise` from `Theorem_35_4`.

Primitive data vs derived API:
- primitive inputs: the relatively open sets `C` and `D`, the sequence `KSeq`, the dense product
  subset inclusion `C' ×ˢ D' ⊆ C ×ˢ D`, density of `C' ×ˢ D'` in `C ×ˢ D`, and pointwise
  boundedness of the owner product family `fun i ↦ uncurry (KSeq i)` on `C' ×ˢ D'`;
- primitive source-facing shape hypothesis: every `KSeq i` is concave-convex on `C × D`;
- derived API: a subsequence chosen by a strictly monotone reindexing `φ`, a finite
  concave-convex limit
  bifunction `K`, and local uniform convergence of the reindexed owner family
  `fun i ↦ uncurry (KSeq (φ i))` on `C ×ˢ D`; compact-subset and closed-bounded uniform
  convergence forms are then provided as bridge theorems in this file.

Layer target: `source-facing`, using the Chapter 35 shape owner and the canonical local-uniform
convergence owner, with subsequences represented by the chapter-standard `StrictMono`
reindexing surface.
-/

-- Proof sketch: choose a countable dense subset of `C' ×ˢ D'`, enumerate it, and apply the
-- diagonal Bolzano-Weierstrass extraction argument to the bounded scalar fibers
-- `(fun i ↦ uncurry (KSeq i)) i p_j`. This yields a strictly monotone reindexing `φ : ℕ → ℕ`
-- for which the
-- reindexed sequence `KSeq ∘ φ` converges pointwise on a dense subset of `C ×ˢ D`. Then invoke
-- Theorem 35.4 on `KSeq ∘ φ` to obtain a finite concave-convex limit `K` and local uniform
-- convergence of `fun i ↦ uncurry (KSeq (φ i))` on `C ×ˢ D`, hence uniform convergence on every
-- closed
-- bounded subset of `C × D`. As in Theorem 10.9, the bounded scalar-fiber subsequence extraction
-- uses `LocallyCompactSpace 𝕜` via `ProperSpace.of_locallyCompactSpace` to make the relevant
-- closed bounded subsets of `𝕜` compact.
/-- Theorem 35.5: if `C` and `D` are relatively open and `K₁, K₂, …` is a sequence of finite
concave-convex functions on `C × D` whose value sequence is bounded at every point of a dense
product subset `C' × D' ⊆ C × D`, then some subsequence converges locally uniformly on `C × D`,
hence uniformly on every closed bounded subset of `C × D`, to a finite concave-convex function.
The textbook `ℝ^m × ℝ^n` statement is the specialization `𝕜 := ℝ`
to Euclidean spaces; the scalar ambient hypothesis `[LocallyCompactSpace 𝕜]` is the
chapter-canonical compactness input for the diagonal extraction step (via
`ProperSpace.of_locallyCompactSpace`). -/
theorem exists_subsequence_tendstoLocallyUniformlyOn_of_concaveConvexOn_of_dense_pointwiseBoundedOn
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hbounded : PointwiseBoundedOn (fun i ↦ uncurry (KSeq i)) (C' ×ˢ D')) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : U → X → 𝕜,
      IsConcaveConvexOn 𝕜 C D K ∧
        TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop (C ×ˢ D) :=
  sorry

-- Proof sketch: apply the core owner theorem above to obtain the reindexing `φ`, the
-- concave-convex limit `K`, and local uniform convergence on `C ×ˢ D`; then restrict to the
-- compact subset `S` and use the standard compact bridge from local uniform to uniform
-- convergence.
/-- Compact-subset bridge form of Theorem 35.5: under the same hypotheses, one extracted
subsequence converges uniformly on each compact `S ⊆ C ×ˢ D`. -/
theorem
    exists_subsequence_tendstoUniformlyOn_on_compact_of_concaveConvexOn_of_dense_pointwiseBoundedOn
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hbounded : PointwiseBoundedOn (fun i ↦ uncurry (KSeq i)) (C' ×ˢ D'))
    {S : Set (U × X)} (hS_compact : IsCompact S) (hS_subset : S ⊆ C ×ˢ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : U → X → 𝕜,
      IsConcaveConvexOn 𝕜 C D K ∧
        TendstoUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop S := by
  obtain ⟨φ, hφ, K, hK_shape, hK_loc⟩ :=
    exists_subsequence_tendstoLocallyUniformlyOn_of_concaveConvexOn_of_dense_pointwiseBoundedOn
      KSeq hC_open hD_open hshape hCD'_subset hdense hbounded
  refine ⟨φ, hφ, K, hK_shape, ?_⟩
  have hK_loc_S :
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop S :=
    hK_loc.mono hS_subset
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS_compact).1 hK_loc_S

-- Proof sketch: combine the compact-subset bridge above with compactness of closed bounded sets.
-- The needed properness of `U × X` is canonically derived from finite-dimensionality and
-- local compactness of `𝕜`.
/-- Closed-bounded bridge form of Theorem 35.5: one extracted subsequence converges uniformly on
each closed bounded `S ⊆ C ×ˢ D`; compactness of closed bounded sets is obtained from the ambient
finite-dimensional layer over the locally compact scalar field `𝕜`. -/
theorem
    exists_subsequence_tendstoUniformlyOn_on_closed_bounded_of_concaveConvexOn_of_dense_pointwiseBoundedOn
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hbounded : PointwiseBoundedOn (fun i ↦ uncurry (KSeq i)) (C' ×ˢ D'))
    {S : Set (U × X)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : U → X → 𝕜,
      IsConcaveConvexOn 𝕜 C D K ∧
        TendstoUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop S := by
  letI : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  letI : ProperSpace (U × X) := FiniteDimensional.proper (𝕜 := 𝕜) (E := U × X)
  simpa using
    exists_subsequence_tendstoUniformlyOn_on_compact_of_concaveConvexOn_of_dense_pointwiseBoundedOn
      KSeq hC_open hD_open hshape hCD'_subset hdense hbounded
      (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded) hS_subset

end

/-! ### Text_35_5_6 (from Chap07) -/
open Set
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.6 starts from the chapter domain hypothesis
  `p ∈ interior (dom K)` for saddle bifunctions.
- `core/canonical`: directional-derivative APIs act on the product function
  `Function.uncurry K` and consume the graph-domain owner `dom(uncurry K)`.
- `bridge/view`: this file records the direct owner bridge from the Chapter 34 saddle domain
  `dom K` (and its ambient/intrinsic interior variants) to the graph-domain owner
  `dom(uncurry K)`.

Ambient-vs-relative topology choice:
- The chapter clause `p ∈ interior (dom K)` is retained as source input.
- The intrinsic surface `p ∈ ri[𝕜](dom K)` is retained as the reusable topology owner.
- Both feed the same graph-domain target owner `dom(uncurry K)`.

Domain-style sampling used here:
- `SaddleFunction.dom`;
- `dom(uncurry K)`;
- `ri[𝕜](·)`;
- `interior_subset`.

Primitive data vs derived API:
- primitive owner data already exist upstream: `SaddleFunction.dom K`,
  `dom(uncurry K)`, and `ri[𝕜](dom K)`;
- derived API here: bridge lemmas from `dom K`, `interior (dom K)`, and `ri[𝕜](dom K)` into
  `dom(uncurry K)`.

Layer target: `bridge/view`.
-/

recall SaddleFunction.dom
recall SaddleFunction.mem_dom

/- Text 35.5.6 reuses the ambient-to-intrinsic `dom K` bridge from Text 35.5.5. -/
recall SaddleFunction.interior_dom_subset_ri_dom
recall SaddleFunction.mem_ri_dom_of_mem_interior_dom

namespace SaddleFunction

universe u v

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [LT α] [Bot α] [Top α]

/-- Bridge from the Chapter 34 product-domain owner to the graph-domain owner of `uncurry K`. -/
theorem mem_dom_uncurry_of_mem_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ dom K) :
    p ∈ dom(Function.uncurry K) := by
  exact (SaddleFunction.mem_dom.mp hp).2 p.1

end

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace (U × X)]
variable [LT α] [Bot α] [Top α]

/-- Interior points of the Chapter 34 product-domain owner are interior points for
`dom(uncurry K)`. -/
theorem interior_dom_subset_interior_dom_uncurry
    (K : U → X → α) :
    interior (dom K) ⊆ interior (dom(Function.uncurry K)) :=
  interior_mono (fun _ hp => mem_dom_uncurry_of_mem_dom hp)

/-- Pointwise form of `interior_dom_subset_interior_dom_uncurry`. -/
theorem mem_dom_uncurry_of_mem_interior_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ interior (dom K)) :
    p ∈ dom(Function.uncurry K) :=
  mem_dom_uncurry_of_mem_dom (interior_subset hp)

end

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {X : Type v} {E : Type*} {α : Type*}
variable [TopologicalSpace (U × X)]
variable [AddCommGroup E] [Module 𝕜 E] [AddTorsor E (U × X)]
variable [LT α] [Bot α] [Top α]

/-- Intrinsic-interior bridge for Text 35.5.6 in subset form. -/
theorem ri_dom_subset_dom_uncurry
    {K : U → X → α} :
    ri[𝕜](dom K) ⊆ dom(Function.uncurry K) :=
  fun _ hp => mem_dom_uncurry_of_mem_dom (intrinsicInterior_subset hp)

/-- Pointwise form of `ri_dom_subset_dom_uncurry`. -/
theorem mem_dom_uncurry_of_mem_ri_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ ri[𝕜](dom K)) :
    p ∈ dom(Function.uncurry K) :=
  ri_dom_subset_dom_uncurry hp

end

end SaddleFunction
