import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_5_0 (from Chap01) -/
noncomputable section

section

universe u

variable {𝕜 : Type*} [CommSemiring 𝕜] [ConditionallyCompleteLattice 𝕜]
local instance instDecidableLT : DecidableLT 𝕜 := Classical.decRel (· < ·)
/-- Canonical scalar action on `WithTopBot 𝕜` for the convexity owner used in Text 5.5.0. -/
local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x :=
    match x with
    | ⊥ => ⊥
    | (a : 𝕜) => ((r * a : 𝕜) : WithTopBot 𝕜)
    | ⊤ => ⊤

/-- Helper for Text 5.5.0: on finite values, the lifted `WithTopBot` scalar action is ordinary
scalar multiplication in `𝕜`. -/
@[simp] private theorem smul_coe_withTopBot (a u : 𝕜) :
    a • (u : WithTopBot 𝕜) = ((a * u : 𝕜) : WithTopBot 𝕜) := by
  -- The local action was defined by multiplying the finite branch.
  rfl
variable [IsOrderedAddMonoid (WithTopBot 𝕜)] [PosSMulMono 𝕜 (WithTopBot 𝕜)]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.0 states that the support function `δᵛ(· | C)` of a subset
  `C` of `ℝ^n` is convex.
- `core/canonical`: the owner abstractions are the chapter support function `supportFunction`
  from `Defintion_4_8_2`, whose source-facing notation is `δᵛ(· | C)`, and the canonical
  convexity owner `ConvexOn 𝕜 Set.univ` on
  `WithTopBot 𝕜`-valued functions, with supremum closure supplied by
  `Function.ConvexOn.iSup`.
- `bridge/view`: this file contributes the convexity theorem
  `supportFunction_isConvex` for that existing owner, together with its primitive
  linearity-layer precursor `supportFunction_isConvex_of_forall_isLinear` and the compatibility
  bridge theorem `Function.isConvex_supportFunction`; the support-function formula
  remains upstream in `supportFunction`, while finite-valued presentations belong in downstream
  bridge items.
- Primitive data vs derived API: the primitive data are the set `C : Set Y` and the resulting
  function `δᵛ(· | C)`. The convexity assertion is derived from pointwise linearity in `x`,
  and the `HasLinearPairing` theorem is a bridge recovering this primitive linearity premise.

Domain-style sampling used here:
- the project owner `supportFunction` together with its notation `δᵛ(· | C)`;
- the project supremum-closure pattern `Function.ConvexOn.iSup` from `Theorem_5_5`,
  used below with the family argument inferred from the proof family;
- the chapter owner predicate `ConvexOn` on `Set.univ`;
- the chapter pairing owner `HasPairing`, with `HasLinearPairing` used as a bridge layer;
- the linearity owner `IsLinearMap` and its bundling bridge `IsLinearMap.mk'`;
- the mathlib linear-owner theorem `LinearMap.convexOn`.

- Layer target: `bridge/view`; this item reuses the upstream owner instead of keeping a parallel
  local support-function definition. Although the source is written in `ℝ^n`, the owner statement
  has the same mathematical meaning on any module equipped with the chosen linear pairing, so the
  public API is kept at that canonical ambient level.
--/

section Primitive

variable {Y : Type*} [HasPairing X Y 𝕜]

/-- Helper for Text 5.5.0: a pairing evaluation map, viewed in `WithTopBot 𝕜`, is convex on the
whole space whenever its scalar-valued form is linear. -/
private theorem convexOn_univ_pairing_coe
    {y : Y} (hy : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, y⟫ₚ : 𝕜))) :
    ConvexOn 𝕜 (Set.univ : Set X) (fun x : X ↦ (⟪x, y⟫ₚ : WithTopBot 𝕜)) := by
  let L : X →ₗ[𝕜] 𝕜 := IsLinearMap.mk' _ hy
  refine ⟨convex_univ, ?_⟩
  intro x hx y' hy' a b ha hb hab
  -- Rewrite the Jensen term through the bundled linear map.
  change (((L (a • x + b • y') : 𝕜) : WithTopBot 𝕜) ≤
      a • (L x : WithTopBot 𝕜) + b • (L y' : WithTopBot 𝕜))
  rw [map_add, map_smul, map_smul]
  -- The lifted scalar actions on the two finite branches reduce to ordinary multiplication.
  rw [smul_coe_withTopBot, smul_coe_withTopBot]
  exact le_rfl

-- Proof sketch: rewrite the extended-value support function `δᵛ(· | C)` as the
-- pointwise supremum of the `WithTopBot 𝕜`-valued linear functionals
-- `x ↦ (⟪x, y⟫ₚ : WithTopBot 𝕜)` indexed by `y : C`. Each functional is convex on `Set.univ`,
-- and the indexed supremum is convex by `Function.ConvexOn.iSup`.
/-- Primitive linearity-layer form of Text 5.5.0: if each pairing evaluation map
`x ↦ ⟪x, y⟫ₚ` is linear on points `y ∈ C`, then the support function `δᵛ(· | C)` is convex. -/
theorem supportFunction_isConvex_of_forall_isLinear (C : Set Y)
    (hlin : ∀ y ∈ C, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, y⟫ₚ : 𝕜))) :
    ConvexOn 𝕜 (Set.univ : Set X) (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  have hs : (δᵛ(· | C) : X → WithTopBot 𝕜) =
      (⨆ y : C, (⟪·, (y : Y)⟫ₚ : X → WithTopBot 𝕜)) := by
    simpa using
      (supportFunction_eq_iSup (X := X) (Y := Y) (L := WithTopBot 𝕜) (C := C))
  rw [hs]
  refine Function.ConvexOn.iSup (𝕜 := 𝕜) (C := (Set.univ : Set X)) convex_univ ?_
  intro y
  exact convexOn_univ_pairing_coe (hy := hlin (y : Y) y.property)

end Primitive

section LinearPairingBridge

variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Text 5.5.0: the support function `δᵛ(· | C)` of a set is convex. Specializing to the standard
real inner product on `ℝ^n` recovers the textbook statement. -/
theorem supportFunction_isConvex (C : Set Y)
    : ConvexOn 𝕜 (Set.univ : Set X)
        (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  exact supportFunction_isConvex_of_forall_isLinear (C := C)
    (fun y _hy ↦ HasLinearPairing.isLinear_pairing_left y)

/-- Namespace bridge for the global owner name: the support function is convex on `Set.univ`
in the canonical `ConvexOn` owner language. -/
theorem Function.isConvex_supportFunction (C : Set Y)
    : ConvexOn 𝕜 (Set.univ : Set X)
        (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  exact supportFunction_isConvex_of_forall_isLinear (C := C)
    (fun y _hy ↦ HasLinearPairing.isLinear_pairing_left y)

end LinearPairingBridge

end

/-! ### Text_5_5_0_1 (from Chap01) -/
noncomputable section

universe u v w

namespace Function

/-- Helper for Text 5.5.0.1: the canonical codomain lift views a finite-valued function as
`WithTopBot`-valued. -/
abbrev toWithTopBot {E : Type u} {α : Type v} (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

/-- Helper for Text 5.5.0.1: backward-compatible spelling for `Function.toWithTopBot`. -/
abbrev toWithBotTop {E : Type u} {α : Type v} (f : E → α) : E → WithBotTop α :=
  f.toWithTopBot

/-- Helper for Text 5.5.0.1: the chapter owner `Function.IsConvex` is convexity of the epigraph
of a `WithTopBot`-valued function. -/
abbrev IsConvex (𝕜 : Type w) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type v} [AddCommMonoid α] [SMul 𝕜 α] [LE α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Helper for Text 5.5.0.1: convexity on all of `E` lifts to convexity of the canonical
`WithTopBot` codomain extension. -/
theorem isConvex_coe_of_convexOn_univ {𝕜 : Type w}
    [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    {β : Type v} [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 β] [PosSMulMono 𝕜 β]
    {f : E → β} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    f.toWithTopBot.IsConvex 𝕜 := by
  simpa [Function.toWithTopBot, Function.IsConvex, epi_univ_eq_setOf_le] using hf.convex_epigraph

/-- Helper for Text 5.5.0.1: coercing a finite coordinatewise supremum into `WithBotTop` equals
the corresponding indexed supremum there. -/
theorem toWithBotTop_sSup_range_eq_iSup {E : Type u} {ι : Type v} {α : Type*}
    [ConditionallyCompleteLattice α] [Nonempty ι]
    (f : E → ι → α) (hf_bddAbove : ∀ x : E, BddAbove (Set.range (f x))) :
    (fun x ↦ ((sSup (Set.range (f x)) : α) : WithBotTop α)) =
      ⨆ i : ι, fun x ↦ (f x i : WithBotTop α) := by
  funext x
  rw [iSup_apply, sSup_range]
  have h_withTop :
      ((((⨆ i : ι, f x i : α) : WithTop α) : WithBotTop α)) =
        (((⨆ i : ι, ((f x i : α) : WithTop α)) : WithTop α) : WithBotTop α) := by
    exact congrArg (fun t : WithTop α ↦ (t : WithBotTop α))
      (WithTop.coe_iSup (f := f x) (hf_bddAbove x))
  have h_bddAbove_withTop : BddAbove (Set.range fun i : ι ↦ ((f x i : α) : WithTop α)) := by
    refine ⟨((sSup (Set.range (f x)) : α) : WithTop α), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact WithTop.coe_le_coe.2 (le_csSup (hf_bddAbove x) (Set.mem_range_self i))
  have h_withBot :
      (((⨆ i : ι, ((f x i : α) : WithTop α)) : WithTop α) : WithBotTop α) =
        ⨆ i : ι, ((((f x i : α) : WithTop α) : WithBotTop α)) := by
    exact WithBot.coe_iSup (f := fun i : ι ↦ ((f x i : α) : WithTop α)) h_bddAbove_withTop
  exact h_withTop.trans h_withBot

end Function

/-- The function on a finite-coordinate space sending `x` to the supremum of its coordinates.
This owner is index-finite and scalar-agnostic; concrete coordinate models are downstream
specializations. -/
def greatestCoordinate {ι : Type u} {α : Type v} [SupSet α]
    [Finite ι] [Nonempty ι] : (ι → α) → α :=
  fun x ↦ sSup (Set.range x)

section

variable {ι : Type u} {α : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item asserts convexity of the finite nonempty-coordinate function sending
  `x` to the greatest of its coordinates.
- `core/canonical`: the owner abstractions are the chapter convexity predicate
  `Function.IsConvex`, the closure theorem `Function.IsConvex.iSup` for pointwise suprema, and
  the linear coordinate projections `LinearMap.proj i`.
- `bridge/view`: the textbook greatest-coordinate function is the finite supremum
  `sSup (Set.range x)` of the coordinates of `x`, and after coercion to `WithTopBot α` it is the
  indexed supremum of the coordinate projections `x ↦ x i`.
- Primitive data vs derived API: `greatestCoordinate` is the primitive source-facing owner, with
  nonemptiness of the index type included in the owner layer (so no empty-index sentinel value is
  encoded in the definition). The canonical convexity theorem is stated directly on the indexed
  `iSup` owner; the finite-owner `greatestCoordinate` convexity theorem is derived through the
  `toWithTopBot` bridge.
- Domain-style sampling used here: the project bridge `Function.toWithTopBot`,
  `Function.toWithBotTop_sSup_range_eq_iSup` (compatibility theorem name),
  `Function.IsConvex.iSup`,
  `Function.isConvex_coe_of_convexOn_univ`, `LinearMap.proj`, `LinearMap.convexOn`, and
  `Finite.bddAbove_range`.
- Assumption layer for the convexity theorem:
  scalar assumptions come from the convexity API (`Function.IsConvex.iSup` and
  `Function.isConvex_coe_of_convexOn_univ`), while codomain assumptions come from finite `sSup`
  and order-compatible scalar monotonicity; the scalar and codomain are kept decoupled.
- Layer target: `source-facing`, with the owner defined once at the finite-index level and reused
  by the later positive-homogeneity and simplex-support-function items.
-/

section finiteIndex

variable [Finite ι]

@[simp] theorem greatestCoordinate_apply [SupSet α] [Nonempty ι] (x : ι → α) :
    greatestCoordinate x = sSup (Set.range x) :=
  rfl

theorem greatestCoordinate_toWithBotTop_eq_iSup [ConditionallyCompleteLattice α]
    [Nonempty ι] :
    greatestCoordinate.toWithBotTop =
      ⨆ i : ι, fun x : ι → α ↦ (x i : WithBotTop α) := by
  simpa [greatestCoordinate] using
    (Function.toWithBotTop_sSup_range_eq_iSup
      (f := fun x : ι → α ↦ fun i : ι ↦ x i)
      (hf_bddAbove := fun x : ι → α ↦ Finite.bddAbove_range x))

/-- Canonical owner bridge: coercing `greatestCoordinate` to `WithTopBot` is the pointwise
coordinate supremum. This is definitionally equivalent to
`greatestCoordinate_toWithBotTop_eq_iSup`. -/
theorem greatestCoordinate_toWithTopBot_eq_iSup [ConditionallyCompleteLattice α]
    [Nonempty ι] :
    greatestCoordinate.toWithTopBot =
      ⨆ i : ι, fun x : ι → α ↦ (x i : WithBotTop α) := by
  simpa using (greatestCoordinate_toWithBotTop_eq_iSup (ι := ι) (α := α))

end finiteIndex

/-- Helper for Text 5.5.0.1: each coordinate is bounded above by the greatest coordinate. -/
private theorem coordinate_le_greatestCoordinate [ConditionallyCompleteLattice α]
    [Finite ι] [Nonempty ι] (x : ι → α) (i : ι) :
    x i ≤ greatestCoordinate x := by
  -- The `i`-th coordinate is one of the values appearing in the finite range supremum.
  rw [greatestCoordinate_apply]
  exact le_csSup (Finite.bddAbove_range x) (Set.mem_range_self i)

/-- Helper for Text 5.5.0.1: the finite supremum of the coordinate projections satisfies Jensen's
inequality on `Set.univ`. -/
private theorem convexOn_univ_greatestCoordinate {R : Type w} [Semiring R] [PartialOrder R]
    [AddCommMonoid α] [ConditionallyCompleteLattice α]
    [IsOrderedAddMonoid α] [Module R α] [PosSMulMono R α]
    [Finite ι] [Nonempty ι] :
    ConvexOn R (Set.univ : Set (ι → α)) (greatestCoordinate : (ι → α) → α) := by
  -- Route correction: prove Jensen directly on the finite supremum owner, then lift to
  -- `toWithBotTop`; the chapter `iSup` closure theorem is exposed on the dual `WithTopBot` owner.
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Compare each coordinate of the convex combination to the same convex combination of the
  -- coordinate suprema, then take the supremum over all coordinates.
  rw [greatestCoordinate_apply, greatestCoordinate_apply, greatestCoordinate_apply]
  refine csSup_le (Set.range_nonempty (a • x + b • y)) ?_
  rintro z ⟨i, rfl⟩
  change a • x i + b • y i ≤ a • sSup (Set.range x) + b • sSup (Set.range y)
  exact add_le_add
    (smul_le_smul_of_nonneg_left
      (coordinate_le_greatestCoordinate (ι := ι) (α := α) x i) ha)
    (smul_le_smul_of_nonneg_left
      (coordinate_le_greatestCoordinate (ι := ι) (α := α) y i) hb)

section finiteIndex

variable [Finite ι]

/-- Text 5.5.0.1: the greatest-coordinate function is convex. -/
theorem greatestCoordinate_isConvex {R : Type w} [Semiring R] [PartialOrder R]
    [AddCommMonoid α] [ConditionallyCompleteLattice α]
    [IsOrderedAddMonoid α] [Module R α] [PosSMulMono R α] [Nonempty ι] :
    ((greatestCoordinate : (ι → α) → α).toWithBotTop).IsConvex R := by
  -- Lift the finite-valued Jensen proof to the chapter extended-value owner.
  exact Function.isConvex_coe_of_convexOn_univ
    (convexOn_univ_greatestCoordinate (ι := ι) (α := α) (R := R))

/-- Canonical owner form behind Text 5.5.0.1: the `WithBotTop`-valued coordinate supremum is
convex. -/
theorem iSup_coordinate_isConvex {R : Type w} [Semiring R] [PartialOrder R]
    [AddCommMonoid α] [ConditionallyCompleteLattice α]
    [IsOrderedAddMonoid α] [Module R α] [PosSMulMono R α] [Nonempty ι] :
    (⨆ i : ι, fun x : ι → α ↦ (x i : WithBotTop α)).IsConvex R := by
  -- Rewrite the indexed-supremum bridge back to `greatestCoordinate`.
  rw [← greatestCoordinate_toWithBotTop_eq_iSup]
  exact greatestCoordinate_isConvex (ι := ι) (α := α) (R := R)

end finiteIndex

end

/-! ### Text_5_5_0_2 (from Chap01) -/
noncomputable section

universe u v w

section

variable {ι : Type u} {𝕜 : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α] [Finite ι]

open scoped Pointwise Function

namespace Text_5_5_0_2

/-- Helper for Text 5.5.0.2: the owner used here sends a finite-coordinate point to the supremum
of its coordinate range. This is the local source-faithful replacement for the missing imported
owner artifact. -/
def greatestCoordinate {ι : Type u} {α : Type w} [SupSet α] [Finite ι] [Nonempty ι] :
    (ι → α) → α :=
  fun x ↦ sSup (Set.range x)

/-- Helper for Text 5.5.0.2: unfolding the local greatest-coordinate owner exposes the supremum
of the coordinate range. -/
@[simp] theorem greatestCoordinate_apply {ι : Type u} {α : Type w} [SupSet α] [Finite ι]
    [Nonempty ι] (x : ι → α) :
    greatestCoordinate x = sSup (Set.range x) :=
  rfl

end Text_5_5_0_2

open Text_5_5_0_2

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item states that the finite-coordinate function sending `x` to the
  greatest of its coordinates is positively homogeneous.
- `core/canonical`: the owner abstraction is the chapter predicate
  `Function.PositivelyHomogeneous : ((ι → α) → α) → Prop`, applied to the owner
  `greatestCoordinate`
  from
  Text 5.5.0.1.
- `bridge/view`: the phrase "greatest of the components" is rendered canonically by the
  imported owner `greatestCoordinate`, whose defining formula is the finite supremum
  `sSup (Set.range x)` of the coordinate range.
- Primitive data vs derived API: `greatestCoordinate` is the primitive source-facing
  object; the pointwise positive-scalar scaling law
  `greatestCoordinate_map_smul_pos` is the primitive theorem-level bridge, and the owner theorem
  `greatestCoordinate_positivelyHomogeneous` is derived from it.
- Layer target: `source-facing`, stated via the canonical owner predicate.

Domain-style sampling used here:
- `Function.PositivelyHomogeneous` from `Definition_4_8`;
- `Set.range_smul` for the canonical scaling of a coordinate range;
- `OrderIso.smulRight` + `OrderIso.map_csSup'` for transport of finite suprema through positive
  scalar multiplication;
- the standard supremum expression `sSup (Set.range x)` for the largest coordinate value.
-/

/-- Helper for Text 5.5.0.2: pointwise scalar multiplication of a coordinate function scales its
coordinate range set. -/
lemma range_smul_coordinate_eq [SMul 𝕜 α] (c : 𝕜) (x : ι → α) :
    Set.range (c • x) = c • Set.range x := by
  -- The range-level statement is the canonical set-theoretic form of pointwise scaling.
  simpa using (Set.range_smul c x)

/-- Helper for Text 5.5.0.2: a positive scalar commutes with the finite supremum of a coordinate
range. -/
lemma csSup_range_smul [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] (c : 𝕜⁺) (x : ι → α) :
    sSup ((c : 𝕜) • Set.range x) = c • sSup (Set.range x) := by
  -- Positive scaling acts by an order isomorphism, so it transports this finite supremum.
  simpa using
    ((OrderIso.smulRight (β := α) c.2).map_csSup' (s := Set.range x) (Set.range_nonempty x)
      (Finite.bddAbove_range x)).symm

/-- Primitive positive-scalar scaling law behind Text 5.5.0.2 for the
finite-coordinate greatest-coordinate owner. -/
theorem greatestCoordinate_map_smul_pos [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] (c : 𝕜⁺) (x : ι → α) :
    greatestCoordinate (c • x) = c • greatestCoordinate x := by
  change greatestCoordinate ((c : 𝕜) • x) = (c : 𝕜) • greatestCoordinate x
  -- Rewrite both sides into the finite-supremum owner from the source proof.
  rw [greatestCoordinate_apply (x := ((c : 𝕜) • x))]
  rw [range_smul_coordinate_eq]
  rw [greatestCoordinate_apply (x := x)]
  -- The order-isomorphism lemma is exactly the statement that maximum commutes with positive scaling.
  exact csSup_range_smul (ι := ι) (𝕜 := 𝕜) (α := α) c x

/-- Textbook scalar-plus-positivity bridge for `greatestCoordinate_map_smul_pos`. -/
theorem greatestCoordinate_map_smul [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] {c : 𝕜} (hc : 0 < c) (x : ι → α) :
    greatestCoordinate (c • x) = c • greatestCoordinate x := by
  -- Package the positive scalar into `𝕜⁺` to reuse the primitive owner-level scaling law.
  exact greatestCoordinate_map_smul_pos ⟨c, hc⟩ x

/-- Text 5.5.0.2: the function sending `x` to the greatest of its coordinates is positively
homogeneous on finite-coordinate spaces over conditionally complete lattices with
positive-scalar order monotonicity/reflectivity. -/
theorem greatestCoordinate_positivelyHomogeneous [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] :
    (greatestCoordinate : (ι → α) → α).PositivelyHomogeneous 𝕜 := by
  -- The owner predicate asks for the pointwise positive-scalar identity proved above.
  intro c x
  exact greatestCoordinate_map_smul_pos c x

end

/-! ### Text_5_5_0_3 (from Chap01) -/
noncomputable section

open scoped BigOperators
open scoped Rockafellar

universe u v

namespace Function

/-- Helper for Text 5.5.0.3: the canonical codomain lift views a finite-valued function as
`WithTopBot`-valued. -/
abbrev toWithTopBot {E : Type u} {α : Type v} (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

end Function

section

variable {ι : Type u}

/-
Source/core/bridge triage:
- `source-facing`: the item evaluates the support function of the standard simplex and identifies
  it with the greatest component of `x`; textbook finite-dimensional coordinate versions are
  specializations of this owner-level statement.
- `core/canonical`: the owner abstractions are the chapter support-function declaration
  `δᵛ(x | C)` from `Defintion_4_8_2`, the owner `greatestCoordinate` from Text 5.5.0.1,
  and mathlib's simplex owner `stdSimplex 𝕜 ι : Set (ι → 𝕜)`.
- `bridge/view`: the coordinate formula `{y | ∀ i, 0 ≤ y i ∧ ∑ i, y i = 1}` is used only as a
  theorem-level bridge rewriting of the canonical owner `stdSimplex 𝕜 ι`.
- semantic guard: `stdSimplex 𝕜 ι` is empty when `ι` is empty, so the intrinsic
  `WithTopBot`-valued supremum formula is the canonical no-hypothesis surface; the
  `greatestCoordinate` surface is a nonempty-index bridge.
- Primitive data vs derived API: there is no new simplex data in this file; `stdSimplex 𝕜 ι`
  is the upstream owner.
- Domain-style sampling used here: `supportFunction`, `supportFunction_def`, `stdSimplex`,
  `single_mem_stdSimplex`, `greatestCoordinate`, and `Function.toWithTopBot`.
- Layer target: `source-facing` main theorem stated on the intrinsic simplex owner
  `stdSimplex 𝕜 ι : Set (ι → 𝕜)`, with a theorem-level coordinate bridge.
-/

section OrderedScalar

variable {𝕜 : Type v}
variable [ConditionallyCompleteLattice 𝕜]

/-- Helper for Text 5.5.0.3: the greatest coordinate of a finite family is the supremum of its
coordinate range. -/
def greatestCoordinate [Nonempty ι] : (ι → 𝕜) → 𝕜 :=
  fun x ↦ sSup (Set.range x)

/-- Helper for Text 5.5.0.3: unfolding `greatestCoordinate` exposes the supremum of the
coordinate range. -/
@[simp] theorem greatestCoordinate_apply [Nonempty ι] (x : ι → 𝕜) :
    greatestCoordinate x = sSup (Set.range x) :=
  rfl

/-- Helper for Text 5.5.0.3: coercing `greatestCoordinate` to `WithTopBot` turns the finite
coordinate supremum into the indexed supremum. -/
theorem greatestCoordinate_toWithTopBot_eq_iSup [Finite ι] [Nonempty ι] :
    greatestCoordinate.toWithTopBot =
      ⨆ i : ι, fun x : ι → 𝕜 ↦ (x i : WithTopBot 𝕜) := by
  funext x
  have hx_bdd : BddAbove (Set.range x) := Finite.bddAbove_range x
  have hx_bdd_bot : BddAbove (Set.range fun i : ι ↦ ((x i : 𝕜) : WithBot 𝕜)) :=
    Finite.bddAbove_range (fun i : ι ↦ ((x i : 𝕜) : WithBot 𝕜))
  -- Rewrite the finite owner to the supremum of the coordinate range, then move the supremum
  -- through the coercion into `WithTopBot`.
  simp only [Function.toWithTopBot, iSup_apply]
  rw [greatestCoordinate_apply, sSup_range]
  rw [WithBot.coe_iSup hx_bdd]
  rw [WithTop.coe_iSup (fun i : ι ↦ ((x i : 𝕜) : WithBot 𝕜)) hx_bdd_bot]

section FintypeIndex

variable [Fintype ι]
variable [Semiring 𝕜] [IsOrderedAddMonoid 𝕜] [PosMulMono 𝕜] [ZeroLEOneClass 𝕜]

local instance instHasPairingPiDot : HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 where
  pairing x y := y ⬝ᵥ x

-- Proof sketch: show first that every simplex point `w` gives
-- `⟪x, w⟫ₚ ≤ sSup (Set.range x)` because the coordinates of `w` are nonnegative
-- and sum to `1`,
-- so `⟪x, w⟫ₚ` is a convex combination of the coordinates of `x`. For the reverse inequality,
-- evaluate at each singleton weight `Pi.single i 1` and then take `⨆ i`.
/-- Text 5.5.0.3 on the intrinsic simplex owner: the support function of `stdSimplex 𝕜 ι` is the
greatest coordinate. This requires the index type to be nonempty. -/
theorem supportFunction_stdSimplex_eq_greatestCoordinate [Nonempty ι] :
    (fun x : ι → 𝕜 ↦ supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x) =
      greatestCoordinate.toWithTopBot := by
  funext x
  classical
  have hx_bdd : BddAbove (Set.range x) := Set.Finite.bddAbove (Set.toFinite (Set.range x))
  have hle_greatest : ∀ j : ι, x j ≤ greatestCoordinate x := by
    intro j
    rw [greatestCoordinate_apply]
    exact le_csSup hx_bdd (Set.mem_range_self j)
  rw [supportFunction_def]
  change
      (⨆ y : stdSimplex 𝕜 ι,
        (⟪x, (y : ι → 𝕜)⟫ₚ : WithTopBot 𝕜)) =
      greatestCoordinate.toWithTopBot x
  have hgreatest_eq_iSup :
      greatestCoordinate.toWithTopBot x = ⨆ i : ι, (x i : WithTopBot 𝕜) := by
    simpa [iSup_apply] using
      congrFun (greatestCoordinate_toWithTopBot_eq_iSup (ι := ι)) x
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro y
    have hy_nonneg : 0 ≤ (y : ι → 𝕜) := fun j ↦ y.2.1 j
    have hsum : (∑ j, (y : ι → 𝕜) j) = 1 := y.2.2
    have hinner : (⟪x, (y : ι → 𝕜)⟫ₚ : 𝕜) ≤ greatestCoordinate x := by
      calc
        ⟪x, (y : ι → 𝕜)⟫ₚ = (y : ι → 𝕜) ⬝ᵥ x := rfl
        _ ≤ (y : ι → 𝕜) ⬝ᵥ fun _ : ι ↦ greatestCoordinate x := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact mul_le_mul_of_nonneg_left (hle_greatest j) (hy_nonneg j)
        _ = ∑ j, (y : ι → 𝕜) j * greatestCoordinate x := by simp [dotProduct]
        _ = (∑ j, (y : ι → 𝕜) j) * greatestCoordinate x := by rw [← Finset.sum_mul]
        _ = greatestCoordinate x := by simp [hsum]
    change (((y : ι → 𝕜) ⬝ᵥ x : 𝕜) : WithTopBot 𝕜) ≤ greatestCoordinate.toWithTopBot x
    rw [Function.toWithTopBot, WithTop.coe_le_coe, WithBot.coe_le_coe]
    exact hinner
  · calc
      greatestCoordinate.toWithTopBot x = ⨆ i : ι, (x i : WithTopBot 𝕜) := hgreatest_eq_iSup
      _ ≤ ⨆ y : stdSimplex 𝕜 ι, (⟪x, (y : ι → 𝕜)⟫ₚ : WithTopBot 𝕜) := by
        refine iSup_le ?_
        intro i
        refine le_iSup_of_le ⟨Pi.single i (1 : 𝕜), single_mem_stdSimplex 𝕜 i⟩ ?_
        change ((x i : 𝕜) : WithTopBot 𝕜) ≤
          ((((⟨Pi.single i (1 : 𝕜), single_mem_stdSimplex 𝕜 i⟩ : stdSimplex 𝕜 ι) : ι → 𝕜) ⬝ᵥ
            x : 𝕜) : WithTopBot 𝕜)
        rw [WithTop.coe_le_coe, WithBot.coe_le_coe]
        change x i ≤ (Pi.single i (1 : 𝕜)) ⬝ᵥ x
        simp [single_dotProduct]

/-- Pointwise form of `supportFunction_stdSimplex_eq_greatestCoordinate`. -/
theorem supportFunction_stdSimplex_eq_greatestCoordinate_apply [Nonempty ι] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x = greatestCoordinate.toWithTopBot x := by
  simpa using
    congrFun (supportFunction_stdSimplex_eq_greatestCoordinate (ι := ι)) x
 
/-- Intrinsic `WithTopBot`-valued form of Text 5.5.0.3:
the support function of `stdSimplex 𝕜 ι` is the coordinate supremum. -/
theorem supportFunction_stdSimplex_eq_iSup [Nontrivial 𝕜] :
    (fun x : ι → 𝕜 ↦ supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x) =
      (fun x : ι → 𝕜 ↦ ⨆ i : ι, (x i : WithTopBot 𝕜)) := by
  funext x
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    rw [supportFunction_stdSimplex_eq_greatestCoordinate_apply (ι := ι) x]
    simpa [iSup_apply] using
      congrFun (greatestCoordinate_toWithTopBot_eq_iSup (ι := ι)) x
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    rw [supportFunction_def, stdSimplex_of_isEmpty_index (𝕜 := 𝕜) (ι := ι)]
    simp [iSup_of_empty]

/-- Pointwise form of `supportFunction_stdSimplex_eq_iSup`. -/
theorem supportFunction_stdSimplex_eq_iSup_apply [Nontrivial 𝕜] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x = ⨆ i : ι, (x i : WithTopBot 𝕜) := by
  simpa using congrFun (supportFunction_stdSimplex_eq_iSup (ι := ι)) x

/-- Coordinate-form intrinsic bridge for Text 5.5.0.3:
the support function of `{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}` equals the coordinate supremum. -/
theorem supportFunction_coordinateSimplex_eq_iSup [Nontrivial 𝕜] :
    (fun x : ι → 𝕜 ↦
      supportFunction (L := WithTopBot 𝕜)
        ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x) =
      (fun x : ι → 𝕜 ↦ ⨆ i : ι, (x i : WithTopBot 𝕜)) := by
  simpa [stdSimplex] using supportFunction_stdSimplex_eq_iSup (ι := ι)

/-- Pointwise form of `supportFunction_coordinateSimplex_eq_iSup`. -/
theorem supportFunction_coordinateSimplex_eq_iSup_apply [Nontrivial 𝕜] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜)
      ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x =
      ⨆ i : ι, (x i : WithTopBot 𝕜) := by
  simpa using congrFun (supportFunction_coordinateSimplex_eq_iSup (ι := ι)) x

/-- Coordinate-form bridge for Text 5.5.0.3:
the support function of `{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}` equals the greatest coordinate. -/
theorem supportFunction_coordinateSimplex_eq_greatestCoordinate [Nonempty ι] :
    (fun x : ι → 𝕜 ↦
      supportFunction (L := WithTopBot 𝕜)
        ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x) =
      greatestCoordinate.toWithTopBot := by
  simpa [stdSimplex] using
    supportFunction_stdSimplex_eq_greatestCoordinate (ι := ι)

/-- Pointwise form of `supportFunction_coordinateSimplex_eq_greatestCoordinate`. -/
theorem supportFunction_coordinateSimplex_eq_greatestCoordinate_apply [Nonempty ι] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜)
      ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x =
      greatestCoordinate.toWithTopBot x := by
  simpa using
    congrFun
      (supportFunction_coordinateSimplex_eq_greatestCoordinate (ι := ι)) x

end FintypeIndex

end OrderedScalar

end

/-! ### Text_5_5_0_4 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 5.5.0.4 considers on `ℝ^n` the map
  `x ↦ max { |x j| | j = 1, ..., n }`; the canonical finite-coordinate owner layer is an
  arbitrary finite index type `ι`, and the reused norm owner already works on finite families in
  any real seminormed coordinate spaces `G i`.
- `core/canonical`: the owner theorem is already upstream as `Function.isConvex_norm`, stating
  global convexity of the norm as a `WithTopBot ℝ`-valued function.
- `bridge/view`: specialize that owner to a dependent finite product `((i : ι) → G i)`, then
  rewrite with `Pi.norm_def'` to get the finite-coordinate supremum expression.
- Primitive data vs derived API: no new owner is introduced here; this file provides only the
  finite-coordinate bridge statements of the existing canonical owner.
- Domain-style sampling used here: `Function.isConvex_norm`, `Pi.norm_def'`.
- Layer target: keep the public owner at `Function.isConvex_norm`; keep this item at the abstract
  finite-index bridge layer and leave concrete `ℝ^n` formulas to downstream specialization.
-/

/- Text 5.5.0.4 uses the canonical owner theorem `Function.isConvex_norm`; no parallel local
owner is introduced in this file. -/
recall Function.isConvex_norm

section

variable {ι : Type*} [Fintype ι]
variable {G : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

/-- Coordinate bridge form of Text 5.5.0.4: on any finite coordinate family of real seminormed
spaces, the coordinate-supremum expression for the norm is globally convex. -/
theorem Function.isConvex_pi_univSup_nnnorm :
    ((fun x : (i : ι) → G i ↦
      ((Finset.univ.sup fun j : ι ↦ ‖x j‖₊ : NNReal) : ℝ)).toWithTopBot).IsConvex ℝ := by
  simpa [Pi.norm_def'] using (Function.isConvex_norm (E := (i : ι) → G i))

end

/-! ### Text_5_5_0_5 (from Chap01) -/
noncomputable section

open scoped BigOperators
open scoped Rockafellar

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

local instance : HasPairing E E 𝕜 where
  pairing x y := ∑ i, x i * y i

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item computes the support function of the explicit coordinate set
  `D = {y | ∑ i, |y i| ≤ 1}` and identifies it with the maximum absolute value of the
  coordinates.
- `core/canonical`: the owner abstractions are the chapter support function `δᵛ(x | C)`,
  the source-facing coordinate `ℓ¹` unit ball
  `coordinateL1Ball = {y | ∑ i, |y i| ≤ 1}`, and the coordinate `ℓ∞` owner `linftyNorm`
  defined intrinsically as the finite maximum `maxᵢ |x i|`.
  The pairing layer is explicit and model-independent:
  `⟪x, y⟫ₚ = ∑ i, x i * y i`, so the support-function statement is proved directly from the
  coordinate formula.
- Layer target: `core/canonical`; the main entry is the pointwise owner theorem
  `supportFunction_coordinateL1Ball_eq_linftyNorm`.

Domain-style sampling used here:
- the project owner `supportFunction` and its notation/specification theorem `supportFunction_def`;
- the coordinate pairing owner `⟪x, y⟫ₚ = ∑ i, x i * y i`;
- the coordinate-set owner `coordinateL1Ball` and coordinate-max owner `linftyNorm`.
-/

/-- The coordinate `ℓ¹` unit ball `D = {y | ∑ i, |y i| ≤ 1}` on a finite coordinate family. -/
def coordinateL1Ball {ι : Type*} [Fintype ι] {𝕜 : Type*}
    [AddCommGroup 𝕜] [LinearOrder 𝕜] [One 𝕜] :
    Set (ι → 𝕜) :=
  {y : ι → 𝕜 | ∑ i, |y i| ≤ 1}

@[simp] theorem mem_coordinateL1Ball {ι : Type*} [Fintype ι] {𝕜 : Type*}
    [AddCommGroup 𝕜] [LinearOrder 𝕜] [One 𝕜] (y : ι → 𝕜) :
    y ∈ coordinateL1Ball ↔ ∑ i, |y i| ≤ 1 :=
  Iff.rfl

/-- Canonical coordinate `ℓ∞` owner used in Text 5.5.0.5:
the finite maximum `maxᵢ |x i|` on a finite coordinate family. -/
def linftyNorm {ι : Type*} [Fintype ι] {𝕜 : Type*} [AddGroup 𝕜] [LinearOrder 𝕜]
    (x : ι → 𝕜) : 𝕜 :=
  if hι : Fintype.card ι = 0 then
    0
  else
    letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hι)
    Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ |x i|

@[simp] theorem linftyNorm_eq_sup'_univ_abs {ι : Type*} [Fintype ι] {𝕜 : Type*}
    [AddGroup 𝕜] [LinearOrder 𝕜] [Nonempty ι] (x : ι → 𝕜) :
    linftyNorm x = Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ |x i|) := by
  have hcard : Fintype.card ι ≠ 0 := by
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance)
  simp [linftyNorm, hcard]

/-- Upper bound used in the support-function computation for the coordinate `ℓ¹` ball:
`⟪x, y⟫ ≤ ‖x‖_∞` whenever `∑ i, |y i| ≤ 1`. -/
private theorem pairing_le_linftyNorm_of_mem_coordinateL1Ball
    [Nonempty ι] (x y : E) (hy : y ∈ coordinateL1Ball) :
    (⟪x, y⟫ₚ : 𝕜) ≤ linftyNorm x := by
  have hsum_le_one : ∑ i, |y i| ≤ 1 := hy
  have hxi : ∀ i, |x i| ≤ linftyNorm x := by
    intro i
    rw [linftyNorm_eq_sup'_univ_abs x]
    exact Finset.le_sup' (fun j : ι ↦ |x j|) (Finset.mem_univ i)
  have hterm : ∀ i, |x i * y i| ≤ linftyNorm x * |y i| := by
    intro i
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hxi i) (abs_nonneg (y i))
  have hlin_nonneg : 0 ≤ linftyNorm x := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact le_trans (abs_nonneg (x i)) (hxi i)
  calc
    (⟪x, y⟫ₚ : 𝕜) = ∑ i, x i * y i := rfl
    _ ≤ |∑ i, x i * y i| := le_abs_self _
    _ ≤ ∑ i, |x i * y i| := by
      simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : ι ↦ x i * y i))
    _ ≤ ∑ i, linftyNorm x * |y i| := Finset.sum_le_sum (fun i _ ↦ hterm i)
    _ = linftyNorm x * ∑ i, |y i| := by rw [Finset.mul_sum]
    _ ≤ linftyNorm x * 1 := by
      exact mul_le_mul_of_nonneg_left hsum_le_one hlin_nonneg
    _ = linftyNorm x := by simp

/-- Canonical owner-side theorem for Text 5.5.0.5: the support function of the coordinate
`ℓ¹` unit ball is the coordinate `ℓ∞` norm. -/
theorem supportFunction_coordinateL1Ball_eq_linftyNorm (x : E) :
    δᵛ(x | (coordinateL1Ball : Set E)) = ((linftyNorm x : 𝕜) : WithTopBot 𝕜) := by
  classical
  by_cases hι : IsEmpty ι
  · have hx0 : x = (0 : E) := Subsingleton.elim _ _
    subst hx0
    have hlin0 : linftyNorm (0 : E) = 0 := by
      simp [linftyNorm]
    rw [supportFunction_def, hlin0]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro y
      have hy_le : (∑ i, (0 : E) i * (y : E) i) ≤ 0 := by
        simp
      change
        (((∑ i, (0 : E) i * (y : E) i : 𝕜) : WithTopBot 𝕜) ≤
          (0 : WithTopBot 𝕜))
      exact_mod_cast hy_le
    · refine le_iSup_of_le ⟨(0 : E), by simp [coordinateL1Ball]⟩ ?_
      have h0_le : (0 : 𝕜) ≤ (∑ i, (0 : E) i * (0 : E) i) := by
        simp
      change
        ((0 : WithTopBot 𝕜) ≤
          ((∑ i, (0 : E) i * (0 : E) i : 𝕜) : WithTopBot 𝕜))
      exact_mod_cast h0_le
  · have hnonempty : Nonempty ι := not_isEmpty_iff.mp hι
    letI : Nonempty ι := hnonempty
    obtain ⟨i, -, hi_sup⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |x j|)
    have hi_sup : linftyNorm x = |x i| := by
      rw [linftyNorm_eq_sup'_univ_abs x]
      exact hi_sup
    rw [supportFunction_def]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro y
      change
        (((⟪x, (y : E)⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤
          ((linftyNorm x : 𝕜) : WithTopBot 𝕜))
      exact_mod_cast pairing_le_linftyNorm_of_mem_coordinateL1Ball x y.1 y.2
    · rw [hi_sup]
      let t : 𝕜 := if 0 ≤ x i then (1 : 𝕜) else -1
      let y0 : E := fun j ↦ if j = i then t else 0
      have hy0 : y0 ∈ coordinateL1Ball := by
        change (∑ j, |y0 j|) ≤ 1
        have hsum : (∑ j, |y0 j|) = |t| := by
          have hif : ∀ j : ι, |(if j = i then t else 0 : 𝕜)| = (if j = i then |t| else 0) := by
            intro j
            by_cases h : j = i <;> simp [h]
          calc
            (∑ j, |y0 j|) = ∑ j, |(if j = i then t else 0 : 𝕜)| := by
              simp [y0]
            _ = ∑ j, (if j = i then |t| else 0) := by
              exact Finset.sum_congr rfl (fun j _ ↦ hif j)
            _ = |t| := by
              simp [Finset.sum_ite_eq', Finset.mem_univ]
        have ht_abs : |t| = (1 : 𝕜) := by
          by_cases hnonneg : 0 ≤ x i <;> simp [t, hnonneg]
        calc
          (∑ j, |y0 j|) = |t| := hsum
          _ = (1 : 𝕜) := ht_abs
          _ ≤ 1 := le_rfl
      refine le_iSup_of_le ⟨y0, hy0⟩ ?_
      have hmul : x i * t = |x i| := by
        by_cases hnonneg : 0 ≤ x i
        · simp [t, hnonneg, abs_of_nonneg]
        · have hneg : x i < 0 := lt_of_not_ge hnonneg
          simp [t, hnonneg, abs_of_neg hneg]
      have hpair : (⟪x, y0⟫ₚ : 𝕜) = |x i| := by
        have hif : ∀ j : ι, x j * y0 j = (if j = i then x i * t else 0) := by
          intro j
          by_cases h : j = i <;> simp [y0, h, t]
        calc
          (⟪x, y0⟫ₚ : 𝕜) = ∑ j, x j * y0 j := rfl
          _ = ∑ j, (if j = i then x i * t else 0) := by
            exact Finset.sum_congr rfl (fun j _ ↦ hif j)
          _ = x i * t := by
            simp [Finset.sum_ite_eq', Finset.mem_univ]
          _ = |x i| := hmul
      have hle : |x i| ≤ (⟪x, y0⟫ₚ : 𝕜) := by
        simp [hpair]
      change
        (((|x i| : 𝕜) : WithTopBot 𝕜) ≤
          (((⟪x, y0⟫ₚ : 𝕜) : WithTopBot 𝕜)))
      exact_mod_cast hle

/-- Function-valued bridge form of `supportFunction_coordinateL1Ball_eq_linftyNorm`. -/
theorem supportFunction_coordinateL1Ball_eq_linftyNorm_fun :
    (δᵛ(· | (coordinateL1Ball : Set E)) : E → WithTopBot 𝕜) =
      fun x ↦ ((linftyNorm x : 𝕜) : WithTopBot 𝕜) := by
  funext x
  exact supportFunction_coordinateL1Ball_eq_linftyNorm x

-- Proof sketch: combine `supportFunction_coordinateL1Ball_eq_linftyNorm` with the finite
-- coordinate-maximum formula `linftyNorm_eq_sup'_univ_abs`.
/-- Text 5.5.0.5: the support function of the coordinate `ℓ¹` unit ball
`{y | ∑ i, |y i| ≤ 1}` is the finite coordinate maximum `max_i |x i|`. -/
theorem supportFunction_coordinateL1Ball_eq_sup'_univ_abs [Nonempty ι] (x : E) :
    δᵛ(x | (coordinateL1Ball : Set E)) =
      (((Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ (|x i| : 𝕜)) : 𝕜) :
        WithTopBot 𝕜) := by
  rw [supportFunction_coordinateL1Ball_eq_linftyNorm x]
  exact congrArg (fun r : 𝕜 ↦ (r : WithTopBot 𝕜)) (linftyNorm_eq_sup'_univ_abs x)

end

/-! ### Text_5_5_0_6 (from Chap01) -/
noncomputable section

open Metric
open scoped ENNReal NNReal Rockafellar

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Canonical owner-side formula: Rockafellar's gauge of the closed unit ball is the extended
norm. -/
theorem egauge_closedBall_zero_one_eq_enorm (x : X) :
    γ(x | closedBall (0 : X) 1) = ‖x‖ₑ := by
  refine le_antisymm ?_ ?_
  · simpa [enorm_eq_nnnorm] using
      (egauge_le_of_mem_smul (x := x) (s := closedBall (0 : X) 1) <| by
        refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
        · simpa using inv_norm_smul_mem_unitClosedBall x
        · by_cases hx : x = 0
          · simp [hx]
          · change ((‖x‖₊ : ℝ) • (‖x‖⁻¹ • x)) = x
            rw [smul_smul]
            change (‖x‖ * ‖x‖⁻¹) • x = x
            simp [norm_ne_zero_iff.mpr hx])
  · rw [le_egauge_iff]
    intro c hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [mem_closedBall_zero_iff] at hy
    have h : ‖((c : ℝ) • y)‖₊ ≤ c := by
      calc
        ‖((c : ℝ) • y)‖₊ = ‖(c : ℝ)‖₊ * ‖y‖₊ := by
          simpa using nnnorm_smul (c : ℝ) y
        _ = c * ‖y‖₊ := by simp
        _ ≤ c * 1 := by gcongr; simpa using hy
        _ = c := by simp
    simpa [enorm_eq_nnnorm] using h

end

section

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [SeminormedAddCommGroup X]

local notation "E" => ι → X

/-
Source/core/bridge triage:
- `source-facing`: the intrinsic owner-side proposition fixes the centered unit cube as the closed
  sup-norm unit ball on a finite coordinate family and identifies Rockafellar's gauge of this set
  with the canonical sup norm.
- `core/canonical`: the chapter owner for Rockafellar's gauge is `γ(x | C) = egauge ℝ≥0 C x` from
  `Defintion_4_8_2`.
- `bridge/view`: the source-facing centered-cube language is bridged directly through the intrinsic
  owner `closedBall (0 : E) 1`; coordinate inequalities are recovered by a downstream bridge
  theorem.
- Domain-style sampling used here: the chapter owner `γ(x | C) = egauge ℝ≥0 C x`,
  mathlib's `egauge`, `egauge_le_of_mem_smul`, `le_egauge_iff`,
  `inv_norm_smul_mem_unitClosedBall`, and `pi_norm_le_iff_of_nonneg`.
- Primitive data vs derived API: the intrinsic closed-ball owner is the primitive set datum; the
  coordinate formulas are bridge theorems.
- Layer target: `core/canonical`; keep theorem surfaces on the intrinsic owner and expose the
  coordinate inequality surface through bridge API.
-/

/-- Intrinsic bridge for `centeredUnitCube`: closed-ball membership is equivalent to pointwise norm
bounds. -/
theorem mem_centeredUnitCube_iff_norm (y : E) :
    y ∈ (closedBall (0 : E) 1 : Set E) ↔ ∀ i : ι, ‖y i‖ ≤ 1 := by
  rw [mem_closedBall_zero_iff]
  exact pi_norm_le_iff_of_nonneg zero_le_one

end

section

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "E" => ι → X

-- Proof sketch: specialize the canonical owner theorem
-- `egauge_closedBall_zero_one_eq_enorm`.
/-- Text 5.5.0.6 (canonical owner-side form): for any finite coordinate family in a real normed
space, Rockafellar's gauge `γ(· | C)` of the centered unit cube is the canonical sup norm. -/
theorem egauge_centeredUnitCube_eq_enorm (x : E) :
    γ(x | (closedBall (0 : E) 1 : Set E)) = ‖x‖ₑ := by
  simpa using (egauge_closedBall_zero_one_eq_enorm (x := x))

end

section

variable {ι : Type*} [Fintype ι]

local notation "E" => ι → ℝ

/-- Source-facing real-coordinate bridge for `centeredUnitCube`: coordinate inequalities are
equivalent to closed-ball membership. -/
theorem mem_centeredUnitCube (y : E) :
    y ∈ (closedBall (0 : E) 1 : Set E) ↔ ∀ i : ι, -(1 : ℝ) ≤ y i ∧ y i ≤ 1 := by
  rw [mem_centeredUnitCube_iff_norm]
  constructor
  · intro hy i
    simpa [Real.norm_eq_abs, abs_le] using hy i
  · intro hy i
    simpa [Real.norm_eq_abs, abs_le] using hy i

end
end

/-! ### Text_5_5_1 (from Chap01) -/
noncomputable section

universe u v w

section

variable {E : Type u} {𝕜 : Type v} {α : Type w}
variable [Semiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

/-- Helper for Text 5.5.1: the `WithTopBot α`-valued heights of the vertical fiber of `F`
above `x`. -/
def verticalHeights (F : Set (E × α)) (x : E) : Set (WithTopBot α) :=
  ((↑) : α → WithTopBot α) '' {μ : α | (x, μ) ∈ F}

/-- Helper for Text 5.5.1: the function attached to `F` by taking the infimum of the
vertical heights above each base point. -/
noncomputable def verticalInfimum [ConditionallyCompleteLattice α] (F : Set (E × α)) :
    E → WithTopBot α :=
  fun x ↦ sInf (verticalHeights F x)

omit [AddCommMonoid E] in
/-- Helper for Text 5.5.1: `verticalInfimum` is definitionally the infimum of
`verticalHeights`. -/
theorem verticalInfimum_eq_sInf_verticalHeights [ConditionallyCompleteLattice α]
    (F : Set (E × α)) (x : E) :
    verticalInfimum (E := E) F x = sInf (verticalHeights (E := E) F x) :=
  rfl

end Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.1 defines the convex hull `conv(g)` of a function `g` by taking the
  infimum of the vertical fiber in the convex hull of the epigraph of `g`.
- `core/canonical`: the owner abstractions are the epigraph owner `epi` from Definition 4.1, the
  canonical set owner `Function.convexEpigraph g := _root_.convexHull 𝕜 (epi g)`, and
  `Function.verticalInfimum : Set (E × α) → E → WithTopBot α` from Theorem 5.3.
- Primitive data vs derived API: the function `g` and the canonical set owner
  `Function.convexEpigraph g` are primitive; the displayed infimum formula is the first companion
  specification.
- Ambient minimization: the convex-epigraph owner itself only uses convex-hull operations, so it
  lives at the weaker `PartialOrder` layer on `𝕜`; only the vertical-infimum formula for `conv(g)`
  needs conditional completeness on the codomain layer.

Domain-style sampling used here:
- `epi`;
- `Function.convexEpigraph`;
- `Function.verticalInfimum`;
- `_root_.convexHull`;
- `Function.verticalHeights`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`.
- Layer target: `source-facing`; the public definition remains Rockafellar's `conv(g)`, while the
  chapter owners `epi`, `Function.convexEpigraph`, and `Function.verticalInfimum` supply the
  canonical construction.
-/

section ConvexEpigraph

variable [AddCommMonoid α] [Module 𝕜 α] [LE α]
variable [PartialOrder 𝕜]

/-- Helper for Text 5.5.1: the canonical set owner for the convex hull of the epigraph of `g`. -/
def Function.convexEpigraph (g : E → WithTopBot α) : Set (E × α) :=
  _root_.convexHull 𝕜 (epi g)

-- Proof sketch: `Function.convexEpigraph g` is literally a convex hull, so the ambient
-- convexity theorem `convex_convexHull` applies immediately once the scalar owner is fixed.
/-- Helper for Text 5.5.1: the canonical set owner `Function.convexEpigraph g` is convex. -/
theorem Function.convex_convexEpigraph (g : E → WithTopBot α) :
    Convex 𝕜 (Function.convexEpigraph (𝕜 := 𝕜) g) := by
  simpa [Function.convexEpigraph] using
    (convex_convexHull 𝕜 (epi g))

end ConvexEpigraph

section ConvexHull

variable [AddCommMonoid α] [Module 𝕜 α]
variable [PartialOrder 𝕜] [ConditionallyCompleteLattice α]

/-- Text 5.5.1: the convex hull `conv(g)` of a function `g` is the function obtained by taking,
for each `x`, the infimum of the codomain heights in the convex hull of the epigraph of `g`. -/
def Function.convexHull (g : E → WithTopBot α) : E → WithTopBot α :=
  Function.verticalInfimum (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g)

/-- Helper for Text 5.5.1: Rockafellar notation for the function convex hull. -/
notation:max "conv(" g ")" => Function.convexHull g

-- Proof sketch: this is the canonical owner-level restatement of the definition, so `rfl`
-- closes the goal once the scalar parameter of `Function.convexEpigraph` is fixed.
/-- Helper for Text 5.5.1: in canonical-owner form, `conv(g)` is the vertical infimum of
`Function.convexEpigraph g`. -/
theorem Function.convexHull_eq_verticalInfimum_convexEpigraph
    (g : E → WithTopBot α) :
    Function.convexHull (E := E) (𝕜 := 𝕜) (α := α) g =
      Function.verticalInfimum (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g) := by
  rfl

-- Proof sketch: rewrite the canonical owner `Function.convexEpigraph g` back to the raw set
-- expression `_root_.convexHull 𝕜 (epi g)` used in the textbook display formula.
/-- Helper for Text 5.5.1: bridge/view form with the raw set expression
`_root_.convexHull 𝕜 (epi g)`. -/
theorem Function.convexHull_eq_verticalInfimum_convexHull_epigraph
    (g : E → WithTopBot α) :
    Function.convexHull (E := E) (𝕜 := 𝕜) (α := α) g =
      Function.verticalInfimum (E := E) (α := α) (_root_.convexHull 𝕜 (epi g)) := by
  simpa [Function.convexEpigraph] using
    (Function.convexHull_eq_verticalInfimum_convexEpigraph
      (E := E) (𝕜 := 𝕜) (α := α) g)

-- Proof sketch: unfold `Function.convexHull` to `Function.verticalInfimum` of
-- `Function.convexEpigraph g`, then use `verticalInfimum_eq_sInf_verticalHeights`.
/-- Helper for Text 5.5.1: the value of `conv(g)` at `x` is the infimum of the intrinsic height owner
`Function.verticalHeights` above `x` for `Function.convexEpigraph g`. -/
theorem Function.convexHull_eq_sInf_verticalHeights
    (g : E → WithTopBot α) (x : E) :
    Function.convexHull (E := E) (𝕜 := 𝕜) (α := α) g x =
      sInf (Function.verticalHeights (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g) x) := by
  simpa [Function.convexHull] using
    (Function.verticalInfimum_eq_sInf_verticalHeights
      (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g) x)

end ConvexHull

end

/-! ### Text_5_5_2 (from Chap01) -/
noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.2 states that the function `f = conv(g)` introduced in Text 5.5.1 is
  convex.
- `core/canonical`: the owner abstraction for the conclusion is the chapter predicate
  `Function.IsConvex : (E → WithBotTop 𝕜) → Prop` from Theorem 4.2.
- `bridge/view`: the source-facing owner `conv(g)` from Text 5.5.1 is defined canonically as
  `Function.verticalInfimum (Function.convexEpigraph g)`.
- Primitive data vs derived API: the function `conv(g)` is primitive upstream; its convexity is
  the derived statement here.
- Ambient minimization: the statement uses only the chapter owners `Function.convexHull`,
  `Function.verticalInfimum`, and `Function.IsConvex`, all of which already live on an arbitrary
  additive commutative `𝕜`-module `E`, so any concrete finite-dimensional coordinate model would be
  an unnecessary specialization here.
- Domain-style sampling used here: `Function.IsConvex`, `Function.convexHull`,
  `Function.convexEpigraph`, `Function.isConvex_verticalInfimum`,
  and `_root_.convexHull`.
- Layer target: `source-facing`; this file keeps the textbook theorem about `conv(g)` and reuses
  the earlier chapter owner declarations directly.
-/

namespace Function

/-- Helper for Text 5.5.2: import-safe owner for the convex hull of the epigraph of `g`. -/
def convexEpigraph (g : E → WithBotTop 𝕜) : Set (E × 𝕜) :=
  _root_.convexHull 𝕜 (epi g)

/-- Helper for Text 5.5.2: import-safe owner for Rockafellar's function convex hull `conv(g)`. -/
def convexHull (g : E → WithBotTop 𝕜) : E → WithBotTop 𝕜 :=
  verticalInfimum (Function.convexEpigraph (𝕜 := 𝕜) g)

/-- Helper for Text 5.5.2: Rockafellar notation for the function convex hull. -/
notation:max "conv(" g ")" => Function.convexHull g

-- Route correction: `Text_5_5_1` duplicates the `verticalInfimum` owner from `Theorem_5_3`,
-- so this file keeps the minimal Text 5.5.1 owner surface locally and still follows the same
-- theorem-5.3 proof route.
-- Proof sketch: rewrite `conv(g)` to the vertical infimum of the convex hull of `epi g`,
-- then apply Theorem 5.3 to that convex set.
/-- Text 5.5.2: the convex hull `conv(g)` of an extended-ordered-valued function `g` is convex. -/
theorem isConvex_conv (g : E → WithBotTop 𝕜) : (conv(g)).IsConvex 𝕜 := by
  -- First identify `conv(g)` with the vertical infimum of the convex hull of `epi g)`.
  rw [Function.convexHull]
  -- Then invoke Theorem 5.3 on the convex hull of the epigraph.
  exact Function.isConvex_verticalInfimum <| by
    simpa [Function.convexEpigraph] using (convex_convexHull 𝕜 (epi g))

end Function

end

/-! ### Text_5_5_3 (from Chap01) -/
noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

/-- Canonical owner for the convex minorants of `g`. -/
def convexMinorants (g : E → WithBotTop 𝕜) : Set (E → WithBotTop 𝕜) :=
  {h | h.IsConvex 𝕜 ∧ h ≤ g}

end Function
end

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.3 states that `f = conv(g)` is the greatest convex minorant of `g`,
  equivalently the greatest convex function majorized by `g`.
- `core/canonical`: the owner abstractions already present in this section are
  `conv(g)` from Text 5.5.1 and
  `Function.IsConvex : (E → WithBotTop 𝕜) → Prop` from Theorem 4.2.
- `bridge/view`: the order-theoretic phrase "greatest convex minorant of `g`" is most naturally
  expressed by `IsGreatest (Function.convexMinorants g) (conv(g))`.
- Primitive data vs derived API: the primitive input is `g`; convexity of `conv(g)` comes from
  Text 5.5.2, and maximality among convex minorants is the derived API here.
- Ambient minimization: the owner construction and convexity theorem already live on an arbitrary
  additive commutative `𝕜`-module `E`, so specializing back to `EuclideanSpace ℝ (Fin n)` would
  only reintroduce a concrete model layer with no mathematical role in this item.

Domain-style sampling used here:
- `conv`;
- `Function.IsConvex`;
- `Function.IsConvex.convex_epigraph`;
- `IsGreatest`.
- Layer target: `source-facing`; this file keeps the new greatest-minorant statement and reuses
  the earlier chapter owner declarations directly instead of redefining them locally.
-/

namespace Function

/-- Every convex minorant of `g` lies below `conv(g)`. -/
theorem le_conv_of_le
    {g h : E → WithBotTop 𝕜} (hh_convex : h.IsConvex 𝕜) (hh_le : h ≤ g) :
    h ≤ conv(g) := by
  have hsubset : epi g ⊆ epi h := by
    rintro ⟨x, μ⟩ hx
    rcases mem_epi_restrict_iff.mp hx with ⟨-, hxμ⟩
    exact mem_epi_restrict_iff.mpr ⟨by simp, (hh_le x).trans hxμ⟩
  have hh_epi : Convex 𝕜 (epi h) := by
    simpa [epi_univ_eq_setOf_le] using hh_convex.convex_epigraph
  rw [convexHull]
  exact le_verticalInfimum_of_subset_epi <|
    convexHull_min hsubset hh_epi

end Function

end

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

section NoBotOrder

variable [NoBotOrder 𝕜]

/-- `conv(g)` is a pointwise minorant of `g`. -/
theorem conv_le
    (g : E → WithBotTop 𝕜) :
    conv(g) ≤ g := by
  rw [convexHull]
  exact verticalInfimum_le_of_epi_subset (subset_convexHull 𝕜 (epi g))

/-- Order-theoretic maximality principle: if `conv(g)` is convex, then it is the greatest convex
minorant of `g`. -/
theorem isGreatest_conv_minorant_of_isConvex
    (g : E → WithBotTop 𝕜) (hconv : (conv(g)).IsConvex 𝕜) :
    IsGreatest (convexMinorants g) (conv(g)) := by
  refine ⟨⟨hconv, conv_le g⟩, ?_⟩
  intro h hh
  exact le_conv_of_le hh.1 hh.2

end NoBotOrder

end Function

end

section

variable {E : Type u} {𝕜 : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

-- Proof sketch: apply the primitive maximality theorem
-- `isGreatest_conv_minorant_of_isConvex` using the convexity bridge
-- `isConvex_conv g` from Text 5.5.2.
/-- Text 5.5.3: `conv(g)` is the greatest convex minorant of `g`, equivalently the
greatest convex function majorized by `g`. -/
theorem isGreatest_conv_minorant
    (g : E → WithBotTop 𝕜) :
    IsGreatest (convexMinorants g) (conv(g)) :=
  isGreatest_conv_minorant_of_isConvex g (isConvex_conv g)

end Function

end

/-! ### Text_5_5_4 (from Chap01) -/
noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [Preorder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.4 identifies the already-defined convex hull `conv(g)` with the
  infimum of weighted sums of function values over all finite convex-combination representations
  of `x`.
- `core/canonical`: the owner abstraction already introduced earlier in the chapter is
  `conv(g)`. On the point side, the canonical finite convex-combination owners already present
  upstream are `StdSimplex 𝕜 ι` for the weights, the owner-side finite sum `w.sum`,
  `convexCombination` for the represented point, and the `StdSimplex` owner packaging from
  Definition 2.2.10 / Theorem 2.3.
- `bridge/view`: Theorem 2.3 identifies membership in
  `convexHull 𝕜 {p : E × 𝕜 | g p.1 ≤ p.2}` with finite convex combinations of epigraph points.
  Rewriting the point coordinate through `convexCombination_eq_sum` turns the vertical-fiber
  formula from Text 5.5.1 into the displayed infimum over simplex finite sums.
- Primitive data vs derived API: the primitive input is the function `g`; the finite
  convex-combination value formula is a derived specification of `conv(g)`, while the
  simplex coefficients and the point-side convex-hull certificate are reused upstream owners.

Domain-style sampling used here:
- `Function.convexHull_eq_sInf_verticalHeights`;
- `Finset.mem_convexHull'`;
- `StdSimplex`;
- `StdSimplex.sum`;
- `convexCombination_eq_sum`.
- Ambient minimization: the finite-convex-combination formula only uses the module structure
  already present in `Function.convexHull`, so the canonical ambient owner level is an arbitrary
  `𝕜`-module `E`, not the concrete coordinate model `EuclideanSpace ℝ (Fin n)`. Using the
  stronger affine-space owner `ConvexSpace.convexCombination` here would force
  `[AddCommGroup E]`, so the public point equation stays in the sum form compatible with the
  weaker source-faithful ambient assumptions.
- Layer target: `bridge/view`; this file reuses the owner declarations from Text 5.5.1 and keeps
  only the new convex-combination formula.
-/

-- Proof sketch: start from `Function.convexHull_eq_sInf_verticalHeights` and unfold the intrinsic
-- height owner. By Theorem 2.3,
-- membership of `(x, μ)` in `convexHull 𝕜 {p : E × 𝕜 | g p.1 ≤ p.2}` is equivalent to a finite
-- convex combination of epigraph points with intrinsically finite simplex
-- weights `w : StdSimplex 𝕜 ι` and points `z : ι → E`. Rewriting the point coordinate with
-- `convexCombination_eq_sum` gives the textbook weighted-sum condition.
-- Minimizing the individual heights down to `g i` yields the displayed infimum, and the formula
-- remains meaningful in `WithBotTop 𝕜` even when some summands are `⊥`.

/-- Canonical owner for admissible finite convex-combination values of `g` at `x`. -/
def Function.convexCombinationValues (g : E → WithBotTop 𝕜) (x : E) : Set (WithBotTop 𝕜) :=
  {r : WithBotTop 𝕜 |
    ∃ (ι : Type*) (w : StdSimplex 𝕜 ι) (z : ι → E),
      x = w.sum (fun i a ↦ a • z i) ∧
        r = (by
          classical
          exact w.sum (fun i a ↦ (a : WithBotTop 𝕜) * g (z i)) : WithBotTop 𝕜)}

end

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.5.4: `conv(g)(x)` is the infimum of the weighted sums `∑ i, λ i * g (x i)` over all
finite convex-combination representations `x = ∑ i, λ i • x i`. -/
theorem Function.convexHull_eq_sInf_convexCombination_values
    (g : E → WithBotTop 𝕜) (x : E) :
    conv(g) x = sInf (Function.convexCombinationValues g x) := sorry

/-- Expanded set-builder view of
`Function.convexHull_eq_sInf_convexCombination_values`. -/
theorem Function.convexHull_eq_sInf_convexCombination_values_set
    (g : E → WithBotTop 𝕜) (x : E) :
    conv(g) x =
      sInf
        {r : WithBotTop 𝕜 |
          ∃ (ι : Type*) (w : StdSimplex 𝕜 ι) (z : ι → E),
            x = w.sum (fun i a ↦ a • z i) ∧
              r = (by
                classical
                exact w.sum (fun i a ↦ (a : WithBotTop 𝕜) * g (z i)) : WithBotTop 𝕜)} := by
  simpa [Function.convexCombinationValues] using
    Function.convexHull_eq_sInf_convexCombination_values (g := g) x

end

/-! ### Text_5_5_5 (from Chap01) -/
noncomputable section

universe u v w

section

variable {E : Type u} {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] {I : Sort v}

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.5 identifies the convex hull of an arbitrary family of functions with
  the vertical infimum attached to the convex hull of the union of their scalar epigraphs.
- `core/canonical`: besides `conv(g)` from Text 5.5.1, theorem surfaces stay directly on the
  existing canonical set owners `_root_.convexHull` and `epi`.
- `bridge/view`: the indexed-family source expression is the canonical owner expression itself:
  `_root_.convexHull 𝕜 (⋃ i, epi (f i))`.
- Primitive data vs derived API: the indexed family `f : I → E → WithTopBot 𝕜` is primitive; the
  vertical-infimum identity for `conv(⨅ i, f i)` is the source-facing bridge theorem, and the
  intrinsic `verticalHeights` value formula is its canonical companion.

Domain-style sampling used here:
- `Function.convexHull`;
- `Function.isGreatest_conv_minorant`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`;
- `_root_.convexHull`;
- `epi`.
- Ambient minimization: the family convex-hull construction only uses convex hulls and pointwise
  infima in `E × 𝕜`, so it should live on the same arbitrary `𝕜`-module ambient as the
  single-function owner `Function.convexHull`.
- Layer target: `core/canonical` on existing owners without introducing a new owner alias.
-/

/-- Text 5.5.5: the convex hull of the pointwise infimum of a family is the vertical infimum
attached to the convex hull of the union of the scalar epigraphs. -/
theorem conv_iInf_eq_verticalInfimum_convexHull_iUnion_epi
    (f : I → E → WithTopBot 𝕜) :
    conv(⨅ i, f i) =
      verticalInfimum (_root_.convexHull 𝕜 (⋃ i, epi (f i))) := by
  let g : E → WithTopBot 𝕜 := ⨅ i : I, f i
  let U : Set (E × 𝕜) := ⋃ i, epi (f i)
  have hmain : conv(g) = verticalInfimum (_root_.convexHull 𝕜 U) := by
    refine le_antisymm ?_ ?_
    · refine le_verticalInfimum_of_subset_epi ?_
      apply convexHull_min
      · intro p hp
        rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
        rcases mem_epi_restrict_iff.mp hi with ⟨_, hip⟩
        have hconv : conv(g) ≤ f i :=
          (Function.conv_le g).trans (iInf_le (fun j ↦ f j) i)
        exact mem_epi_restrict_iff.mpr ⟨by simp, (hconv p.1).trans hip⟩
      · simpa [epi_univ_eq_setOf_le] using
          (isConvex_conv g).convex_epigraph
    · exact Function.le_conv_of_le
        (Function.isConvex_verticalInfimum (convex_convexHull 𝕜 U))
        (by
          refine le_iInf fun i ↦ ?_
          exact verticalInfimum_le_of_epi_subset <|
            Set.Subset.trans
              (by intro p hp; exact Set.mem_iUnion.mpr ⟨i, hp⟩)
              (subset_convexHull 𝕜 U))
  simpa [g, U] using hmain

-- Proof sketch: Text 5.5.5 identifies the family convex hull with the vertical infimum attached
-- to `_root_.convexHull 𝕜 (⋃ i, epi (f i))`.
-- The displayed formula is then the intrinsic owner-level
-- specification `verticalInfimum_eq_sInf_verticalHeights`.
/-- The value of `conv(⨅ i, f i)` at `x` is the infimum of the intrinsic height owner
`Function.verticalHeights` above `x` for the convex hull of the family epigraph union. -/
theorem conv_iInf_apply_eq_sInf_verticalHeights_convexHull_iUnion_epi
    (f : I → E → WithTopBot 𝕜) (x : E) :
    conv(⨅ i, f i) x =
      sInf (verticalHeights (_root_.convexHull 𝕜 (⋃ i, epi (f i))) x) := by
  rw [conv_iInf_eq_verticalInfimum_convexHull_iUnion_epi,
    verticalInfimum_eq_sInf_verticalHeights]

end Function

end
