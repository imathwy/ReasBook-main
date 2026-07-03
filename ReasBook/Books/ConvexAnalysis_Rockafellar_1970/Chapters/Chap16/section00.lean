import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_16_0_1 (from Chap03) -/
noncomputable section

open scoped Pointwise Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.1 records four standard transformation rules for Fenchel conjugates
  and support functions under translation, addition of a linear form, and addition of a constant.
- `core/canonical`: the owner declarations already present earlier in the chapter are
  `convexConjugate_affineChange`,
  `supportFunction_set_add_apply`, and `supportFunction_def`.
- `bridge/view`: each displayed source formula is a thin specialization of those owners, so this
  file keeps the four source-facing formulas explicitly while deriving them directly from the
  upstream owner API instead of introducing a second owner layer.

Domain-style sampling used here:
- `convexConjugate_affineChange`;
- `supportFunction_set_add_apply`;
- `supportFunction_def`.

Primitive data vs derived API:
- primitive owner data is already upstream: the affine-change owners for Fenchel conjugates and
  the pointwise Minkowski-sum support-function theorem;
- derived source-facing API: the direct translation formula, the pure linear-form specialization,
  the pure constant specialization, and the singleton-translation specialization.

Layer target: `bridge/view`.
-/

section Conjugate

variable {α : Type*} [AddCommGroup α]
variable {X : Type*} {Y : Type*}
variable [AddCommGroup X] [AddCommGroup Y]
variable [HasPairing X Y (WithTopBot α)]
variable [HasPairingAddLeft X Y (WithTopBot α)]
variable [HasPairingSubRight X Y (WithTopBot α)]
variable [SupSet (WithTopBot α)]

-- Proof sketch: specialize the chapter affine-change owner with both bijections equal to
-- the identity, zero linear perturbation, and zero constant term.
/-- Text 16.0.1 (1): translating the argument of `h` by `a` adds the linear form
`x⋆ ↦ ⟪a, x⋆⟫` to the conjugate. -/
theorem convexConjugate_translate
    (h : X → WithTopBot α) (a : X) :
    (fun x ↦ h (x - a))⋆ =
      fun xStar : Y ↦ h⋆ xStar + ⟪a, xStar⟫ₚ := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) a (0 : Y) (0 : WithTopBot α))

-- Proof sketch: specialize the same affine-change owner to zero translation and zero constant.
/-- Text 16.0.1 (2): adding the pairing form `x ↦ ⟪x, a⋆⟫ₚ` shifts the dual variable by `-a⋆`. -/
theorem convexConjugate_add_inner
    [HasPairingZeroLeft X Y (WithTopBot α)]
    (h : X → WithTopBot α) (aStar : Y) :
    (fun x ↦ h x + ⟪x, aStar⟫ₚ)⋆ = fun xStar ↦ h⋆ (xStar - aStar) := by
  simpa [pairing_zero_left, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) (0 : X) aStar (0 : WithTopBot α))

-- Proof sketch: specialize the same affine-change owner to zero translation and zero pairing
-- perturbation.
/-- Text 16.0.1 (3): adding the constant `α` subtracts the same constant from the conjugate. -/
theorem convexConjugate_add_const
    [HasPairingZeroLeft X Y (WithTopBot α)]
    (h : X → WithTopBot α) (β : WithTopBot α) :
    (fun x ↦ h x + β : X → WithTopBot α)⋆ = fun xStar : Y ↦ h⋆ xStar - β := by
  simpa [pairing_zero_left, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) (0 : X) (0 : Y) β)

end Conjugate

section SupportFunction

variable {𝕜 : Type*} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {X : Type*} {Y : Type*}
variable [Add Y] [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]

-- Proof sketch: apply the owner Minkowski-sum theorem `supportFunction_set_add` with the
-- singleton `{a}` and rewrite the resulting singleton support value by
-- `supportFunction_singleton`.
/-- Text 16.0.1 (4), owner form: translating a set by `a` adds the linear form
`x⋆ ↦ ⟪x⋆, a⟫ₚ` to its support function. -/
theorem supportFunction_translate_set
    (C : Set Y) (a : Y) :
    (δᵛ(· | C + ({a} : Set Y)) : X → WithTopBot 𝕜) =
      fun xStar ↦ δᵛ(xStar | C) + (⟪xStar, a⟫ₚ : WithTopBot 𝕜) := by
  funext xStar
  simpa [supportFunction_singleton] using
    (supportFunction_set_add_apply C ({a} : Set Y) xStar)

/-- Text 16.0.1 (4), pointwise form: evaluating the translated support function at `x⋆` adds the
linear term `⟪x⋆, a⟫ₚ`. -/
theorem supportFunction_translate_set_apply
    (C : Set Y) (a : Y) (xStar : X) :
    (δᵛ(xStar | C + ({a} : Set Y)) : WithTopBot 𝕜) =
      δᵛ(xStar | C) + (⟪xStar, a⟫ₚ : WithTopBot 𝕜) := by
  simpa using congrFun (supportFunction_translate_set C a) xStar

end SupportFunction

/-! ### Text_16_0_2 (from Chap03) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {X : Type u} {Y : Type v}
variable {α : Type w}
variable [ConditionallyCompleteLattice α] [One α]
variable [HasPairing Y X α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.2 says that the polar `Cᵒ` of a convex set is the `1`-sublevel set
  of its support function `δ*(· | C)`.
- `core/canonical`: the project already exposes this notion as the canonical owner definition
  `Set.polar`.
- `bridge/view`: Rockafellar's notation `δ*(x* | C)` is represented by `supportFunction C xStar`,
  and here the source sentence is exposed directly as a theorem at the generalized pairing layer.

Domain-style sampling used here:
- the project definition `Set.polar` from `Text_14_0_5`;
- the support-function owner `supportFunction`, via notation `δᵛ[WithBotTop α](· | C)`.

Primitive data vs derived API:
- primitive input: a set `C`;
- primitive owner: the already-defined polar set `Set.polar C`;
- derived/source-facing view: the textbook level-set description
  `{xStar | δᵛ[WithBotTop α](xStar | C) ≤ 1}`.

Layer target: `core/canonical`.

The source's convexity hypothesis is redundant for this bare identification, so the existing owner
is kept and only the source-facing bridge theorem is exposed.
-/

namespace Set

-- Proof sketch: unfold `Set.polar`; membership in a preimage of `Set.Iic (1 : WithBotTop α)` is
-- exactly the corresponding support-function inequality.
/-- Text 16.0.2 (membership form): a dual point is in `Cᵒ[α]` iff the support function of `C`
at that point is at most `1`. This is the source-facing sublevel-set sentence at the canonical
pairing/extended-codomain layer. -/
theorem mem_polar_iff_supportFunction_le_one {C : Set X} {xStar : Y} :
    xStar ∈ Cᵒ[α] ↔
      (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ≤ (1 : WithBotTop α) := by
  change
    (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ∈ Set.Iic (1 : WithBotTop α) ↔
      (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ≤ (1 : WithBotTop α)
  simp

-- Proof sketch: extensionality reduces set equality to the previous membership theorem.
/-- Text 16.0.2 (set form): `Cᵒ[α]` is exactly the `1`-sublevel set of `δᵛ[WithBotTop α](· | C)`. -/
theorem polar_eq_supportFunction_sublevel (C : Set X) :
    Cᵒ[α] = {xStar : Y | (δᵛ[WithBotTop α](xStar | C) : WithBotTop α) ≤ (1 : WithBotTop α)} := by
  ext xStar
  exact mem_polar_iff_supportFunction_le_one

end Set

end

/-! ### Text_16_0_3 (from Chap03) -/
noncomputable section

open scoped Rockafellar

section

universe u v w z

variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [DenselyOrdered α] [NoBotOrder α] [NoTopOrder α] [Nonempty α]
variable [Zero FStar]
variable [HasPairing E EStar α] [HasPairing F FStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.3 is the first-coordinate specialization of Theorem 16.3.1:
  for `h(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)`, one gets `h*(ξ₁⋆) = f*(ξ₁⋆, 0)`.
- `core/canonical`: the owner abstractions are the linear-image owner `Function.linearImage`
  (notation `◁`) and Fenchel conjugation `convexConjugate` (notation `⋆`).
- `bridge/view`: the projection owner is the canonical product map `Prod.fst`, and the dual
  insertion map is `fun ξ₁⋆ : EStar ↦ (ξ₁⋆, 0)`.

Domain-style sampling used here:
- `convexConjugate_linearImage_eq_comp` from Theorem 16.3.1;
- canonical product owners `Prod.fst` and `fun ξ₁⋆ : EStar ↦ (ξ₁⋆, 0)`;
- product pairing decomposition `pairing_prod`.

Layer target: `source-facing`, with the pairing/product owner-level statement first; the scalar
specialization belongs downstream rather than in this source-item API surface.

Redundant-source-assumption elimination: the source says `f` is convex, but the specialization of
Theorem 16.3.1 remains valid for arbitrary `WithTopBot α`-valued `f`, so no convexity
hypothesis is kept in the public statement.

Primitive side condition: for this concrete projection/insertion specialization, the second
pairing must annihilate the zero dual element (`∀ x : F, ⟪x, 0⟫ₚ = 0`).
-/

-- Proof sketch: apply `convexConjugate_linearImage_eq_comp` with primal map
-- `Prod.fst` and dual map `fun ξ₁⋆ : EStar ↦ (ξ₁⋆, 0)`, verify the pairing compatibility by
-- `pairing_prod`, then evaluate at `ξ₁⋆`.
/-- Text 16.0.3 in owner-level function form: if `h` is the image of `f` under the projection
`(ξ₁, ξ₂) ↦ ξ₁`, then `h* = f* ∘ inl`, where `inl ξ₁⋆ = (ξ₁⋆, 0)`. -/
theorem convexConjugate_firstCoordinateProjectionImage_eq_comp_inl
    (f : E × F → WithTopBot α)
    (hpair_zero_right : ∀ x : F, (⟪x, (0 : FStar)⟫ₚ : α) = 0) :
    (Prod.fst ◁ f)⋆ = f⋆ ∘ (fun ξ₁Star : EStar ↦ (ξ₁Star, (0 : FStar))) := by
  simpa using
    (convexConjugate_linearImage_eq_comp
      (A := Prod.fst)
      (Astar := fun ξ₁Star : EStar ↦ (ξ₁Star, (0 : FStar)))
      (hA := by
        intro x yStar
        simp [pairing_prod, hpair_zero_right])
      (f := f))

/-- Text 16.0.3 in owner-level form: if `h` is the image of `f` under the projection
`(ξ₁, ξ₂) ↦ ξ₁`, so that `h(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)`, then
`h*(ξ₁⋆) = f*(ξ₁⋆, 0)`. -/
theorem convexConjugate_firstCoordinateProjectionImage_eq
    (f : E × F → WithTopBot α)
    (hpair_zero_right : ∀ x : F, (⟪x, (0 : FStar)⟫ₚ : α) = 0)
    (ξ₁Star : EStar) :
    (Prod.fst ◁ f)⋆ ξ₁Star = f⋆ (ξ₁Star, (0 : FStar)) := by
  simpa using
    congrFun
      (convexConjugate_firstCoordinateProjectionImage_eq_comp_inl
        (f := f) hpair_zero_right)
      ξ₁Star

end

/-! ### Text_16_0_4 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

universe u v

section

variable {E : Type u} {ι : Type v} {𝕜 : Type*}
variable [Field 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [HasLinearPairing E E 𝕜]

local notation "Y" => ι → 𝕜

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.4 studies functions on a finite-dimensional real linear pairing space
  `E`, specialized in the source to `R^n`, of the form
  `h(x) = ∑ i, gᵢ(⟪aᵢ, x⟫ₚ)` and identifies the conjugate `h*` through the dual-side infimum
  attached to the row map `A(x) = (⟪aᵢ, x⟫ₚ)_i` into the finite coordinate space
  `ι → 𝕜`, specialized in the source to `R^m`.
- `core/canonical`: the project owners are `convexConjugate`, `Function.linearImage`,
  `lowerSemicontinuousHull`, and the chapter convexity predicate `Function.IsConvex`; the textbook
  `A* g*` is therefore rendered by
  `Function.linearImage (coordinateDualLinearMap a) (convexConjugate g)`.
- `bridge/view`: the scalar functions `gᵢ : 𝕜 → WithBotTop 𝕜` already live on the canonical scalar
  owner
  `convexConjugate`, so the theorem surface is written directly with `(g i)⋆`. Any comparison with
  one-dimensional coordinate model is proof-internal only, while the coordinate sum
  `g(y) = ∑ i, gᵢ(yᵢ)` remains the concrete source-facing function on `ι → 𝕜`.

Domain-style sampling used here:
- `Function.linearImage` from Theorem 5.7;
- `lowerSemicontinuousHull` from Text 7.0.4;
- `convexConjugate` from Defn. 12.2;
- linear pairing owner `HasLinearPairing`.

Primitive data vs derived API:
- primitive inputs: the coefficient family `a : ι → E` and the scalar family
  `g : ι → 𝕜 → β` for an additive codomain `β`;
- primitive source-facing constructions: the row map `coordinateInnerLinearMap a` and the
  separable sum `separableCoordinateSum g`;
- derived API: the source-facing function `coordinateLinearCombination a g`, the dual-map
  formula, the separable-conjugate formula, the owner-style relative-interior bridge for
  `riDom[𝕜](separableCoordinateSum g)`, the closure identity for `h*`, the exact formula under
  the relative-interior hypothesis, and the attainment clause. The public regularity hypotheses are
  kept on the chapter owner predicate `Function.IsConvex`.

Layer target: `source-facing`, stated directly with the canonical owners
`convexConjugate`, `Function.linearImage`, and `lowerSemicontinuousHull`.
-/

/-- The linear map `A : E → (ι → 𝕜)`, specialized in the source to
`A : R^n → R^m`, with `i`-th coordinate `x ↦ ⟪aᵢ, x⟫ₚ`. -/
def coordinateInnerLinearMap (a : ι → E) : E →ₗ[𝕜] Y :=
  LinearMap.pi fun i ↦ HasLinearPairing.pairingLinear (a i)

-- Proof sketch: unfold `coordinateInnerLinearMap` and read off the `i`-th coordinate of the
-- product linear map.
/-- The `i`-th coordinate of `coordinateInnerLinearMap a x` is `⟪aᵢ, x⟫ₚ`. -/
@[simp]
theorem coordinateInnerLinearMap_apply (a : ι → E) (x : E) (i : ι) :
    coordinateInnerLinearMap a x i = (⟪a i, x⟫ₚ : 𝕜) := by
  simp [coordinateInnerLinearMap, HasLinearPairing.pairing_eq_pairingLinear]

/- The source's `R^m` is rendered here by the canonical finite-coordinate space `ι → 𝕜`. -/
variable [Fintype ι]

/-- The separable coordinate sum `y ↦ ∑ i, gᵢ(yᵢ)` on the intrinsic function-space owner
`ι → α`. The duality theorems below specialize this owner to `α = 𝕜`, `β = WithBotTop 𝕜`, and
then bridge to the finite-coordinate model `ι → 𝕜` by reading each point coordinatewise. -/
def separableCoordinateSum {α β : Type*} [AddCommMonoid β]
    (g : ι → α → β) : (ι → α) → β :=
  fun y ↦ ∑ i, g i (y i)

-- Proof sketch: unfold `separableCoordinateSum`.
/-- Evaluating `separableCoordinateSum g` at `y` gives the coordinatewise sum
`∑ i, gᵢ(yᵢ)`. -/
@[simp] theorem separableCoordinateSum_apply {α β : Type*} [AddCommMonoid β]
    (g : ι → α → β) (y : ι → α) :
    separableCoordinateSum g y = ∑ i, g i (y i) := rfl

/-- The coordinate linear-combination constructor `x ↦ ∑ i, gᵢ(⟪aᵢ, x⟫ₚ)`. The codomain remains at
the primitive additive layer and specializes to `WithBotTop 𝕜` for the duality statements below. -/
def coordinateLinearCombination {β : Type*} [AddCommMonoid β]
    (a : ι → E) (g : ι → 𝕜 → β) : E → β :=
  fun x ↦ separableCoordinateSum g (coordinateInnerLinearMap a x)

-- Proof sketch: unfold `coordinateLinearCombination`.
/-- Evaluating `coordinateLinearCombination a g` at `x` gives
`∑ i, gᵢ(⟪aᵢ, x⟫ₚ)`. -/
@[simp] theorem coordinateLinearCombination_apply {β : Type*} [AddCommMonoid β]
    (a : ι → E) (g : ι → 𝕜 → β) (x : E) :
    coordinateLinearCombination a g x = ∑ i, g i (⟪a i, x⟫ₚ : 𝕜) := by
  unfold coordinateLinearCombination separableCoordinateSum
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [coordinateInnerLinearMap_apply]

/-- The canonical dual-side coefficient map `A* : (ι → 𝕜) → E`,
`A*(y⋆) = ∑ i, yᵢ⋆ aᵢ`. -/
def coordinateDualLinearMap (a : ι → E) : Y →ₗ[𝕜] E where
  toFun yStar := ∑ i, yStar i • a i
  map_add' yStar zStar := by
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t yStar := by
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

-- Proof sketch: unfold `coordinateDualLinearMap`.
/-- Evaluating `coordinateDualLinearMap a` at `y⋆` gives `∑ i, yᵢ⋆ aᵢ`. -/
@[simp] theorem coordinateDualLinearMap_apply
    (a : ι → E) (yStar : Y) :
    coordinateDualLinearMap a yStar = ∑ i, yStar i • a i :=
  rfl

variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local instance : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y
local instance : HasPairing 𝕜 𝕜 (WithBotTop 𝕜) := instHasPairingWithBotTop

-- Proof sketch: unfold `convexConjugate` on the product space `R^m` and separate the supremum
-- over coordinates. The resulting independent one-dimensional suprema are exactly the scalar
-- conjugates `(g i)⋆`.
/-- The Fenchel conjugate of the separable sum `y ↦ ∑ i, gᵢ(yᵢ)` is the separable sum of the
scalar conjugates `y⋆ ↦ ∑ i, gᵢ⋆(yᵢ⋆)`. -/
theorem convexConjugate_separableCoordinateSum_eq_sum_convexConjugate
    (g : ι → 𝕜 → WithBotTop 𝕜) :
    ((separableCoordinateSum g : (ι → 𝕜) → WithBotTop 𝕜)⋆) =
      (separableCoordinateSum (fun i : ι ↦ (g i)⋆) :
        (ι → 𝕜) → WithBotTop 𝕜) := sorry

-- Proof sketch: unfold `Function.linearImage` at the dual-side map and then rewrite the value of
-- the source function by `separableCoordinateSum_apply`. The fiber condition
-- `A* y⋆ = x⋆` becomes the textbook constraint on the coefficients.
/-- The dual-side image `A* g*` at `x⋆` is the infimum of
`∑ i, gᵢ⋆(ηᵢ⋆)` over all `y⋆ = (ηᵢ⋆)` satisfying `A* y⋆ = x⋆`. -/
theorem linearImage_coordinateDualLinearMap_eq_sInf
    (a : ι → E) (g : ι → 𝕜 → WithBotTop 𝕜) (xStar : E) :
    (coordinateDualLinearMap a ◁
        (separableCoordinateSum (fun i : ι ↦ (g i)⋆) : Y → WithBotTop 𝕜)) xStar =
      sInf
        ((fun yStar : Y ↦ ∑ i, (g i)⋆ (yStar i)) ''
          {yStar : Y | coordinateDualLinearMap a yStar = xStar}) := sorry

/- The source's `R^n` is rendered here by the ambient finite-dimensional real pairing space `E`. -/
variable [TopologicalSpace 𝕜]

/-- The source relative-interior hypothesis: some `x ∈ E`, specialized in the source to `R^n`,
satisfies
`⟪aᵢ, x⟫ₚ ∈ ri(dom gᵢ)` for every `i`. -/
def HasCoordinateRelativeInteriorPoint {β : Type*} [Top β] [LT β]
    (a : ι → E) (g : ι → 𝕜 → β) : Prop :=
  ∃ x : E, ∀ i : ι, ⟪a i, x⟫ₚ ∈ riDom[𝕜](g i)

-- Proof sketch: the effective domain of `separableCoordinateSum g` is the product of the
-- one-dimensional effective domains of the `gᵢ`, and the relative interior of that product is the
-- product of the relative interiors. Applying this to the point `coordinateInnerLinearMap a x`
-- converts the source coordinatewise hypothesis into the owner hypothesis used by Theorem 16.3.3.
/-- The source coordinatewise relative-interior hypothesis gives the owner-style hypothesis that
some `A x` lies in `ri(dom g)` for the separable sum `g(y) = ∑ i, gᵢ(yᵢ)`. -/
theorem
    exists_mem_intrinsicInterior_dom_separableCoordinateSum_of_hasCoordinateRelativeInteriorPoint
    {β : Type*} [AddCommMonoid β] [Top β] [LT β]
    (a : ι → E) (g : ι → 𝕜 → β)
    (hri : HasCoordinateRelativeInteriorPoint a g) :
    ∃ x : E,
      coordinateInnerLinearMap a x ∈
        riDom[𝕜]((separableCoordinateSum g : Y → β)) :=
  sorry

variable [TopologicalSpace E] [TopologicalSpace (WithBotTop 𝕜)]

-- Proof sketch: identify `coordinateLinearCombination a g` with the canonical composite
-- `separableCoordinateSum g ∘ coordinateInnerLinearMap a` by definition. Rewrite the
-- conjugate of the separable sum by
-- `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate`, then apply the
-- owner theorem
-- `convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_adjoint_of_convex`,
-- then rewrite `A†` by `coordinateDualLinearMap`.
/-- If each scalar `gᵢ` is convex and lower semicontinuous, then the conjugate of
`h(x) = ∑ i, gᵢ(⟪aᵢ, x⟫ₚ)` is the closure of the dual-side image `A* g*`, rendered by
`cl(·)`. -/
theorem convexConjugate_coordinateLinearCombination_eq_cl_linearImage_coordinateDual
    [FiniteDimensional 𝕜 E]
    (a : ι → E) (g : ι → 𝕜 → WithBotTop 𝕜)
    (hconv : ∀ i : ι, (g i).IsConvex 𝕜)
    (hlsc : ∀ i : ι, LowerSemicontinuous (g i)) :
    (coordinateLinearCombination a g)⋆ =
      cl(coordinateDualLinearMap a ◁
        (separableCoordinateSum (fun i : ι ↦ (g i)⋆) : Y → WithBotTop 𝕜)) := sorry

-- Proof sketch: first convert `HasCoordinateRelativeInteriorPoint a g` to the owner hypothesis
-- `∃ x, coordinateInnerLinearMap a x ∈ intrinsicInterior 𝕜 dom(separableCoordinateSum g)`
-- by
-- `exists_mem_intrinsicInterior_dom_separableCoordinateSum_of_hasCoordinateRelativeInteriorPoint`.
-- Then apply the owner theorem
-- `convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom`,
-- then rewrite `A†` by `coordinateDualLinearMap`. Finally rewrite the separable conjugate by
-- `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate`.
/- Text 16.0.4: if each scalar function `gᵢ` is convex and there exists
`x ∈ R^n` with `⟪aᵢ, x⟫ₚ ∈ ri(dom gᵢ)` for every `i`, then the conjugate of
`h(x) = ∑ i, gᵢ(⟪aᵢ, x⟫ₚ)` is exactly the dual-side image `A* g*`. -/
theorem convexConjugate_coordinateLinearCombination_eq_linearImage_coordinateDual_of_ri
    [FiniteDimensional 𝕜 E]
    (a : ι → E) (g : ι → 𝕜 → WithBotTop 𝕜)
    (hconv : ∀ i : ι, (g i).IsConvex 𝕜)
    (hri : HasCoordinateRelativeInteriorPoint a g) :
    (coordinateLinearCombination a g)⋆ =
      coordinateDualLinearMap a ◁
        (separableCoordinateSum (fun i : ι ↦ (g i)⋆) : Y → WithBotTop 𝕜) := sorry

-- Proof sketch: use the same owner relative-interior bridge as above, then invoke the
-- attained-or-vacuous clause from Theorem 16.3.3 for `coordinateInnerLinearMap a` and
-- `separableCoordinateSum g`.
-- Rewrite `convexConjugate (separableCoordinateSum g)` by
-- `convexConjugate_separableCoordinateSum_eq_sum_convexConjugate` to recover the
-- source coefficientwise formula and rewrite `A†` by `coordinateDualLinearMap`.
/-- Under the same hypotheses, the dual-fiber infimum defining `A* g*` is either vacuous,
giving the value `⊤`, or attained at some `y⋆` with `A* y⋆ = x⋆`. -/
theorem
    convexConjugate_coordinateLinearCombination_apply_eq_top_or_exists_coordinateDual
    [FiniteDimensional 𝕜 E]
    (a : ι → E) (g : ι → 𝕜 → WithBotTop 𝕜)
    (hconv : ∀ i : ι, (g i).IsConvex 𝕜)
    (hri : HasCoordinateRelativeInteriorPoint a g) (xStar : E) :
    (coordinateLinearCombination a g)⋆ xStar = ⊤ ∨
      ∃ yStar : Y, coordinateDualLinearMap a yStar = xStar ∧
        (coordinateLinearCombination a g)⋆ xStar =
          ∑ i, (g i)⋆ (yStar i) := sorry

end

/-! ### Text_16_0_5 (from Chap03) -/
noncomputable section

universe u u' v v' w'

section

open scoped Rockafellar

variable {E : Type u} {EStar : Type u'} {F : Type v} {FStar : Type v'} {L : Type w'}
variable [SupSet L] [InfSet L] [Sub L]
variable [HasPairing E EStar L] [HasPairing F FStar L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.5 rewrites the closure-free instance of the dual precomposition
  formula `(gA)^* = A^* g^*` as an explicit supremum-infimum identity at a fixed `x*`.
- `core/canonical`: the project owners are `convexConjugate` for Fenchel conjugation and
  `Function.linearImage` for the infimum over a fiber.
- `bridge/view`: the displayed left-hand side is the pointwise formula
  `convexConjugate_eq_iSup_pairing_sub` for `g ∘ A`, while the right-hand side is the pointwise
  formula `Function.linearImage_eq_sInf_image` for the dual-side map applied to
  `convexConjugate g`.

Domain-style sampling used here:
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- `Function.linearImage`, its notation `◁`, and `Function.linearImage_eq_sInf_image` from
  Theorem 5.7;
- map-fiber owners via `Function.linearImage`.

Primitive data vs derived API:
- primitive inputs: a primal map `A`, a dual-side map `AStar`, a function `g`, a
  closure-free duality hypothesis `hdual : (g ∘ A)⋆ = AStar ◁ g⋆`, and the evaluation point
  `xStar`;
- derived API: the owner-level pointwise equality
  `(g ∘ A)⋆ xStar = (AStar ◁ g⋆) xStar` and its displayed supremum-infimum expansion.

Layer target: `bridge/view`; the source sentence is a pointwise unpacking of the closure-free dual
formula, so the theorem is stated directly in that supremum-infimum form.

Ambient note: the theorem itself only uses the owner declarations `convexConjugate` and
`Function.linearImage` plus maps `A` and `AStar`, so the API stays at the primitive
pairing-and-inf/sup layer. The adjoint-based Euclidean wording is a downstream specialization.
-/

-- Proof sketch: evaluate the owner-level equality `hdual` at `xStar`.
/-- Evaluating the closure-free dual formula at `xStar` gives the pointwise owner equality
`(g ∘ A)⋆ xStar = (AStar ◁ g⋆) xStar`. -/
theorem
    convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula
    (A : E → F) (AStar : FStar → EStar) (g : F → L)
    (hdual : (g ∘ A)⋆ = AStar ◁ g⋆)
    (xStar : EStar) :
    (g ∘ A)⋆ xStar = (AStar ◁ g⋆) xStar := by
  simpa using congrFun hdual xStar

/-- Text 16.0.5: when the closure operation is unnecessary in the dual formula
`(g ∘ A)^* = AStar ◁ g^*`, evaluating at `x*` identifies the Fenchel supremum of
`x ↦ g (A x)` with the infimum of `g*` over the dual fiber `AStar y* = x*`. The source's adjoint
Euclidean statement is a specialization. -/
theorem convexConjugate_comp_map_apply_eq_sInf_image_conjugate_of_closureFreeDualFormula
    (A : E → F) (AStar : FStar → EStar) (g : F → L)
    (hdual : (g ∘ A)⋆ = AStar ◁ g⋆)
    (xStar : EStar) :
    (g ∘ A)⋆ xStar =
      sInf (g⋆ '' {yStar : FStar | AStar yStar = xStar}) := by
  simpa [Function.linearImage_eq_sInf_image] using
    convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula
      A AStar g hdual xStar

-- Proof sketch: rewrite the left-hand side by `convexConjugate_eq_iSup_pairing_sub`.
/-- Source-view supremum-infimum restatement of Text 16.0.5 at fixed `xStar`. -/
theorem iSup_pairing_sub_comp_map_eq_sInf_image_conjugate_of_closureFreeDualFormula
    (A : E → F) (AStar : FStar → EStar) (g : F → L)
    (hdual : (g ∘ A)⋆ = AStar ◁ g⋆)
    (xStar : EStar) :
    (⨆ x : E, (⟪x, xStar⟫ₚ - g (A x))) =
      sInf (g⋆ '' {yStar : FStar | AStar yStar = xStar}) := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    convexConjugate_comp_map_apply_eq_sInf_image_conjugate_of_closureFreeDualFormula
      A AStar g hdual xStar

end
