import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

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
