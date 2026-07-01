import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

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
