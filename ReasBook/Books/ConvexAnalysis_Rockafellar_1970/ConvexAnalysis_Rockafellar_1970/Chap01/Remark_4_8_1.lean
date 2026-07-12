import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

attribute [local instance] Classical.propDecidable
open scoped Rockafellar

section

variable {E : Type u}
variable {α : Type*} [Zero α] [Preorder α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 4.8.1 observes that the epigraph of the indicator function is the
  half-cylinder over `C`, and concludes that `C` is convex exactly when its indicator function is
  convex.
- `core/canonical`: the owner abstractions are the chapter indicator owner `indicator`,
  the chapter epigraph owner `epi`, mathlib's set convexity predicate `Convex`, and the canonical
  whole-space owner `ConvexOn 𝕜 Set.univ`.
- `bridge/view`: `epi_indicator_eq_prod` is the canonical half-cylinder identity; the convexity
  theorems below then read convexity of `C` directly from that product description.

Primitive data vs derived API:
- primitive data: only the set `C : Set E`;
- derived API: the product epigraph description of `δ[α](· | C)` and the resulting scalar-convexity
  equivalence.

Domain-style sampling used here:
- `epi` from Definition 4.1;
- `indicator` from Defintion 4.8.1;
- the source-facing notation `δ[α](· | C)` attached to that owner;
- `ConvexOn` on `Set.univ`;
- `Convex` on subsets of a scalar module;
- product convexity via `Convex.prod`.
-/

-- The indicator contributes only two values, so the finite-height epigraph is exactly the
-- restricted zero epigraph over `C`.
/-- Helper for Remark 4.8.1: the finite-height epigraph of the indicator is the restricted
epigraph of the constant-zero branch over `C`. -/
theorem epi_indicator_eq_epi_restrict_zero (C : Set E) :
    epi (δ[α](· | C)) = epi (0 : E → WithTopBot α) C := by
  ext p
  rcases p with ⟨x, μ⟩
  by_cases hx : x ∈ C
  · -- On `C`, the indicator is `0`, so both epigraph conditions are the same.
    simp [indicator_def, hx]
  · -- Outside `C`, the finite-height epigraph is empty because the indicator value is `⊤`.
    simp [indicator_def, hx]

/-- Helper for Remark 4.8.1: a finite height lies above `0` in `WithTopBot α` exactly when it is
nonnegative in `α`. -/
theorem withTopBot_zero_le_coe_iff {μ : α} :
    ((0 : WithTopBot α) ≤ (μ : WithTopBot α)) ↔ 0 ≤ μ := by
  change
    ((((0 : α) : WithBot α) : WithTop (WithBot α)) ≤
        (((μ : α) : WithBot α) : WithTop (WithBot α))) ↔
      0 ≤ μ
  rw [WithTop.coe_le_coe]
  exact WithBot.coe_le_coe

-- Rewriting the restricted zero epigraph through the previous bridge makes the half-cylinder
-- description literal.
/-- The chapter epigraph of the indicator function is the half-cylinder over `C` cut out by the
nonnegative height condition. -/
theorem epi_indicator_eq_prod (C : Set E) :
    epi (δ[α](· | C)) = C ×ˢ Set.Ici (0 : α) := by
  rw [epi_indicator_eq_epi_restrict_zero]
  ext p
  rcases p with ⟨x, μ⟩
  -- The only remaining translation is from lifted nonnegativity to nonnegativity in `α`.
  constructor
  · rintro ⟨hx, hμ⟩
    exact ⟨hx, (withTopBot_zero_le_coe_iff (μ := μ)).1 hμ⟩
  · rintro ⟨hx, hμ⟩
    exact ⟨hx, (withTopBot_zero_le_coe_iff (μ := μ)).2 hμ⟩

end

section

variable {𝕜 : Type*} {E : Type u} {α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [SMulZeroClass 𝕜 α]
variable [PosSMulMono 𝕜 α]

/-- Helper for Remark 4.8.1: lift the scalar action on `α` to `WithTopBot α` by acting on finite
values and fixing the boundary points. -/
local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

namespace Function

/-- Helper for Remark 4.8.1: the chapter owner `Function.IsConvex` records convexity of the
finite-height epigraph `epi f`. -/
abbrev IsConvex (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E α : Type*} [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [LE α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

end Function

/-- Helper for Remark 4.8.1: the indicator lies below `0` exactly on the underlying set. -/
theorem indicator_le_zero_iff_mem {C : Set E} {x : E} :
    δ[α](x | C) ≤ (0 : WithTopBot α) ↔ x ∈ C := by
  by_cases hx : x ∈ C
  · -- On `C`, the indicator is exactly `0`.
    simp [indicator_def, hx]
  · -- Outside `C`, the indicator is `⊤`, which cannot lie below a finite height.
    simp [indicator_def, hx]

/-- Helper for Remark 4.8.1: the lifted `WithTopBot` action sends the finite zero branch to
itself. -/
@[simp] theorem smul_zero_withTopBot (a : 𝕜) :
    a • (0 : WithTopBot α) = (0 : WithTopBot α) := by
  change (((a • (0 : α)) : α) : WithTopBot α) = (((0 : α) : α) : WithTopBot α)
  exact congrArg (fun t : α ↦ (t : WithTopBot α)) (smul_zero (A := α) a)

/-- Helper for Remark 4.8.1: the lifted `WithTopBot` action fixes the top endpoint. -/
@[simp] theorem smul_top_withTopBot (a : 𝕜) :
    a • (⊤ : WithTopBot α) = (⊤ : WithTopBot α) := by
  rfl

-- Route correction: rather than redoing the old manual height estimate, rewrite the restricted
-- zero epigraph to the half-cylinder product and use `Convex.prod`.
/-- Canonical bridge: the restricted epigraph of the constant-zero branch over `C` is convex
exactly when `C` is convex. -/
theorem convex_epi_restrict_zero_iff (C : Set E) :
    Convex 𝕜 (epi (0 : E → WithTopBot α) C) ↔ Convex 𝕜 C := by
  have hEq : epi (0 : E → WithTopBot α) C = C ×ˢ Set.Ici (0 : α) := by
    calc
      epi (0 : E → WithTopBot α) C = epi (δ[α](· | C)) := by
        symm
        exact epi_indicator_eq_epi_restrict_zero (α := α) C
      _ = C ×ˢ Set.Ici (0 : α) := epi_indicator_eq_prod (α := α) C
  constructor
  · intro hEpi
    have hProd : Convex 𝕜 (C ×ˢ Set.Ici (0 : α)) := by
      simpa [hEq] using hEpi
    intro x hx y hy a b ha hb hab
    have hx0 : (x, (0 : α)) ∈ C ×ˢ Set.Ici (0 : α) := by
      simp [hx]
    have hy0 : (y, (0 : α)) ∈ C ×ˢ Set.Ici (0 : α) := by
      simp [hy]
    -- Testing the product convexity on height `0` recovers convexity of the cross-section `C`.
    have hxy := hProd hx0 hy0 ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk] using hxy.1
  · intro hC
    rintro ⟨x, μx⟩ hx ⟨y, μy⟩ hy a b ha hb hab
    refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
    have hxμ : (0 : α) ≤ μx := (withTopBot_zero_le_coe_iff (μ := μx)).1 hx.2
    have hyμ : (0 : α) ≤ μy := (withTopBot_zero_le_coe_iff (μ := μy)).1 hy.2
    have hlin :
        a • (0 : α) + b • (0 : α) ≤ a • μx + b • μy :=
      add_le_add
        (smul_le_smul_of_nonneg_left hxμ ha)
        (smul_le_smul_of_nonneg_left hyμ hb)
    have hzero : (0 : α) ≤ a • μx + b • μy := by
      have hleft : a • (0 : α) + b • (0 : α) = (0 : α) := by
        rw [smul_zero (A := α) a, smul_zero (A := α) b, zero_add]
      rw [hleft] at hlin
      exact hlin
    exact (withTopBot_zero_le_coe_iff (μ := a • μx + b • μy)).2 hzero

-- The finite-height owner uses exactly the product epigraph characterized above.
/-- Derived global-view bridge: the chapter owner `Function.IsConvex` is equivalent to convexity
of the underlying set. -/
theorem indicator_isConvex_iff (C : Set E) :
    (δ[α](· | C)).IsConvex 𝕜 ↔ Convex 𝕜 C := by
  -- Rewrite the owner definition through the half-cylinder bridge and close with the product
  -- convexity equivalence already established.
  rw [Function.IsConvex, epi_indicator_eq_epi_restrict_zero]
  exact convex_epi_restrict_zero_iff (𝕜 := 𝕜) (α := α) C

-- Route correction: the `ConvexOn` theorem needs the lifted `WithTopBot` scalar action, so the
-- source half-cylinder proof is used for the finite-height owner above, while the whole-space
-- owner is verified directly on the indicator inequality.
/-- Remark 4.8.1 on the canonical owner layer: the indicator of `C` is convex on `Set.univ`
exactly when `C` itself is convex. -/
theorem indicator_convexOn_univ_iff (C : Set E) :
    ConvexOn 𝕜 (Set.univ : Set E) (δ[α](· | C)) ↔ Convex 𝕜 C := by
  constructor
  · intro hConv
    intro x hx y hy a b ha hb hab
    have hzero :
        indicator α C (a • x + b • y) ≤
          a • indicator α C x + b • indicator α C y :=
      hConv.2 (by simp) (by simp) ha hb hab
    have hrhs :
        a • indicator α C x + b • indicator α C y = (0 : WithTopBot α) := by
      simp [indicator_def, hx, hy]
    have hmem :
        indicator α C (a • x + b • y) ≤ (0 : WithTopBot α) := by
      rw [hrhs] at hzero
      exact hzero
    -- Height `0` in the indicator epigraph detects exactly membership in `C`.
    exact (indicator_le_zero_iff_mem (α := α) (C := C)).1 hmem
  · intro hC
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    by_cases hxC : x ∈ C
    · by_cases hyC : y ∈ C
      · have hxyC : a • x + b • y ∈ C := hC hxC hyC ha hb hab
        -- When both endpoints lie in `C`, every indicator value is `0`.
        simp [indicator_def, hxC, hyC, hxyC]
      · -- If one endpoint is outside `C`, the right-hand side acquires the `⊤` branch.
        calc
          indicator α C (a • x + b • y) ≤ (⊤ : WithTopBot α) := le_top
          _ = a • indicator α C x + b • indicator α C y := by
            simp [indicator_def, hxC, hyC]
    · -- If `x ∉ C`, the same `⊤` branch makes the convexity inequality immediate.
      calc
        indicator α C (a • x + b • y) ≤ (⊤ : WithTopBot α) := le_top
        _ = a • indicator α C x + b • indicator α C y := by
          simp [indicator_def, hxC]

end
