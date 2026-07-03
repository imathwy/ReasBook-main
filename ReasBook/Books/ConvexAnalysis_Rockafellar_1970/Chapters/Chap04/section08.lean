import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_4_8_1 (from Chap01) -/
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

/-! ### Remark_4_8_1_Positive_Homogeneity (from Chap01) -/
universe u v w

section

variable {𝕜 : Type u} {E : Type v} {F : Type w}

namespace Function

/-- Finite-height epigraph for an ordered codomain. -/
def positiveHomogeneityEpigraph [Preorder F] (f : E → F) : Set (E × F) :=
  {p : E × F | f p.1 ≤ p.2}

/-- The epigraph is a positive cone when it is closed under multiplication by positive scalars. -/
def IsPositiveCone [LT 𝕜] [Zero 𝕜] [SMul 𝕜 (E × F)] (S : Set (E × F)) : Prop :=
  ∀ c : 𝕜, 0 < c → ∀ p ∈ S, c • p ∈ S

/-- Remark 4.8.1, positive-homogeneity form: under the standard order-compatibility assumptions
for positive scalar multiplication on the codomain, positive homogeneity is equivalent to the
finite-height epigraph being a positive cone. -/
theorem positivelyHomogeneous_iff_epigraph_isPositiveCone
    [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E] [SMul 𝕜 F] [SMul 𝕜 (E × F)] [Preorder F]
    (f : E → F)
    (hmono : ∀ {c : 𝕜}, 0 < c → ∀ {a b : F}, a ≤ b → c • a ≤ c • b)
    (hcancel : ∀ {c : 𝕜}, 0 < c → ∀ {a b : F}, c • a ≤ c • b → a ≤ b) :
    f.PositivelyHomogeneous 𝕜 ↔
      IsPositiveCone (𝕜 := 𝕜) (positiveHomogeneityEpigraph f) := by
  sorry

end Function

end

/-! ### Example_4_8_2 (from Chap01) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: the item gives the absolute-value function as an example of a positively
  homogeneous convex function that is not linear; positive homogeneity uses the ordered-ring
  layer, nonlinearity uses the strict-ordered-ring layer, and convexity uses the same
  ordered-ring layer.
- `core/canonical`: the primitive owner abstractions are the canonical function `abs`,
  `Function.PositivelyHomogeneous` on the finite codomain surface `(abs : 𝕜 → 𝕜)`,
  the finite-valued convexity owner `ConvexOn 𝕜 Set.univ (abs : 𝕜 → 𝕜)`, and mathlib's
  predicate `IsLinearMap`.
- `bridge/view`: the identity `abs_mul` proves positive homogeneity; the convexity owner
  statement uses `Function.isConvex_coe_of_convexOn_univ` together with the triangle inequality
  bridge `abs_sub`; failure of
  `map_neg` shows nonlinearity.
- Primitive data vs derived API: no local wrapper function belongs here. The primitive object is
  the canonical function `abs`; positive homogeneity, convexity on `Set.univ`, and nonlinearity
  are source-facing theorem facts. The chapter owner statements on `WithTopBot` are then explicit
  bridge consequences.

Domain-style sampling used here:
- `abs : 𝕜 → 𝕜` on the ordered-ring layer;
- `Function.PositivelyHomogeneous` from Definition 4.8;
- `ConvexOn`, `Function.isConvex_coe_of_convexOn_univ`, `abs_sub`, `abs_mul`;
- `IsLinearMap.map_neg`.
- Layer target: `source-facing` at the primitive owner layer, with chapter-codomain statements
  provided as direct bridge consequences.
-/

namespace Function

/-- Helper for Example 4.8.2: the canonical codomain lift sends a finite-valued function to the
same function viewed in `WithTopBot`. -/
abbrev toWithTopBot {E α : Type*} (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

/-- Helper for Example 4.8.2: the chapter owner `Function.IsConvex` is convexity of the epigraph
of a `WithTopBot`-valued map. -/
abbrev IsConvex (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E α : Type*} [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [LE α]
    (f : E → WithTopBot α) : Prop :=
  Convex 𝕜 (epi f)

/-- Helper for Example 4.8.2: convexity on `Set.univ` for a finite-valued map yields convexity of
its canonical `WithTopBot` lift. -/
theorem isConvex_coe_of_convexOn_univ {𝕜 E β : Type*}
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 β] [PosSMulMono 𝕜 β]
    {f : E → β} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    f.toWithTopBot.IsConvex 𝕜 := by
  simpa [Function.toWithTopBot, Function.IsConvex, epi_univ_eq_setOf_le] using hf.convex_epigraph

end Function

/-- Helper for Example 4.8.2: scalar multiplication on `WithTopBot 𝕜` is multiplication by the
coerced scalar. -/
local instance instSMulWithTopBot {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

/-- Example 4.8.2 (primitive owner surface): absolute value is positively homogeneous. -/
theorem abs_positivelyHomogeneous_coe {𝕜 : Type*}
    [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    (abs : 𝕜 → 𝕜).PositivelyHomogeneous 𝕜 := by
  intro c x
  simp [smul_eq_mul, abs_of_pos c.2, abs_mul]

/-- Example 4.8.2 (chapter bridge surface): absolute value is positively homogeneous after the
canonical codomain lift to `WithTopBot`. -/
theorem abs_positivelyHomogeneous {𝕜 : Type*}
    [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    ((abs : 𝕜 → 𝕜).toWithTopBot).PositivelyHomogeneous 𝕜 := by
  -- Map the finite-valued homogeneity equality through the canonical coercion into `WithTopBot`.
  intro c x
  change (((abs ((c : 𝕜) * x) : 𝕜) : WithTopBot 𝕜) =
    ((c : 𝕜) : WithTopBot 𝕜) * ((abs x : 𝕜) : WithTopBot 𝕜))
  simp [abs_mul, abs_of_pos c.2]

/-- Example 4.8.2 (primitive owner surface): absolute value is convex on `Set.univ`. -/
theorem abs_convexOn_univ {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    ConvexOn 𝕜 (Set.univ : Set 𝕜) (abs : 𝕜 → 𝕜) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have htri : |a * x + b * y| ≤ |a * x| + |b * y| := by
    simpa [sub_eq_add_neg, abs_neg, add_assoc, add_comm, add_left_comm] using
      (abs_sub (a * x) (-(b * y)))
  calc
    |a • x + b • y| = |a * x + b * y| := by simp [smul_eq_mul]
    _ ≤ |a * x| + |b * y| := htri
    _ = a * |x| + b * |y| := by
      simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a • |x| + b • |y| := by simp [smul_eq_mul]

/-- Example 4.8.2 (chapter bridge surface): absolute value is convex after the canonical codomain
lift to `WithTopBot`. -/
theorem abs_isConvex {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] :
    ((abs : 𝕜 → 𝕜).toWithTopBot).IsConvex 𝕜 := by
  exact Function.isConvex_coe_of_convexOn_univ abs_convexOn_univ

/-- Example 4.8.2: absolute value is not linear on any strictly ordered ring. -/
theorem abs_not_isLinearMap {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    ¬ IsLinearMap 𝕜 (abs : 𝕜 → 𝕜) := by
  intro h
  have hneg := h.map_neg (1 : 𝕜)
  have hone : (1 : 𝕜) = -1 := by
    simpa using hneg
  have h01 : (0 : 𝕜) < -1 := by
    exact hone ▸ (zero_lt_one : (0 : 𝕜) < 1)
  exact (not_lt_of_gt (neg_one_lt_zero : (-1 : 𝕜) < 0)) h01

/-! ### Definition_4_8 (from Chap01) -/
universe u v w

section

variable {𝕜 : Type u} {E : Type v} {F : Type w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 4.8 introduces the positive-homogeneity property of a function.
- `core/canonical`: the owner abstraction is the function-side property
  `Function.PositivelyHomogeneous 𝕜` on `f : E → F`, matching the chapter owner pattern
  `f.IsProper` / `f.IsConvex`; its primitive content is the textbook pointwise scaling law for
  positive scalars, expressed intrinsically over the primitive positive subtype.
- `bridge/view`: concrete model specializations belong downstream; this file keeps only the
  codomain-agnostic owner for positive-scalar homogeneity and exposes textbook `0 < c` binder
  form through a thin theorem-level bridge.
- Primitive data vs derived API: the primitive owner quantifies over intrinsic positive scalars
  `a : 𝕜⁺` with pointwise law
  `f (a • x) = a • f x`; the theorem
  `Function.PositivelyHomogeneous.iff_forall_pos_scalar` gives the explicit-binder bridge, and
  `Function.PositivelyHomogeneous.map_smul` is its pointwise consequence. This owner layer matches
  the later degree-`p` generalization at `f.PositivelyHomogeneousOfDegree 1`.
- Domain-style sampling used here: the project owners `Function.IsProper`,
  `Function.IsConvex`, and the later generalization `Function.PositivelyHomogeneousOfDegree` all
  use short unbundled `Prop` owners with theorem-level companion API. Mathlib does not expose an
  exact owner for positive-scalar homogeneity with this interface, so this file remains the
  canonical chapter owner rather than a wrapper around an upstream declaration.
-/

namespace Function

/-- Intrinsic owner for positive scalars in `𝕜`. -/
abbrev PositiveScalars (𝕜 : Type u) [LT 𝕜] [Zero 𝕜] : Type u := {c : 𝕜 // 0 < c}

/-- Textbook shorthand for the intrinsic positive-scalar owner `Function.PositiveScalars`. -/
scoped notation:max 𝕜 "⁺" => PositiveScalars 𝕜

/-- Canonical action of intrinsic positive scalars via coercion to the ambient scalar type. -/
instance instSMulPositiveScalars [LT 𝕜] [Zero 𝕜] (β : Type*) [SMul 𝕜 β] :
    SMul (𝕜⁺) β where
  smul a x := (a : 𝕜) • x

/-- Canonical coercion from intrinsic positive scalars to nonnegative scalars. -/
instance instCoePositiveScalarsToIci [Zero 𝕜] [Preorder 𝕜] :
    CoeTC (𝕜⁺) (Set.Ici (0 : 𝕜)) where
  coe a := ⟨(a : 𝕜), le_of_lt a.2⟩

/-- Coercing a positive scalar to the nonnegative subtype preserves its underlying value. -/
@[simp] theorem coe_positiveScalars_toIci [Zero 𝕜] [Preorder 𝕜] (a : 𝕜⁺) :
    ((a : Set.Ici (0 : 𝕜)) : 𝕜) = (a : 𝕜) :=
  rfl

/-- Bridge lemma for the intrinsic positive-scalar action back to ambient scalar action. -/
@[simp] theorem positiveScalars_smul_eq_coe_smul [LT 𝕜] [Zero 𝕜] {β : Type*}
    [SMul 𝕜 β] (a : 𝕜⁺) (x : β) :
    a • x = (a : 𝕜) • x :=
  rfl

/-- Definition 4.8: a function is positively homogeneous of degree `1` if scaling its argument by
a positive scalar scales its value by the same scalar. -/
def PositivelyHomogeneous (𝕜 : Type u) [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E] [SMul 𝕜 F]
    (f : E → F) : Prop :=
  ∀ a : 𝕜⁺, ∀ x : E, f (a • x) = a • f x

variable [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E] [SMul 𝕜 F]
variable {f : E → F}

/-- The Chapter 1 positive-homogeneity owner can be read intrinsically over positive scalars. -/
theorem PositivelyHomogeneous.iff_forall_pos :
    f.PositivelyHomogeneous 𝕜 ↔
      ∀ a : 𝕜⁺, ∀ x : E, f (a • x) = a • f x :=
  Iff.rfl

/-- Bridge from the intrinsic positive-scalar owner to the textbook scalar-plus-positivity
binder form. -/
theorem PositivelyHomogeneous.iff_forall_pos_scalar :
    f.PositivelyHomogeneous 𝕜 ↔
      ∀ c : 𝕜, 0 < c → ∀ x : E, f (c • x) = c • f x := by
  constructor
  · intro hf c hc x
    exact hf ⟨c, hc⟩ x
  · intro hf a x
    exact hf a a.2 x

/-- A positively homogeneous function carries intrinsic positive scalar multiples to the
corresponding scalar multiples of its value. -/
theorem PositivelyHomogeneous.map_smul_pos (hf : f.PositivelyHomogeneous 𝕜)
    (a : 𝕜⁺) (x : E) :
    f (a • x) = a • f x :=
  hf a x

/-- A positively homogeneous function carries every positive scalar multiple of an argument to the
corresponding scalar multiple of its value, in the textbook scalar-plus-positivity form. -/
theorem PositivelyHomogeneous.map_smul (hf : f.PositivelyHomogeneous 𝕜) {c : 𝕜}
    (hc : 0 < c) (x : E) :
    f (c • x) = c • f x :=
  (PositivelyHomogeneous.iff_forall_pos_scalar.mp hf) c hc x

end Function

end

/-! ### Theorem_4_8 (from Chap01) -/
universe u v

noncomputable section

variable {𝕜 : Type u} {E : Type v}

namespace Function

section Core

variable {α : Type*}
variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [Module 𝕜 α]

-- Proof sketch: this is only a name-level owner wrapper around the primitive witness data
-- `∃ g, g.toWithBotTop = f`; no mathematical content is changed here.
/-- Owner for a submodule function that is the canonical `WithBotTop` lift of a linear
map. -/
def IsLinearLift {L : Submodule 𝕜 E} (f : L → WithBotTop α) : Prop :=
  ∃ g : L →ₗ[𝕜] α, (g : L → α).toWithBotTop = f

end Core

section OddLayer

variable {α : Type*}
variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup α] [Module 𝕜 α]

-- Proof sketch: unpack the witnessing linear map on `L`; linearity gives
-- `g (-x) = -g x`, and then the oddness owner on `L` follows by rewriting through the equality of
-- the canonical bridge `g.toWithBotTop = f`.
/-- If `f : L → WithBotTop α` is the canonical `WithBotTop α` lift of a `𝕜`-linear map on `L`,
then `f` is odd. -/
theorem IsLinearLift.odd {L : Submodule 𝕜 E} {f : L → WithBotTop α}
    (hf : f.IsLinearLift) :
    Function.Odd f := sorry

end OddLayer

section OrderedConvexLayer

attribute [local instance] WithBotTop.instSMul
local instance instDecidableLT (α : Type*) [LT α] : DecidableLT α :=
  Classical.decRel (fun a b => a < b)

variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 4.8 is about the restriction of a convex positively homogeneous
  function to a subspace `L`, so the main owner-facing theorems below are stated directly for a
  function `f : L → WithBotTop 𝕜`.
- `core/canonical`: the owner abstractions are `Function.PositivelyHomogeneous`,
  `Function.IsConvex`, `Function.Odd`, `Function.IsLinearLift`, the chapter
  codomain lift `Function.toWithBotTop`, and the canonical subspace owner `Submodule 𝕜 E`.
- `bridge/view`: `isLinearLift_iff_odd_on_submodule` is the thin companion that rewrites a
  global function `f : E → WithBotTop 𝕜` through the canonical set restriction
  `(L : Set E).restrict f`; its
  assumptions live on that restricted function rather than on all of `E`.

Domain-style sampling used here:
- `Function.PositivelyHomogeneous`;
- `Function.IsConvex`;
- `Function.IsConvex.comp_linearMap`;
- `Function.Odd`;
- `Function.IsLinearLift`;
- `Function.toWithBotTop`;
- `Submodule 𝕜 E` and `Module.Basis ι 𝕜 L` with finitely supported coordinates `b.repr`.

Primitive data vs derived API:
- primitive owner data: the submodule `L`, the restricted function `f : L → WithBotTop 𝕜`, and a
  linear functional `g : L →ₗ[𝕜] 𝕜`;
- derived API: the oddness owner `Function.Odd f`, the local linearity criterion
  `isLinearLift_iff_odd`, and the basis-checking criterion
  `isLinearLift_of_odd_on_basis`.
- Layer target: `source-facing` for `IsLinearLift.odd`, `isLinearLift_iff_odd`, and
  `isLinearLift_of_odd_on_basis`; `bridge/view` for
  `isLinearLift_iff_odd_on_submodule`.
-/

-- Proof sketch: the forward implication is the previous oddness lemma for a linear representative
-- on `L`. For the converse, use Theorem 4.7 and Corollary 4.7.2 on `f`
-- to force equality in the subadditivity bounds, obtaining additivity on `L`; combine this with
-- positive homogeneity and oddness to extend the scalar law from positive scalars to all of `𝕜`,
-- and package the result as a linear functional on `L`. The textbook properness hypothesis is
-- used only through the primitive local exclusion `∀ x : L, f x ≠ ⊥`.
/-- Theorem 4.8: under positive homogeneity, convexity, and local exclusion of `⊥`, a function
`f : L → WithBotTop 𝕜` is the canonical `WithBotTop 𝕜` lift of a `𝕜`-linear functional on `L`
if and only if `f` is odd. -/
theorem isLinearLift_iff_odd {L : Submodule 𝕜 E}
    (f : L → WithBotTop 𝕜) (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_convex : f.IsConvex 𝕜) (hf_ne_bot : ∀ x : L, f x ≠ ⊥) :
    f.IsLinearLift ↔ Function.Odd f := sorry

/-- Textbook-phrasing companion of `isLinearLift_iff_odd`, using `⊥ < f x` instead of the
primitive assumption `f x ≠ ⊥`. -/
theorem isLinearLift_iff_odd_of_bot_lt {L : Submodule 𝕜 E}
    (f : L → WithBotTop 𝕜) (hf_hom : f.PositivelyHomogeneous 𝕜)
    (hf_convex : f.IsConvex 𝕜) (hf_bot : ∀ x : L, ⊥ < f x) :
    f.IsLinearLift ↔ Function.Odd f :=
  isLinearLift_iff_odd f hf_hom hf_convex (fun x => (WithBot.bot_lt_iff_ne_bot.1 (hf_bot x)))

/-- Bridge form of Theorem 4.8 for a global function `f : E → WithBotTop 𝕜`, stated through the
canonical restricted owner `fL := (L : Set E).restrict f`. -/
theorem isLinearLift_iff_odd_on_submodule
    (f : E → WithBotTop 𝕜) (L : Submodule 𝕜 E) :
    let fL : L → WithBotTop 𝕜 := (L : Set E).restrict f
    fL.PositivelyHomogeneous 𝕜 →
      fL.IsConvex 𝕜 →
      (∀ x : L, fL x ≠ ⊥) →
      (fL.IsLinearLift ↔ Function.Odd fL) := by
  dsimp
  exact fun hf_hom hf_convex hf_ne_bot =>
    isLinearLift_iff_odd ((L : Set E).restrict f) hf_hom hf_convex
      (fun x => by simpa using hf_ne_bot x)

/-- If `f (-b i) = -f (b i)` holds on the vectors of one basis of `L`, then
`f : L → WithBotTop 𝕜` is the canonical `WithBotTop 𝕜` lift of a `𝕜`-linear functional on `L`. -/
-- Proof sketch: express each `x : L` through the finitely supported coordinates `b.repr x`. The
-- basis assumptions give oddness on each basis vector, and positive homogeneity extends that to
-- each scalar multiple of a basis vector. Then Theorem 4.7 and Corollary 4.7.2 identify `f x`
-- with the corresponding finite linear combination of the basis values, yielding a linear
-- functional on `L`.
theorem isLinearLift_of_odd_on_basis {L : Submodule 𝕜 E}
    (f : L → WithBotTop 𝕜) {ι : Type*} (b : Module.Basis ι 𝕜 L)
    (hf_hom : f.PositivelyHomogeneous 𝕜) (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ x : L, f x ≠ ⊥) (hb : ∀ i : ι, f (-b i) = -f (b i)) :
    f.IsLinearLift := sorry

/-- Textbook-phrasing companion of `isLinearLift_of_odd_on_basis`, using `⊥ < f x` as the
local nondegeneracy hypothesis. -/
theorem isLinearLift_of_odd_on_basis_of_bot_lt {L : Submodule 𝕜 E}
    (f : L → WithBotTop 𝕜) {ι : Type*} (b : Module.Basis ι 𝕜 L)
    (hf_hom : f.PositivelyHomogeneous 𝕜) (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : L, ⊥ < f x) (hb : ∀ i : ι, f (-b i) = -f (b i)) :
    f.IsLinearLift :=
  isLinearLift_of_odd_on_basis f b hf_hom hf_convex
    (fun x => (WithBot.bot_lt_iff_ne_bot.1 (hf_bot x))) hb

end OrderedConvexLayer

end Function

end
