import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_9_0 (from Chap02) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.9.0 introduces the lineality space of a proper convex function via
  its recession function.
- `core/canonical`: the primitive chapter owner remains `Function.constancySpace`, but this
  numbered item is function-facing, so the canonical owner surface should be the intrinsic
  function owner `Function.lineal f`, not the derived expression
  `Function.constancySpace ((f)₀⁺)` scattered across theorem headers.
- `bridge/view`: membership bridges are inherited from Definition 8.7.0 and restated directly on
  the function-facing owner.
- Primitive data vs derived API: primitive data are still only the recession function and the
  `Function.constancySpace` owner; `Function.lineal` is the intrinsic function-facing owner built
  from them.
- Layer target: `core/canonical` owner on functions, with thin bridge theorems.

Domain-style sampling used here:
- `Function.recessionCone` and `Function.mem_recessionCone_iff` from Definition 8.5.0;
- `Function.constancySpace`, `Function.mem_constancySpace_iff_mem_recessionCone`, and
  `Function.mem_constancySpace_iff` from Definition 8.7.0;
- `Function.recessionFunction` and notation `(f)₀⁺` from Corollary 8.5.1;
- the set-side owner `Set.lineal` / `Set.mem_lineal_iff` from Definitions 8.4.2 and 8.4.3;
- mathlib's bundled cone owner `PointedCone.lineal`.
-/

open scoped Rockafellar

namespace Function

section

variable {E α : Type*}
variable [Add E] [Neg E]
variable [AddGroup α] [ConditionallyCompleteLattice α]

/-- Definition 8.9.0: the lineality space of a function `f` is the constancy space of its
recession function. -/
def lineal (f : E → WithTopBot α) : Set E :=
  Function.constancySpace ((f)₀⁺)

namespace Rockafellar

scoped[Rockafellar] notation "lin(" f ")" => Function.lineal f

end Rockafellar

/-- Unfolding bridge: `lineal f` is definitionally the constancy space of the recession function
`(f)₀⁺`. -/
theorem lineal_eq_constancySpace (f : E → WithTopBot α) :
    lin(f) = Function.constancySpace ((f)₀⁺) :=
  rfl

/-- Canonicalization bridge: the derived expression `Function.constancySpace ((f)₀⁺)` rewrites to
the function-facing owner `lin(f)`. -/
@[simp] theorem constancySpace_recessionFunction_eq_lineal (f : E → WithTopBot α) :
    Function.constancySpace ((f)₀⁺) = lin(f) :=
  rfl

/-- Membership in `lineal f` means both `y` and `-y` are nonpositive directions for `(f)₀⁺`. -/
@[simp] theorem mem_lineal_iff_mem_recessionCone {f : E → WithTopBot α} {y : E} :
    y ∈ lin(f) ↔ y ∈ Function.recessionCone ((f)₀⁺) ∧ -y ∈ Function.recessionCone ((f)₀⁺) := by
  change y ∈ Function.constancySpace ((f)₀⁺) ↔
      y ∈ Function.recessionCone ((f)₀⁺) ∧ -y ∈ Function.recessionCone ((f)₀⁺)
  simpa using
    (Function.mem_constancySpace_iff_mem_recessionCone (f₀ := ((f)₀⁺)) (y := y))

/-- Membership in `lineal f` is exactly the textbook pair of nonpositivity inequalities for
the recession function. -/
@[simp] theorem mem_lineal_iff {f : E → WithTopBot α} {y : E} :
    y ∈ lin(f) ↔ ((f)₀⁺) y ≤ 0 ∧ ((f)₀⁺) (-y) ≤ 0 := by
  change y ∈ Function.constancySpace ((f)₀⁺) ↔ ((f)₀⁺) y ≤ 0 ∧ ((f)₀⁺) (-y) ≤ 0
  exact (Function.mem_constancySpace_iff (f₀ := ((f)₀⁺)) (y := y))

end

end Function

/-! ### Definition_8_9_1 (from Chap02) -/
noncomputable section

open scoped Rockafellar

section

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.9.1 describes the directions along which a proper convex function
  has constant translation profiles.
- `core/canonical`: the chapter already owns exactly that direction space as
  `lineal f` from Definition 8.9.0.
- `bridge/view`: the genuinely new content attached to this numbered item is the comparison with
  the epigraph lineality condition from Theorem 8.8 at slope `0`.
- Primitive data vs derived API: this file introduces no new primitive owner data. The owner is the
  existing function-facing `lineal`; the zero-slope epigraph-pair formulation is derived
  scalar-generic bridge API.
- Minimality note for the ambient layer: `lineal` itself is already defined on the generalized
  `WithTopBot α` layer in Definition 8.9.0. Correspondingly, the primitive bridge between profile
  constancy and zero translation slope is stated here on the weaker `SMulWithZero` action layer,
  while the owner-level `lin(f)` criterion and epigraph-lineality bridge are imported at the
  scalar-generic Chapter 8 layers from Corollary 8.6.1 and Theorem 8.8.
- Layer target: scalar-general `core/canonical` recall/bridge for the owner and scalar-general
  `bridge/view` theorems for the zero-slope epigraph-lineality formulation.

Domain-style sampling used here:
- `Function.lineal` and `Function.mem_lineal_iff` from Definition 8.9.0;
- `Function.forall_translate_profile_constant_iff_mem_constancySpace` from Corollary 8.6.1;
- `Function.HasTranslationSlope` from Theorem 8.8;
- `ConvexERealFunction.recessionFunction` from the nearby Chapter 2 API;
- `translation_formula_epigraph_lineality_recession_value_tfae` from Theorem 8.8;
- the set-side owner `Set.lineal`, used through `lin[𝕜](epi f)`.
-/

/- Definition 8.9.1: the source's affine-direction owner is the already owned
`Function.lineal`. -/
recall Function.lineal

/- The source-facing membership wording for that owner remains `mem_lineal_iff`. -/
recall Function.mem_lineal_iff

namespace Function

section

variable {𝕜 : Type*} [Zero 𝕜]
variable {α : Type*} [AddMonoid α] [SMulWithZero 𝕜 α]
variable {E : Type*} [AddMonoid E] [SMulWithZero 𝕜 E]

/-- A translate profile is constant in its scalar parameter exactly when its translation slope is
`0`. -/
theorem forall_translate_profile_constant_iff_hasTranslationSlope_zero
    {f : E → WithTopBot α} {y : E} :
    (∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y)) ↔
      f.HasTranslationSlope 𝕜 y (0 : α) := by
  constructor
  · intro h x τ
    have hxt : f (x + τ • y) = f (x + (0 : 𝕜) • y) := h x τ (0 : 𝕜)
    calc
      f (x + τ • y) = f (x + (0 : 𝕜) • y) := hxt
      _ = f x := by simp
      _ = f x + ((τ • (0 : α) : α) : WithTopBot α) := by simp
  · intro h x s τ
    have hs : f (x + s • y) = f x := by
      calc
        f (x + s • y) = f x + ((s • (0 : α) : α) : WithTopBot α) := h x s
        _ = f x := by simp
    have hτ : f (x + τ • y) = f x := by
      calc
        f (x + τ • y) = f x + ((τ • (0 : α) : α) : WithTopBot α) := h x τ
        _ = f x := by simp
    exact hs.trans hτ.symm

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- For a proper convex function, `y ∈ lin(f)` means exactly that every translate profile
`t ↦ f (x + t • y)` is constant in `t`. -/
@[simp] theorem mem_lineal_iff_forall_translate_profile_constant
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) ↔
      ∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y) := by
  exact
    (Function.forall_translate_profile_constant_iff_mem_constancySpace
      f hf_convex hf_proper y).symm

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- For a proper convex function, membership in `lin(f)` is equivalent to the owner-level zero
translation slope condition. -/
theorem mem_lineal_iff_hasTranslationSlope_zero
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) ↔ f.HasTranslationSlope 𝕜 y (0 : α) :=
  (mem_lineal_iff_forall_translate_profile_constant
      (f := f) hf_convex hf_proper (y := y)).trans
    forall_translate_profile_constant_iff_hasTranslationSlope_zero

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [SMul 𝕜 α]
variable {E : Type*} [AddCommGroup E] [SMul 𝕜 E]

/-- For a proper convex function, zero translation slope is equivalent to epigraph lineality at
zero slope, i.e. to membership of `(y, 0)` in `lin[𝕜](epi f)`. -/
theorem hasTranslationSlope_zero_iff_zero_mem_lin_epi
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    f.HasTranslationSlope 𝕜 y (0 : α) ↔ (y, (0 : α)) ∈ lin[𝕜](epi f) := by
  have h_tfae :=
    translation_formula_epigraph_lineality_recession_value_tfae
      (f := f) hf_convex hf_proper (y := y) (v := (0 : α))
  exact h_tfae
    (f.HasTranslationSlope 𝕜 y (0 : α))
    (by simp)
    ((y, (0 : α)) ∈ lin[𝕜](epi f))
    (by simp)

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- For a proper convex function, membership in `lin(f)` is equivalent to epigraph lineality at
zero slope, i.e. to membership of `(y, 0)` in `lin[𝕜](epi f)`. -/
@[simp] theorem mem_lineal_iff_zero_mem_lin_epi
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) ↔ (y, (0 : α)) ∈ lin[𝕜](epi f) := by
  exact (mem_lineal_iff_hasTranslationSlope_zero
      (f := f) hf_convex hf_proper (y := y)).trans
    (hasTranslationSlope_zero_iff_zero_mem_lin_epi
      (f := f) hf_convex hf_proper (y := y))

/-- Any lineality direction gives the canonical zero-slope epigraph-lineality vector. -/
theorem zero_mem_lin_epi_of_mem_lineal
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) → (y, (0 : α)) ∈ lin[𝕜](epi f) := by
  intro hy
  exact (mem_lineal_iff_zero_mem_lin_epi hf_convex hf_proper).1 hy

/-- Zero-slope epigraph-lineality membership recovers the canonical owner `lin(f)`. -/
theorem mem_lineal_of_zero_mem_lin_epi
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    (y, (0 : α)) ∈ lin[𝕜](epi f) → y ∈ lin(f) := by
  intro hy
  exact (mem_lineal_iff_zero_mem_lin_epi hf_convex hf_proper).2 hy

end

end Function

end

/-! ### Definition_8_9_2 (from Chap02) -/
noncomputable section

section

variable {𝕜 : Type*} [DivisionRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddGroup α] [ConditionallyCompleteLattice α]

open scoped Rockafellar

namespace Function

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.9.2 introduces the numerical invariants lineality and rank of a
  convex function.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.lineal` from Definition 8.9.0, reused in Definition 8.9.1 as the source's
  affine-direction space, together with the affine-dimension owner `Set.affineDim`.
- `bridge/view`: the numerical invariants are exposed directly from these owners
  rather than through a second wrapper layer.
- Primitive data vs derived API: the primitive data are the affine dimensions of `dom(f)` and of
  `lineal f`; the scalar quantities `lineality[𝕜](f)` and `rank[𝕜](f)` are derived API.

Domain-style sampling used here:
- `Set.affineDim` from Definition 2.4.10;
- `Function.lineal` and `Function.mem_lineal_iff` from Definition 8.9.0;
- `Function.mem_lineal_iff_zero_mem_lin_epi`
  from Definition 8.9.1.

Layer target: `core/canonical` owner layer on `Function`, with theorem surfaces using the
owner-level notation directly.
-/

variable (𝕜)

/-- Definition 8.9.2: the lineality of a convex function is the affine dimension of the owner
`lineal f` used in Definition 8.9.1 for its affine-direction space. -/
abbrev lineality (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] : ℤ :=
  dim[𝕜](lin(f))

scoped[Rockafellar] notation (name := functionLinealityNotation_8_9_2)
    "lineality[" 𝕜 "](" f ")" => Function.lineality 𝕜 f

/-- The lineality of a function is the affine dimension of `lineal f`. -/
theorem lineality_eq (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] :
    lineality[𝕜](f) = dim[𝕜](lin(f)) :=
  rfl

/-- Definition 8.9.2: the rank of a convex function is the affine dimension of its effective
domain minus its lineality. -/
abbrev rank (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction] : ℤ :=
  dim[𝕜](dom(f)) - lineality[𝕜](f)

scoped[Rockafellar] notation (name := functionRankNotation_8_9_2)
    "rank[" 𝕜 "](" f ")" => Function.rank 𝕜 f

/-- The rank of a function is the affine dimension of its effective domain minus its lineality. -/
theorem rank_eq (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction] :
    rank[𝕜](f) = dim[𝕜](dom(f)) - lineality[𝕜](f) :=
  rfl

end Function

end

/-! ### Theorem_8_9_3 (from Chap02) -/
noncomputable section

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} [DivisionRing 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α] [Module 𝕜 α]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.9.3 identifies the proper convex functions of rank `0` with the
  partial affine functions.
- `core/canonical`: the owner objects already present in the project are the chapter predicates
  `Function.IsProper` and `Function.IsConvex`, together with the affine-support owner
  `AffineSubspace 𝕜 E` and the intrinsic affine-branch owner `affOn[𝕜](·, ·)`, the Chapter 1
  codomain-lift owner
  `Function.toWithTopBot`, and the Chapter 1 support-cut owner
  `Function.toWithTopBotOn` together with its source-facing bridge
  `Function.toWithTopBotOn_eq_add_indicator`.
- `bridge/view`: the textbook phrase "agree with an affine function on an affine set and are `⊤`
  elsewhere" is expressed on theorem surfaces by the canonical extension owner
  `g.toWithTopBotOn M`, with equivalent source-facing support-cut formula
  `Function.toWithTopBot g + δ(· | M)` available from
  `Function.toWithTopBotOn_eq_add_indicator`; no separate project-local wrapper predicate
  is needed.

Domain-style sampling used here:
- `Function.IsProper` from `Definition_4_6`;
- `Function.IsConvex` from `Theorem_4_2`;
- the chapter affine-on-a-support owner `affOn[𝕜](·, ·)` from `Definition_4_3`;
- mathlib's affine-support owner `AffineSubspace 𝕜 E`;
- `Function.toWithTopBotOn` from `Remark_4_4_5`;
- `Function.toWithTopBotOn_eq_add_indicator` from `Remark_4_4_5`;
- the later project owner shape for partial functions in `Text_12_3_3`, which uses the same
  support-cut owner on an affine support.

Primitive data vs derived API:
- partial affineness is a property of a `WithTopBot α`-valued function relative to an affine
  support set, with primitive affine data given by an ambient branch and intrinsic
  `affOn[𝕜](·, ·)`
  control on that support;
- the primitive owner surface is the canonical extension owner `g.toWithTopBotOn M`, while the
  equivalent source-facing support-cut formula
  `Function.toWithTopBot g + δ(· | M)` and the piecewise formulas,
  properties such as `dom(f) = M` are derived API.

Ambient-layer note:
- this file now exposes Theorem 8.9.3 on the same scalar/codomain owner layer already used by
  `lin` and `rank`: scalar `𝕜` with `DivisionRing` + `PartialOrder`, and codomain `α` carried
  by `WithTopBot α` with the canonical additive/order structure used by recession and lineality
  owners.

Layer target: this item stays `source-facing`, but its public statement now uses the affine-support
owner data directly through the chapter extension owner `toWithTopBotOn`, with the support-cut
formula exposed as a bridge, instead of introducing a one-off `Function.IsPartialAffine`
predicate or a separate domain-equality wrapper.
-/

namespace Function

/-- Checked owner-layer bridge on the codomain-generalized layer:
`lin(f)` is still the constancy-space owner of the recession function. -/
theorem lineal_eq_constancySpace_recessionFunction
    {E : Type*} [Add E] [Neg E]
    {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α]
    (f : E → WithTopBot α) :
    lin(f) = Function.constancySpace ((f)₀⁺) := by
  simpa using (lineal_eq_constancySpace (f := f))

/-- Checked owner-layer bridge on the codomain-generalized layer:
`rank[𝕜](f)` is still the affine-dimension difference `dim(dom f) - lineality[𝕜](f)`. -/
theorem rank_eq_dim_dom_sub_lineality
    {𝕜 : Type*} [DivisionRing 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α]
    (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction] :
    rank[𝕜](f) = dim[𝕜](dom(f)) - lineality[𝕜](f) := by
  simpa using (rank_eq (𝕜 := 𝕜) (f := f))

/-- Checked owner-layer bridge on the codomain-generalized layer:
global convexity is still epigraph convexity. -/
theorem isConvex_iff_convex_epi_codomainLayer
    {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E]
    {α : Type*} [AddCommMonoid α] [LE α] [SMul 𝕜 α]
    (f : E → WithTopBot α) :
    Function.IsConvex 𝕜 f ↔ Convex 𝕜 (epi f) := by
  simpa using (Function.isConvex_iff_convex_epi (𝕜 := 𝕜) f)

/-- Checked support-cut bridge on affine supports at the codomain-generalized layer. -/
theorem toWithTopBotOn_eq_add_indicator_affineSubspace
    {𝕜 : Type*} [DivisionRing 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {α : Type*} [AddZeroClass α]
    (g : E → α) (M : AffineSubspace 𝕜 E) :
    g.toWithTopBotOn M = toWithTopBot g + (δ(· | M)) := by
  simpa using (Function.toWithTopBotOn_eq_add_indicator g (M : Set E))

/-- Theorem 8.9.3 in extension-owner form: a proper convex function has rank `0` if and only if it is
partial affine, meaning that it agrees with an affine branch on an affine support set and equals
`⊤` off that support. -/
-- Proof sketch: for the forward implication, let `M` be the affine hull of the effective domain.
-- Rank `0` means that the affine dimension of `dom f` equals the affine dimension of the
-- constancy space of `f0⁺`, so the lineality bridge forces `f` to be affine along every line in
-- `M`
-- parallel to that lineality space, yielding an affine functional whose finite branch on `M`
-- gives the displayed partial-affine normal form; properness forces the off-support values to be
-- `⊤`. For the reverse implication, a function of the displayed form has effective domain `M`,
-- its recession function is odd on every direction parallel to `M`, so the constancy space has
-- the same affine dimension as `dom f`, giving rank `0`.
theorem rank_eq_zero_iff_exists_affOn_support
    (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction]
    (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    rank[𝕜](f) = 0 ↔
      ∃ (M : AffineSubspace 𝕜 E) (g : E → α),
        affOn[𝕜](g, M) ∧
          f = g.toWithTopBotOn M := sorry

/-- Source-facing bridge form of Theorem 8.9.3 using `f = g.toWithTopBot + δ(· | M)`. -/
theorem rank_eq_zero_iff_exists_affOn_add_indicator
    (f : E → WithTopBot α)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction]
    (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    rank[𝕜](f) = 0 ↔
      ∃ (M : AffineSubspace 𝕜 E) (g : E → α),
        affOn[𝕜](g, M) ∧
          f = toWithTopBot g + (δ(· | M)) := by
  simpa [Function.toWithTopBotOn_eq_add_indicator] using
    (rank_eq_zero_iff_exists_affOn_support
      (f := f) hf_proper hf_convex)

end Function

/-! ### Theorem_8_9_4 (from Chap02) -/
noncomputable section

namespace ConvexERealFunction

section

/-!
Source/core/bridge triage:

  `rank[𝕜](f) = aff dim(dom f)` for a closed
  proper convex function by excluding nontrivial affine-line directions on which all translate
  profiles are constant.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.lineal f`, `Function.lineality`, `Function.rank`, `dom(·)`,
  `Set.affineDim`, `Function.IsProper`, and `Function.IsConvex`.
- `bridge/view`: the owner-level equivalence `lineality[𝕜](f) = 0 ↔ ...` is the canonical
  bridge from
  `Function.lineal f` to the source's affine-line exclusion, while the displayed rank formula is
  the source-facing corollary obtained from `rank_eq`.

Domain-style sampling used here:
- `Function.lineality` and `Function.lineality_eq` from `Definition_8_9_2`;
- `Function.lineal` from `Definition_8_9_0`;
- `Function.forall_translate_profile_constant_iff_mem_constancySpace`
  from `Corollary_8_6_1`;
- `Function.mem_constancySpace_of_exists_upper_bound_along_line`
  from `Corollary_8_6_1`;
- `Function.rank` and `Function.rank_eq` from `Definition_8_9_2`;
- `dom(·)` from `Definition_4_4` together with `Set.affineDim` from `Definition_2_4_10`;
- `Function.constancySpace` and `Function.mem_constancySpace_iff_mem_recessionCone`
  from `Definiton_8_7_0`.

Primitive data vs derived API:
- primitive data: only the function `f : E → WithTopBot 𝕜`;
- owner-side derived API:
  `lineality[𝕜](f)`, `rank[𝕜](f)`, `dim[𝕜](dom(f))`, convexity, properness,
  and closedness;
- source-facing derived view retained here: the quantified affine-line exclusion
  `¬ ∃ y ≠ 0, ∃ x ∈ dom(f), ∀ t, f (x + t • y) = f x`.

Layer target:
- `bridge/view`: `lineality_eq_zero_iff_not_exists_affineLine`;
- `source-facing`: `rank_eq_dim_dom_iff_not_exists_affineLine`.
-/

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

open scoped Rockafellar

variable (f : E → WithTopBot 𝕜)
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem affDim_eq_zero_iff_not_exists_ne_zero_mem {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (h0 : (0 : E) ∈ C) :
    dim[𝕜](C) = 0 ↔ ¬ ∃ y : E, y ≠ 0 ∧ y ∈ C := by
  constructor
  · intro hC hy
    rcases hy with ⟨y, hyne, hy⟩
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 C
    have h0A : (0 : E) ∈ A := (subset_affineSpan 𝕜 C) h0
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hfin : Module.finrank 𝕜 A.direction = 0 := by
      rw [show dim[𝕜](C) = A.affineDim by rfl, AffineSubspace.affineDim, if_neg hAne] at hC
      exact_mod_cast hC
    have hdir : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have hyA : y ∈ A := (subset_affineSpan 𝕜 C) hy
    have hydir : y ∈ A.direction := by
      simpa using A.vsub_mem_direction hyA h0A
    have hy0 : y = 0 := by
      simpa [hdir] using hydir
    exact hyne hy0
  · intro hC
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 C
    have h0A : (0 : E) ∈ A := (subset_affineSpan 𝕜 C) h0
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hsubset : C ⊆ ({0} : Set E) := by
      intro y hy
      by_contra hy0
      exact hC ⟨y, by simpa using hy0, hy⟩
    have hsubset0 : ({0} : Set E) ⊆ C := by
      intro y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      simpa [hy0] using h0
    have hspan : affineSpan 𝕜 C = affineSpan 𝕜 ({0} : Set E) :=
      le_antisymm (affineSpan_mono 𝕜 hsubset) (affineSpan_mono 𝕜 hsubset0)
    have hdir : A.direction = ⊥ := by
      calc
        A.direction = (affineSpan 𝕜 ({0} : Set E)).direction := by
          simp [A, hspan]
        _ = vectorSpan 𝕜 ({0} : Set E) := by
          rw [direction_affineSpan 𝕜 ({0} : Set E)]
        _ = ⊥ := by
          rw [vectorSpan_singleton 𝕜 (0 : E)]
    rw [show dim[𝕜](C) = A.affineDim by rfl, AffineSubspace.affineDim, if_neg hAne, hdir]
    norm_num

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] in
private theorem zero_mem_lineal
    (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    (0 : E) ∈ lin(f) := by
  have hconst :
      ∀ x : E, ∀ s t : 𝕜, f (x + s • (0 : E)) = f (x + t • (0 : E)) := by
    intro x s t
    simp
  have h0_lineal : (0 : E) ∈ lin(f) :=
    (Function.forall_translate_profile_constant_iff_mem_constancySpace
        f hf_convex hf_proper (0 : E)).1
      hconst
  exact h0_lineal

omit [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] in
private theorem exists_affineLine_iff_exists_ne_zero_mem_lineal
    (hf_closed : LowerSemicontinuous f) (hf_proper : f.IsProper)
    (hf_convex : f.IsConvex 𝕜) :
    (∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x) ↔
      ∃ y : E, y ≠ 0 ∧ y ∈ lin(f) := by
  constructor
  · rintro ⟨y, hyne, x, hxdom, hline⟩
    have hfx_top : f x < (⊤ : WithTopBot 𝕜) := by
      simpa [mem_effectiveDomain] using hxdom
    have hline_le : ∀ t : 𝕜, f (x + t • y) ≤ f x := by
      intro t
      exact le_of_eq (hline t)
    refine ⟨y, hyne, ?_⟩
    exact
      Function.mem_constancySpace_of_exists_upper_bound_along_line
        (f := f) hf_convex hf_proper hf_closed y
        ⟨x, f x, hfx_top, hline_le⟩
  · rintro ⟨y, hyne, hylineal⟩
    have hconst :
        ∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y) :=
      (Function.forall_translate_profile_constant_iff_mem_constancySpace
          f hf_convex hf_proper y).2
        hylineal
    rcases hf_proper.nonempty_dom with ⟨x, hxdom⟩
    refine ⟨y, hyne, x, hxdom, ?_⟩
    intro t
    simpa using hconst x t (0 : 𝕜)

namespace Function

/-- Theorem 8.9.4, owner bridge: a closed proper convex function has zero lineality if and only if
`lin(f)` is trivial, equivalently it has no nontrivial affine-line direction through a
finite point on which `f` is constant. -/
theorem lineality_eq_zero_iff_not_exists_affineLine
    (hf_closed : LowerSemicontinuous f) (hf_proper : f.IsProper)
    (hf_convex : f.IsConvex 𝕜) :
    lineality[𝕜](f) = 0 ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  have hzero_mem_lineal : (0 : E) ∈ lin(f) :=
    zero_mem_lineal (f := f) hf_proper hf_convex
  have hlineality :
      lineality[𝕜](f) = 0 ↔ ¬ ∃ y : E, y ≠ 0 ∧ y ∈ lin(f) := by
    simpa [Function.lineality_eq (𝕜 := 𝕜) (f := f)] using
      (affDim_eq_zero_iff_not_exists_ne_zero_mem (C := lin(f)) hzero_mem_lineal)
  have hExists :
      (∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x) ↔
        ∃ y : E, y ≠ 0 ∧ y ∈ lin(f) :=
    exists_affineLine_iff_exists_ne_zero_mem_lineal (f := f) hf_closed hf_proper hf_convex
  exact hlineality.trans (not_congr hExists).symm

namespace IsClosedProperConvex

/-- Owner-bundled bridge form: the affine-line exclusion criterion can be used directly from
`hf : IsClosedProperConvex[𝕜] f` without repeatedly unpacking lower-semicontinuity, properness,
and convexity assumptions at call sites. -/
theorem lineality_eq_zero_iff_not_exists_affineLine
    (hf : Function.IsClosedProperConvex (𝕜 := 𝕜) f) :
    Function.lineality[𝕜](f) = 0 ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  exact
    Function.lineality_eq_zero_iff_not_exists_affineLine
      (f := f) hf.lowerSemicontinuous hf.proper hf.convex

end IsClosedProperConvex

variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction]

-- Proof sketch: the owner bridge identifies the affine-line exclusion with
-- `lineality[𝕜](f) = 0`.
-- Combining that with `rank_eq`, the source identity
-- `rank[𝕜](f) = dim[𝕜](dom(f))` is exactly the same
-- vanishing-lineality condition, so the public theorem only needs the finite-dimensionality
-- instances already used by those owner invariants.
/-- Theorem 8.9.4: a closed proper convex function has rank equal to the affine dimension of its
effective domain if and only if it has no nontrivial affine-line direction through a finite point
on which `f` is constant. The public statement is organized at the owner level of `rank` and
`lineality`, so it assumes finite-dimensionality only for the affine spans of `dom f` and of the
space `lin(f)`. -/
theorem rank_eq_dim_dom_iff_not_exists_affineLine
    (hf_closed : LowerSemicontinuous f) (hf_proper : f.IsProper)
    (hf_convex : f.IsConvex 𝕜) :
    rank[𝕜](f) = dim[𝕜](dom(f)) ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  constructor
  · intro hrank
    have hlineality : lineality[𝕜](f) = 0 := by
      have hrank' : dim[𝕜](dom(f)) - lineality[𝕜](f) = dim[𝕜](dom(f)) := by
        simpa [Function.rank_eq (𝕜 := 𝕜) (f := f), Function.lineality] using hrank
      linarith
    exact (lineality_eq_zero_iff_not_exists_affineLine f hf_closed hf_proper hf_convex).1
      hlineality
  · intro hnoAffineLine
    have hlineality : lineality[𝕜](f) = 0 :=
      (lineality_eq_zero_iff_not_exists_affineLine f hf_closed hf_proper hf_convex).2
        hnoAffineLine
    rw [Function.rank_eq (𝕜 := 𝕜) (f := f)]
    simpa [Function.lineality, hlineality]

namespace IsClosedProperConvex

/-- Owner-bundled bridge form of `rank_eq_dim_dom_iff_not_exists_affineLine`. -/
theorem rank_eq_dim_dom_iff_not_exists_affineLine
    (hf : Function.IsClosedProperConvex (𝕜 := 𝕜) f) :
    Function.rank[𝕜](f) = dim[𝕜](dom(f)) ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  exact
    Function.rank_eq_dim_dom_iff_not_exists_affineLine
      (f := f) hf.lowerSemicontinuous hf.proper hf.convex

end IsClosedProperConvex

end Function

end

end

end

end ConvexERealFunction

/-! ### Theorem_8_9_5 (from Chap02) -/
noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {𝕜 : Type*} [DivisionRing 𝕜] [LE 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddGroup α] [ConditionallyCompleteLattice α]

open scoped Pointwise Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.9.5 compares the rank of a convex set with the rank of its
  indicator.
- `core/canonical`: the owner abstractions already present upstream are `Set.rank`,
  `Function.rank` on `WithBotTop α` (written source-facingly as `rank[𝕜](f)`), the
  indicator-function owner `indicator`, and the function-side lineality owner `Function.lineal`.
- `bridge/view`: the indicator function is the canonical function-side view of a set, so the
  theorem should be stated directly as an equality between the existing set-side and function-side
  rank owners, not by introducing a new packaged indicator-rank wrapper.

Domain-style sampling used here:
- `Set.rank` from Definition 8.4.6;
- `Function.rank` / notation `rank[𝕜](f)` from Definition 8.9.2;
- `indicator` and `effectiveDomain_indicator` from Definition 4.8.1;
- `Function.lineal` from Definition 8.9.0;
- `lineal_indicator_eq_lineal` from Theorem 8.7.

Primitive data vs derived API:
- primitive input: the set `C : Set E`;
- derived owner view: the function `δ[α](· | C)`;
- derived theorem-level content: the equality of the set-side and function-side rank invariants.

Layer target: `bridge/view`, preserving `Set.rank` as the set-side owner and using the indicator
owner only as the canonical function-side comparison view.
-/

namespace Set

section

variable {C : Set E}
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]

/-- Owner-level core: once the canonical bridge
`Function.lineal (δ[α](· | C)) = lin[𝕜](C)` is available, rank comparison is purely
`Set.rank`/`Function.rank` bookkeeping. -/
theorem rank_eq_rank_indicator_of_lineal_eq_lineal
    (hlineal : lin(δ[α](· | C)) = lin[𝕜](C)) :
    rank[𝕜](C) = rank[𝕜](δ[α](· | C)) := by
  letI : FiniteDimensional 𝕜 (affineSpan 𝕜 (dom((δ[α](· | C))))).direction := by
    have hdom : dom((δ[α](· | C))) = C := by
      simpa using (effectiveDomain_indicator (α := α) C)
    exact hdom.symm ▸
      (inferInstance : FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction)
  letI : FiniteDimensional 𝕜 (affineSpan 𝕜 (lin(δ[α](· | C)))).direction := by
    rw [hlineal]
    infer_instance
  have hdom : dom((δ[α](· | C))) = C := by
    simpa using (effectiveDomain_indicator (α := α) C)
  rw [Set.rank_eq, Function.rank_eq, Function.lineality_eq]
  simp [hdom, hlineal]

end

section

variable {𝕜 : Type*} [DivisionRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [FloorSemiring 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [IsOrderedAddMonoid α]

variable {C : Set E}

variable [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]

/-- Theorem 8.9.5: the rank of a convex set equals the rank of its indicator. -/
theorem rank_eq_rank_indicator (hC_convex : Convex 𝕜 C) :
    rank[𝕜](C) = rank[𝕜](δ[α](· | C)) := by
  exact rank_eq_rank_indicator_of_lineal_eq_lineal
    (lineal_indicator_eq_lineal (α := α) (𝕜 := 𝕜) (C := C) hC_convex)

end

end Set

end
