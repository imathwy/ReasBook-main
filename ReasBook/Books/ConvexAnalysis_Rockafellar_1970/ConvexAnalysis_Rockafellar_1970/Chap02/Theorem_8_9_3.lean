import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_2

-- Declarations for this item will be appended below by the statement pipeline.

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
