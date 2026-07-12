import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

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
