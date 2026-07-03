import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_9_4 (from Chap02) -/
section

universe u v

variable {I : Sort v}

namespace Function

section Properness

variable {E : Type u}
variable {α : Type*} [ConditionallyCompleteLattice α]

/-- Theorem 9.4 (2), owner-level strengthening: if every finite point of the pointwise supremum
admits a branch value strictly above `⊥`, and that supremum has nonempty effective domain, then
the supremum is proper.
The source hypothesis "nonempty family and every `f_i` proper" is a stronger sufficient condition.
This clause is naturally owned by `Function.IsProper`, so it is exposed directly in the
`Function` namespace rather than through a parallel `ConvexERealFunction` wrapper. -/
-- Proof sketch: a point of `dom(⨆ i, f i)` gives nonemptiness of `dom(⨆ i, f i)`. For any `y`,
-- if `(⨆ i, f i) y = ⊤` then it is automatically not `⊥`; otherwise `y ∈ dom(⨆ i, f i)`.
-- The hypothesis then gives an index `i` with `⊥ < f i y`. Taking the supremum preserves
-- this lower bound,
-- so `(⨆ i, f i) y ≠ ⊥`.
theorem IsProper.iSup_of_dom_nonempty
    (f : I → E → WithTopBot α)
    (hbot : ∀ x ∈ dom(⨆ i, f i), ∃ i, (⊥ : WithTopBot α) < f i x)
    (hdom : dom(⨆ i, f i).Nonempty) :
    (⨆ i, f i).IsProper := by
  refine (isProper_iff _).2 ?_
  refine ⟨hdom, ?_⟩
  intro y
  by_cases htop : (⨆ i, f i) y = ⊤
  · simp [htop]
  · have hy_dom : y ∈ dom(⨆ i, f i) := by
      exact mem_effectiveDomain.mpr (lt_of_le_of_ne le_top htop)
    rcases hbot y hy_dom with ⟨i, hi_bot⟩
    exact (bot_lt_iff_ne_bot).1 <|
      lt_of_lt_of_le hi_bot <| by
        simpa [iSup_apply] using (le_iSup (fun j ↦ f j y) i)

end Properness

end Function

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 9.4 studies the pointwise supremum
  `f = sup_i fᵢ` of an arbitrary family of convex functions, with closed-family clauses about
  closedness, properness, and recession
  functions, and one common-relative-interior clause about closures.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsConvex`, `LowerSemicontinuous`, `Function.IsProper`,
  `Function.recessionFunction`, and `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `f` is the pointwise supremum `⨆ i, f i`; his `cl f` is the
  chapter owner `lowerSemicontinuousHull f`; and `ri (dom fᵢ)` is represented directly by the
  effective-domain owner `riDom[𝕜](f i)` in the scalar-generic closure clause.

Domain-style sampling used here:
- `Function.IsConvex.iSup`;
- `lowerSemicontinuous_iSup`;
- `Function.IsProper`;
- `Function.recessionFunction_isLeast_translationUpperBounds`.

Primitive data vs derived API:
- primitive data: the indexed family `f : I → E → WithTopBot α`,
  with the scalar `𝕜` for convex structure kept separate from the codomain `α` for
  order/topology owners;
- owner hypotheses: convexity for the family; finite-point local `⊥`-exclusion for the properness
  clause; pointwise `⊥`-exclusion together with `Nonempty I` for the recession clause;
  lower semicontinuity for the closed-family clauses; and a common relative-interior point for the
  closure clause;
- derived API: the already-owned convexity and lower semicontinuity of `⨆ i, f i`, the owner
  properness theorem `Function.IsProper.iSup_of_dom_nonempty`, and the source-facing
  recession-function formula together with the lower-semicontinuous-hull formula.

Layer target: `source-facing`, with all clauses attached directly to the canonical owner namespace
`Function`, while reusing the earlier project owner theorem `Function.IsConvex.iSup` instead of
restating the convexity clause locally.

Ambient-space refinement: the source's `R^n` statements are split across the weakest owner-level
ambient assumptions needed by each clause. Only the common-relative-interior closure clause keeps
the finite-dimensional ordered normed-field layer; the convexity, lower-semicontinuity,
properness, and recession clauses all live at more intrinsic scalar-generic owner levels.
-/

section Convexity

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [SMul 𝕜 α] [ConditionallyCompleteLattice α]

/- The convexity clause for `⨆ i, f i` already appeared as Theorem 5.5, so this file reuses the
canonical owner theorem directly rather than keeping a parallel local restatement. -/
recall Function.IsConvex.iSup

end Convexity

section Closedness

variable {E : Type u} [TopologicalSpace E]

/- Theorem 9.4 (1): if every `fᵢ` is closed, then their pointwise supremum is closed. This is
exactly the canonical owner theorem `lowerSemicontinuous_iSup`, so the main entry is a direct
recall rather than a parallel local wrapper. -/
recall lowerSemicontinuous_iSup

end Closedness

section Properness

variable {E : Type u}

/- Theorem 9.4 (2): the source hypothesis "nonempty family and every `fᵢ` proper" yields this
owner-level criterion: if the supremum has nonempty effective domain and every finite value of the
supremum is strictly above `⊥` along at least one branch, then the supremum is proper.
This clause is already owned by
`Function.IsProper.iSup_of_dom_nonempty`, so the source-facing entry here is a direct recall. -/
recall Function.IsProper.iSup_of_dom_nonempty

end Properness

section Recession

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [SMul 𝕜 α] [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E]
variable (f : I → E → WithTopBot α)

open scoped Rockafellar

-- Proof sketch: the scalar epigraph of `⨆ i, f i` is the intersection of the scalar epigraphs of
-- the `f i`. Under closed convexity and one point in the effective domain of the supremum,
-- Corollary 8.3.3 gives
-- the recession cone of this intersection as the intersection of the recession cones, which is
-- exactly the pointwise supremum formula for recession functions.
/-- Theorem 9.4 (3): if a nonempty family `f_i` is closed convex and pointwise strictly above `⊥`,
and the pointwise supremum has nonempty effective domain, then the recession function of the
supremum is the pointwise supremum of the recession functions `f_i0⁺`. -/
theorem recessionFunction_iSup_eq_iSup_recessionFunction
    [Nonempty I]
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, (⊥ : WithTopBot α) < f i x)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hdom : dom(⨆ i, f i).Nonempty) :
    (⨆ i, f i)₀⁺ = ⨆ i, (f i)₀⁺ := sorry

end Recession

section LowerSemicontinuousHull

variable {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {α : Type*}
  [AddCommMonoid α] [SMul 𝕜 α] [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable (f : I → E → WithTopBot α)

open scoped Rockafellar

-- Proof sketch: Lemma 7.3 identifies a point of `⋂ i, ri (dom f_i)` with a common
-- relative-interior point of the epigraphs of the `f i` once the height is chosen above the
-- finite value of the pointwise supremum at that same point.
-- Theorem 6.5 then turns the intersection formula for epigraph closures into the pointwise formula
-- `cl (sup_i f_i) = sup_i cl f_i`. Unlike the
-- properness clauses, this identity does not need `[Nonempty I]`: for an empty family the
-- hypotheses are vacuous and both sides are the constant `⊥` function.
/-- Theorem 9.4 (4): if the common-relative-interior set and the effective domain of the pointwise
supremum meet, then the closure `cl f` of the supremum is the pointwise supremum of the closures
`cl f_i`. -/
theorem lowerSemicontinuousHull_iSup_eq_iSup_of_nonempty_iInter_riDom_and_dom
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hri_dom : ((⋂ i, riDom[𝕜](f i)) ∩ dom(⨆ i, f i)).Nonempty) :
    cl(⨆ i, f i) = ⨆ i, cl(f i) := sorry

end LowerSemicontinuousHull

end Function

end
