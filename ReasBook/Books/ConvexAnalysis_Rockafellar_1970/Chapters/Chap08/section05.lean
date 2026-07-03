

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_8_5_1 (from Chap02) -/
universe u v w

section

variable {E : Type u}
variable {α : Type v}

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.5.1 says that for a proper convex function `f`, the recession
  function `f0⁺` is the least function `h` satisfying the translation inequality
  `f (x + y) ≤ f x + h y`.
- `core/canonical`: the owner is `Function.recessionFunction` on a `WithTopBot α`-valued function
  `f : E → WithTopBot α`, and the least-element conclusion is naturally expressed by `IsLeast` in
  the pointwise ordered function lattice `E → WithTopBot α`. The primitive leastness layer is the
  difference-bound surface `f (x + y) - f x ≤ h y` over base points `x ∈ dom(f)`; the
  translation-inequality form is a derived bridge requiring properness.
- `bridge/view`: the previous theorem's formula for `f0⁺` is rendered concretely as the supremum of
  the finite differences `f (x + y) - f x` over base points in `dom(f)`.

Domain-style sampling used here:
- the chapter owner `Function.IsProper` and its pointwise bridge
  `Function.isProper_iff` from `Definition_4_6`;
- the chapter effective-domain owner `dom(·)` with membership theorem `mem_effectiveDomain`;
- the complete-lattice least-element interface `IsLeast` on function spaces;
- the supremum construction `sSup` on `WithTopBot α`.

Primitive data vs derived API:
- primitive input: the function `f`;
- source-facing object introduced here: `recessionFunction f`;
- derived API: the translation-inequality least-element statement for `recessionFunction f` in
  the pointwise ordered function space, most canonically parameterized by the translation
  increment `y` in `f (x + y) ≤ f x + h y`; on additive groups, the textbook
  `f z ≤ f x + h (z - x)` form is the corresponding reindexing `y = z - x`.

Editorial note: the source text is truncated after the opening of a second sentence beginning
"Let `g` be the positively ...". Only the visible least-element clause is formalized here.
-/

/-- The recession function `f0⁺` is the supremum of the differences `f (x + y) - f x` over
points `x` in `dom(f)`. -/
noncomputable def recessionFunction [Add E] [AddGroup α]
    [ConditionallyCompleteLattice α] (f : E → WithTopBot α) (y : E) : WithTopBot α :=
  sSup {r : WithTopBot α | ∃ x ∈ dom(f), r = f (x + y) - f x}

end Function

namespace Rockafellar

/- Rockafellar's recession-function notation. In `open scoped Rockafellar`, a term `f` can be
written as `(f)₀⁺`. -/

scoped postfix:max "₀⁺" => Function.recessionFunction

end Rockafellar

namespace Function

open scoped Rockafellar

section

variable [Add E] [AddGroup α] [ConditionallyCompleteLattice α]
variable (f : E → WithTopBot α)

-- Proof sketch: unfold `recessionFunction`; the right-hand side is exactly its defining
-- supremum formula.
/-- The defining formula for the recession function is the supremum over the effective domain. -/
@[simp] theorem recessionFunction_apply (y : E) :
    ((f)₀⁺) y = sSup {r : WithTopBot α | ∃ x ∈ dom(f), r = f (x + y) - f x} :=
  rfl

end

section

variable [Add E]
variable [Preorder α] [AddGroup α]

/-- `h` is a difference upper bound for `f` when each finite base point `x ∈ dom(f)` satisfies
`f (x + y) - f x ≤ h y` for every translation increment `y`. This is the primitive surface
matching the defining supremum of `recessionFunction`. -/
def DifferenceUpperBound (f h : E → WithTopBot α) : Prop :=
  ∀ x ∈ dom(f), ∀ y, f (x + y) - f x ≤ h y

end

section

variable [Add E]
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable (f : E → WithTopBot α)

/-- The recession function is the least difference upper bound over the effective domain. -/
theorem recessionFunction_isLeast_differenceUpperBounds :
    IsLeast {h : E → WithTopBot α | DifferenceUpperBound f h} ((f)₀⁺) := by
  refine ⟨?_, ?_⟩
  · intro x hx y
    rw [recessionFunction_apply]
    exact le_sSup ⟨x, hx, rfl⟩
  · intro h hh y
    rw [recessionFunction_apply]
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact hh x hx y

end

section

variable [Add E]
variable [Preorder α] [Add α]

/-- `h` is a translation upper bound for `f` when every finite base point `x ∈ dom(f)` satisfies
`f (x + y) ≤ f x + h y` for every translation increment `y`. -/
def TranslationUpperBound (f h : E → WithTopBot α) : Prop :=
  ∀ x ∈ dom(f), ∀ y, f (x + y) ≤ f x + h y

end

section

variable [Add E]
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
variable (f : E → WithTopBot α)

/-- Translation and difference upper bounds are equivalent under the primitive local assumption
that finite base points are never mapped to `⊥`. -/
theorem translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α)) {h : E → WithTopBot α} :
    TranslationUpperBound f h ↔ DifferenceUpperBound f h := by
  constructor
  · intro hh x hx y
    have hx_ne_bot : f x ≠ (⊥ : WithTopBot α) := hf_ne_bot x hx
    have hx_ne_top : f x ≠ (⊤ : WithTopBot α) := ne_of_lt (mem_effectiveDomain.mp hx)
    have hxy : f (x + y) ≤ f x + h y := hh x hx y
    exact (WithBotTop.sub_le_iff_le_add (b := f x) (c := h y)
      (Or.inl hx_ne_bot) (Or.inl hx_ne_top)).2 (by simpa [add_comm] using hxy)
  · intro hh x hx y
    have hx_ne_bot : f x ≠ (⊥ : WithTopBot α) := hf_ne_bot x hx
    have hx_ne_top : f x ≠ (⊤ : WithTopBot α) := ne_of_lt (mem_effectiveDomain.mp hx)
    have hxy : f (x + y) - f x ≤ h y := hh x hx y
    simpa [add_comm] using
      (WithBotTop.sub_le_iff_le_add (b := f x) (c := h y)
        (Or.inl hx_ne_bot) (Or.inl hx_ne_top)).1 hxy

/-- Under properness, translation and difference upper bounds are equivalent. -/
theorem translationUpperBound_iff_differenceUpperBound
    (hf_proper : f.IsProper) {h : E → WithTopBot α} :
    TranslationUpperBound f h ↔ DifferenceUpperBound f h :=
  translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot
    (f := f) (h := h) (fun x _ => hf_proper.ne_bot x)

end

section

variable [Add E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable (f : E → WithTopBot α)

-- Proof sketch: use the preceding theorem's formula
-- `f0⁺ y = sSup {f (x + y) - f x | x ∈ dom(f)}`. If `h` satisfies the
-- translation inequality at every base point `x ∈ dom(f)`, specialize it to `z = x + y` to
-- obtain `f (x + y) - f x ≤ h y` for every admissible `x`, hence `f0⁺ y ≤ h y` after taking the
-- supremum. Applying the same formula with `h = f0⁺` gives the required translation inequality
-- for `f0⁺` itself, so it is the least such function.
/-- The recession function is the least translation upper bound under the primitive local
assumption that finite base points are never mapped to `⊥`. -/
theorem recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α)) :
    IsLeast {h : E → WithTopBot α | TranslationUpperBound f h} ((f)₀⁺) := by
  refine ⟨?_, ?_⟩
  · exact (translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot (f := f)
      (h := ((f)₀⁺)) hf_ne_bot).2
      (recessionFunction_isLeast_differenceUpperBounds (f := f)).1
  · intro h hh
    exact (recessionFunction_isLeast_differenceUpperBounds (f := f)).2
      ((translationUpperBound_iff_differenceUpperBound_of_dom_ne_bot
        (f := f) (h := h) hf_ne_bot).1 hh)

-- Proof sketch: properness gives exactly the local finite-point non-`⊥` condition required by the
-- primitive theorem above, so the source-facing statement is an immediate specialization.
/-- Corollary 8.5.1: for a proper function `f`, the recession function `f0⁺` is the least
function `h` such that `f (x + y) ≤ f x + h y` for all base points `x ∈ dom(f)` and translation
increments `y`. On additive groups this is equivalent to the textbook form
`f z ≤ f x + h (z - x)` for all `z` and `x ∈ dom(f)`. -/
theorem recessionFunction_isLeast_translationUpperBounds
    (hf_proper : f.IsProper) :
    IsLeast {h : E → WithTopBot α | TranslationUpperBound f h} ((f)₀⁺) :=
  recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot (f := f)
    (fun x _ => hf_proper.ne_bot x)

/-- The recession function is itself a translation upper bound under the primitive local
finite-point non-`⊥` condition. -/
theorem recessionFunction_translationUpperBound_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α)) :
    TranslationUpperBound f ((f)₀⁺) :=
  (recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot (f := f) hf_ne_bot).1

/-- Any translation upper bound dominates the recession function pointwise under the primitive
local finite-point non-`⊥` condition. -/
theorem recessionFunction_le_of_translationUpperBound_of_dom_ne_bot
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithTopBot α))
    {h : E → WithTopBot α}
    (hh : TranslationUpperBound f h) :
    ((f)₀⁺) ≤ h :=
  (recessionFunction_isLeast_translationUpperBounds_of_dom_ne_bot (f := f) hf_ne_bot).2 hh

/-- The recession function is itself a translation upper bound. -/
theorem recessionFunction_translationUpperBound
    (hf_proper : f.IsProper) :
    TranslationUpperBound f ((f)₀⁺) :=
  recessionFunction_translationUpperBound_of_dom_ne_bot (f := f) (fun x _ => hf_proper.ne_bot x)

/-- Any translation upper bound dominates the recession function pointwise. -/
theorem recessionFunction_le_of_translationUpperBound
    (hf_proper : f.IsProper) {h : E → WithTopBot α}
    (hh : TranslationUpperBound f h) :
    ((f)₀⁺) ≤ h :=
  recessionFunction_le_of_translationUpperBound_of_dom_ne_bot (f := f)
    (fun x _ => hf_proper.ne_bot x) hh

end

end Function

end

/-! ### Corollary_8_5_2 (from Chap02) -/
noncomputable section

section

open Filter
open scoped Rockafellar

variable {E : Type*} {𝕜 : Type*}

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.5.2 states that the right scalar multiples `f_λ` converge to the
  recession function `(f)₀⁺` as `λ → 0+`, first at points of `dom f` and then, under
  `0 ∈ dom f`, at every point of the ambient scalar topological module.
- `core/canonical`: the owner abstractions already present upstream are the canonical `Function`
  owner `recessionFunction` on codomain `WithBotTop 𝕜`, the scaled-epigraph owner
  `rightScalarMul`, the convexity predicate `f.IsConvex`, the primitive codomain condition
  `∀ z, f z ≠ ⊥`, the effective-domain owner `dom(·)`, and the closedness hypothesis
  `LowerSemicontinuous`; source-facing properness forms are derived wrappers.
- `bridge/view`: the second clause is proved from the closed-case quotient limit in Theorem 8.5
  together with the positive-scalar rescaling identity for `rightScalarMul`.

Domain-style sampling used here:
- `rightScalarMul`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `Function.recessionFunction`;
- `Function.tendsto_differenceQuotient_atTop_recessionFunction`.
- `dom(·)` and `mem_effectiveDomain`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the closed/convex hypotheses, the primitive no-`⊥`
  condition `∀ z, f z ≠ ⊥`, and the owner-domain memberships `y ∈ dom f` and `0 ∈ dom f`;
- derived API: source-facing `f.IsProper` wrappers and the one-sided limit formula for right
  scalar multiples at `0`.

Layer target: this item stays `source-facing`, but its public API is placed directly on the
canonical owner namespace `Function` and uses the existing notation `(f)₀⁺`.

Ambient-space refinement: although the source states the corollary on `R^n`, the supporting owner
API from Text 5.4.3 and Theorem 8.5 already lives on arbitrary scalar topological modules, and no
coordinate-level argument is used here.
-/

namespace Function

section MemDom

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [DenselyOrdered 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousAdd 𝕜] [ContinuousMul 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddTorsor E] [ContinuousSMul 𝕜 E]
variable {f : E → WithBotTop 𝕜}

-- Proof sketch: apply the boundary-limit statement from Corollary 7.5.1 to the closed convex
-- perspective function whose positive slices are the right scalar multiples `f_λ`. The hypotheses
-- `hf_convex`, `hf_ne_bot`, and `hf_closed` provide the primitive closed convex setup at this
-- layer, while `hy : y ∈ dom f` supplies a finite base point. The boundary value at `λ = 0`
-- is exactly the recession value `((f)₀⁺) y`.
/-- Primitive boundary-limit form of Corollary 8.5.2 (1): for a closed convex function with no
`⊥` values, the right scalar multiples `f_λ` converge to the recession function `(f)₀⁺` at every
point `y` of `dom f`. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_mem_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithBotTop 𝕜))
    (hf_closed : LowerSemicontinuous f)
    {y : E} (hy : y ∈ dom(f)) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := sorry

/-- Corollary 8.5.2 (1): derived source-facing form with properness. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_mem_dom
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    {y : E} (hy : y ∈ dom(f)) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := by
  simpa using tendsto_rightScalarMul_to_recessionFunction_of_mem_dom_of_ne_bot
    (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed hy

end MemDom

section ZeroMemDom

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {f : E → WithBotTop 𝕜}

-- Proof sketch: specialize the closed-case quotient-limit formula from Theorem 8.5 at the base
-- point `x = 0`, using `h0 : (0 : E) ∈ dom f`. Rewrite the quotient
-- `(f (t • y) - f 0) / t` as the value of `rightScalarMul` at `t⁻¹` via
-- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`, then change variables `λ = t⁻¹` to
-- obtain the limit of `f_λ(y)` as `λ → 0+`.
/-- Primitive boundary-limit form of Corollary 8.5.2 (2): if `0 ∈ dom f` and `f` has no `⊥`
values, then the same limit formula for `f_λ(y)` and `((f)₀⁺) y` holds for every `y` in the
ambient scalar topological module. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithBotTop 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) (y : E) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := sorry

/-- Corollary 8.5.2 (2): derived source-facing form with properness. -/
theorem tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (h0 : (0 : E) ∈ dom(f)) (y : E) :
    Tendsto (fun lam : 𝕜≥0 ↦ (lam •ʳ f) y)
      (nhdsWithin (⟨0, le_rfl⟩ : 𝕜≥0) (Set.Ioi (⟨0, le_rfl⟩ : 𝕜≥0)))
      (nhds (((f)₀⁺) y)) := by
  simpa using tendsto_rightScalarMul_to_recessionFunction_of_zero_mem_dom_of_ne_bot
    (f := f) hf_convex (fun z ↦ hf_proper.ne_bot z) hf_closed h0 y

end ZeroMemDom

end Function

end

/-! ### Theorem_8_5 (from Chap02) -/
noncomputable section

section

variable {E : Type*}

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 8.5 states the structural properties of the recession function `f0⁺` of
  a proper convex function and gives its global and closed-case quotient formulas.
- `core/canonical`: the owner abstractions already introduced earlier in the chapter are
  `Function.recessionFunction`, `Function.IsConvex 𝕜`, `Function.IsProper`, the primitive
  non-`⊥` codomain condition `∀ x, f x ≠ ⊥`, and the
  generic positive-homogeneity predicate `Function.PositivelyHomogeneous`.
- `bridge/view`: the displayed supremum formula is already the exact owner theorem
  `Function.recessionFunction_apply` from Corollary 8.5.1, while the closed-case clauses
  below remain source-facing quotient and limit formulations.

Domain-style sampling used here:
- `Function.recessionFunction`;
- `Function.recessionFunction_apply`;
- `Function.IsConvex 𝕜`;
- `Function.IsProper`;
- `isClosed_recessionCone`;
- `LowerSemicontinuous`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithTopBot α`;
- owner hypotheses: clause (2) stays at the additive-zero properness owner layer, while
  clauses (1), (3), and (5) use the primitive codomain side condition
  `∀ z, f z ≠ ⊥` together with convexity/closedness; the fixed-basepoint closed-case formulas
  (6) and (7) stay on the same primitive non-`⊥` codomain layer rather than taking
  `f.IsProper` directly;
- minimality note for remaining concrete clauses: parts (6) and (7) are stated with scalar
  difference quotients `((f (x + t • y) - f x) / (t : WithTopBot 𝕜))` and `t : 𝕜`, so the
  ordered scalar-module layer there is statement-level data, not proof-local
  artifacts;
- derived API: positive homogeneity, properness, and convexity of `f0⁺`, the
  already-established global supremum formula, and the closed-case quotient formulas at a fixed
  base point.

Layer target: this file stays `source-facing`, with theorem surfaces attached directly to the
canonical owner namespace `Function` (for `recessionFunction`) instead of compatibility wrappers.
-/

namespace Function

section

variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [Add E]
variable (f : E → WithTopBot α)

/-- Theorem 8.5 (2): the recession function `f0⁺` of a proper convex function is proper. -/
-- Proof sketch: `(f0⁺) 0 = 0` gives a point of the epigraph, while the recession-cone
-- description of the epigraph shows that no value of `f0⁺` can be `⊥`.
theorem recessionFunction_isProper (hf_proper : f.IsProper) : (f₀⁺).IsProper := sorry

end

section

variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [Add E]
variable (f : E → WithTopBot α)

/- Theorem 8.5 (4): for every vector `y`, the recession function satisfies the global formula
`f0⁺(y) = sup {f (x + y) - f x | x ∈ dom f}`. This is exactly the owner theorem from
Corollary 8.5.1. -/
recall recessionFunction_apply

end

section

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable (f : E → WithTopBot 𝕜)

/-- Primitive owner form of Theorem 8.5 (1): under convexity and the primitive non-`⊥`
codomain condition, the recession function `f0⁺` is positively homogeneous. -/
-- Proof sketch: view the epigraph of `f0⁺` as the recession cone of the epigraph of
-- `f`. Recession cones are closed under positive scaling, so the resulting vertical infimum is
-- positively homogeneous.
theorem recessionFunction_positivelyHomogeneous_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜)) :
    ((f)₀⁺).PositivelyHomogeneous 𝕜 := sorry

/-- Theorem 8.5 (1), proper specialization. -/
theorem recessionFunction_positivelyHomogeneous
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    ((f)₀⁺).PositivelyHomogeneous 𝕜 :=
  recessionFunction_positivelyHomogeneous_of_ne_bot (f := f) hf_convex
    (fun z => hf_proper.ne_bot z)

end

section

variable {𝕜 : Type*} {α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α]
variable (f : E → WithTopBot α)

/-- Primitive owner form of Theorem 8.5 (3): under convexity and the primitive non-`⊥`
codomain condition, the recession function `f0⁺` is convex. -/
-- Proof sketch: identify the epigraph of `f0⁺` with the recession cone of the
-- epigraph of `f`. Convexity of `epi f` implies convexity of its recession cone.
theorem recessionFunction_isConvex_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot α)) :
    ((f)₀⁺).IsConvex 𝕜 := sorry

/-- Theorem 8.5 (3), proper specialization. -/
theorem recessionFunction_isConvex
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    ((f)₀⁺).IsConvex 𝕜 :=
  recessionFunction_isConvex_of_ne_bot (f := f) hf_convex
    (fun z => hf_proper.ne_bot z)

end

section

variable {𝕜 : Type*} {α : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [TopologicalSpace α] [OrderTopology α]
variable [Module 𝕜 α]
variable [TopologicalSpace (WithTopBot α)] [OrderTopology (WithTopBot α)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithTopBot α)

open Filter
open scoped Topology

/-- Primitive owner form of Theorem 8.5 (5): if `f` is closed, convex, and nowhere `⊥`, then its
recession function `f0⁺` is closed as well, here expressed by lower semicontinuity in a scalar
topological vector space, with codomain neighborhoods taken in the order topology on
`WithTopBot α`. -/
-- Proof sketch: the epigraph of `f0⁺` is the recession cone of the epigraph of `f`.
-- Lower semicontinuity makes `epi f` closed, and the recession cone of a closed convex set is
-- closed, so `f0⁺` is lower semicontinuous.
theorem recessionFunction_lowerSemicontinuous_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot α))
    (hf_closed : LowerSemicontinuous f) :
    LowerSemicontinuous ((f)₀⁺) := sorry

/-- Theorem 8.5 (5), proper specialization. -/
theorem recessionFunction_lowerSemicontinuous
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) :
    LowerSemicontinuous ((f)₀⁺) :=
  recessionFunction_lowerSemicontinuous_of_ne_bot (f := f) hf_convex
    (fun z => hf_proper.ne_bot z) hf_closed

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithTopBot 𝕜)

open Filter
open scoped Topology

/-- Theorem 8.5 (6): if `f` is closed, nowhere `⊥`, and `x ∈ dom f`, then `f0⁺(y)` is the
supremum of the positive difference quotients `[(f (x + λ y) - f x) / λ]` based at `x`. -/
-- Proof sketch: apply Theorem 8.3 to the closed convex epigraph of `f`. For a fixed base point
-- `(x, f x)` in `epi f`, the smallest slope `v` for which the ray in direction `(y, v)` stays in
-- `epi f` is independent of `x`, and this slope is exactly the supremum of the positive
-- difference quotients at that base point.
theorem recessionFunction_eq_sSup_differenceQuotients_at_point
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    {x : E} (hx : x ∈ dom f) (y : E) :
    ((f)₀⁺) y =
      sSup {r : WithTopBot 𝕜 |
        ∃ t : 𝕜, 0 < t ∧ r = (f (x + t • y) - f x) / (t : WithTopBot 𝕜)} := sorry

/-- Theorem 8.5 (7): if `f` is closed, nowhere `⊥`, and `x ∈ dom f`, then the positive
difference quotient `[(f (x + λ y) - f x) / λ]` tends to `f0⁺(y)` as `λ → +∞`. -/
-- Proof sketch: Theorem 23.1 shows that for a convex function the difference quotient in `λ` is
-- monotone nondecreasing. The preceding supremum formula identifies its least upper bound with
-- `(f0⁺) y`, so monotone convergence yields the limit at `+∞`.
theorem tendsto_differenceQuotient_atTop_recessionFunction
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    {x : E} (hx : x ∈ dom f) (y : E) :
    Tendsto (fun t : 𝕜 ↦ (f (x + t • y) - f x) / (t : WithTopBot 𝕜)) atTop
      (𝓝 (((f)₀⁺) y)) := sorry

end

end Function

end
