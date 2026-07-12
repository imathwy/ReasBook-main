import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

namespace Function

section

variable {E : Type u} {ι : Type v} {α β : Type*}
variable [LE β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.8 rewrites a finite inequality-constrained problem with
  objective in `α` and constraints in an ordered zero type `β` as one `WithTopBot α`-valued
  objective obtained by adjoining the indicator of the common feasible set cut out by the
  inequalities.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.toWithTopBotOn` for extension by `+∞` outside a feasible set and
  `weakConvexInequalitySolutionSetOn` for the canonical feasible set of a finite weak
  convex-inequality subsystem with zero right-hand-side bounds.
- `bridge/view`: the source formula `f₀.toWithTopBot + δ[α](· | C)` is the Chapter 1 bridge for
  `Function.toWithTopBotOn f₀ C`, and the finite subsystem indexed by `s : Finset ι` is
  equivalently the textbook set `{x | ∀ i ∈ s, f i x ≤ 0}`.

Domain-style sampling used here:
- `Function.toWithTopBotOn` and `Function.toWithTopBotOn_eq_add_indicator` from
  `Chap01.Remark_4_4_5`;
- `indicator` / `δ[α](· | C)` from `Chap01.Defintion_4_8_1`;
- `weakConvexInequalitySolutionSetOn` and `mem_weakConvexInequalitySolutionSetOn` from
  `Chap04.Text_21_0_1`.

Primitive data vs derived API:
- primitive data: an `α`-valued objective `f₀`, a finite index set `s`, and `β`-valued
  constraint functions `f i`;
- canonical owner surface:
  `Function.toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)`;
- derived API: the source formula via direct reuse of
  `Function.toWithTopBotOn_eq_add_indicator`, the pointwise branch formula, and the
  empty-family specialization.

Layer target: `source-facing` through the existing `core/canonical` owner. Definition 6.28.8 is
not a second root declaration; it is this concrete use of `Function.toWithTopBotOn` on the
Chapter 4 finite feasible-set owner.
-/

/- Definition 6.28.8: the constrained objective is the canonical extension
`Function.toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f)`,
equivalently `f₀.toWithTopBot + δ[α](· | {x | ∀ i ∈ s, f i x ≤ 0})`. -/
recall Function.toWithTopBotOn

section

variable [Zero β]

recall weakConvexInequalitySolutionSetOn

/-- Primitive owner spelling of Definition 6.28.8 on the Chapter 4 finite weak feasible-set
owner, with no additive codomain assumptions. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_piecewise
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      (weakConvexInequalitySolutionSetOn s f).piecewise f₀.toWithTopBot ⊤ :=
  rfl

/-- Source-set spelling of the primitive owner for Definition 6.28.8:
`{x | ∀ i ∈ s, f i x ≤ 0}.piecewise f₀.toWithTopBot ⊤`. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_piecewise_setOf
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      ({x : E | ∀ i ∈ s, f i x ≤ 0}).piecewise f₀.toWithTopBot ⊤ := by
  simpa [weakConvexInequalitySolutionSetOn_eq_setOf] using
    toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_piecewise
      (f₀ := f₀) (s := s) (f := f)

/-- On the finite weak feasible-set owner, the constrained objective agrees with `f₀` on feasible
points. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_of_mem
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) {x : E}
    (hx : x ∈ weakConvexInequalitySolutionSetOn s f) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x = f₀.toWithTopBot x := by
  simpa using Function.toWithTopBotOn_of_mem f₀ (weakConvexInequalitySolutionSetOn s f) hx

/-- Outside the finite weak feasible-set owner, the constrained objective is `+∞`. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_of_notMem
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) {x : E}
    (hx : x ∉ weakConvexInequalitySolutionSetOn s f) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x = (⊤ : WithTopBot α) := by
  simpa using Function.toWithTopBotOn_of_notMem f₀ (weakConvexInequalitySolutionSetOn s f) hx

/-- Pointwise owner form of Definition 6.28.8, phrased at the canonical feasible-set owner
layer. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_apply
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) (x : E) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x =
      if x ∈ weakConvexInequalitySolutionSetOn s f then f₀.toWithTopBot x else ⊤ := by
  by_cases hx : x ∈ weakConvexInequalitySolutionSetOn s f
  · simp [hx]
  · simp [hx]

/-- Source-set spelling of the pointwise form of Definition 6.28.8:
`if (∀ i ∈ s, f i x ≤ 0) then f₀.toWithTopBot x else ⊤`. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_apply_setOf
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) (x : E) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) x =
      if ∀ i ∈ s, f i x ≤ 0 then f₀.toWithTopBot x else ⊤ := by
  simpa [mem_weakConvexInequalitySolutionSetOn] using
    toWithTopBotOn_weakConvexInequalitySolutionSetOn_apply
      (f₀ := f₀) (s := s) (f := f) (x := x)

/-- With no inequality constraints, Definition 6.28.8 reduces to the ambient codomain lift of the
objective. -/
@[simp] theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_empty
    (f₀ : E → α) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn (∅ : Finset ι) f) =
      f₀.toWithTopBot := by
  ext x
  simp [Function.toWithTopBotOn]

end

section

variable [AddZeroClass α] [Zero β]

/-- Owner-to-source bridge for Definition 6.28.8 on the Chapter 4 finite weak feasible-set
owner. -/
theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_add_indicator
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      f₀.toWithTopBot + (δ(· | weakConvexInequalitySolutionSetOn s f)) := by
  simpa using
    Function.toWithTopBotOn_eq_add_indicator f₀ (weakConvexInequalitySolutionSetOn s f)

/-- Source-set spelling of Definition 6.28.8:
`f₀.toWithTopBot + δ[α](· | {x | ∀ i ∈ s, f i x ≤ 0})`. -/
theorem toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_add_indicator_setOf
    (f₀ : E → α) (s : Finset ι) (f : ι → E → β) :
    toWithTopBotOn f₀ (weakConvexInequalitySolutionSetOn s f) =
      f₀.toWithTopBot + (δ(· | {x : E | ∀ i ∈ s, f i x ≤ 0})) := by
  simpa [weakConvexInequalitySolutionSetOn_eq_setOf] using
    toWithTopBotOn_weakConvexInequalitySolutionSetOn_eq_add_indicator
      (f₀ := f₀) (s := s) (f := f)

end

end

end Function
