import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped ConvexAnalysis

variable {X : Type u} {Y : Type v}

/- Theorem 3.1.2.3 lies in the chapter's convex-analysis / infimal-projection domain.

Sampled owner-style declarations:
- chapter `extendedRealEffectiveDomain` / notation `dom` in `Definition_3_1_1_2`
- chapter `extendedRealRealPart` and `coe_extendedRealRealPart` in `Definition_3_1_1_3`
- mathlib `ConvexOn`
- mathlib `sInf`

Best owner abstraction:
- source-facing owner: the constrained `EReal`-valued fiberwise infimum `partialInfProjection`
- core/canonical convexity owner:
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)` for
  `ψ = partialInfProjection Q (Real.toEReal ∘ φ)`

Primitive data:
- a feasible set `Q : Set (X × Y)`
- an extended-real objective `φ : X × Y → EReal`

Derived API:
- the source-facing constrained infimum `partialInfProjection Q φ`
- the displayed fiber-value specification theorem `partialInfProjection_eq_sInf`
- the finite-value bridge
  `extendedRealRealPart_partialInfProjection_eq_sInf`

Source/core/bridge triage:
- source-facing: the constrained fiberwise infimum over `Q`
- core/canonical: the chapter `EReal` convexity owner
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)`
- bridge/view: the finite-value real surface
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ))`

A `WithTop ℝ`-valued owner would not faithfully represent unbounded-below fibers, so this file
keeps the constrained source-facing owner directly in `EReal` and then uses the chapter's
canonical `EReal` convexity bridge on its finite-value domain.
-/

/-- The constrained partial infimum of `φ` over the fiber of `Q` above `x`, recorded in `EReal`
so that unbounded-below fibers are represented faithfully by `⊥`. -/
def partialInfProjection (Q : Set (X × Y)) (φ : X × Y → EReal) : X → EReal :=
  fun x ↦ sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x})

/-- Evaluating the constrained partial infimum gives the infimum of the `φ`-values attained on
the feasible fiber above `x`. -/
@[simp] theorem partialInfProjection_eq_sInf
    {Q : Set (X × Y)} {φ : X × Y → EReal} {x : X} :
    partialInfProjection Q φ x =
      sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) :=
  rfl

/-- At a point where the constrained partial infimum is finite, its canonical real part agrees
with the textbook infimum of the real fiber values. -/
theorem extendedRealRealPart_partialInfProjection_eq_sInf
    {Q : Set (X × Y)} {φ : X × Y → ℝ} {x : X}
    (hx : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ))) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) x =
      sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) := sorry

section RealConvex

variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

/-- Theorem 3.1.2.3: if `Q ⊆ X × Y` is convex and `φ : X × Y → ℝ` is convex on `Q`, then the
constrained partial infimum is convex in the chapter's `EReal` sense: its finite real part is
convex on its finite-value domain. The companion theorem
`extendedRealRealPart_partialInfProjection_eq_sInf` identifies that finite real part with the
textbook fiberwise real infimum wherever the partial infimum is finite. -/
theorem partialInfProjection_convexOn
    {Q : Set (X × Y)} {φ : X × Y → ℝ}
    (hQ : Convex ℝ Q) (hφ : ConvexOn ℝ Q φ) :
    ConvexOn ℝ (dom (partialInfProjection Q (Real.toEReal ∘ φ)))
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ))) := sorry

end RealConvex

end
