import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap17.Proposition_17_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

open InnerProductSpace
open scoped Pointwise Set

/- Source/core/bridge triage:
- `source-facing`: `GateauxDifferentiableAt` is the Chapter 17 Gâteaux-differentiability owner for
  convex `]-∞,+∞]`-valued functions, namely the existence of a continuous linear map whose values
  realize all directional derivatives from Definition 17.1. Proposition 17.48 then records the
  regularity consequences of that source notion.
- `core/canonical`: the owner abstractions are `GateauxDifferentiableAt`,
  `directionalDerivative`, `∂`,
  `LowerSemicontinuousAt`, and `interior (effectiveDomain f)`.
- `bridge/view`: `ERealFunction.GateauxDifferentiableAt.toReal` sends the source
  directional-derivative formulation to the Chapter 2 owner `_root_.GateauxDifferentiableAt`.
  Proposition 17.2 identifies source directional derivatives with the canonical owner
  `directionalDerivative`, Proposition 17.14 turns the resulting linear minorant into a
  subgradient, Proposition 16.4 turns subdifferentiability into lower semicontinuity, and
  Fact 6.14 plus Corollary 8.39 supply the finite-dimensional interior/continuity
  consequences. -/

section DifferentiabilityAndContinuity

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Gâteaux differentiability for an extended-real-valued function at `x`: a continuous linear map
realizes all directional derivatives from Definition 17.1. -/
def GateauxDifferentiableAt (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  ∃ A : H →L[ℝ] ℝ, ∀ y : H, HasDirectionalDerivativeAt f x y (A y : EReal)

/-- On the effective domain, the extended-real difference quotient agrees with the real quotient
obtained from `EReal.toReal`. -/
private theorem quotient_eq_coe_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H} (hx : x ∈ effectiveDomain f)
    {α : ℝ} (hα : 0 < α) (hαdom : x + α • y ∈ effectiveDomain f) :
    ((f (x + α • y) : EReal) - (f x : EReal)) / α =
      ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := sorry

/-- Gâteaux differentiability already places `x` in the effective domain because each directional
derivative in Definition 17.1 is only defined there. -/
theorem GateauxDifferentiableAt.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hdiff : GateauxDifferentiableAt f x) :
    x ∈ effectiveDomain f := sorry

/-- Extended-real Gâteaux differentiability yields the Chapter 2 canonical
`_root_.GateauxDifferentiableAt` owner for the finite real representative of `f`. -/
theorem GateauxDifferentiableAt.toReal
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hdiff : GateauxDifferentiableAt f x) :
    _root_.GateauxDifferentiableAt (fun z ↦ (f z : EReal).toReal) x := sorry

/-- A Gâteaux derivative of the real-valued representative on a subset of the effective domain
induces the corresponding source directional derivatives. -/
private theorem hasDirectionalDerivativeAt_of_hasGateauxDerivativeWithinAt_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {U : Set H} {x : H} (hxU : x ∈ U)
    (hU_dom : U ⊆ effectiveDomain f) {A : H →L[ℝ] ℝ}
    (hA : HasGateauxDerivativeWithinAt (fun z ↦ (f z : EReal).toReal) A U x) (y : H) :
    HasDirectionalDerivativeAt f x y (A y : EReal) := sorry

namespace GateauxDifferentiableAt

/-- On a subset of the effective domain, Gâteaux differentiability of the finite real
representative within that subset implies the Chapter 17 source notion of Gâteaux
differentiability. -/
theorem of_toRealWithin_subset_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {U : Set H} {x : H} (hxU : x ∈ U)
    (hU_dom : U ⊆ effectiveDomain f)
    (hgateaux : GateauxDifferentiableWithinAt (fun z ↦ (f z : EReal).toReal) U x) :
    GateauxDifferentiableAt f x := sorry

end GateauxDifferentiableAt

-- Proof sketch: source Gâteaux differentiability gives a finite directional derivative in every
-- direction. Proposition 17.2 identifies those values with the canonical directional derivative,
-- so every direction lies in `dom (directionalDerivative f x)`. Proposition 17.2 (8) then yields
-- `cone (effectiveDomain f - {x}) = univ`, which is exactly `x ∈ core (effectiveDomain f)`.
/-- Source Gâteaux differentiability of a convex `]-∞,+∞]`-valued function forces the base point to
lie in the algebraic core of its effective domain. -/
theorem mem_core_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hdiff : GateauxDifferentiableAt f x) :
    x ∈ Set.core (effectiveDomain f) := sorry

end DifferentiabilityAndContinuity

section LowerSemicontinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

-- Proof sketch: represent the chosen source derivative map by its Riesz vector `gradf`. For each
-- direction `y`, Proposition 17.2 rewrites the source derivative value as `f′(x; y)`, so
-- Proposition 17.14 identifies `gradf` as a subgradient at `x`. Proposition 16.4 (5) then yields
-- lower semicontinuity at `x`.
/-- Proposition 17.48 (1): clause (i). If a convex `]-∞,+∞]`-valued function is Gâteaux
differentiable at an effective-domain point `x` in the source Chapter 17 sense, then it is lower
semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_of_convexOn_of_gateauxDifferentiableAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hdiff : GateauxDifferentiableAt f x) :
    LowerSemicontinuousAt f.asEReal x := sorry

end LowerSemicontinuity

section FiniteDimensional

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

-- Proof sketch: source Gâteaux differentiability gives a finite directional derivative in every
-- direction. Proposition 17.2 identifies those values with the canonical directional derivative,
-- so every direction lies in `dom (directionalDerivative f x)`. Proposition 17.2 (8) then yields
-- `cone (effectiveDomain f - {x}) = univ`, i.e. `x ∈ core (effectiveDomain f)`. In finite
-- dimension this cone equality forces the affine span of `effectiveDomain f` to be all of `H`,
-- hence `interior (effectiveDomain f)` is nonempty; the convex-set core/interior bridge then
-- upgrades core membership to interior membership.
/-- Proposition 17.48 (2): clause (ii). In finite dimension, a Gâteaux differentiability point of
a convex `]-∞,+∞]`-valued function lies in the interior of its effective domain. The
differentiability hypothesis is again the source Chapter 17 notion. -/
theorem mem_interior_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hdiff : GateauxDifferentiableAt f x) :
    x ∈ interior (effectiveDomain f) := sorry

-- Proof sketch: clause (iii) is exactly the canonical finite-dimensional continuity theorem for
-- the finite representative of a convex function on the interior of its effective domain.
/- Proposition 17.48 (3): in finite dimension, the finite-valued representative of a convex
`]-∞,+∞]`-valued function is continuous on the interior of its effective domain. This is exactly
`_root_.ConvexOn.continuousOn_interior` applied to `hconv.toReal_convexOn_effectiveDomain`. -/
#check _root_.ConvexOn.continuousOn_interior

end FiniteDimensional

end ERealFunction
