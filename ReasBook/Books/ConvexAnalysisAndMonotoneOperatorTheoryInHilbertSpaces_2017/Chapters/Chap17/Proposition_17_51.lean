import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_48

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityAndContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.51 assumes Gâteaux differentiability on an open subset `U` of
  `effectiveDomain f`, understood pointwise as the Chapter 17 owner
  `GateauxDifferentiableAt f x` for `x ∈ U`; the source-facing API therefore takes only the
  pointwise differentiability owner and derives `U ⊆ effectiveDomain f` from
  `GateauxDifferentiableAt.mem_effectiveDomain`, while the `toReal` bridge theorem keeps the
  explicit domain hypothesis needed to construct that owner. The conclusion is continuity on
  `interior (effectiveDomain f)`.
- `core/canonical`: the reusable owners are `GateauxDifferentiableAt`,
  `effectiveDomain`, `ContinuousPoint`, `ContinuousAtOnEffectiveDomain`, and `ContinuousOn` for
  the finite real representative `fun x ↦ (f x : EReal).toReal`.
- `bridge/view`: the root-level setwise condition
  `GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) U` converts to the source-facing
  Chapter 17 surface `U ⊆ {x : H | GateauxDifferentiableAt f x}` via
  `GateauxDifferentiableAt.of_toRealWithin_subset_effectiveDomain`. -/

-- Semantic recall: `lean_leansearch` returned only generic convex-continuity lemmas, so this file
-- keeps the project-specific `ERealFunction` owner surface rather than rewriting the statement.

-- Proof sketch: choose `x ∈ U`; Proposition 17.48 gives lower semicontinuity of `f` at `x`. On a
-- small ball `C ⊆ U`, the localized function `g = f + ι_C` belongs to `Γ₀(H)`, so Corollary 8.39
-- gives continuity of the finite representative on `interior C`; hence `f` is continuous at `x`.
-- Theorem 8.38 then propagates this local continuity to all of `interior (effectiveDomain f)`.
/-
Bridge/view: Gâteaux differentiability of the finite real representative on `U` yields the
Chapter 17 source differentiability owner at each point of `U`.
-/
omit [CompleteSpace H] in
theorem gateauxDifferentiableAtOn_of_toReal_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) {U : Set H} (hU_dom : U ⊆ effectiveDomain f)
    (hgateaux : GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) U) :
    U ⊆ {x : H | GateauxDifferentiableAt f x} := by
  intro x hx
  exact GateauxDifferentiableAt.of_toRealWithin_subset_effectiveDomain hx hU_dom (hgateaux x hx)

/-- Every point of an open subset on which the Chapter 17 Gâteaux differentiability owner holds is
automatically an effective-domain point and a Chapter 16 source continuity point of `f`. -/
theorem continuousPoint_of_mem_of_convexOn_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {U : Set H} (hU_open : IsOpen U) (hgateaux : U ⊆ {x : H | GateauxDifferentiableAt f x})
    {x : H} (hx : x ∈ U) :
    ContinuousPoint f x := sorry

/-- The Chapter 16 continuity-on-effective-domain owner attached to a point of an open
subset on which the Chapter 17 Gâteaux differentiability owner holds pointwise. -/
theorem continuousAtOnEffectiveDomain_of_mem_of_convexOn_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {U : Set H} (hU_open : IsOpen U) (hgateaux : U ⊆ {x : H | GateauxDifferentiableAt f x})
    {x : H} (hx : x ∈ U) :
    ContinuousAtOnEffectiveDomain f x := by
  exact
    ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain
      (continuousPoint_of_mem_of_convexOn_gateauxDifferentiableOn
        f hconv hU_open hgateaux hx)

/-- A nonempty open effective-domain subset on which the finite real representative of `f` is
Gâteaux differentiable in the Chapter 17 sense supplies a Chapter 16 source continuity point of
`f`. -/
theorem exists_continuousPoint_of_convexOn_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (U : Set H) (hU_nonempty : U.Nonempty) (hU_open : IsOpen U)
    (hgateaux : U ⊆ {x : H | GateauxDifferentiableAt f x}) :
    ∃ x : H, ContinuousPoint f x := by
  rcases hU_nonempty with ⟨x, hx⟩
  exact
    ⟨x,
      continuousPoint_of_mem_of_convexOn_gateauxDifferentiableOn
        f hconv hU_open hgateaux hx⟩

/-- Proposition 17.51: if a convex `]-∞,+∞]`-valued function is Gâteaux differentiable on a
nonempty open subset `U` of its effective domain, then its finite-valued representative is
continuous on `interior (effectiveDomain f)`. -/
theorem continuousOn_interior_effectiveDomain_of_convexOn_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (U : Set H)
    (hU_nonempty : U.Nonempty) (hU_open : IsOpen U)
    (hgateaux : U ⊆ {x : H | GateauxDifferentiableAt f x}) :
    ContinuousOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := sorry

/-- Companion bridge/view for Proposition 17.51 phrased with
`GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) U`. -/
theorem continuousOn_interior_effectiveDomain_of_convexOn_toReal_gateauxDifferentiableOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (U : Set H)
    (hU_nonempty : U.Nonempty) (hU_open : IsOpen U) (hU_dom : U ⊆ effectiveDomain f)
    (hgateaux : GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) U) :
    ContinuousOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := by
  exact
    continuousOn_interior_effectiveDomain_of_convexOn_gateauxDifferentiableOn
      f hconv U hU_nonempty hU_open
      (gateauxDifferentiableAtOn_of_toReal_gateauxDifferentiableOn f hU_dom hgateaux)

end DifferentiabilityAndContinuity

end ERealFunction
