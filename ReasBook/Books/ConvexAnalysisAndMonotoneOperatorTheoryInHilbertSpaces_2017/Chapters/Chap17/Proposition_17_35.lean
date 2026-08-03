import Mathlib
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap17.Proposition_17_6

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.35 evaluates the source-facing Fenchel conjugate of `f` at the
  Gâteaux gradient `gradf` of `f` at `x`.
- `core/canonical`: the owner abstractions are the conjugate `f.asEReal∗`, the subdifferential
  `∂ f`, and `HasGateauxDerivativeAt`.
- `bridge/view`: Proposition 17.6 turns the Gâteaux gradient into a subgradient, and Proposition
  16.10 rewrites that subgradient membership as the Fenchel--Young equality needed to isolate the
  conjugate term. -/

/-- Helper for Proposition 17 35: the Gâteaux gradient yields the Fenchel--Young equality at `x`.
-/
private theorem fenchel_young_eq_at_gateaux_gradient
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    (f x : EReal) + f.asEReal∗ gradf =
      ((⟪x, gradf⟫_ℝ : ℝ) : EReal) := by
  -- The source proof first turns the gradient into a subgradient.
  have hsub : gradf ∈ (∂ f) x :=
    gateauxGradient_mem_subdifferential f hconv hx gradf hgrad
  -- Then Proposition 16.10 converts subgradient membership into Fenchel--Young equality.
  exact
    (mem_subdifferential_iff_fenchel_young_eq f x gradf).1 hsub

/-- Helper for Proposition 17 35: a finite Fenchel--Young equality can be rearranged to isolate
the conjugate term. -/
private theorem conjugate_eq_inner_sub_of_fenchel_young
    {a s t : EReal} (ha_bot : a ≠ ⊥) (ha_top : a ≠ ⊤) (hfy : a + s = t) :
    s = t - a := by
  -- Compare both sides using the two subtraction characterizations valid for finite `a`.
  apply le_antisymm
  · exact
      (EReal.le_sub_iff_add_le (.inl ha_bot) (.inl ha_top)).2
        (by simpa [add_comm, add_left_comm, add_assoc] using hfy.le)
  · exact
      (EReal.sub_le_iff_le_add (.inl ha_bot) (.inl ha_top)).2
        (by simpa [add_comm, add_left_comm, add_assoc] using hfy.symm.le)

/-- Proposition 17 35: if a proper convex `]-∞,+∞]`-valued function is Gâteaux differentiable at
`x` with gradient `gradf`, then the Fenchel conjugate of `f` at `gradf` is
`⟪x, gradf⟫ - f x`. -/
theorem conjugate_gateauxGradient_eq_inner_sub_of_hasGateauxDerivativeAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    f.asEReal∗ gradf = ((⟪x, gradf⟫_ℝ : ℝ) : EReal) - f x := by
  -- Route correction: follow the source route `gradient -> subgradient -> Fenchel--Young`, and
  -- only do the `EReal` subtraction algebra after the contact equality is established.
  have hfy :
      (f x : EReal) + f.asEReal∗ gradf =
        ((⟪x, gradf⟫_ℝ : ℝ) : EReal) :=
    fenchel_young_eq_at_gateaux_gradient f hconv hx gradf hgrad
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (f x).2
  -- The value `f x` is finite on the effective domain, so the equality rearranges cleanly.
  simpa using conjugate_eq_inner_sub_of_fenchel_young hx_bot hx_top hfy

end DifferentiabilityOfConvexFunctions

end ERealFunction
