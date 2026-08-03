import BauschkeLean.Chap27.Lemma_27_20
import BauschkeLean.Chap27.Proposition_27_14

open scoped BigOperators InnerProductSpace SetValuedOperator

noncomputable section

universe u

namespace ERealFunction

section ConvexInequalityConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {m : ℕ}

local notation "MultiplierSpace" => EuclideanSpace ℝ (Fin m)

-- Semantic recall note: `lean_leansearch` surfaced generic smooth Lagrange-multiplier theorems,
-- but the verified project-facing owners for this source item are `Argmin[...]`,
-- `effectiveDomain`, `∂`, `HasGateauxDerivativeAt`, and the Chapter 27 finite-family precedent
-- from `Corollary_27_15`.

/-- The feasible set cut out by the finite family of convex inequalities `g_i(x) ≤ 0`. -/
def convexInequalityFeasibleSet
    (g : Fin m → H → Set.Ioi (⊥ : EReal)) : Set H :=
  {x : H | ∀ i : Fin m, (g i x : EReal) ≤ 0}

/-
The finite inequality feasible set is the intersection of the nonpositive sublevel sets
`lowerLevelSet (g i) 0`.
-/
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem convexInequalityFeasibleSet_eq_iInter_lowerLevelSet
    (g : Fin m → H → Set.Ioi (⊥ : EReal)) :
    convexInequalityFeasibleSet g =
      ⋂ i : Fin m, lowerLevelSet (fun x : H ↦ (g i x : EReal)) 0 := by
  ext x
  simp [convexInequalityFeasibleSet, lowerLevelSet]

/-- The Slater condition from Proposition 27.21. -/
def ConvexInequalitySlaterCondition
    (f : H → Set.Ioi (⊥ : EReal))
    (g : Fin m → H → Set.Ioi (⊥ : EReal)) : Prop :=
  (∀ i : Fin m, {x : H | (g i x : EReal) ≤ 0} ⊆ interior (effectiveDomain (g i))) ∧
    (effectiveDomain f ∩ ⋂ i : Fin m, {x : H | (g i x : EReal) < 0}).Nonempty

/-- The weighted objective `x ↦ f(x) + ∑ i ν_i g_i(x)` attached to a multiplier vector `νbar`.
-/
def convexInequalityLagrangianObjective
    (f : H → Set.Ioi (⊥ : EReal))
    (g : Fin m → H → Set.Ioi (⊥ : EReal))
    (νbar : MultiplierSpace) : H → EReal :=
  fun x : H ↦ (f x : EReal) + ∑ i : Fin m, (νbar i : EReal) * (g i x : EReal)

/-- A subgradient KKT system for the finite convex inequality constraints at `xbar`. -/
class ConvexInequalitySubgradientKKTSystem
    (f : H → Set.Ioi (⊥ : EReal))
    (g : Fin m → H → Set.Ioi (⊥ : EReal))
    (xbar : H) (νbar : MultiplierSpace) (u : Fin m → H) : Prop where
  nonneg : ∀ i : Fin m, 0 ≤ νbar i
  subgradient : ∀ i : Fin m, u i ∈ (∂ (g i)) xbar
  stationarity : -∑ i : Fin m, νbar i • u i ∈ (∂ f) xbar
  feasible : ∀ i : Fin m, (g i xbar : EReal) ≤ 0
  complementary_slackness :
    ∀ i : Fin m, (νbar i : EReal) * (g i xbar : EReal) = 0

omit [CompleteSpace H] in
/-- A subgradient KKT witness is feasible for the finite inequality constraint set. -/
theorem ConvexInequalitySubgradientKKTSystem.mem_convexInequalityFeasibleSet
    {f : H → Set.Ioi (⊥ : EReal)} {g : Fin m → H → Set.Ioi (⊥ : EReal)}
    {xbar : H} {νbar : MultiplierSpace} {u : Fin m → H}
    (hKKT : ConvexInequalitySubgradientKKTSystem f g xbar νbar u) :
    xbar ∈ convexInequalityFeasibleSet g :=
  hKKT.feasible

/-- A gradient KKT system for the finite convex inequality constraints at `xbar`. -/
class ConvexInequalityGradientKKTSystem
    (g : Fin m → H → Set.Ioi (⊥ : EReal))
    (xbar gradf : H) (gradg : Fin m → H) (νbar : MultiplierSpace) : Prop where
  stationarity : gradf = -∑ i : Fin m, νbar i • gradg i
  nonneg : ∀ i : Fin m, 0 ≤ νbar i
  feasible : ∀ i : Fin m, (g i xbar : EReal) ≤ 0
  complementary_slackness :
    ∀ i : Fin m, (νbar i : EReal) * (g i xbar : EReal) = 0

omit [CompleteSpace H] in
/-- A gradient KKT witness is feasible for the finite inequality constraint set. -/
theorem ConvexInequalityGradientKKTSystem.mem_convexInequalityFeasibleSet
    {g : Fin m → H → Set.Ioi (⊥ : EReal)} {xbar gradf : H}
    {gradg : Fin m → H} {νbar : MultiplierSpace}
    (hKKT : ConvexInequalityGradientKKTSystem g xbar gradf gradg νbar) :
    xbar ∈ convexInequalityFeasibleSet g :=
  hKKT.feasible

/-- Proposition 27.21 (1): let `f ∈ Γ₀(H)` and let `(g_i)_{i ∈ Fin m}` be a finite family in
`Γ₀(H)` satisfying the Slater condition. Then
`xbar` solves `minimize f(x)` subject to `g_i(x) ≤ 0` for every `i` if and only if there exist
nonnegative multipliers `νbar` and subgradients `u i ∈ ∂ g_i(xbar)` such that
`-∑ i, νbar_i • u_i ∈ ∂ f(xbar)` and every constraint satisfies feasibility together with
complementary slackness. The source assumes a positive number of constraints, but that positivity
hypothesis is redundant for the finite-family KKT statement, so it is omitted. -/
theorem mem_argmin_convexInequalityFeasibleSet_iff_exists_nonneg_multipliers_subgradient_of_slater
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : Fin m → H → Set.Ioi (⊥ : EReal)} (hg : ∀ i : Fin m, g i ∈ Γ₀(H))
    (hslater : ConvexInequalitySlaterCondition f g)
    {xbar : H} :
    xbar ∈ Argmin[convexInequalityFeasibleSet g] f.asEReal ↔
      ∃ νbar : MultiplierSpace,
        ∃ u : Fin m → H,
          ConvexInequalitySubgradientKKTSystem f g xbar νbar u := sorry

/-- Proposition 27.21 (2): every subgradient KKT witness from clause `(1)` makes `xbar` a
minimizer of the weighted objective `x ↦ f(x) + ∑ i νbar_i g_i(x)`. The regularity and positivity
assumptions from clause `(1)` are redundant for this affine-tilt consequence, so the theorem uses
only the KKT owner itself. -/
theorem mem_argmin_convexInequalityLagrangianObjective_of_kkt
    {f : H → Set.Ioi (⊥ : EReal)}
    {g : Fin m → H → Set.Ioi (⊥ : EReal)}
    {xbar : H} {νbar : MultiplierSpace} {u : Fin m → H}
    (hKKT : ConvexInequalitySubgradientKKTSystem f g xbar νbar u) :
    xbar ∈ Argmin (convexInequalityLagrangianObjective f g νbar) := sorry

/-- Proposition 27.21 (3): if `f` and each `g_i` are Gâteaux differentiable at the feasible
effective-domain point `xbar`, then the subgradient characterization from clause `(1)` becomes the
explicit gradient KKT system `gradf = -∑ i, νbar_i • gradg_i` together with feasibility,
nonnegativity, and complementary slackness. As in clause `(1)`, the positivity hypothesis on the
number of constraints is redundant and omitted. -/
theorem mem_argmin_convexInequalityFeasibleSet_iff_exists_nonneg_multipliers_gradient_of_gateaux
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : Fin m → H → Set.Ioi (⊥ : EReal)} (hg : ∀ i : Fin m, g i ∈ Γ₀(H))
    (hslater : ConvexInequalitySlaterCondition f g)
    {xbar gradf : H}
    (hxbar : xbar ∈ effectiveDomain f)
    (hgradf :
      HasGateauxDerivativeAt
        (fun x : H ↦ (f x : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H gradf) xbar)
    {gradg : Fin m → H}
    (hgradg :
      ∀ i : Fin m,
        HasGateauxDerivativeAt
          (fun x : H ↦ (g i x : EReal).toReal)
          (InnerProductSpace.toDualMap ℝ H (gradg i)) xbar) :
    xbar ∈ Argmin[convexInequalityFeasibleSet g] f.asEReal ↔
      ∃ νbar : MultiplierSpace,
        ConvexInequalityGradientKKTSystem g xbar gradf gradg νbar := sorry

end ConvexInequalityConstraints

end ERealFunction
