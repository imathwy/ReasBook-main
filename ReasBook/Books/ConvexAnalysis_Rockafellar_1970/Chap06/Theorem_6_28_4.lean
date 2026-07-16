import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7

noncomputable section

universe u v

namespace OrdinaryConvexProgram
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.4 identifies Kuhn-Tucker multipliers and optimal points with
  saddle-points of the Lagrangian, and then rewrites that saddle condition in the source
  coordinatewise form.
- `core/canonical`: the already built Chapter 6 owners are `P.IsKuhnTuckerVector`,
  `P.feasibleSet`, `P.feasibleObjective`, `P.weightedObjective`, `P.IsOptimalSolution`,
  `P.saddleLagrangian`, the source multiplier domain `multiplierSet`, and the source-order
  saddle-point owner `Bifunction.IsSaddlePointOn`, together with the pairing-based Chapter 23
  owner `_root_.subdifferentialAt`.
- `bridge/view`: the source order `(u⋆, x)` is represented directly by
  `Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E) (saddleLagrangian P) u⋆ x`,
  avoiding swapped-kernel ambient owner noise on theorem surfaces.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerVector` and `OrdinaryConvexProgram.weightedObjective`
  from `Definition_6_28_3`;
- `OrdinaryConvexProgram.multiplierSet` from `Definition_6_28_6`;
- `Bifunction.IsSaddlePointOn` from `Definition_6_28_7`;
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`.
-/

section Saddle

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: rewrite the source supremum/infimum saddle condition for `P.saddleLagrangian`
-- into the equalities used in Definition 6.28.3. On the constraint set and for admissible
-- multipliers, the Lagrangian is exactly the weighted objective, while outside those source
-- domains the `⊥`/`⊤` branches force the dual and primal inequalities that recover
-- Kuhn-Tucker admissibility and primal optimality.
/-- Theorem 6.28.4 (1): a multiplier pair `(lam, μ)` is a Kuhn-Tucker vector for `P` and `x` is
an optimal solution of `P` if and only if `(lam, μ, x)` is a saddle-point of the source-order
Lagrangian of `P`. -/
theorem isKuhnTuckerVector_and_isOptimalSolution_iff_isSaddlePoint_saddleLagrangian
    (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) :
    P.IsKuhnTuckerVector lam μ ∧ P.IsOptimalSolution x ↔
      Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E)
        (saddleLagrangian P) (lam, μ) x := sorry

end Saddle

section KuhnTuckerPoint

variable {𝕜 : Type v} [Semiring 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- The source Kuhn-Tucker point conditions at `x`: feasibility of `x`, nonnegativity of the
inequality multipliers, complementary slackness, and primal minimization of the weighted
objective. For pairing ambient models, minimization yields the usual
`0 ∈ ∂(weightedObjective)` stationarity condition and is exposed below as a derived bridge. -/
structure IsKuhnTuckerPoint (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) : Prop where
  feasible : x ∈ P.feasibleSet
  nonneg : ∀ i, 0 ≤ lam i
  complementarySlackness :
    ∀ i, ((lam i : WithBotTop 𝕜) * extendZero (P.inequality i) x = 0)
  isMin : IsMinOn (P.weightedObjective lam μ) Set.univ x

-- Proof sketch: combine part (1) with the pointwise source description of the saddle inequalities.
-- Feasibility of `x` recovers the clauses `f_i(x) ≤ 0` and `h_j(x) = 0`, the maximization in the
-- multiplier variable forces `lam i ≥ 0` together with complementary slackness, and the
-- minimization in the primal variable is exactly `IsMinOn (P.weightedObjective lam μ) univ x`.
/-- Theorem 6.28.4 (2): the saddle-point condition for the Lagrangian is equivalent to the source
Kuhn-Tucker point conditions, packaged canonically as feasibility, nonnegative multipliers,
complementary slackness, and primal minimization of the weighted objective at `x`. -/
theorem isSaddlePoint_saddleLagrangian_iff_isKuhnTuckerPoint
    (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) :
    Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E)
      (saddleLagrangian P) (lam, μ) x ↔
        P.IsKuhnTuckerPoint lam μ x := sorry

end KuhnTuckerPoint

section StationaryBridge

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- Pairing-level bridge: if the distinguished zero dual element pairs to zero, then the minimizer
field in `P.IsKuhnTuckerPoint` gives the Chapter 23 stationarity form
`0 ∈ ∂(weightedObjective)` used in the source display. -/
theorem IsKuhnTuckerPoint.stationary_pairing
    {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜]
    (hpair_zero : ∀ z : E, (HasPairing.pairing z (0 : Y) : 𝕜) = 0)
    {lam : ι → 𝕜} {μ : κ → 𝕜} {x : E}
    (h : P.IsKuhnTuckerPoint lam μ x) :
    (0 : Y) ∈ _root_.subdifferentialAt (Y := Y) (P.weightedObjective lam μ) x := by
  rw [_root_.mem_subdifferentialAt_pairing]
  intro z
  have hz : P.weightedObjective lam μ x ≤ P.weightedObjective lam μ z :=
    (isMinOn_univ_iff.mp h.isMin) z
  simpa [hpair_zero (z - x)] using hz

/-- Canonical-dual specialization of `IsKuhnTuckerPoint.stationary_pairing`. -/
theorem IsKuhnTuckerPoint.stationary
    {lam : ι → 𝕜} {μ : κ → 𝕜} {x : E}
    (h : P.IsKuhnTuckerPoint lam μ x) :
    (0 : StrongDual 𝕜 E) ∈ (∂ (P.weightedObjective lam μ) at x) := by
  exact
    IsKuhnTuckerPoint.stationary_pairing (P := P) (Y := StrongDual 𝕜 E)
      (hpair_zero := fun z : E => rfl) h

end StationaryBridge

end OrdinaryConvexProgram
