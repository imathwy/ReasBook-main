import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_28_6

noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

open Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.6 says that, once an ordinary convex program has at least one
  Kuhn--Tucker multiplier, the Kuhn--Tucker multipliers are exactly the maximizers of the dual
  function
  `g(u) = inf_x L(u, x)`.
- `core/canonical`: the existing Chapter 6 owners are `P.IsKuhnTuckerMultiplier`,
  `P.IsKuhnTuckerVector`, `P.saddleLagrangian`, `Bifunction.perturbationFunction`,
  `multiplierSet`, and `IsMaxOn`.
- `bridge/view`: the source multiplier vector is represented canonically by the split pair
  `u : (Fin r → 𝕜) × (Fin s → 𝕜)` already used throughout the ordinary-convex-program API.
- abstraction normalization: this corollary does not use real-specific structure or the concrete
  codomain `EReal`; it therefore lives at the Chapter 6 canonical layer
  `OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerMultiplier`, `OrdinaryConvexProgram.IsKuhnTuckerVector`, and
  `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `OrdinaryConvexProgram.multiplierSet` from `Definition_6_28_6`;
- `IsMaxOn` / `isMaxOn_univ_iff` from mathlib's extrema API;
- the Chapter 6 theorem style in `Theorem_31_3`, where dual attainment is expressed canonically
  via `IsMaxOn ... Set.univ`.

Primitive data vs derived API:
- primitive source data: the program `P` and the Lagrangian owner `P.saddleLagrangian`;
- primitive owner reused from upstream: `perturbationFunction P.saddleLagrangian`;
- derived API: the characterization of Kuhn--Tucker multipliers as the maximizers of that dual
  function on the source multiplier set.

Layer target: `source-facing`, stated directly on the existing Kuhn--Tucker and Lagrangian
owners without introducing a parallel ordinary-program alias for the row-infimum owner.
-/

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

local notation "dualObjective" => perturbationFunction P.saddleLagrangian

-- Proof sketch: if `u` is Kuhn--Tucker, Theorem 6.28.6 identifies
-- `(perturbationFunction P.saddleLagrangian) u` with the common maximin/minimax value, so `u` is
-- a global maximizer of the dual function. Conversely, choose `u₀` from `hExists`; the same
-- theorem makes `u₀` a maximizer with the common extremal value. Any maximizer `u` therefore has
-- the same row infimum as `u₀`, so the row infimum at `u` is finite and agrees with both global
-- extremal values. Applying Theorem 6.28.6 again yields `P.IsKuhnTuckerMultiplier u`.
/-- Corollary 6.28.6: assuming `P` has at least one Kuhn--Tucker multiplier, a split multiplier
pair `u` representing the source multiplier vector is a Kuhn--Tucker multiplier exactly when
the dual function `g(u) = inf_x L(u, x)`, rendered here by the chapter owner
`perturbationFunction P.saddleLagrangian`, attains its supremum over the canonical multiplier set
`Eᵣ = multiplierSet` at `u`. -/
theorem isKuhnTuckerMultiplier_iff_isMaxOn_dualObjective
    (hExists : ∃ u : (Fin r → 𝕜) × (Fin s → 𝕜), P.IsKuhnTuckerMultiplier u)
    (u : (Fin r → 𝕜) × (Fin s → 𝕜)) :
    P.IsKuhnTuckerMultiplier u ↔
      IsMaxOn dualObjective multiplierSet u := by
  constructor
  · intro hKT
    rcases
      (P.isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
        u).1 hKT with
      ⟨_, hmaximin, _⟩
    intro v hv
    calc
      dualObjective v = (⨅ x, P.saddleLagrangian v x) := by
        simpa using perturbationFunction_apply P.saddleLagrangian v
      _ ≤ (⨆ w, ⨅ x, P.saddleLagrangian w x) := by
        exact le_iSup (fun w => ⨅ x, P.saddleLagrangian w x) v
      _ = (⨅ x, P.saddleLagrangian u x) := hmaximin
      _ = dualObjective u := by
        simpa using (perturbationFunction_apply P.saddleLagrangian u).symm
  · intro hMax
    rcases hExists with ⟨u0, hKT0⟩
    rcases
      (P.isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
        u0).1 hKT0 with
      ⟨h0bot, h0maximin, h0minimax⟩
    have hu0_mem : u0 ∈ multiplierSet := by
      simpa using hKT0.nonneg
    have hrow0_le_row :
        (⨅ x, P.saddleLagrangian u0 x) ≤ (⨅ x, P.saddleLagrangian u x) := by
      simpa [perturbationFunction_apply] using hMax hu0_mem
    have hrow_le_maximin :
        (⨅ x, P.saddleLagrangian u x) ≤ (⨆ w, ⨅ x, P.saddleLagrangian w x) := by
      exact le_iSup (fun w => ⨅ x, P.saddleLagrangian w x) u
    have hmaximin_le_row :
        (⨆ w, ⨅ x, P.saddleLagrangian w x) ≤ (⨅ x, P.saddleLagrangian u x) := by
      calc
        (⨆ w, ⨅ x, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u0 x) := h0maximin
        _ ≤ (⨅ x, P.saddleLagrangian u x) := hrow0_le_row
    have hmaximin :
        (⨆ w, ⨅ x, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u x) :=
      le_antisymm hmaximin_le_row hrow_le_maximin
    have hrow_eq :
        (⨅ x, P.saddleLagrangian u0 x) = (⨅ x, P.saddleLagrangian u x) := by
      calc
        (⨅ x, P.saddleLagrangian u0 x) = (⨆ w, ⨅ x, P.saddleLagrangian w x) := h0maximin.symm
        _ = (⨅ x, P.saddleLagrangian u x) := hmaximin
    have hbot :
        ⊥ < (⨅ x, P.saddleLagrangian u x) := by
      simpa [hrow_eq] using h0bot
    have hminimax :
        (⨅ x, ⨆ w, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u x) := by
      calc
        (⨅ x, ⨆ w, P.saddleLagrangian w x) = (⨅ x, P.saddleLagrangian u0 x) := h0minimax
        _ = (⨅ x, P.saddleLagrangian u x) := hrow_eq
    exact
      (P.isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
        u).2
        ⟨hbot, hmaximin, hminimax⟩

end OrdinaryConvexProgram

end
