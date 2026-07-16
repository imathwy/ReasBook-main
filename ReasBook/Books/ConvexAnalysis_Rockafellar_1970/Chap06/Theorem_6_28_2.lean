import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

noncomputable section

open scoped BigOperators

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The canonical finite pairing on the intrinsic perturbation index owner
`P.ConstraintIndex = ι ⊕ κ`. -/
def perturbationPairing
    (uStar u : P.ConstraintIndex → 𝕜) : WithBotTop 𝕜 :=
  ((∑ i : P.ConstraintIndex, uStar i * u i : 𝕜) : WithBotTop 𝕜)

-- Proof sketch: unfold `perturbationPairing`; the finite sum vanishes at the zero perturbation
-- vector.
/-- The intrinsic multiplier-perturbation pairing vanishes at the zero perturbation vector. -/
@[simp] theorem perturbationPairing_zero
    (uStar : P.ConstraintIndex → 𝕜) :
    P.perturbationPairing uStar 0 = 0 := sorry

end OrdinaryConvexProgram

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.2 characterizes Kuhn--Tucker multipliers by a global inequality
  for the perturbation value function `p(u)`.
- `core/canonical`: the Chapter 6 owner already present for the multiplier condition is
  `P.IsKuhnTuckerVector`, together with the existing optimal-value owner `P.optimalValue`.
- `bridge/view`: the source writes vectors in one perturbation space. The project's intrinsic
  owner for that space is `P.ConstraintIndex → 𝕜`, with split multipliers `(lam, μ)` mapped into
  it by the canonical bridge `P.splitMultiplier lam μ`.

Domain-style sampling used here:

- `P.optimalValue` and `P.IsKuhnTuckerVector` from `Definition_6_28_3`;
- finite sums over `P.ConstraintIndex` from mathlib's `BigOperators` API;
- indexed infima over subtype-defined feasible sets, as in the Chapter 6 optimal-value owner.

Primitive data vs derived API:

- primitive data: the program `P`, the split multiplier pair `(lam, μ)`, and one intrinsic
  perturbation vector `u : P.ConstraintIndex → 𝕜`;
- source-facing bridge objects: the scalar-threshold perturbation value
  `P.perturbationValue u`, the intrinsic pairing `P.perturbationPairing`, and the split-to-
  intrinsic bridge `P.splitMultiplier`;
- main owner statement: the equivalence between `P.IsKuhnTuckerVector lam μ` and the global lower
  support inequality for `P.perturbationValue`.

Layer target: `source-facing`, stated directly on the existing Kuhn--Tucker owner with only the
minimal bridge data needed to express the perturbation inequality in the book's terms.
-/

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]

variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- Bridge owner: the split multiplier blocks `(lam, μ)` viewed as one intrinsic multiplier map on
`P.ConstraintIndex`. -/
abbrev splitMultiplier (lam : ι → 𝕜) (μ : κ → 𝕜) :
    P.ConstraintIndex → 𝕜 :=
  Sum.elim lam μ

/-- The scalar-threshold perturbation value `p(u)` of `P`, obtained by taking the infimum of the
objective over points of the constraint set satisfying the perturbed inequality and equality
levels encoded by `u`. -/
def perturbationValue (u : P.ConstraintIndex → 𝕜) : WithBotTop 𝕜 :=
  ⨅ x : {x : P.constraintSet //
      (∀ i : ι, P.inequality i x ≤ u (Sum.inl i)) ∧
      (∀ j : κ, P.equality j x = u (Sum.inr j))},
    P.objective x.1

-- Proof sketch: compare the subtype indexing `P.perturbationValue 0` with the feasible-point
-- subtype defining `P.optimalValue`; both describe exactly the points of `P.constraintSet`
-- satisfying the zero right-hand-side inequality and equality constraints.
/-- At the zero perturbation vector, the perturbation value is the unperturbed optimal value. -/
theorem perturbationValue_zero_eq_optimalValue :
    P.perturbationValue 0 = P.optimalValue := sorry

-- Proof sketch: use `P.perturbationValue_zero_eq_optimalValue` to rewrite the source term `p(0)`
-- as the optimal value in the defining Kuhn--Tucker owner. Then compare the infimum of the
-- weighted objective in `P.IsKuhnTuckerVector lam μ` with the family of perturbed infima
-- `P.perturbationValue u`, so that the Kuhn--Tucker condition becomes exactly the global
-- support inequality `p(u) + ⟨(lam, μ), u⟩ ≥ p(0)` for every perturbation `u`.
/-- Theorem 6.28.2: if the unperturbed perturbation value `p(0)` is finite, then a split
multiplier pair `(lam, μ)` is a Kuhn--Tucker vector for `P` if and only if every intrinsic
perturbation vector `u : P.ConstraintIndex → 𝕜` satisfies
`p(u) + ⟨splitMultiplier(lam, μ), u⟩ ≥ p(0)`. -/
theorem isKuhnTuckerVector_iff_forall_perturbationValue_add_perturbationPairing_ge_at_zero
    (lam : ι → 𝕜) (μ : κ → 𝕜)
    (hfinite : ⊥ < P.perturbationValue 0 ∧ P.perturbationValue 0 < ⊤) :
    P.IsKuhnTuckerVector lam μ ↔
      ∀ u : P.ConstraintIndex → 𝕜,
        P.perturbationValue u + P.perturbationPairing (P.splitMultiplier lam μ) u ≥
          P.perturbationValue 0 := sorry

end OrdinaryConvexProgram

end
