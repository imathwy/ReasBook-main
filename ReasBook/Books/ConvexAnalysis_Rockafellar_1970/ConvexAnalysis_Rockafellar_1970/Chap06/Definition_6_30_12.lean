import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11

noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [ConditionallyCompleteLattice α] [Add α] [Zero U]
variable [HasPairing U UStar (WithBotTop α)]

local notation "shiftedSup(" G ", " uStar ")" =>
  (⨆ u : U, ⟪u, uStar⟫ₚ + upperPerturbationFunction G u)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.12 introduces the notion of a Kuhn--Tucker vector `u⋆` for
  the concave program attached to a bifunction `G`.
- `core/canonical`: the existing Chapter 6 owners are
  `Bifunction.upperPerturbationFunction` from Definition 6.30.11 and the Chapter 12 Fenchel
  owner `convexConjugate` applied to `- upperPerturbationFunction G` once the additive
  order-dual codomain structure is available.
- `bridge/view`: at the present weak codomain generality the source displayed supremum identity is
  kept as the primitive owner-side formulation, while the pointwise inequality
  `⟪u, u⋆⟫ₚ + upperPerturbationFunction G u ≤ upperPerturbationFunction G 0` is the equivalent
  supporting-hyperplane reformulation and a later companion theorem bridges the source supremum
  to the canonical conjugate owner.

Domain-style sampling used here:
- `Bifunction.upperPerturbationFunction` and `upperPerturbationFunction_apply` from
  Definition 6.30.11;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- `Bifunction.IsKuhnTuckerVector` from Definition 6.29.19 as the infimum-side owner pattern;
- `Bifunction.IsDualKuhnTuckerVector` from Definition 6.30.17 as the dual supremum-side owner
  pattern.

Primitive data vs derived API:
- primitive source data: the bifunction `G` and the dual vector `u⋆`;
- primitive owner in this file: `Bifunction.IsConcaveKuhnTuckerVector G uStar`, defined by the
  interval-membership finiteness and equality statement for the shifted supremum over
  perturbations;
- derived API: bundled finiteness, the supporting-hyperplane inequality, finiteness of the dual
  value `upperPerturbationFunction G 0`, and the bridge to the Fenchel conjugate owner.

Layer target: `source-facing`. This item introduces a genuine new property of dual vectors for a
concave program, so it is exposed directly on the existing bifunction owner rather than through a
witness package or a restated conjugate wrapper.
-/

/-- Definition 6.30.12: a vector `u⋆` is a Kuhn--Tucker vector for the concave program attached
to `G` when the supremum of the shifted perturbation values
`⟪u, u⋆⟫ₚ + upperPerturbationFunction G u` is finite and equals the unperturbed optimal value
`upperPerturbationFunction G 0`. This is the source-facing owner for the Chapter 6 concave
program, with the canonical conjugate view deferred to companion theorems. -/
class IsConcaveKuhnTuckerVector (G : U → X → WithBotTop α) (uStar : UStar) : Prop where
  supremum_mem_Ioo : shiftedSup(G, uStar) ∈ Set.Ioo (⊥ : WithBotTop α) ⊤
  supremum_eq_upperPerturbationFunction_zero :
    shiftedSup(G, uStar) = upperPerturbationFunction G 0

namespace IsConcaveKuhnTuckerVector

variable {G : U → X → WithBotTop α} {uStar : UStar}

/-- Lower finiteness bound from the defining interval-membership field. -/
theorem supremum_bot_lt (h : IsConcaveKuhnTuckerVector G uStar) :
    ⊥ < shiftedSup(G, uStar) :=
  h.supremum_mem_Ioo.1

/-- Upper finiteness bound from the defining interval-membership field. -/
theorem supremum_lt_top (h : IsConcaveKuhnTuckerVector G uStar) :
    shiftedSup(G, uStar) < ⊤ :=
  h.supremum_mem_Ioo.2

-- Proof sketch: unpack the defining interval-membership field `supremum_mem_Ioo`.
/-- A concave Kuhn--Tucker vector makes the defining shifted perturbation supremum finite. -/
theorem supremum_finite (h : IsConcaveKuhnTuckerVector G uStar) :
    ⊥ < shiftedSup(G, uStar) ∧ shiftedSup(G, uStar) < ⊤ :=
  ⟨h.supremum_bot_lt, h.supremum_lt_top⟩

-- Proof sketch: take the symmetric form of the defining equality
-- `h.supremum_eq_upperPerturbationFunction_zero`.
/-- A concave Kuhn--Tucker vector rewrites the unperturbed upper perturbation value as the
defining shifted supremum. -/
theorem upperPerturbationFunction_zero_eq_supremum
    (h : IsConcaveKuhnTuckerVector G uStar) :
    upperPerturbationFunction G 0 = shiftedSup(G, uStar) :=
  h.supremum_eq_upperPerturbationFunction_zero.symm

-- Proof sketch: rewrite `upperPerturbationFunction G 0` using
-- `upperPerturbationFunction_zero_eq_supremum`; then every term of the indexed supremum is below
-- the supremum itself.
/-- A concave Kuhn--Tucker vector satisfies the supporting-hyperplane inequality
`⟪u, u⋆⟫ₚ + upperPerturbationFunction G u ≤ upperPerturbationFunction G 0` for every
perturbation `u`. -/
theorem pairing_add_upperPerturbationFunction_le_upperPerturbationFunction_zero
    (h : IsConcaveKuhnTuckerVector G uStar) (u : U) :
    ⟪u, uStar⟫ₚ + upperPerturbationFunction G u ≤ upperPerturbationFunction G 0 := by
  rw [h.upperPerturbationFunction_zero_eq_supremum]
  exact le_iSup (fun u : U ↦ ⟪u, uStar⟫ₚ + upperPerturbationFunction G u) u

-- Proof sketch: rewrite `upperPerturbationFunction G 0` using
-- `upperPerturbationFunction_zero_eq_supremum`, then transfer the lower and upper bounds from
-- `supremum_mem_Ioo`.
/-- A concave Kuhn--Tucker vector forces the unperturbed upper perturbation value to lie in the
finite interval `Set.Ioo (⊥ : WithBotTop α) ⊤`. -/
theorem upperPerturbationFunction_zero_mem_Ioo
    (h : IsConcaveKuhnTuckerVector G uStar) :
    upperPerturbationFunction G 0 ∈ Set.Ioo (⊥ : WithBotTop α) ⊤ := by
  rw [h.upperPerturbationFunction_zero_eq_supremum]
  exact h.supremum_mem_Ioo

-- Proof sketch: rewrite `upperPerturbationFunction G 0` using
-- `upperPerturbationFunction_zero_eq_supremum`, then transfer the lower and upper bounds from
-- `supremum_mem_Ioo`.
/-- A concave Kuhn--Tucker vector forces the unperturbed upper perturbation value to be finite. -/
theorem upperPerturbationFunction_zero_finite
    (h : IsConcaveKuhnTuckerVector G uStar) :
    ⊥ < upperPerturbationFunction G 0 ∧ upperPerturbationFunction G 0 < ⊤ := by
  exact h.upperPerturbationFunction_zero_mem_Ioo

end IsConcaveKuhnTuckerVector

end

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [Add α] [InvolutiveNeg α] [ConditionallyCompleteLattice α]
variable [HasPairing U UStar (WithBotTop α)]

local notation "shiftedSup(" G ", " uStar ")" =>
  (⨆ u : U, ⟪u, uStar⟫ₚ + upperPerturbationFunction G u)

-- Proof sketch: expand the Fenchel conjugate of `- upperPerturbationFunction G` by
-- `convexConjugate_eq_iSup_pairing_sub`; then rewrite subtraction on `WithBotTop α` as addition
-- of the negation and simplify `-(- upperPerturbationFunction G u)`.
/-- The source shifted supremum from Definition 6.30.12 is exactly the Fenchel conjugate of the
negated upper perturbation function, evaluated at `u⋆`. -/
theorem shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction
    (G : U → X → WithBotTop α) (uStar : UStar) :
    shiftedSup(G, uStar) = (- upperPerturbationFunction G)⋆ uStar := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine iSup_congr ?_
  intro u
  rw [WithBotTop.sub_eq_add_neg]
  simp

namespace IsConcaveKuhnTuckerVector

variable [Zero U]
variable {G : U → X → WithBotTop α} {uStar : UStar}

-- Proof sketch: rewrite the source shifted supremum by
-- `shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction`, then use the defining equality
-- `supremum_eq_upperPerturbationFunction_zero`.
/-- Under the canonical additive structure on `WithBotTop α`, a concave Kuhn--Tucker vector
identifies the Fenchel conjugate of `- upperPerturbationFunction G` at `u⋆` with the unperturbed
upper perturbation value. -/
theorem convexConjugate_neg_upperPerturbationFunction_eq_upperPerturbationFunction_zero
    (h : IsConcaveKuhnTuckerVector G uStar) :
    (- upperPerturbationFunction G)⋆ uStar = upperPerturbationFunction G 0 := by
  rw [← shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction G uStar,
    h.supremum_eq_upperPerturbationFunction_zero]

end IsConcaveKuhnTuckerVector

end

end Bifunction
