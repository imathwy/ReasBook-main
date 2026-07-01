import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_6_29_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_2

noncomputable section

universe u v w x

namespace OrdinaryConvexProgram

section

open scoped Rockafellar

variable {𝕜 : Type x} {E : Type u} {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.4 says that the bifunction associated with an ordinary convex
  program is proper.
- `core/canonical`: Chapter 1 already owns properness of an extended-value function as
  `Function.IsProper`, and the Chapter 6 bifunction attached to `P` is already `P.perturbedProblem`.
- `bridge/view`: the graph-function surface is therefore directly
  `(Function.uncurry P.perturbedProblem).IsProper`.

Domain-style sampling used here:
- `Function.IsProper` from `Chap01.Definition_4_6`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.dom_perturbedProblem_nonempty` from `Lemma_6_29_3`;
- `Bifunction.mem_dom_iff_exists_mem_dom_uncurry` from `Proposition_6_29_2`.

Primitive data vs derived API:
- primitive source data: the program `P`;
- primitive owner-side hypothesis: nonemptiness of the bifunction domain
  `dom P.perturbedProblem`, i.e. existence of one finite graph point;
- source-facing hypothesis: nonemptiness of `P.constraintSet`, used only to build that primitive
  domain witness via Lemma 6.29.3;
- derived conclusion: properness of the graph function `(Function.uncurry P.perturbedProblem)`.

Layer target: `source-facing`, on the existing owner `P.perturbedProblem`.
-/

-- Proof sketch: from a domain witness `u ∈ dom P.perturbedProblem`, the canonical bridge
-- `Bifunction.mem_dom_iff_exists_mem_dom_uncurry` gives a finite graph point of
-- `Function.uncurry P.perturbedProblem`. Since `P.perturbedProblem` is built using
-- `Function.toWithBotTopOn`, graph values are never `⊥`.
/-- Core owner form: if the bifunction domain of the perturbed problem is nonempty, then its graph
function is proper in the Chapter 1 sense. -/
theorem uncurry_perturbedProblem_isProper_of_dom_nonempty
    (hdom : (dom P.perturbedProblem).Nonempty) :
    (Function.uncurry P.perturbedProblem).IsProper := by
  rw [Function.isProper_iff]
  refine ⟨?_, ?_⟩
  · rcases hdom with ⟨u, hu⟩
    rcases (Bifunction.mem_dom_iff_exists_mem_dom_uncurry).1 hu with ⟨x, hx⟩
    exact ⟨(u, x), hx⟩
  · rintro ⟨u, x⟩
    rw [Function.uncurry, P.perturbedProblem_apply]
    split_ifs <;> simp

/-- Lemma 6.29.4 (source-facing form): if the constraint set of an ordinary convex program is
nonempty, then the graph function of its perturbed problem is proper. -/
theorem uncurry_perturbedProblem_isProper (hC : P.constraintSet.Nonempty) :
    (Function.uncurry P.perturbedProblem).IsProper :=
  P.uncurry_perturbedProblem_isProper_of_dom_nonempty (P.dom_perturbedProblem_nonempty hC)

end

end OrdinaryConvexProgram
