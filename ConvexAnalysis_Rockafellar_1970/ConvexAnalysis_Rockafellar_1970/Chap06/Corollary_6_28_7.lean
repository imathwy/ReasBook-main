import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_28_4

noncomputable section

universe u
universe v
universe w

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {α : Type w} [AddCommGroup α] [SMul 𝕜 α]
variable [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable {U : Type u} [AddCommMonoid U] [SMul 𝕜 U]
variable {X : Type*}

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.7 uses the dual-objective shape
  `g(u) = inf_x L(u, x)`, which is the Chapter 6 perturbation-function owner of a bifunction.
- `core/canonical`: the canonical row-infimum owner is `Bifunction.perturbationFunction`, and
  the canonical curvature owner is `Function.IsConcave`.
- `bridge/view`: if every slice `u ↦ F u x` is concave, then
  `perturbationFunction F = fun u ↦ inf_x F u x` is concave by `Function.IsConcave.iInf`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and `Bifunction.perturbationFunction_apply` from
  `Definition_6_29_1`;
- `Function.IsConcave.iInf` from `Proposition_6_28_4`;
- `Function.IsConcave` from `Definition_6_30_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F` and slice concavity hypotheses
  `∀ x, (F · x).IsConcave 𝕜`;
- derived API: concavity of the canonical row-infimum owner `perturbationFunction F`.

Layer target: `core/canonical`, so downstream source items can reuse this owner-level bridge
without introducing item-specific wrappers around the same pointwise-infimum argument.
-/

/-- Row-infimum concavity bridge: if every slice `u ↦ F u x` is concave, then the
perturbation function `u ↦ inf_x F u x` is concave. -/
theorem perturbationFunction_isConcave
    (F : U → X → WithBotTop α)
    (hSlice : ∀ x : X, (F · x).IsConcave 𝕜) :
    (perturbationFunction F).IsConcave 𝕜 := by
  have hpert : perturbationFunction F = fun u ↦ ⨅ x, F u x := by
    funext u
    simpa using (perturbationFunction_apply F u)
  have hslices :
      (fun u ↦ ⨅ x, F u x) = (⨅ x : X, fun u ↦ F u x) := by
    funext u
    simp [iInf_apply]
  rw [hpert, hslices]
  exact Function.IsConcave.iInf (fun x ↦ by simpa using hSlice x)

end Bifunction

end

section

variable {𝕜 : Type v} [Ring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedAddMonoid 𝕜]
variable [DecidableLT 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

open Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.7 states that the dual function attached to the Lagrangian,
  namely `g(u) = inf_x L(u, x)`, is concave.
- `core/canonical`: the Chapter 6 owner for a bifunction row-infimum `u ↦ inf_x F u x` is
  `Bifunction.perturbationFunction`, and the chapter owner for the conclusion is
  `Function.IsConcave`.
- `bridge/view`: specialize the canonical bifunction bridge
  `Bifunction.perturbationFunction_isConcave` to the Lagrangian owner
  `P.saddleLagrangian`.
- abstraction normalization: no step of this bridge needs the concrete codomain `EReal` or the
  concrete scalar `ℝ`; the source-facing corollary is exposed on
  `OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ` with only the primitive slice-concavity
  hypothesis.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and `Bifunction.perturbationFunction_apply` from
  `Definition_6_29_1`;
- `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`;
- `Bifunction.perturbationFunction_isConcave` from this file;
- `Function.IsConcave.iInf` from `Proposition_6_28_4`;
- `Function.IsConcave` from `Definition_6_30_2`.

Primitive data vs derived API:
- primitive source data: the program `P` and its Lagrangian owner `P.saddleLagrangian`;
- primitive curvature hypothesis: `∀ x, (P.saddleLagrangian · x).IsConcave 𝕜`;
- derived API: concavity of the canonical row-infimum owner
  `perturbationFunction P.saddleLagrangian`.

Layer target: `bridge/view`, stated directly on the existing perturbation-function owner instead
of a parallel ordinary-program alias for the same row-infimum construction.
-/

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

/-- Corollary 6.28.7: the dual function of an ordinary convex program, defined by
`g(u) = inf_x L(u, x)`, is the perturbation function of the Lagrangian bifunction and is concave
on the multiplier space. The statement is expressed directly on the chapter owner
`(perturbationFunction P.saddleLagrangian).IsConcave`. In owner-normalized bridge form, the
assumption is exactly concavity of each Lagrangian slice in the multiplier variable. -/
theorem lagrangianDualObjective_isConcave
    (hSlice : ∀ x : E, (P.saddleLagrangian · x).IsConcave 𝕜) :
    (perturbationFunction P.saddleLagrangian).IsConcave 𝕜 := by
  simpa using
    (Bifunction.perturbationFunction_isConcave
      (F := P.saddleLagrangian) hSlice)

end OrdinaryConvexProgram

end
