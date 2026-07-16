import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_15
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_18
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 31.2.2 introduces the Fenchel-side functions
  `f x = c x + δ[𝕜](x | x ≥ 0)` and `g u = -δ[𝕜](u | u ≥ a)` for linear-program
  data `(c, a, A)`.
- `core/canonical`: the Chapter 31 owner for the resulting bifunction is already
  `fenchelPerturbation`, while the Section 30 owner for the same LP perturbation and feasible
  slice is `linearProgram` with `linearProgramFeasibleSet`.
- `bridge/view`: this item keeps the source-facing displayed `f` and `g`, uses the canonical
  owner `fenchelPerturbation` for the bifunction itself, and identifies that owner with
  `linearProgram`.

Domain-style sampling used here:
- `linearProgram` and `linearProgramFeasibleSet` from `Definition_6_30_18`;
- `optimalValue` from `Definition_6_29_15`;
- `fenchelPerturbation` and `objective_fenchelPerturbation_apply` from `Lemma_31_0_6`;
- the ordered-module owners `orthant[𝕜](X)` and `Set.Ici`;
- the indicator notation `δ[𝕜](· | C)`.

Primitive data vs derived API:
- primitive source data: the objective dual element `c`, the right-hand side `a`, and the linear
  map `A`;
- primitive source-facing helpers: the displayed functions `f` and `g`;
- main source-facing owner: the resulting bifunction, now exposed through the canonical Chapter 31
  owner `fenchelPerturbation`;
- derived API: the pointwise source formulas for `f` and `g`, the identification of the resulting
  perturbation with the existing Section 30 LP owner `linearProgram`, and the corresponding
  optimal-value formula stated directly on that canonical LP owner.

Layer target: `bridge/view`. The source-facing displayed data `f` and `g` remain explicit, but
the bifunction itself is refined to the existing canonical owner `fenchelPerturbation` instead of
being duplicated as a second local wrapper.
-/

section Primal

variable {𝕜 : Type*} {X : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]

/-- The primal-side function in the Fenchel representation of linear-program data `(c, a, A)`:
the linear objective branch `x ↦ c x` plus the indicator of the nonnegative orthant. -/
def linearProgramFenchelPrimal
    (c : Module.Dual 𝕜 X) :
    X → WithBotTop 𝕜 :=
  fun x ↦ ((c x : 𝕜) : WithBotTop 𝕜) + δ[𝕜](x | orthant[𝕜](X))

@[simp] theorem linearProgramFenchelPrimal_apply
    (c : Module.Dual 𝕜 X) (x : X) :
    linearProgramFenchelPrimal c x =
      ((c x : 𝕜) : WithBotTop 𝕜) + δ[𝕜](x | orthant[𝕜](X)) :=
  rfl

end Primal

section Concave

variable {𝕜 : Type*} {U : Type*}
variable [AddGroup 𝕜] [Preorder U]

/-- The concave-side function in the Fenchel representation of linear-program data `(c, a, A)`:
the negative of the indicator of the upper set `{u | a ≤ u}`. -/
def linearProgramFenchelConcave
    (a : U) :
    U → WithBotTop 𝕜 :=
  fun u ↦ -(δ[𝕜](u | Set.Ici a))

@[simp] theorem linearProgramFenchelConcave_apply
    (a : U) (u : U) :
    linearProgramFenchelConcave a u = -(δ[𝕜](u | Set.Ici a)) :=
  rfl

end Concave

section FenchelLinearProgramBridge

variable {𝕜 : Type*} {U X : Type*}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup U] [Preorder U] [Module 𝕜 U]

@[simp] theorem fenchelPerturbation_linearProgramFenchel_apply
    (c : Module.Dual 𝕜 X) (a : U) (A : X →ₗ[𝕜] U) (u : U) (x : X) :
    fenchelPerturbation
        A
        (linearProgramFenchelPrimal c)
        (linearProgramFenchelConcave a) u x =
      linearProgram c a A u x := by
  sorry

-- Proof sketch: expand the Chapter 31 owner `fenchelPerturbation`,
-- rewrite the displayed `f` and `g` by definition, and then use
-- `a ≤ A x + u ↔ a - A x ≤ u` to identify the second indicator with the LP feasibility
-- slice `linearProgramFeasibleSet a A u`.
/-- Definition 31.2.2, canonical-owner form: the Fenchel perturbation built from the displayed
LP-side functions `f` and `g` is exactly the existing Section 30 linear-program owner. -/
theorem fenchelPerturbation_linearProgramFenchel_eq_linearProgram
    (c : Module.Dual 𝕜 X) (a : U) (A : X →ₗ[𝕜] U) :
    fenchelPerturbation
        A
        (linearProgramFenchelPrimal c)
        (linearProgramFenchelConcave a) =
      linearProgram c a A := by
  ext u x
  simpa using fenchelPerturbation_linearProgramFenchel_apply c a A u x

-- Proof sketch: once
-- `fenchelPerturbation_linearProgramFenchel_eq_linearProgram` identifies the branch data with the
-- canonical Section 30 owner `linearProgram`, the optimal-value clause should stay on that owner;
-- then use the LP zero-slice description and `optimalValue` as the infimum over the
-- zero-perturbation feasible set.
/-- The optimal value of the canonical LP owner attached to `(c, a, A)` is the infimum of
`c x` over the unperturbed feasible set. -/
theorem optimalValue_linearProgram_eq_iInf_feasibleSet
    [InfSet (WithBotTop 𝕜)]
    (c : Module.Dual 𝕜 X) (a : U) (A : X →ₗ[𝕜] U) :
    optimalValue (linearProgram c a A) =
      ⨅ x : linearProgramFeasibleSet a A 0, ((c x : 𝕜) : WithBotTop 𝕜) := sorry

end FenchelLinearProgramBridge

end Bifunction
