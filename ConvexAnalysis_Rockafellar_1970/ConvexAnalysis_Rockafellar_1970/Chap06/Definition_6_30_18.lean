import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

noncomputable section

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.18 introduces the perturbation bifunction attached to linear
  program data `(c, a, A)`.
- `core/canonical`: the orthant constraint is the canonical cone owner `ConvexCone.positive`, and
  the perturbation term is encoded by the indicator owner `δ[𝕜](· | C)`.
- `bridge/view`: coordinate/matrix spellings are downstream bridges; this owner file keeps the
  intrinsic ordered-module statement surface.

Domain-style sampling used here:
- `orthant[𝕜](X)` and `ConvexCone.mem_positive`;
- `indicator` / `δ[𝕜](· | C)` from `Chap01.Defintion_4_8_1`;
- `Bifunction.objective` / `(·)₀` from `Chap06.Definition_6_29_12`.

Primitive data vs derived API:
- primitive source data: the objective pairing-side element `c : XStar`, the right-hand side `a`,
  and the linear map `A : X →ₗ[𝕜] U`;
- primitive source-facing owner: `linearProgramFeasibleSet a A u` and
  `linearProgram c a A`;
- derived API: pointwise unfolding, branch lemmas on/off feasibility, and the zero-slice objective
  formula.

Layer target: `source-facing` at the intrinsic ordered-module + linear-map layer.
-/

section

variable {𝕜 : Type*} {U X XStar : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommMonoid U] [Preorder U] [Module 𝕜 U]
variable [HasPairing XStar X 𝕜]

/-- Definition 6.30.18: the feasible set in the perturbation parameter `u` for the linear-program
constraints attached to `(a, A)`. -/
def linearProgramFeasibleSet
    (a : U) (A : X →ₗ[𝕜] U) (u : U) : Set X :=
  {x | x ∈ orthant[𝕜](X) ∧ a ≤ A x + u}

@[simp] theorem mem_linearProgramFeasibleSet_iff
    {a : U} {A : X →ₗ[𝕜] U} {u : U} {x : X} :
    x ∈ linearProgramFeasibleSet a A u ↔
      0 ≤ x ∧ a ≤ A x + u := by
  simp [linearProgramFeasibleSet]

/-- Definition 6.30.18: the bifunction associated with the linear program data `(c, a, A)`. -/
def linearProgram
    (c : XStar) (a : U) (A : X →ₗ[𝕜] U) :
    U → X → WithTopBot 𝕜 :=
  fun u x ↦ ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A u)

@[simp] theorem linearProgram_apply
    (c : XStar) (a : U) (A : X →ₗ[𝕜] U) (u : U) (x : X) :
    linearProgram c a A u x =
      ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A u) :=
  rfl

/-- On the perturbed feasible set, the LP bifunction is just the linear objective branch. -/
@[simp] theorem linearProgram_apply_of_mem
    {c : XStar} {a : U} {A : X →ₗ[𝕜] U} {u : U} {x : X}
    (hx : x ∈ linearProgramFeasibleSet a A u) :
    linearProgram c a A u x = ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
  simp [linearProgram, hx]

/-- Off the perturbed feasible set, the LP bifunction takes the value `+∞`. -/
@[simp] theorem linearProgram_apply_of_notMem
    {c : XStar} {a : U} {A : X →ₗ[𝕜] U} {u : U} {x : X}
    (hx : x ∉ linearProgramFeasibleSet a A u) :
    linearProgram c a A u x = ⊤ := by
  change ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A u) =
      (⊤ : WithTopBot 𝕜)
  simp [hx]

/-- The unperturbed objective `(linearProgram c a A)₀` of the LP bifunction is
`x ↦ ⟪c, x⟫ₚ + δ[𝕜](x | x ∈ orthant[𝕜](X), a ≤ A x + 0)`. -/
@[simp] theorem objective_linearProgram_apply
    (c : XStar) (a : U) (A : X →ₗ[𝕜] U) (x : X) :
    (linearProgram c a A)₀ x =
      ((⟪c, x⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](x | linearProgramFeasibleSet a A 0) := by
  rfl

end

end Bifunction
