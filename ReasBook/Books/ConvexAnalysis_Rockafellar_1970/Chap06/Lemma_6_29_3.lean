import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8

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

- `source-facing`: Lemma 6.29.3 says that every point of the source constraint set `C`
  determines a perturbation parameter lying in the parameter domain `dom F`.
- `core/canonical`: the owner parameter space is `P.ConstraintIndex → β`, and the associated
  bifunction-domain owner is already `dom P.perturbedProblem`.
- `bridge/view`: the source tuple `(f₁(x), …, f_m(x))` is represented intrinsically as the
  ambient constraint-family value `fun i ↦ P.constraint i x`, where `x : E` is paired with
  a membership witness `hxC : x ∈ P.constraintSet`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `P.ConstraintIndex` from `Definition_6_28_2`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `Bifunction.dom` and `Bifunction.mem_dom` from `Definition_6_29_8`.

Primitive data vs derived API:
- primitive source data: the program `P`, an ambient point `x : E`, and a witness
  `hxC : x ∈ P.constraintSet`;
- canonical owner-side target: membership of the corresponding constraint-value parameter in
  `dom P.perturbedProblem`;
- derived corollary: nonemptiness of that parameter domain as soon as `P.constraintSet` is
  nonempty.

Layer target: `source-facing`, on the existing owner `P.perturbedProblem`.
-/

-- Proof sketch: for `x : E` with `hxC : x ∈ P.constraintSet`, let `u` be the parameter whose
-- inequality and equality coordinates are the corresponding constraint values at `x`. Then `x`
-- satisfies the perturbed inequalities and equalities defining `P.perturbedFeasibleSet u`, so
-- `P.perturbedProblem u x` is finite. Hence the parameter lies in the canonical bifunction domain
-- `dom P.perturbedProblem`.
/-- Lemma 6.29.3: every point of the constraint set of an ordinary convex program determines a
perturbation parameter lying in the parameter domain of the associated perturbed problem. -/
theorem constraintValueParameter_mem_dom_perturbedProblem
    {x : E} (hxC : x ∈ P.constraintSet) :
    (fun i ↦ P.constraint i x) ∈ dom P.perturbedProblem := by
  let u : P.ConstraintIndex → β := fun i ↦ P.constraint i x
  rw [Bifunction.mem_dom]
  refine ⟨x, ?_⟩
  rw [_root_.mem_effectiveDomain, P.perturbedProblem_apply]
  have hx :
      x ∈ P.perturbedFeasibleSet u := by
    rw [P.mem_perturbedFeasibleSet_split]
    refine ⟨hxC, ?_, ?_⟩
    · intro i
      simp [u, OrdinaryConvexProgram.constraint]
    · intro j
      simp [u, OrdinaryConvexProgram.constraint]
  simpa [u, hx] using (WithBotTop.coe_lt_top (P.objective ⟨x, hxC⟩))

/-- If the constraint set of an ordinary convex program is nonempty, then the parameter domain of
its perturbed problem is nonempty. -/
theorem dom_perturbedProblem_nonempty (hC : P.constraintSet.Nonempty) :
    (dom P.perturbedProblem).Nonempty := by
  rcases hC with ⟨x, hx⟩
  exact ⟨_, P.constraintValueParameter_mem_dom_perturbedProblem hx⟩

end

end OrdinaryConvexProgram
