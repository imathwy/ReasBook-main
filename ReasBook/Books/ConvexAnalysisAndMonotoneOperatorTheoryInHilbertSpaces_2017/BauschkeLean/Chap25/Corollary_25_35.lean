import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap23.Example_23_3
import BauschkeLean.Chap25.Corollary_25_34

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace ERealFunction

section ParallelSum

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open SetValuedOperator

local notation "doubleOp" => Function.toSetValuedOperator (((2 : ℝ) • (id : H → H)))

/- Source/core/bridge triage:
- `source-facing`: Corollary 25.35 is the proximal-operator identity for `f + g`.
- `core/canonical`: the owner-level operator identity lives on the Chapter 23/25 surface
  `J[...]`, `□`, and `.comp`.
- `bridge/view`: Example 23.3 identifies those resolvents of subdifferentials with the
  singleton-valued operators induced by `Prox[...]`, so this file should reuse that bridge
  directly through the canonical `PosReal` numeric surface. -/

/-- Corollary 25.35: if `f, g ∈ Γ₀(H)` have intersecting effective domains and
`∂ f + ∂ g = ∂ (f + g)`, then the singleton-valued proximity operator of `f + g` is the
parallel sum of the singleton-valued operators induced by `Prox[2f]` and `Prox[2g]`,
precomposed with `x ↦ (2 : ℝ) • x`. This is the source identity `(25.39)` on the canonical
set-valued-operator surface. -/
theorem proximityOperator_add_eq_parallelSum_scaledProx_comp_double
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hsub : (∂ f) + (∂ g) = (∂ (f + g) : SetValuedOperator H H)) :
    (Prox[f + g, pointwiseAdd_mem_gammaZero f g hf hg hdom]).toSetValuedOperator =
      (((Prox[(2 : PosReal), f, hf]).toSetValuedOperator □
          (Prox[(2 : PosReal), g, hg]).toSetValuedOperator : SetValuedOperator H H)).comp
        (((2 : ℝ) • (id : H → H)).toSetValuedOperator) := by
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  calc
    (Prox[f + g, hfg]).toSetValuedOperator = J[(∂ (f + g) : SetValuedOperator H H)] := by
      rw [resolvent_def]
      simpa using singleton_proximityOperator_eq_inverse_add_subdifferential hfg
    _ = J[((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))] := by
      rw [← hsub]
    _ =
        (J[((2 : ℝ) • (∂ f : SetValuedOperator H H))] □
            J[((2 : ℝ) • (∂ g : SetValuedOperator H H))]).comp
          doubleOp := by
        simpa using
          (resolvent_add_eq_parallelSum_double_resolvents_comp_double :
            J[((∂ f : SetValuedOperator H H) + (∂ g : SetValuedOperator H H))] =
              (J[((2 : ℝ) • (∂ f : SetValuedOperator H H))] □
                  J[((2 : ℝ) • (∂ g : SetValuedOperator H H))]).comp
                ((((2 : ℝ) • (id : H → H)).toSetValuedOperator)))
    _ =
        (((Prox[(2 : PosReal), f, hf]).toSetValuedOperator □
            (Prox[(2 : PosReal), g, hg]).toSetValuedOperator : SetValuedOperator H H)).comp
          doubleOp := by
        have hres :
            J[((2 : ℝ) • (∂ f : SetValuedOperator H H))] □
                J[((2 : ℝ) • (∂ g : SetValuedOperator H H))] =
              ((Prox[(2 : PosReal), f, hf]).toSetValuedOperator □
                (Prox[(2 : PosReal), g, hg]).toSetValuedOperator : SetValuedOperator H H) := by
          have htwo : ((2 : PosReal) : ℝ) = (2 : ℝ) := by
            change ((2 : PosReal).1 : ℝ) = (2 : ℝ)
            dsimp [OfNat.ofNat, ERealFunction.instOfNatPosReal]
            norm_num
          simpa [htwo] using
            show
              J[(((2 : PosReal) : ℝ) • (∂ f : SetValuedOperator H H))] □
                  J[(((2 : PosReal) : ℝ) • (∂ g : SetValuedOperator H H))] =
                ((Prox[(2 : PosReal), f, hf]).toSetValuedOperator □
                  (Prox[(2 : PosReal), g, hg]).toSetValuedOperator : SetValuedOperator H H) by
              rw [resolvent_subdifferential_eq_scaledProximityOperator f hf (2 : PosReal),
                resolvent_subdifferential_eq_scaledProximityOperator g hg (2 : PosReal)]
        exact congrArg (fun T : SetValuedOperator H H ↦ T.comp doubleOp) hres

end ParallelSum

end ERealFunction
