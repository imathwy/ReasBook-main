import StacksProject_2024.Chap15.Remark_15_96_5
import StacksProject_2024.Chap15.Lemma_15_94_9

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

namespace BerthelotOgusEtaReduction
namespace Nat

section

variable (f : A) (M : NatModuleCochainComplex A) (i : ℕ)

/-- The submodule `f^i M^i` in the bounded-below Nat bridge for the reduced pair map. -/
abbrev powerSubmodule : Submodule A (M.X i) :=
  principalIdeal (f ^ i) • (⊤ : Submodule A (M.X i))

/-- The submodule `f^(i + 1) M^(i + 1)` in the target of the Nat bridge pair map. -/
abbrev nextPowerSubmodule : Submodule A (M.X (i + 1)) :=
  principalIdeal (f ^ (i + 1)) • (⊤ : Submodule A (M.X (i + 1)))

/-- The Nat Berthelot-Ogus degree term sits inside `f^i M^i`. -/
theorem degreeSubmodule_le_powerSubmodule :
    etaFDegreeSubmodule f M i ≤ powerSubmodule f M i := by
  -- Proof comment: the first defining factor of `etaFDegreeSubmodule` is exactly the range of
  -- multiplication by `f ^ i`, and Lemma `15.94.9` rewrites that range as `f^i M^i`.
  simpa [powerSubmodule, range_lsmul_eq_principalIdeal_smul_top] using
    (show
      etaFDegreeSubmodule f M i ≤
        LinearMap.range (LinearMap.lsmul A (M.X i) (f ^ i)) from
      inf_le_left)

/-- The differential on `η_f M` lands in `f^(i + 1) M^(i + 1)` after the canonical inclusion. -/
abbrev degreeDifferentialToNextPowerSubmodule :
    etaFDegreeSubmodule f M i →ₗ[A] nextPowerSubmodule f M i :=
  (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f M (i + 1))) ∘ₗ
    ((η[f] M).d i (i + 1)).hom

/-- The Nat unreduced pair map `(1, d^i)` from `(η_f M)^i` to
`f^i M^i × f^(i + 1) M^(i + 1)`. -/
abbrev etaPairMap :
    etaFDegreeSubmodule f M i →ₗ[A] powerSubmodule f M i × nextPowerSubmodule f M i :=
  LinearMap.prod
    (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f M i))
    (degreeDifferentialToNextPowerSubmodule f M i)

/-- The Nat reduction of `(1, d^i)` modulo `f`, used by Lemma `15.97.8`. -/
abbrev etaReductionPairMap :
    (CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i →ₗ[A ⧸ principalIdeal f]
      ((powerSubmodule f M i ⧸
          principalIdeal f • (⊤ : Submodule A (powerSubmodule f M i))) ×
        (nextPowerSubmodule f M i ⧸
          principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f M i)))) :=
  LinearMap.prod
    (LinearMap.reduceModIdeal (principalIdeal f)
      (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f M i)))
    (LinearMap.reduceModIdeal (principalIdeal f)
      (degreeDifferentialToNextPowerSubmodule f M i))

end

end Nat
end BerthelotOgusEtaReduction

end
