import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory.Sequence
open IsLocalRing
open Submodule
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

-- Proof sketch: `maximalIdeal R • M ≠ M` by Nakayama, so `Ideal.depth (maximalIdeal R) M` is the
-- supremum of the lengths of regular sequences contained in `maximalIdeal R`. Each such sequence
-- has length at most `Module.supportDim R M` by
-- `Module.supportDim_add_length_eq_supportDim_of_isRegular`, since the quotient by a regular
-- sequence is nontrivial.
/-- Lemma 10.72.3: if `(R, 𝔪)` is a Noetherian local ring and `M` is a nonzero finite
`R`-module, then `depth(M) ≤ dim (Supp(M))`. -/
theorem depth_le_supportDim :
    WithBot.some (moduleDepth R M : ℕ∞) ≤ Module.supportDim R M := by
  change WithBot.some (Ideal.depth (maximalIdeal R) M : ℕ∞) ≤ Module.supportDim R M
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (maximalIdeal_le_jacobson (Module.annihilator R M)))
  have hdim :
      Module.supportDim R M ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial R M
  rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  refine (WithBot.coe_le_iff).2 ⟨(Module.supportDim R M).unbot hdim, ?_, ?_⟩
  · exact (WithBot.coe_unbot _ _).symm
  · refine sSup_le fun d hd ↦ ?_
    rcases hd with ⟨rs, hreg, -, rfl⟩
    have hquot :
        Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≠ ⊥ :=
      by
        letI : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
          Quotient.nontrivial_iff.2 <| by
            simpa [ne_comm] using hreg.top_ne_smul
        exact Module.supportDim_ne_bot_of_nontrivial R _
    have hlen : (((rs.length : ℕ∞) : WithBot ℕ∞)) ≤ Module.supportDim R M := by
      rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg]
      simpa [add_comm] using WithBot.le_add_self hquot (((rs.length : ℕ∞) : WithBot ℕ∞))
    rw [← WithBot.coe_unbot (Module.supportDim R M) hdim] at hlen
    exact WithBot.coe_le_coe.mp hlen

end
