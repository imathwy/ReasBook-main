import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Lemma_12_23_5_Submodule

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uM uN

section

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/- Domain-style sampling for 12.23.5.2:
- primary domain: filtered submodule estimates for a differential on an `R`-module;
- sampled project declarations in the same domain:
  `CategoryTheory.DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`,
  `kernel_inf_stage_sup_next_le_iInf_stage_comap_sup_next`,
  `iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next`;
- best owner abstraction:
  `iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next`;
- primitive data: a linear endomorphism `d`, a filtration `F`, and the stage index `p`;
- derived API: endomorphism and filtered-complex specializations obtained by instantiating the
  general source and target filtrations in the owner theorem;
- source/core/bridge triage:
  `source-facing`: the filtration inequality for one filtered differential module;
  `core/canonical`: the two-filtration submodule theorem
    `iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next`;
  `bridge/view`: the endomorphism specialization obtained by taking `G = F`.

This file therefore recalls the owner theorem directly and keeps 12.23.5.2 only as the
endomorphism specialization `G = F`, rather than introducing a second local wrapper theorem. -/
/- Owner recall: the boundary-stage inequality already belongs to the canonical project theorem
`iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next`. -/
recall iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next

variable (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (p : ℤ)

/- 12.23.5.2 is the `bridge/view` endomorphism specialization of the owner theorem, obtained by
taking `G = F`. -/
#check (iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next d F F p :
    (⨆ r : ℕ, (F p ⊓ Submodule.map d (F (p - r + 1))) ⊔ F (p + 1)) ≤
      (d.range ⊓ F p) ⊔ F (p + 1))

end
