import Mathlib
import StacksProject_2024.stacks_project.Chap07.Example_7_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

variable (S : Scheme.{u})

local notation "J_et" => S.overGrothendieckTopology @Etale
local notation "J_sm" => S.overGrothendieckTopology @Smooth

/- Domain-style sampling for Example 7.22.5:
- primary domain: continuity and cocontinuity comparisons between the big étale and big smooth
  Grothendieck topologies on `Over S`;
- sampled owner API:
  `Scheme.overGrothendieckTopology`,
  `Scheme.grothendieckTopology_monotone`,
  `CategoryTheory.id_isContinuous_of_le`,
  `Functor.IsCocontinuous`,
  `Functor.IsContinuous`;
- source/core/bridge triage:
  `source-facing`: the comparison between the big smooth and big étale sites of `S`;
  `core/canonical`: the owner predicates `Functor.IsContinuous` and `Functor.IsCocontinuous` on
    `S.overGrothendieckTopology`;
  `bridge/view`: the topology comparison `J_et ≤ J_sm`, from which continuity of the identity
    functor `(Over S, J_et) ⥤ (Over S, J_sm)` and cocontinuity in the reverse direction are
    derived.

The primitive owner data are the two induced Grothendieck topologies on `Over S` together with
their comparison `J_et ≤ J_sm`. The continuity and cocontinuity owners for the identity functor
are derived API from that comparison, not parallel local wrappers. The nonemptiness hypothesis in
the final companion theorem belongs to the source-facing non-continuity assertion: for the empty
scheme the smooth and étale sites over `S` collapse.
-/
/-- The big étale topology on `Over S` is finer than the big smooth topology, since every étale
morphism is smooth. -/
theorem overGrothendieckTopology_etale_le_smooth : J_et ≤ J_sm := by
  intro X R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact
    Scheme.grothendieckTopology_monotone
      (fun _ _ f hf ↦ by
        let _ : Etale f := hf
        infer_instance) _ hR

/-- The identity functor on `Over S` is continuous from the big étale site to the big smooth
site. -/
instance over_etale_to_smooth_identity_isContinuous :
    Functor.IsContinuous (𝟭 (Over S)) J_et J_sm :=
  id_isContinuous_of_le (overGrothendieckTopology_etale_le_smooth S)

/-- The identity functor on `Over S` is cocontinuous from the big smooth site to the big étale
site. -/
instance over_smooth_to_etale_identity_isCocontinuous :
    Functor.IsCocontinuous (𝟭 (Over S)) J_sm J_et := by
  refine ⟨fun hS ↦ by simpa using overGrothendieckTopology_etale_le_smooth S _ hS⟩

/-- For a nonempty scheme `S`, the identity functor on `Over S` is not continuous from the big
smooth site to the big étale site. -/
theorem not_over_smooth_to_etale_identity_isContinuous (hS : Nonempty S) :
    ¬ Functor.IsContinuous (𝟭 (Over S)) J_sm J_et := by
  sorry

/-- Example 7.22.5: for a scheme `S`, the identity functor on `Over S` gives a cocontinuous
functor from the big smooth site `(Sch/S)_{smooth}` to the big étale site `(Sch/S)_{étale}`. If
`S` is nonempty, the same identity functor is not continuous from the smooth site to the étale
site. -/
theorem over_smooth_to_etale_identity_cocontinuous_not_continuous :
    Functor.IsCocontinuous (𝟭 (Over S)) J_sm J_et ∧
    ∀ _ : Nonempty S, ¬ Functor.IsContinuous (𝟭 (Over S)) J_sm J_et := by
  refine ⟨inferInstance, ?_⟩
  intro hS
  exact not_over_smooth_to_etale_identity_isContinuous S hS
