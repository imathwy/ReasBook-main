import Mathlib.GroupTheory.Nilpotent

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G]
variable {p : ℕ} [Fact p.Prime]

-- Source/core/bridge triage: this is `bridge/view`. The core owners are `Group.IsNilpotent G`,
-- `Sylow.normal_of_normalizerCondition`, and `Sylow.unique_of_normal`.
/-- Exercise 8-8.4-4: in a finite nilpotent group, the Sylow `p`-subgroups of `G` form a singleton
type, so `G` contains a unique Sylow `p`-subgroup. -/
noncomputable instance unique_sylow_subgroup_of_nilpotent : Unique (Sylow p G) :=
  Sylow.unique_of_normal default <|
    Sylow.normal_of_normalizerCondition normalizerCondition_of_isNilpotent default

end
