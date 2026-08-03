module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

universe u

variable {G : Type u} [Group G] (x : G) (n : ℤ)

/- Definition 54.3: In a group, `x⁻¹` denotes the inverse of `x`, `x ^ n`
denotes an integer power, and `x` generates `G` when its integer powers form
all of `G`. The group is cyclic when it has such a generator. -/
#check x⁻¹
#check x ^ n
#check Subgroup.zpowers
#check Subgroup.mem_zpowers_iff
#check (Subgroup.zpowers x = ⊤)
#check IsCyclic
#check isCyclic_iff_exists_zpowers_eq_top
