module

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.DFinsupp.Submonoid

public section

universe u v

variable {G : Type u} [AddCommGroup G] {J : Type v}
variable (Gα : J → AddSubgroup G)

/-
Definition 67.1. The family `Gα` generates `G` when `(⨆ α, Gα α) = ⊤`.
A term of type `Π₀ α, Gα α` records the formal sum from the definition: it has finite support,
and each component belongs to the corresponding subgroup.
-/
#check (⨆ α, Gα α) = (⊤ : AddSubgroup G)

#check fun [DecidableEq J] (x : G) ↦
  AddSubmonoid.mem_iSup_iff_exists_dfinsupp (fun α ↦ (Gα α).toAddSubmonoid) x
