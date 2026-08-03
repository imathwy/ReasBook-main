module

public import Mathlib.GroupTheory.PresentedGroup

public section

universe u v

namespace FreeGroup.Relations

variable {J : Type u} {G : Type v} [Group G]

/-- The relations subgroup determined by a family of elements of a group. -/
abbrev subgroup (a : J → G) : Subgroup (FreeGroup J) :=
  (FreeGroup.lift a).ker

/-- A set of relators normally generates the kernel of the canonical evaluation map. -/
def NormallyGeneratesKernel (a : J → G) (rels : Set (FreeGroup J)) : Prop :=
  Subgroup.normalClosure rels = subgroup a

/-- The defining equality for `NormallyGeneratesKernel`. -/
theorem normallyGeneratesKernel_iff (a : J → G) (rels : Set (FreeGroup J)) :
    NormallyGeneratesKernel a rels ↔
      Subgroup.normalClosure rels = subgroup a :=
  Iff.rfl

/-- Every relator in a normally generating set lies in the evaluation kernel. -/
theorem subset_ker {a : J → G} {rels : Set (FreeGroup J)}
    (h : NormallyGeneratesKernel a rels) : rels ⊆ subgroup a :=
  fun _ hx ↦ h ▸ Subgroup.subset_normalClosure hx

end FreeGroup.Relations

namespace PresentedGroup

/-- The defining relators normally generate the kernel of the map to their presented group. -/
theorem normallyGeneratesKernel {J : Type u} (rels : Set (FreeGroup J)) :
    FreeGroup.Relations.NormallyGeneratesKernel
      (PresentedGroup.of : J → PresentedGroup rels) rels := by
  change Subgroup.normalClosure rels = (FreeGroup.lift PresentedGroup.of).ker
  rw [show FreeGroup.lift PresentedGroup.of = PresentedGroup.mk rels from
    FreeGroup.lift.symm.injective (by rfl)]
  exact (QuotientGroup.ker_mk' (Subgroup.normalClosure rels)).symm

end PresentedGroup
