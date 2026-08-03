module

public import Topology_Munkres_2000.Book.Definition_81_5.HomeomorphGroup

public section

universe u v

namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E]

/-- The group of self-homeomorphisms of `E` lying over a map `p : E → B`. -/
def group (p : E → B) : Subgroup (E ≃ₜ E) where
  carrier := {h | p ∘ h = p}
  mul_mem' := by
    intro f g hf hg
    change p ∘ f = p at hf
    change p ∘ g = p at hg
    apply funext
    intro x
    exact (congrFun hf (g x)).trans (congrFun hg x)
  one_mem' := by rfl
  inv_mem' := by
    intro f hf
    change p ∘ f = p at hf
    apply funext
    intro x
    simpa using (congrFun hf (f.symm x)).symm

/-- Membership in `CoveringTransformation.group p` means that the homeomorphism lies over `p`. -/
theorem mem_group (p : E → B) (h : E ≃ₜ E) :
    h ∈ group p ↔ p ∘ h = p := Iff.rfl

/-- A covering transformation acts through its underlying homeomorphism. -/
instance instCoeFun (p : E → B) : CoeFun (group p) (fun _ ↦ E → E) where
  coe h := h.1

/-- A map is invariant under every transformation in its covering-transformation group. -/
theorem map_smul (p : E → B) (g : group p) (x : E) : p (g • x) = p x := by
  exact congrFun g.property x

end CoveringTransformation

/-- Textbook notation for the group of covering transformations of `p : E → B`. -/
scoped[CoveringTransformation] notation "𝒞(" E ", " p ", " B ")" =>
  CoveringTransformation.group (p : E → B)
