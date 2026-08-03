module

public import Mathlib.LinearAlgebra.Projection

public section

universe u

/-- Corollary 67.3. If `G` is the internal direct sum of complementary additive
subgroups `G₁` and `G₂`, then `G ⧸ G₂` is additively isomorphic to `G₁`. -/
noncomputable def quotientAddEquivOfIsCompl {G : Type u} [AddCommGroup G]
    (G₁ G₂ : AddSubgroup G) (h : IsCompl G₁ G₂) :
    G ⧸ G₂ ≃+ G₁ :=
  (G₂.toIntSubmodule.quotientEquivOfIsCompl G₁.toIntSubmodule
    (AddSubgroup.toIntSubmodule.isCompl h.symm)).toAddEquiv

/-- The isomorphism of Corollary 67.3 sends the class of an element of `G₁` to that element. -/
@[simp]
theorem quotientAddEquivOfIsCompl_mk_left {G : Type u} [AddCommGroup G]
    (G₁ G₂ : AddSubgroup G) (h : IsCompl G₁ G₂) (x : G₁) :
    quotientAddEquivOfIsCompl G₁ G₂ h (QuotientAddGroup.mk x) = x := by
  exact Submodule.quotientEquivOfIsCompl_apply_mk_right
    (AddSubgroup.toIntSubmodule.isCompl h.symm) x

end
