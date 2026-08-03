module

public import Topology_Munkres_2000.Book.Definition_67_5.Basis
public import Mathlib.Algebra.Group.ULift

public section

universe u v w

variable {J : Type v} {G : Type u} [AddCommGroup G]
variable (a : J → G)

namespace AddMonoidHom

/-- Additive homomorphisms from `G` are determined by their values on the generating family `a`. -/
theorem ext_of_span_eq_top (h_generates : Submodule.span ℤ (Set.range a) = ⊤) {H : Type w}
    [AddCommGroup H] {f g : G →+ H} (h : ∀ α, f (a α) = g (a α)) : f = g := by
  -- Regard the additive maps as ℤ-linear maps, where spanning gives extensionality.
  apply AddMonoidHom.toIntLinearMap_injective
  exact LinearMap.ext_on_range h_generates h

end AddMonoidHom

namespace Module.IsBasis

/-- A function from a basis to an abelian group extends uniquely to an additive homomorphism. -/
theorem existsUnique_addHom (ha : Module.IsBasis ℤ a) {H : Type w} [AddCommGroup H]
    (y : J → H) : ∃! h : G →+ H, ∀ α, h (a α) = y α := by
  let h : G →+ H := (ha.toBasis.constr ℤ y).toAddMonoidHom
  -- The basis construction realizes the prescribed values on every generator.
  have h_values : ∀ α, h (a α) = y α := by
    intro α
    rw [← congrFun ha.coe_toBasis α]
    exact ha.toBasis.constr_basis ℤ y α
  refine ⟨h, h_values, ?_⟩
  intro g hg
  -- Since the basis spans, agreement on its elements forces agreement everywhere.
  exact AddMonoidHom.ext_of_span_eq_top a ((Module.isBasis_iff a).mp ha).2 fun α ↦
    (hg α).trans (h_values α).symm

end Module.IsBasis

namespace Module

/-- Helper for Lemma 67.7: coordinate-valued additive extensions force ℤ-linear independence. -/
lemma linearIndependent_of_exists_addHom
    (h_extend : ∀ y : J → ℤ, ∃ h : G →+ ℤ, ∀ α, h (a α) = y α) :
    LinearIndependent ℤ a := by
  classical
  rw [linearIndependent_iff'ₛ]
  intro s f g h_relation i hi
  obtain ⟨h, h_values⟩ := h_extend fun j ↦ if j = i then 1 else 0
  -- Applying the coordinate functional turns the vector relation into equality of coefficients.
  have h_mapped := congrArg h h_relation
  simpa only [map_sum, map_zsmul, h_values, smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', hi, if_pos] using h_mapped

end Module

/-- Lemma 67.7. Suppose that the family `a` generates the abelian group `G`. Then `a` is a
basis if and only if every indexed family in any abelian group extends to an additive homomorphism
from `G`; such an extension is unique by `AddMonoidHom.ext_of_span_eq_top`. -/
theorem basis_iff_exists_addHom (h_generates : Submodule.span ℤ (Set.range a) = ⊤) :
    Module.IsBasis ℤ a ↔ ∀ {H : Type w} [AddCommGroup H] (y : J → H),
      ∃ h : G →+ H, ∀ α, h (a α) = y α := by
  constructor
  · intro ha H _ y
    -- A basis extends the target values uniquely; retain the existence required here.
    obtain ⟨h, h_values, _⟩ := Module.IsBasis.existsUnique_addHom a ha y
    exact ⟨h, h_values⟩
  · intro h_extend
    -- Integer-valued coordinate extensions give independence, while generation supplies spanning.
    rw [Module.isBasis_iff]
    refine ⟨Module.linearIndependent_of_exists_addHom a ?_, h_generates⟩
    intro y
    -- Lift ℤ into the target universe, then project the resulting extension back to ℤ.
    obtain ⟨h, h_values⟩ := h_extend fun α ↦ ULift.up (y α)
    refine ⟨AddEquiv.ulift.toAddMonoidHom.comp h, ?_⟩
    intro α
    rw [AddMonoidHom.comp_apply, h_values]
    rfl

end
