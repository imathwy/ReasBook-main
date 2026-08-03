module

public import Topology_Munkres_2000.Book.Definition_68_5
public import Topology_Munkres_2000.Book.Lemma_68_1.Extension
import all Topology_Munkres_2000.Book.Lemma_68_1.Extension

public section

namespace MonoidHom

universe u v w x

variable {ι : Type u} {G : ι → Type v} {H : Type w}
variable [∀ α, Group (G α)] [Group H]

/-- Helper for Lemma 68.3: restricting a homomorphism to the range of an injective
homomorphism gives the same equation as precomposing with the original homomorphism. -/
private lemma comp_range_subtype_eq_iff {A : Type v} {B : Type w} {K : Type x}
    [Group A] [Group B] [Group K] (i : A →* B) (hi : Function.Injective i)
    (h : B →* K) (f : A →* K) :
    h.comp i.range.subtype =
        f.comp (MonoidHom.ofInjective hi).symm.toMonoidHom ↔
      h.comp i = f := by
  have h_range_restrict :
      i.rangeRestrict = (MonoidHom.ofInjective hi).toMonoidHom := by
    ext a
    simp only [i.coe_rangeRestrict, MulEquiv.coe_toMonoidHom,
      MonoidHom.ofInjective_apply]
  constructor
  · intro h_range
    ext a
    -- Evaluate the range equation on the image of `a`, where the inverse equivalence cancels.
    have h_at_image := DFunLike.congr_fun h_range (i.rangeRestrict a)
    rw [h_range_restrict] at h_at_image
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MonoidHom.ofInjective_apply, MulEquiv.symm_apply_apply] using h_at_image
  · intro h_source
    ext y
    -- Pull a range element back to its unique source and use the original equation there.
    have h_at_preimage :=
      DFunLike.congr_fun h_source ((MonoidHom.ofInjective hi).symm y)
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MonoidHom.apply_ofInjective_symm] using h_at_preimage

/-- Lemma 68.3. An external free product has the unique extension property for families of
group homomorphisms from its factors. -/
theorem IsExternalFreeProduct.hasExtension {i : ∀ α, G α →* H}
    (h_free : IsExternalFreeProduct i) : HasFreeProductExtension i := by
  refine fun K _ f ↦ ?_
  let f_range : ∀ α, (i α).range →* K := fun α ↦
    (f α).comp (MonoidHom.ofInjective (h_free.injective α)).symm.toMonoidHom
  -- Extend the transported maps from the internal free product of the factor ranges.
  obtain ⟨h, h_range, h_unique⟩ := h_free.isFreeProduct.hasExtension K f_range
  refine ⟨h, ?_, ?_⟩
  · intro α
    -- The range adapter turns the internal extension equation into the requested one.
    exact (comp_range_subtype_eq_iff (i α) (h_free.injective α) h (f α)).mp
      (h_range α)
  · intro h' h'_source
    -- Conversely, every competing external extension satisfies the internal equations.
    apply h_unique h'
    intro α
    exact (comp_range_subtype_eq_iff (i α) (h_free.injective α) h' (f α)).mpr
      (h'_source α)

end MonoidHom
