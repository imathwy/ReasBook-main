module

public import Topology_Munkres_2000.Book.Lemma_68_3.Extension
import all Topology_Munkres_2000.Book.Lemma_68_1.Extension
import Mathlib.Algebra.Group.ULift

public section

universe u v w x y

namespace MonoidHom.HasFreeProductExtension

/-- Helper for Theorem 68.4: an extension property quantified in a common larger universe
still gives a unique extension into a group in its original universe. -/
private lemma existsUnique_extension_of_universeLift
    {ι : Type u} (G : ι → Type v) {H : Type w} {K : Type x}
    [∀ α, Group (G α)] [Group H] [Group K]
    (i : ∀ α, G α →* H)
    (h_extension : HasFreeProductExtension.{u, v, w, max y x} i)
    (f : ∀ α, G α →* K) :
    ∃! h : H →* K, ∀ α, h.comp (i α) = f α := by
  unfold MonoidHom.HasFreeProductExtension at h_extension
  let up : K →* ULift.{y} K := MulEquiv.ulift.symm.toMonoidHom
  let down : ULift.{y} K →* K := MulEquiv.ulift.toMonoidHom
  let f_up : ∀ α, G α →* ULift.{y} K := fun α ↦ up.comp (f α)
  obtain ⟨h_up, h_up_spec, h_up_unique⟩ := h_extension (ULift.{y} K) f_up
  let h : H →* K := down.comp h_up
  have h_spec : ∀ α, h.comp (i α) = f α := by
    intro α
    apply MonoidHom.ext
    intro a
    -- Apply the lowering map to the lifted extension equation on each factor.
    have h_up_at := DFunLike.congr_fun (h_up_spec α) a
    simpa only [h, f_up, up, down, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using congrArg down h_up_at
  refine ⟨h, h_spec, ?_⟩
  intro k hk
  have k_up_spec : ∀ α, (up.comp k).comp (i α) = f_up α := by
    intro α
    apply MonoidHom.ext
    intro a
    -- Lifting preserves the competing map's equations on the factors.
    have hk_at := DFunLike.congr_fun (hk α) a
    simpa only [f_up, up, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
      congrArg up hk_at
  have k_up_eq : up.comp k = h_up := h_up_unique (up.comp k) k_up_spec
  apply MonoidHom.ext
  intro z
  -- Lower the unique lifted equality to recover equality of the original homomorphisms.
  have hz := DFunLike.congr_fun k_up_eq z
  simpa only [h, up, down, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using congrArg down hz

/-- Helper for Theorem 68.4: mutually compatible extensions in both directions compose to
the identity on the source group. -/
private lemma comp_eq_id_of_extension_specs
    {ι : Type u} (G : ι → Type v) {H : Type w} {H' : Type x}
    [∀ α, Group (G α)] [Group H] [Group H']
    (i : ∀ α, G α →* H)
    (h_extension : HasFreeProductExtension.{u, v, w, max w x} i)
    (i' : ∀ α, G α →* H') (f : H →* H') (g : H' →* H)
    (hf : ∀ α, f.comp (i α) = i' α) (hg : ∀ α, g.comp (i' α) = i α) :
    g.comp f = MonoidHom.id H := by
  obtain ⟨h, -, h_unique⟩ :=
    existsUnique_extension_of_universeLift.{u, v, w, w, x} G i h_extension i
  have h_comp_spec : ∀ α, (g.comp f).comp (i α) = i α := by
    intro α
    rw [MonoidHom.comp_assoc, hf α, hg α]
  have h_id_spec : ∀ α, (MonoidHom.id H).comp (i α) = i α := by
    intro α
    rw [MonoidHom.id_comp]
  -- Both the composite and the identity extend the original factor maps, so uniqueness applies.
  calc
    g.comp f = h := h_unique (g.comp f) h_comp_spec
    _ = MonoidHom.id H := (h_unique (MonoidHom.id H) h_id_spec).symm

/-- Theorem 68.4 (Uniqueness of free products). Two group realizations of the same indexed
family with the free-product extension property are related by a unique multiplicative
equivalence commuting with every inclusion. The monomorphism and generation conditions in the
textbook formulation follow from this extension property. -/
theorem uniqueMulEquiv {ι : Type u} (G : ι → Type v) {H : Type w} {H' : Type x}
    [∀ α, Group (G α)] [Group H] [Group H']
    (i : ∀ α, G α →* H) (i' : ∀ α, G α →* H')
    (h_extension : HasFreeProductExtension.{u, v, w, max w x} i)
    (h_extension' : HasFreeProductExtension.{u, v, x, max w x} i') :
    ∃! e : H ≃* H', ∀ α, e.toMonoidHom.comp (i α) = i' α := by
  obtain ⟨f, hf, hf_unique⟩ :=
    existsUnique_extension_of_universeLift.{u, v, w, x, w} G i h_extension i'
  obtain ⟨g, hg, -⟩ :=
    existsUnique_extension_of_universeLift.{u, v, x, w, x} G i' h_extension' i
  -- The factor equations determine both composites as the corresponding identity maps.
  have hgf : g.comp f = MonoidHom.id H :=
    comp_eq_id_of_extension_specs G i h_extension i' f g hf hg
  have hfg : f.comp g = MonoidHom.id H' :=
    comp_eq_id_of_extension_specs G i' h_extension' i g f hg hf
  let e : H ≃* H' := MonoidHom.toMulEquiv f g hgf hfg
  have he_forward : e.toMonoidHom = f := by
    rfl
  have he_spec : ∀ α, e.toMonoidHom.comp (i α) = i' α := by
    intro α
    rw [he_forward, hf α]
  refine ⟨e, he_spec, ?_⟩
  intro e' he'
  -- Any competing equivalence has the uniquely determined forward homomorphism.
  have he'f : e'.toMonoidHom = f := hf_unique e'.toMonoidHom he'
  apply MulEquiv.ext
  intro z
  calc
    e' z = e'.toMonoidHom z := rfl
    _ = f z := DFunLike.congr_fun he'f z
    _ = e.toMonoidHom z := (DFunLike.congr_fun he_forward z).symm
    _ = e z := rfl

end MonoidHom.HasFreeProductExtension
