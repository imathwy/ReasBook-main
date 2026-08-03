module

public import Mathlib.Algebra.DirectSum.Module

public section

universe u v w

namespace DirectSum

variable {J : Type v} {G : Type u} [AddCommGroup G]
variable {Gα : J → AddSubgroup G}

/-- Helper for Lemma 67.1: surjectivity of the canonical summation map makes
additive homomorphisms from the ambient group determined by their restrictions. -/
lemma addHom_ext_of_surjective_coeAddMonoidHom [DecidableEq J]
    {H : Type w} [AddCommGroup H]
    (h_surjective : Function.Surjective (DirectSum.coeAddMonoidHom Gα))
    {f g : G →+ H}
    (h_restrict : ∀ α, f.comp (Gα α).subtype = g.comp (Gα α).subtype) :
    f = g := by
  -- Pull an ambient element back to the external direct sum.
  ext x
  obtain ⟨y, rfl⟩ := h_surjective x
  -- Equality on every summand gives equality on the whole external sum.
  have h_comp :
      f.comp (DirectSum.coeAddMonoidHom Gα) =
        g.comp (DirectSum.coeAddMonoidHom Gα) := by
    refine DirectSum.addHom_ext' fun α ↦ ?_
    apply AddMonoidHom.ext
    intro z
    simp only [AddMonoidHom.comp_apply]
    calc
      f (DirectSum.coeAddMonoidHom Gα
          (DirectSum.of (fun β ↦ Gα β) α z)) =
          f ((Gα α).subtype z) :=
        congrArg f (DirectSum.coeAddMonoidHom_of Gα α z)
      _ = g ((Gα α).subtype z) := DFunLike.congr_fun (h_restrict α) z
      _ = g (DirectSum.coeAddMonoidHom Gα
          (DirectSum.of (fun β ↦ Gα β) α z)) :=
        congrArg g (DirectSum.coeAddMonoidHom_of Gα α z).symm
  exact DFunLike.congr_fun h_comp y

/-- Helper for Lemma 67.1: a family of additive subgroups generating the ambient
group makes its canonical direct-sum summation homomorphism surjective. -/
lemma coeAddMonoidHom_surjective_of_iSup_eq_top [DecidableEq J]
    (h_generate : (⨆ α, Gα α) = ⊤) :
    Function.Surjective (DirectSum.coeAddMonoidHom Gα) := by
  -- It suffices to show that the range contains every generating subgroup.
  apply AddMonoidHom.range_eq_top.mp
  apply top_unique
  rw [← h_generate]
  refine iSup_le fun α ↦ ?_
  intro x hx
  -- A member of one subgroup is the image of the corresponding external generator.
  refine ⟨DirectSum.of (fun β ↦ Gα β) α ⟨x, hx⟩, ?_⟩
  exact DirectSum.coeAddMonoidHom_of Gα α ⟨x, hx⟩

/-- Helper for Lemma 67.1: extending the external summand inclusions produces a
left inverse to the canonical summation homomorphism, hence makes it injective. -/
lemma coeAddMonoidHom_injective_of_addHom_extension [DecidableEq J]
    (h_extension : ∀ {H : Type (max u v)} [AddCommGroup H]
      (hα : ∀ α, Gα α →+ H),
      ∃ h : G →+ H, ∀ α, h.comp (Gα α).subtype = hα α) :
    Function.Injective (DirectSum.coeAddMonoidHom Gα) := by
  -- Extend all canonical external inclusions simultaneously.
  obtain ⟨p, hp⟩ := h_extension (fun α ↦ DirectSum.of (fun β ↦ Gα β) α)
  -- On generators, the resulting map is a left inverse to summation.
  have h_left :
      p.comp (DirectSum.coeAddMonoidHom Gα) =
        AddMonoidHom.id (⨁ α, Gα α) := by
    refine DirectSum.addHom_ext' fun α ↦ ?_
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    calc
      p (DirectSum.coeAddMonoidHom Gα
          (DirectSum.of (fun β ↦ Gα β) α x)) =
          p ((Gα α).subtype x) :=
        congrArg p (DirectSum.coeAddMonoidHom_of Gα α x)
      _ = DirectSum.of (fun β ↦ Gα β) α x := DFunLike.congr_fun (hp α) x
  -- A map admitting a left inverse is injective.
  apply Function.LeftInverse.injective (g := p)
  intro x
  exact DFunLike.congr_fun h_left x

/-- Lemma 67.1 (forward direction). Every family of additive homomorphisms from the
summands of an internal direct sum extends uniquely to the ambient group. -/
theorem IsInternal.existsUnique_addHom [DecidableEq J] (h_internal : IsInternal Gα)
    {H : Type w} [AddCommGroup H]
    (hα : ∀ α, Gα α →+ H) :
    ∃! h : G →+ H, ∀ α, h.comp (Gα α).subtype = hα α := by
  classical
  -- Internalness identifies the external direct sum with the ambient group.
  let e : (⨁ α, Gα α) ≃+ G :=
    AddEquiv.ofBijective (DirectSum.coeAddMonoidHom Gα) h_internal
  let h : G →+ H :=
    (DirectSum.toAddMonoid hα).comp e.symm.toAddMonoidHom
  -- The inverse equivalence sends a subgroup element to its external generator.
  have h_inverse_of (α : J) (x : Gα α) :
      e.symm.toAddMonoidHom ((Gα α).subtype x) =
        DirectSum.of (fun β ↦ Gα β) α x := by
    calc
      e.symm.toAddMonoidHom ((Gα α).subtype x) =
          e.symm ((Gα α).subtype x) := by
        rw [AddEquiv.coe_toAddMonoidHom]
      _ = e.symm (e (DirectSum.of (fun β ↦ Gα β) α x)) :=
        congrArg e.symm (DirectSum.coeAddMonoidHom_of Gα α x).symm
      _ = DirectSum.of (fun β ↦ Gα β) α x :=
        e.symm_apply_apply (DirectSum.of (fun β ↦ Gα β) α x)
  -- Therefore the transported universal map has every prescribed restriction.
  have h_restrict : ∀ α, h.comp (Gα α).subtype = hα α := by
    intro α
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, h]
    rw [h_inverse_of, DirectSum.toAddMonoid_of]
  refine ⟨h, h_restrict, ?_⟩
  intro g hg
  -- Surjectivity lets equality on all summands determine the ambient homomorphism.
  apply addHom_ext_of_surjective_coeAddMonoidHom h_internal.2
  intro α
  exact (hg α).trans (h_restrict α).symm

/-- Companion for Lemma 67.1: if the subgroups `Gα α` generate `G` and every family of
additive homomorphisms from them extends to `G`, then they form an internal direct sum. -/
theorem isInternal_of_addHom_extension [DecidableEq J]
    (h_generate : (⨆ α, Gα α) = ⊤)
    (h_extension : ∀ {H : Type (max u v)} [AddCommGroup H] (hα : ∀ α, Gα α →+ H),
      ∃ h : G →+ H, ∀ α, h.comp (Gα α).subtype = hα α) :
    IsInternal Gα := by
  -- Extension gives injectivity, while generation gives surjectivity.
  exact ⟨coeAddMonoidHom_injective_of_addHom_extension h_extension,
    coeAddMonoidHom_surjective_of_iSup_eq_top h_generate⟩

end DirectSum

end
