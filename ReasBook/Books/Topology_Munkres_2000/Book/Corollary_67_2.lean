module

public import Topology_Munkres_2000.Book.Lemma_67_1
public import Mathlib.LinearAlgebra.Projection

public section

universe u v w

namespace DirectSum.IsInternal

/-- Helper for Corollary 67.2: the summands of an internal direct sum of additive
subgroups generate the ambient additive group. -/
lemma addSubgroup_iSup_eq_top {ι : Type*} {M : Type*} [AddCommGroup M]
    [DecidableEq ι] {A : ι → AddSubgroup M} (h : DirectSum.IsInternal A) :
    (⨆ i, A i) = ⊤ := by
  -- Transport the family through the order isomorphism with ℤ-submodules.
  apply AddSubgroup.toIntSubmodule.injective
  rw [OrderIso.map_iSup]
  exact h.submodule_iSup_eq_top

/-- Helper for Corollary 67.2: mapping the summands of an internal direct sum
through the containing subgroup's subtype generates that containing subgroup. -/
lemma addSubgroup_iSup_map_subtype {ι : Type*} {M : Type*} [AddCommGroup M]
    [DecidableEq ι] (P : AddSubgroup M) {A : ι → AddSubgroup P}
    (h : DirectSum.IsInternal A) :
    (⨆ i, (A i).map P.subtype) = P := by
  -- Mapping commutes with the supremum, whose source is top by internalness.
  rw [← AddSubgroup.map_iSup, h.addSubgroup_iSup_eq_top,
    ← AddMonoidHom.range_eq_map]
  exact AddSubgroup.range_subtype P

end DirectSum.IsInternal

namespace AddMonoidHom

/-- Helper for Corollary 67.2: additive homomorphisms on complementary additive
subgroups extend simultaneously to the ambient additive group. -/
lemma exists_extension_of_isCompl {M : Type*} {N : Type*}
    [AddCommGroup M] [AddCommGroup N] (P Q : AddSubgroup M) (hPQ : IsCompl P Q)
    (f : P →+ N) (g : Q →+ N) :
    ∃ h : M →+ N, h.comp P.subtype = f ∧ h.comp Q.subtype = g := by
  let hLinear : M →ₗ[ℤ] N :=
    LinearMap.ofIsCompl (AddSubgroup.toIntSubmodule.isCompl hPQ)
      f.toIntLinearMap g.toIntLinearMap
  refine ⟨hLinear.toAddMonoidHom, ?_, ?_⟩
  · -- The linear extension restricts to the prescribed map on `P`.
    ext x
    exact LinearMap.ofIsCompl_apply_left
      (AddSubgroup.toIntSubmodule.isCompl hPQ) x
  · -- Its restriction to the other complementary subgroup is prescribed as well.
    ext x
    exact LinearMap.ofIsCompl_apply_right
      (AddSubgroup.toIntSubmodule.isCompl hPQ) x

end AddMonoidHom

/-- Corollary 67.2. If two complementary subgroups are each internal direct sums,
then their summands, mapped into the ambient group and indexed by a tagged disjoint union,
form an internal direct sum of the ambient group. -/
theorem DirectSum.IsInternal.sum_of_isCompl
    {G : Type u} [AddCommGroup G] {J : Type v} {K : Type w}
    (G₁ G₂ : AddSubgroup G) (HJ : J → AddSubgroup G₁) (HK : K → AddSubgroup G₂)
    [DecidableEq J] [DecidableEq K] (h_outer : IsCompl G₁ G₂)
    (hJ : DirectSum.IsInternal HJ) (hK : DirectSum.IsInternal HK) :
    DirectSum.IsInternal
      (Sum.elim (fun j ↦ (HJ j).map G₁.subtype) (fun k ↦ (HK k).map G₂.subtype)) := by
  classical
  -- The two mapped inner families generate their complementary ambient subgroups.
  have h_generate :
      (⨆ γ, Sum.elim (fun j ↦ (HJ j).map G₁.subtype)
        (fun k ↦ (HK k).map G₂.subtype) γ) = ⊤ := by
    calc
      (⨆ γ, Sum.elim (fun j ↦ (HJ j).map G₁.subtype)
          (fun k ↦ (HK k).map G₂.subtype) γ) =
          (⨆ j, (HJ j).map G₁.subtype) ⊔
            (⨆ k, (HK k).map G₂.subtype) :=
        iSup_sum
      _ = G₁ ⊔ G₂ := congrArg₂ (· ⊔ ·)
        (hJ.addSubgroup_iSup_map_subtype G₁)
        (hK.addSubgroup_iSup_map_subtype G₂)
      _ = ⊤ := h_outer.sup_eq_top
  -- It remains to implement the source proof's extension property.
  refine DirectSum.isInternal_of_addHom_extension h_generate ?_
  intro H _ hγ
  let eJ (j : J) : HJ j ≃+ (HJ j).map G₁.subtype :=
    AddSubgroup.equivMapOfInjective (HJ j) G₁.subtype G₁.subtype_injective
  let eK (k : K) : HK k ≃+ (HK k).map G₂.subtype :=
    AddSubgroup.equivMapOfInjective (HK k) G₂.subtype G₂.subtype_injective
  -- First extend the prescribed maps independently over `G₁` and `G₂`.
  obtain ⟨fJ, hfJ, _⟩ := hJ.existsUnique_addHom
    (fun j ↦ (hγ (Sum.inl j)).comp (eJ j).toAddMonoidHom)
  obtain ⟨fK, hfK, _⟩ := hK.existsUnique_addHom
    (fun k ↦ (hγ (Sum.inr k)).comp (eK k).toAddMonoidHom)
  obtain ⟨h, hG₁, hG₂⟩ :=
    AddMonoidHom.exists_extension_of_isCompl G₁ G₂ h_outer fJ fK
  refine ⟨h, ?_⟩
  intro γ
  cases γ with
  | inl j =>
      -- Pull an element of the mapped summand back through its canonical equivalence.
      apply AddMonoidHom.ext
      intro x
      obtain ⟨y, rfl⟩ := (eJ j).surjective x
      simp only [AddMonoidHom.comp_apply]
      calc
        h ((eJ j y : (HJ j).map G₁.subtype) : G) =
            h (G₁.subtype ((HJ j).subtype y)) :=
          congrArg h (AddSubgroup.coe_equivMapOfInjective_apply
            (HJ j) G₁.subtype G₁.subtype_injective y)
        _ = fJ ((HJ j).subtype y) := DFunLike.congr_fun hG₁ ((HJ j).subtype y)
        _ = hγ (Sum.inl j) (eJ j y) := DFunLike.congr_fun (hfJ j) y
  | inr k =>
      -- The second summand is handled by the same image-equivalence calculation.
      apply AddMonoidHom.ext
      intro x
      obtain ⟨y, rfl⟩ := (eK k).surjective x
      simp only [AddMonoidHom.comp_apply]
      calc
        h ((eK k y : (HK k).map G₂.subtype) : G) =
            h (G₂.subtype ((HK k).subtype y)) :=
          congrArg h (AddSubgroup.coe_equivMapOfInjective_apply
            (HK k) G₂.subtype G₂.subtype_injective y)
        _ = fK ((HK k).subtype y) := DFunLike.congr_fun hG₂ ((HK k).subtype y)
        _ = hγ (Sum.inr k) (eK k y) := DFunLike.congr_fun (hfK k) y

end
