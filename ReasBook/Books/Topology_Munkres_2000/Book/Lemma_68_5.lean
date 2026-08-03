module

public import Topology_Munkres_2000.Book.Lemma_68_3.Extension
public import Topology_Munkres_2000.Book.Theorem_68_4
import all Topology_Munkres_2000.Book.Lemma_68_1.Extension
import Mathlib.Algebra.Group.ULift

public section

universe u v w

/-- Helper for Lemma 68.5: reduced words with the same underlying list are equal. -/
private lemma reducedWord_eq_of_toList_eq
    {ι : Type u} {A : Type v} [Group A] {K : ι → Subgroup A}
    {r s : Subgroup.ReducedWord K} (h : r.toList = s.toList) : r = s := by
  -- After fixing the list, all remaining fields in the nested word structures are proofs.
  cases r with
  | mk toWord₁ neOne₁ chain₁ =>
      cases s with
      | mk toWord₂ neOne₂ chain₂ =>
          cases toWord₁ with
          | mk list₁ mem₁ =>
              cases toWord₂ with
              | mk list₂ mem₂ =>
                  dsimp only at h
                  subst list₂
                  rfl

namespace Subgroup.IsFreeProduct

/-- Helper for Lemma 68.5: a multiplicative equivalence transports an internal free-product
decomposition to the images of its factors. -/
lemma mapMulEquiv {ι : Type u} {A : Type v} {B : Type w} [Group A] [Group B]
    {K : ι → Subgroup A} (h_free : Subgroup.IsFreeProduct K) (e : A ≃* B) :
    Subgroup.IsFreeProduct (fun α ↦ (K α).map e.toMonoidHom) := by
  rw [Subgroup.isFreeProduct_iff] at h_free ⊢
  constructor
  · intro α β hαβ
    rw [Subgroup.disjoint_def]
    intro y hyα hyβ
    -- Pull an element in both mapped factors back to the disjoint source factors.
    have hyα' : e.symm y ∈ K α := Subgroup.mem_map_equiv.mp hyα
    have hyβ' : e.symm y ∈ K β := Subgroup.mem_map_equiv.mp hyβ
    have hy_one : e.symm y = 1 :=
      Subgroup.disjoint_def.mp (h_free.1 hαβ) hyα' hyβ'
    calc
      y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e 1 := congrArg e hy_one
      _ = 1 := e.map_one
  · intro y
    obtain ⟨r, hr_prod, hr_unique⟩ := h_free.2 (e.symm y)
    -- Map the source normal form letterwise and record each reducedness condition separately.
    have h_map_mem : ∀ z ∈ r.toList.map e,
        ∃ α, z ∈ (K α).map e.toMonoidHom := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      obtain ⟨α, hxα⟩ := r.toWord.mem_subgroup x hx
      exact ⟨α, Subgroup.mem_map_of_mem e.toMonoidHom hxα⟩
    have h_map_ne_one : ∀ z ∈ r.toList.map e, z ≠ 1 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact e.map_ne_one_iff.mpr (r.ne_one x hx)
    have h_map_chain : (r.toList.map e).IsChain
        (fun x z ↦ ∀ α, ¬ (x ∈ (K α).map e.toMonoidHom ∧
          z ∈ (K α).map e.toMonoidHom)) := by
      rw [List.isChain_map]
      refine r.chain_separated.imp (fun x z hxz ↦ ?_)
      intro α hmem
      apply hxz α
      exact ⟨(Subgroup.mem_map_iff_mem e.injective).mp hmem.1,
        (Subgroup.mem_map_iff_mem e.injective).mp hmem.2⟩
    let mapped := Subgroup.ReducedWord.ofList
      (fun α ↦ (K α).map e.toMonoidHom) (r.toList.map e)
      h_map_mem h_map_ne_one h_map_chain
    have h_mapped_list : mapped.toList = r.toList.map e :=
      Subgroup.ReducedWord.toList_ofList
        (fun α ↦ (K α).map e.toMonoidHom) (r.toList.map e)
        h_map_mem h_map_ne_one h_map_chain
    have h_mapped_prod : mapped.prod = y := by
      calc
        mapped.prod = mapped.toList.prod :=
          Subgroup.ReducedWord.prod_def _ mapped
        _ = (r.toList.map e).prod := congrArg List.prod h_mapped_list
        _ = e r.toList.prod := (map_list_prod e r.toList).symm
        _ = e r.prod := congrArg e (Subgroup.ReducedWord.prod_def K r).symm
        _ = e (e.symm y) := congrArg e hr_prod
        _ = y := e.apply_symm_apply y
    refine ⟨mapped, h_mapped_prod, ?_⟩
    intro other hother_prod
    -- Pull any competing mapped word back to the source decomposition.
    have h_back_mem : ∀ z ∈ other.toList.map e.symm, ∃ α, z ∈ K α := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      obtain ⟨α, hxα⟩ := other.toWord.mem_subgroup x hx
      exact ⟨α, Subgroup.mem_map_equiv.mp hxα⟩
    have h_back_ne_one : ∀ z ∈ other.toList.map e.symm, z ≠ 1 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact e.symm.map_ne_one_iff.mpr (other.ne_one x hx)
    have h_back_chain : (other.toList.map e.symm).IsChain
        (fun x z ↦ ∀ α, ¬ (x ∈ K α ∧ z ∈ K α)) := by
      rw [List.isChain_map]
      refine other.chain_separated.imp (fun x z hxz ↦ ?_)
      intro α hmem
      apply hxz α
      exact ⟨Subgroup.mem_map_equiv.mpr hmem.1,
        Subgroup.mem_map_equiv.mpr hmem.2⟩
    let back := Subgroup.ReducedWord.ofList K (other.toList.map e.symm)
      h_back_mem h_back_ne_one h_back_chain
    have h_back_list : back.toList = other.toList.map e.symm :=
      Subgroup.ReducedWord.toList_ofList K (other.toList.map e.symm)
        h_back_mem h_back_ne_one h_back_chain
    have h_back_prod : back.prod = e.symm y := by
      calc
        back.prod = back.toList.prod := Subgroup.ReducedWord.prod_def K back
        _ = (other.toList.map e.symm).prod := congrArg List.prod h_back_list
        _ = e.symm other.toList.prod := (map_list_prod e.symm other.toList).symm
        _ = e.symm other.prod :=
          congrArg e.symm (Subgroup.ReducedWord.prod_def _ other).symm
        _ = e.symm y := congrArg e.symm hother_prod
    have h_back_eq : back = r := hr_unique back h_back_prod
    have h_back_eq_list := congrArg (fun q : Subgroup.ReducedWord K ↦ q.toList) h_back_eq
    have h_other_list : other.toList = mapped.toList := by
      -- Mapping the source-list equality forward cancels the inverse equivalence letterwise.
      have h_forward_list := congrArg (List.map e) h_back_eq_list
      simpa only [back, mapped, Subgroup.ReducedWord.toList_ofList, List.map_map,
        Function.comp_def, e.apply_symm_apply, List.map_id'] using h_forward_list
    exact reducedWord_eq_of_toList_eq h_other_list

end Subgroup.IsFreeProduct

namespace MonoidHom

/-- Helper for Lemma 68.5: the free-product extension property makes every factor map
injective. -/
lemma HasFreeProductExtension.injective {ι : Type u} {G : ι → Type v} {H : Type w}
    [∀ α, Group (G α)] [Group H] {i : ∀ α, G α →* H}
    (h_extension : HasFreeProductExtension.{u, v, w, max (max u v) w} i) :
    ∀ α, Function.Injective (i α) := by
  classical
  unfold MonoidHom.HasFreeProductExtension at h_extension
  intro β
  obtain ⟨r, hr, -⟩ :=
    h_extension (ULift.{max (max u v) w, v} (G β))
      (Pi.mulSingle β
        (MulEquiv.ulift.symm.toMonoidHom :
          G β →* ULift.{max (max u v) w, v} (G β)))
  -- The extension of the identity/trivial family is a left inverse to the chosen factor map.
  have h_left_inverse : Function.LeftInverse
      (fun y ↦ (MulEquiv.ulift :
        ULift.{max (max u v) w, v} (G β) ≃* G β) (r y)) (i β) := by
    intro x
    have hr_at := DFunLike.congr_fun (hr β) x
    simpa only [MonoidHom.comp_apply, Pi.mulSingle_eq_same, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using congrArg
        (MulEquiv.ulift : ULift.{max (max u v) w, v} (G β) ≃* G β) hr_at
  exact h_left_inverse.injective

/-- Lemma 68.5. The free-product extension property exhibits the ambient group as the external
free product of the factors. -/
theorem HasFreeProductExtension.isExternalFreeProduct {ι : Type u} {G : ι → Type v} {H : Type w}
    [∀ α, Group (G α)] [Group H] {i : ∀ α, G α →* H}
    (h_extension : HasFreeProductExtension.{u, v, w, max (max u v) w} i) :
    IsExternalFreeProduct i := by
  let canonical : ∀ α, G α →* Monoid.CoprodI G := fun _ ↦ Monoid.CoprodI.of
  have h_canonical : IsExternalFreeProduct canonical :=
    Monoid.CoprodI.canonicalIsExternalFreeProduct G
  have h_canonical_extension :
      HasFreeProductExtension.{u, v, max u v, max (max u v) w} canonical :=
    h_canonical.hasExtension
  -- Uniqueness identifies the given realization with the canonical indexed coproduct.
  obtain ⟨e, he, -⟩ := HasFreeProductExtension.uniqueMulEquiv G i canonical
    h_extension h_canonical_extension
  have h_inverse (α : ι) :
      e.symm.toMonoidHom.comp (Monoid.CoprodI.of : G α →* Monoid.CoprodI G) = i α := by
    apply MonoidHom.ext
    intro x
    have he_at := DFunLike.congr_fun (he α) x
    have h_inverse_at := congrArg e.symm he_at
    simpa only [canonical, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using h_inverse_at.symm
  refine ⟨h_extension.injective, ?_⟩
  -- Transport the canonical internal decomposition back and identify its mapped ranges.
  have h_mapped := h_canonical.isFreeProduct.mapMulEquiv e.symm
  simpa only [canonical, ← MonoidHom.range_comp, h_inverse] using h_mapped

end MonoidHom
