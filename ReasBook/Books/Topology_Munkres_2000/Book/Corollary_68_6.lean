module

public import Topology_Munkres_2000.Book.Lemma_68_5
import all Topology_Munkres_2000.Book.Lemma_68_1.Extension

public section

open scoped Subgroup.FreeProduct

namespace Subgroup.IsFreeProduct

universe u v w x

/-- Helper for Corollary 68.6: the free-product extension predicate is equivalent to its
pointwise existence-and-uniqueness formulation. -/
private lemma hasFreeProductExtension_iff {I : Type u} {A : I → Type v} {G : Type w}
    [∀ i, Group (A i)] [Group G] (i : ∀ a, A a →* G) :
    MonoidHom.HasFreeProductExtension.{u, v, w, x} i ↔
      ∀ (L : Type x) [Group L] (f : ∀ a, A a →* L),
        ∃! h : G →* L, ∀ a, h.comp (i a) = f a := by
  -- This exposes the defining universal property once for all subsequent applications.
  rfl

/-- Helper for Corollary 68.6: homomorphisms on the two factors of a binary internal free
product extend uniquely to the ambient group. -/
private lemma existsUniqueBinaryExtension {G : Type u} [Group G]
    (G₁ G₂ : Subgroup G)
    (h_outer : G = *ᵢ (fun b : Bool ↦ if b then G₂ else G₁))
    {L : Type x} [Group L] (f₁ : G₁ →* L) (f₂ : G₂ →* L) :
    ∃! f : G →* L,
      f.comp G₁.subtype = f₁ ∧ f.comp G₂.subtype = f₂ := by
  -- Apply the indexed extension property to the Bool family, with one prescribed map per factor.
  have h_extension :=
    (hasFreeProductExtension_iff
      (fun b : Bool ↦ (if b then G₂ else G₁).subtype)).mp
        (Subgroup.IsFreeProduct.hasExtension.{u, 0, x} h_outer)
  obtain ⟨f, hf, h_unique⟩ := h_extension L (fun
      | false => f₁
      | true => f₂)
  refine ⟨f, ⟨hf false, hf true⟩, ?_⟩
  intro q hq
  -- The two restriction equations are exactly the Bool-indexed uniqueness hypothesis.
  apply h_unique q
  intro b
  cases b with
  | false => exact hq.1
  | true => exact hq.2

/-- Helper for Corollary 68.6: the carrier of a tagged inner factor is the corresponding
subgroup carrier from `HJ` or `HK`. -/
private abbrev mappedSumFactor {G : Type u} [Group G]
    {J : Type v} {K : Type w} {G₁ G₂ : Subgroup G}
    (HJ : J → Subgroup G₁) (HK : K → Subgroup G₂) (gamma : Sum J K) : Type u :=
  match gamma with
  | Sum.inl j => HJ j
  | Sum.inr k => HK k

/-- Helper for Corollary 68.6: each carrier in the tagged family inherits its canonical group
structure from the corresponding subgroup. -/
private instance mappedSumFactorGroup {G : Type u} [Group G]
    {J : Type v} {K : Type w} {G₁ G₂ : Subgroup G}
    (HJ : J → Subgroup G₁) (HK : K → Subgroup G₂) (gamma : Sum J K) :
    Group (mappedSumFactor HJ HK gamma) :=
  match gamma with
  | Sum.inl _ => inferInstance
  | Sum.inr _ => inferInstance

/-- Helper for Corollary 68.6: the tagged inner factors include into `G` by first including
into `G₁` or `G₂` and then into the ambient group. -/
private def mappedSumInclusion {G : Type u} [Group G]
    {J : Type v} {K : Type w} (G₁ G₂ : Subgroup G)
    (HJ : J → Subgroup G₁) (HK : K → Subgroup G₂) :
    ∀ γ : Sum J K, mappedSumFactor HJ HK γ →* G :=
  fun
  | Sum.inl j => G₁.subtype.comp (HJ j).subtype
  | Sum.inr k => G₂.subtype.comp (HK k).subtype

/-- Helper for Corollary 68.6: composing the extension properties of the inner decompositions
and the outer binary decomposition gives the extension property for the tagged family. -/
private lemma hasExtensionForMappedSum {G : Type u} [Group G]
    {J : Type v} {K : Type w} (G₁ G₂ : Subgroup G)
    (HJ : J → Subgroup G₁) (HK : K → Subgroup G₂)
    (h_outer : G = *ᵢ (fun b : Bool ↦ if b then G₂ else G₁))
    (hJ : G₁ = *ᵢ HJ) (hK : G₂ = *ᵢ HK) :
    MonoidHom.HasFreeProductExtension.{max v w, u, u, x}
      (mappedSumInclusion G₁ G₂ HJ HK) := by
  apply (hasFreeProductExtension_iff (mappedSumInclusion G₁ G₂ HJ HK)).mpr
  intro L _ f
  -- First extend independently across each inner free product.
  have hJ_extension :=
    (hasFreeProductExtension_iff (fun j ↦ (HJ j).subtype)).mp
      (Subgroup.IsFreeProduct.hasExtension.{u, v, x} hJ)
  obtain ⟨fJ, hfJ, h_uniqueJ⟩ :=
    hJ_extension L (fun j ↦ f (Sum.inl j))
  have hK_extension :=
    (hasFreeProductExtension_iff (fun k ↦ (HK k).subtype)).mp
      (Subgroup.IsFreeProduct.hasExtension.{u, w, x} hK)
  obtain ⟨fK, hfK, h_uniqueK⟩ :=
    hK_extension L (fun k ↦ f (Sum.inr k))
  -- Then extend the resulting pair of maps across the outer free product.
  obtain ⟨h, h_restrict, h_unique_outer⟩ :=
    existsUniqueBinaryExtension G₁ G₂ h_outer fJ fK
  refine ⟨h, ?_, ?_⟩
  · intro γ
    cases γ with
    | inl j =>
        calc
          h.comp (G₁.subtype.comp (HJ j).subtype) =
              (h.comp G₁.subtype).comp (HJ j).subtype :=
            (MonoidHom.comp_assoc (HJ j).subtype G₁.subtype h).symm
          _ = fJ.comp (HJ j).subtype :=
            congrArg (fun q : G₁ →* L ↦ q.comp (HJ j).subtype) h_restrict.1
          _ = f (Sum.inl j) := hfJ j
    | inr k =>
        calc
          h.comp (G₂.subtype.comp (HK k).subtype) =
              (h.comp G₂.subtype).comp (HK k).subtype :=
            (MonoidHom.comp_assoc (HK k).subtype G₂.subtype h).symm
          _ = fK.comp (HK k).subtype :=
            congrArg (fun q : G₂ →* L ↦ q.comp (HK k).subtype) h_restrict.2
          _ = f (Sum.inr k) := hfK k
  · intro q hq
    -- Inner uniqueness identifies both restrictions of `q` with the maps already constructed.
    have hqJ_spec : ∀ j, (q.comp G₁.subtype).comp (HJ j).subtype = f (Sum.inl j) := by
      intro j
      rw [MonoidHom.comp_assoc]
      exact hq (Sum.inl j)
    have hqK_spec : ∀ k, (q.comp G₂.subtype).comp (HK k).subtype = f (Sum.inr k) := by
      intro k
      rw [MonoidHom.comp_assoc]
      exact hq (Sum.inr k)
    have hqJ : q.comp G₁.subtype = fJ := h_uniqueJ (q.comp G₁.subtype) hqJ_spec
    have hqK : q.comp G₂.subtype = fK := h_uniqueK (q.comp G₂.subtype) hqK_spec
    -- Outer uniqueness now identifies the ambient homomorphism itself.
    exact h_unique_outer q ⟨hqJ, hqK⟩

/-- Helper for Corollary 68.6: the ranges of the composite subgroup inclusions are exactly the
inner subgroups mapped into the ambient group. -/
private lemma rangeFamilyForMappedSum {G : Type u} [Group G]
    {J : Type v} {K : Type w} (G₁ G₂ : Subgroup G)
    (HJ : J → Subgroup G₁) (HK : K → Subgroup G₂) :
    (fun γ ↦ (mappedSumInclusion G₁ G₂ HJ HK γ).range) =
        Sum.elim (fun j ↦ (HJ j).map G₁.subtype)
          (fun k ↦ (HK k).map G₂.subtype) := by
  funext γ
  cases γ with
  | inl j =>
      -- A composite range is the map of the inner subtype range.
      simp only [mappedSumInclusion, MonoidHom.range_comp, Subgroup.range_subtype,
        Sum.elim_inl]
  | inr k =>
      simp only [mappedSumInclusion, MonoidHom.range_comp, Subgroup.range_subtype,
        Sum.elim_inr]

/-- Corollary 68.6. If two subgroups freely generate an ambient group and each is itself a free
product of an indexed family, then the mapped families together freely generate the ambient
group, indexed by their tagged disjoint union. -/
theorem sum {G : Type u} [Group G] {J : Type v} {K : Type w}
    (G₁ G₂ : Subgroup G) (HJ : J → Subgroup G₁) (HK : K → Subgroup G₂)
    (h_outer : G = *ᵢ (fun b : Bool ↦ if b then G₂ else G₁))
    (hJ : G₁ = *ᵢ HJ) (hK : G₂ = *ᵢ HK) :
    G = *ᵢ
      (Sum.elim (fun j ↦ (HJ j).map G₁.subtype) (fun k ↦ (HK k).map G₂.subtype)) := by
  -- The composed inclusions satisfy the free-product extension property.
  have h_external : MonoidHom.IsExternalFreeProduct
      (mappedSumInclusion G₁ G₂ HJ HK) :=
    (hasExtensionForMappedSum G₁ G₂ HJ HK h_outer hJ hK).isExternalFreeProduct
  -- Normalize the ranges in the resulting internal decomposition to the target mapped family.
  rw [← rangeFamilyForMappedSum G₁ G₂ HJ HK]
  exact h_external.isFreeProduct

end Subgroup.IsFreeProduct
