module

public import Topology_Munkres_2000.Book.Definition_68_2

public section

namespace Subgroup

universe u v

variable {G : Type u} {ι : Type v} [Group G]

/-- A family of subgroups is an internal free-product decomposition when distinct subgroups are
disjoint and evaluation gives a bijection from its reduced words to the ambient group. -/
structure IsFreeProduct (H : ι → Subgroup G) : Prop where
  /-- Distinct subgroups in an internal free-product decomposition are disjoint. -/
  pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j))
  /-- Every ambient group element has a unique reduced-word representation. -/
  prod_bijective : Function.Bijective (fun w : ReducedWord H ↦ w.prod)

namespace FreeProduct

/- The source notation `G = *ᵢ H` for an internal free-product decomposition of `G` by the
indexed family `H`. -/
scoped notation:50 G:50 " = " "*" "ᵢ " H:51 => IsFreeProduct (H : _ → Subgroup G)

end FreeProduct

open scoped FreeProduct

/-- Construct an internal free-product decomposition from pairwise disjointness and unique
reduced-word representation. -/
theorem IsFreeProduct.ofUniqueRepresentation (H : ι → Subgroup G)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (h_unique : ∀ x : G, ∃! w : ReducedWord H, w.prod = x) : IsFreeProduct H := by
  refine ⟨h_disjoint, ?_⟩
  constructor
  · intro w₁ w₂ h_prod
    exact (h_unique w₁.prod).unique rfl h_prod.symm
  · intro x
    exact (h_unique x).exists

/-- Internal free-product decomposition is equivalent to pairwise disjointness together with
existence and uniqueness of a reduced word representing each element. -/
theorem isFreeProduct_iff (H : ι → Subgroup G) :
    IsFreeProduct H ↔
      Pairwise (fun i j ↦ Disjoint (H i) (H j)) ∧
        ∀ x : G, ∃! w : ReducedWord H, w.prod = x := by
  constructor
  · intro h_free
    refine ⟨h_free.pairwise_disjoint, fun x ↦ ?_⟩
    rcases h_free.prod_bijective.2 x with ⟨w, hw⟩
    exact ⟨w, hw, fun y hy ↦ h_free.prod_bijective.1 (hy.trans hw.symm)⟩
  · rintro ⟨h_disjoint, h_unique⟩
    exact IsFreeProduct.ofUniqueRepresentation H h_disjoint h_unique

/-- The subgroups in an internal free-product decomposition generate the ambient group. -/
theorem IsFreeProduct.iSup_eq_top {H : ι → Subgroup G} (h_free : IsFreeProduct H) :
    ⨆ i, H i = ⊤ := by
  -- Surjectivity supplies a reduced word, whose underlying word has the same product.
  apply (iSup_eq_top_iff_exists_word H).mpr
  intro x
  obtain ⟨w, hw⟩ := h_free.prod_bijective.2 x
  refine ⟨w.toWord, ?_⟩
  exact (Word.represents_iff w.toWord x).mpr hw

/-- Under pairwise disjointness, a nonidentity element belonging to the family belongs to a
unique member of the family. -/
theorem existsUnique_mem_of_pairwise_disjoint {H : ι → Subgroup G}
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    {x : G} (h_ne_one : x ≠ 1) (h_mem : ∃ i, x ∈ H i) :
    ∃! i, x ∈ H i := by
  rcases h_mem with ⟨i, hi⟩
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra h_ne
  have hx_bot : x ∈ (⊥ : Subgroup G) :=
    (h_disjoint (Ne.symm h_ne)).le_bot ⟨hi, hj⟩
  exact h_ne_one (by simpa using hx_bot)

end Subgroup
