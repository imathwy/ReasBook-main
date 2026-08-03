module

public import Topology_Munkres_2000.Book.Definition_68_3
public import Mathlib.GroupTheory.CoprodI

public section

namespace MonoidHom

universe u v w x

variable {ι : Type u} {A : ι → Type v} {G : Type w}
variable [∀ i, Group (A i)] [Group G]

/-- A family of group homomorphisms has the free-product extension property when every family
of homomorphisms from the factors extends uniquely from the ambient group. -/
def HasFreeProductExtension (i : ∀ a, A a →* G) : Prop :=
  ∀ (K : Type x) [Group K] (f : ∀ a, A a →* K),
    ∃! h : G →* K, ∀ a, h.comp (i a) = f a

end MonoidHom

namespace Subgroup

open scoped FreeProduct

universe u v w

variable {G : Type u} {ι : Type v} [Group G]

/-- Helper for Lemma 68.1: every ambient letter underlying a coproduct word belongs to one of
the specified subgroups. -/
private lemma coprodWordCoeMem {H : ι → Subgroup G}
    (w : Monoid.CoprodI.Word (fun i ↦ H i)) :
    ∀ x ∈ w.toList.map (fun p ↦ (p.2 : G)), ∃ i, x ∈ H i := by
  -- Recover the sigma-indexed subgroup letter that produced the ambient letter.
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact ⟨p.1, p.2.property⟩

/-- Helper for Lemma 68.1: coercing the letters of a coproduct word to the ambient group
preserves their nonidentity property. -/
private lemma coprodWordCoeNeOne {H : ι → Subgroup G}
    (w : Monoid.CoprodI.Word (fun i ↦ H i)) :
    ∀ x ∈ w.toList.map (fun p ↦ (p.2 : G)), x ≠ 1 := by
  -- Pull an ambient identity equation back through the injective subtype coercion.
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  intro h_one
  exact w.ne_one p hp (Subtype.coe_injective h_one)

/-- Helper for Lemma 68.1: distinct adjacent coproduct indices become adjacent ambient
letters that lie in no common subgroup. -/
private lemma coprodWordCoeChainSeparated {H : ι → Subgroup G}
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (w : Monoid.CoprodI.Word (fun i ↦ H i)) :
    (w.toList.map (fun p ↦ (p.2 : G))).IsChain
      (fun x y ↦ ∀ i, ¬ (x ∈ H i ∧ y ∈ H i)) := by
  -- Reduce the mapped chain to the original sigma letters and use uniqueness of their indices.
  rw [List.isChain_map]
  refine w.chain_ne.imp_of_mem_imp (fun p q hp hq hpq ↦ ?_)
  have hp_ne : (p.2 : G) ≠ 1 :=
    fun h_one ↦ w.ne_one p hp (Subtype.coe_injective h_one)
  have hq_ne : (q.2 : G) ≠ 1 :=
    fun h_one ↦ w.ne_one q hq (Subtype.coe_injective h_one)
  exact (noCommonSubgroup_iff_indices_ne h_disjoint p.2.property q.2.property
    hp_ne hq_ne).mpr hpq

/-- Helper for Lemma 68.1: a coproduct reduced word determines an internal reduced word by
coercing each subgroup letter to the ambient group. -/
private def coprodWordToReducedWord {H : ι → Subgroup G}
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (w : Monoid.CoprodI.Word (fun i ↦ H i)) : ReducedWord H :=
  ReducedWord.ofList H (w.toList.map (fun p ↦ (p.2 : G)))
    (coprodWordCoeMem w) (coprodWordCoeNeOne w)
    (coprodWordCoeChainSeparated h_disjoint w)

/-- Helper for Lemma 68.1: evaluation of the internal reduced word agrees with the canonical
map from the indexed coproduct. -/
private lemma coprodWordToReducedWord_prod {H : ι → Subgroup G}
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (H i) (H j)))
    (w : Monoid.CoprodI.Word (fun i ↦ H i)) :
    (coprodWordToReducedWord h_disjoint w).prod =
      Monoid.CoprodI.lift (fun i ↦ (H i).subtype) w.prod := by
  -- Both sides are the ordered product of the same coerced subgroup letters.
  simp only [ReducedWord.prod_def, coprodWordToReducedWord, ReducedWord.toList_ofList,
    Monoid.CoprodI.Word.prod, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p _
  exact Monoid.CoprodI.lift_of (fun i ↦ (H i).subtype) p.2

/-- Helper for Lemma 68.1: the canonical homomorphism from the indexed coproduct to an
internal free product is bijective. -/
private lemma coprodLiftBijective {H : ι → Subgroup G} (h_free : G = *ᵢ H) :
    Function.Bijective (Monoid.CoprodI.lift (fun i ↦ (H i).subtype)) := by
  classical
  -- Injectivity follows by comparing the coproduct normal form with the unique internal one.
  constructor
  · apply (injective_iff_map_eq_one (Monoid.CoprodI.lift (fun i ↦ (H i).subtype))).mpr
    intro x hx
    let w := Monoid.CoprodI.Word.equiv x
    let r := coprodWordToReducedWord h_free.pairwise_disjoint w
    have hw_prod : w.prod = x := Monoid.CoprodI.Word.equiv.symm_apply_apply x
    have hr_prod : r.prod = 1 := by
      dsimp only [r]
      rw [coprodWordToReducedWord_prod, hw_prod, hx]
    have hr_empty_prod : r.prod = (ReducedWord.empty H).prod := by
      simpa only [ReducedWord.prod_empty] using hr_prod
    have hr_empty : r = ReducedWord.empty H := h_free.prod_bijective.1 hr_empty_prod
    have hw_list : w.toList = [] := by
      have h_lists := congrArg (fun s : ReducedWord H ↦ s.toList) hr_empty
      simpa only [r, coprodWordToReducedWord, ReducedWord.toList_ofList,
        ReducedWord.toWord_empty, Word.toList_empty, List.map_eq_nil_iff] using h_lists
    calc
      x = w.prod := hw_prod.symm
      _ = 1 := by simp only [Monoid.CoprodI.Word.prod, hw_list, List.map_nil, List.prod_nil]
  · -- Generation by the factors identifies the range of the canonical map with all of `G`.
    apply MonoidHom.range_eq_top.mp
    calc
      (Monoid.CoprodI.lift (fun i ↦ (H i).subtype)).range =
          ⨆ i, ((H i).subtype).range :=
        Monoid.CoprodI.range_eq_iSup (fun i ↦ H i) (fun i ↦ (H i).subtype)
      _ = ⨆ i, H i := by simp only [Subgroup.range_subtype]
      _ = ⊤ := h_free.iSup_eq_top

/-- Lemma 68.1. An internal free-product decomposition admits a unique homomorphism extending
any family of homomorphisms from its factors. -/
theorem IsFreeProduct.hasExtension {H : ι → Subgroup G} (h_free : G = *ᵢ H) :
    MonoidHom.HasFreeProductExtension.{v, u, u, w} (fun i ↦ (H i).subtype) := by
  classical
  -- Replace the internal free product once by the equivalent indexed coproduct.
  intro K _ f
  let q := Monoid.CoprodI.lift (fun i ↦ (H i).subtype)
  have hq_bijective : Function.Bijective q := coprodLiftBijective h_free
  let e : Monoid.CoprodI (fun i ↦ H i) ≃* G := MulEquiv.ofBijective q hq_bijective
  let h : G →* K := (Monoid.CoprodI.lift f).comp e.symm.toMonoidHom
  have h_inverse_of (i : ι) :
      e.symm.toMonoidHom.comp (H i).subtype =
        (Monoid.CoprodI.of (M := fun i ↦ H i) (i := i) :
          H i →* Monoid.CoprodI (fun i ↦ H i)) := by
    ext x
    have hq_of : q (Monoid.CoprodI.of x) = (x : G) := by
      exact Monoid.CoprodI.lift_of (fun i ↦ (H i).subtype) x
    have hof : e (Monoid.CoprodI.of x) = (x : G) := by
      exact hq_of
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [← hof]
    exact e.symm_apply_apply (Monoid.CoprodI.of x)
  have h_spec (i : ι) : h.comp (H i).subtype = f i := by
    -- Associativity exposes the inverse-on-generators equation and the coproduct computation rule.
    dsimp only [h]
    rw [MonoidHom.comp_assoc, h_inverse_of, Monoid.CoprodI.lift_comp_of]
  refine ⟨h, h_spec, ?_⟩
  intro k hk
  -- Surjectivity of `q` reduces uniqueness to equality on every coproduct summand.
  apply (MonoidHom.cancel_right hq_bijective.2).mp
  apply Monoid.CoprodI.ext_hom
  intro i
  rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc]
  dsimp only [q]
  rw [Monoid.CoprodI.lift_comp_of, hk i, h_spec i]

end Subgroup
