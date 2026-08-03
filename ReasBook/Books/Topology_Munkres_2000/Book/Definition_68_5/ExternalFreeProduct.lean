module

public import Topology_Munkres_2000.Book.Definition_68_3.FreeProduct
public import Mathlib.GroupTheory.CoprodI

public section

open scoped Subgroup.FreeProduct

namespace MonoidHom

universe u v w

variable {ι : Type u} {G : ι → Type v} {H : Type w}
variable [∀ α, Group (G α)] [Group H]

/-- A family of group homomorphisms exhibits its target as an external free product when every
homomorphism is injective and their ranges form an internal free-product decomposition. -/
class IsExternalFreeProduct (i : ∀ α, G α →* H) : Prop where
  /-- Each factor embeds in the ambient group. -/
  injective (α : ι) : Function.Injective (i α)
  /-- The ranges of the embeddings form an internal free-product decomposition. -/
  isFreeProduct : H = *ᵢ (fun α ↦ (i α).range)

/-- The external-free-product property is equivalent to injectivity of every map together with
an internal free-product decomposition by their ranges. -/
theorem isExternalFreeProduct_iff (i : ∀ α, G α →* H) :
    IsExternalFreeProduct i ↔
      (∀ α, Function.Injective (i α)) ∧
        H = *ᵢ (fun α ↦ (i α).range) := by
  constructor
  · intro h
    exact ⟨h.injective, h.isFreeProduct⟩
  · rintro ⟨h_injective, h_free⟩
    exact ⟨h_injective, h_free⟩

end MonoidHom

namespace Monoid.CoprodI

universe u v

variable {ι : Type u} (G : ι → Type v) [∀ α, Group (G α)]

/-- Helper for Definition 68.5: distinct canonical factor ranges in an indexed coproduct are
disjoint. -/
private lemma pairwiseDisjoint_range_of :
    Pairwise (fun α β ↦
      Disjoint ((of : G α →* Monoid.CoprodI G).range)
        ((of : G β →* Monoid.CoprodI G).range)) := by
  classical
  intro α β hαβ
  rw [Subgroup.disjoint_def]
  intro x hxα hxβ
  obtain ⟨a, ha⟩ := hxα
  obtain ⟨b, hb⟩ := hxβ
  -- Retract to the first factor: its letter survives, while the other factor maps to `1`.
  have h_retract := congrArg
    (lift (Pi.mulSingle α (MonoidHom.id (G α)))) (ha.trans hb.symm)
  have ha_one : a = 1 := by
    simpa only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply,
      Pi.mulSingle_eq_of_ne' hαβ, MonoidHom.one_apply] using h_retract
  calc
    x = of a := ha.symm
    _ = of 1 := congrArg of ha_one
    _ = 1 := map_one of

/-- Helper for Definition 68.5: the canonical factor ranges generate the indexed coproduct. -/
private lemma iSup_range_of_eq_top :
    (⨆ α, ((of : G α →* Monoid.CoprodI G).range)) = ⊤ := by
  -- The supremum is the range of the universal lift, which is the identity homomorphism.
  calc
    (⨆ α, ((of : G α →* Monoid.CoprodI G).range)) =
        (lift (fun α ↦ (of : G α →* Monoid.CoprodI G))).range :=
      (range_eq_iSup G _).symm
    _ = (MonoidHom.id (Monoid.CoprodI G)).range := by rw [lift_of']
    _ = ⊤ := MonoidHom.range_eq_top.mpr Function.surjective_id

/-- Helper for Definition 68.5: a reduced ambient list of canonical coproduct letters lifts to a
canonical `Monoid.CoprodI.Word`. -/
private lemma existsWordMappingToReducedList
    (l : List (Monoid.CoprodI G))
    (h_mem : ∀ x ∈ l, ∃ α, x ∈ (of : G α →* Monoid.CoprodI G).range)
    (h_ne_one : ∀ x ∈ l, x ≠ 1)
    (h_chain : l.IsChain (fun x y ↦
      ∀ α, ¬ (x ∈ (of : G α →* Monoid.CoprodI G).range ∧
        y ∈ (of : G α →* Monoid.CoprodI G).range))) :
    ∃ v : Word G, v.toList.map (fun p ↦ of p.2) = l := by
  classical
  induction l with
  | nil =>
      -- The empty ambient list is represented by the empty canonical word.
      refine ⟨Word.empty, ?_⟩
      rfl
  | cons x xs ih =>
      obtain ⟨α, a, ha⟩ := h_mem x List.mem_cons_self
      have h_mem_tail : ∀ y ∈ xs, ∃ β, y ∈ (of : G β →* Monoid.CoprodI G).range := by
        intro y hy
        exact h_mem y (List.mem_cons_of_mem x hy)
      have h_ne_one_tail : ∀ y ∈ xs, y ≠ 1 := by
        intro y hy
        exact h_ne_one y (List.mem_cons_of_mem x hy)
      have h_chain_tail := h_chain.tail
      obtain ⟨v, hv⟩ := ih h_mem_tail h_ne_one_tail h_chain_tail
      have ha_ne_one : a ≠ 1 := by
        intro ha_one
        apply h_ne_one x List.mem_cons_self
        rw [← ha, ha_one, map_one]
      have h_fstIdx : v.fstIdx ≠ some α := by
        rw [Word.fstIdx_ne_iff]
        rintro ⟨β, b⟩ hb_head hαβ
        have hb_mapped_head : of b ∈ xs.head? := by
          rw [← hv, List.head?_map]
          exact Option.mem_map_of_mem (fun p ↦ of p.2) hb_head
        have h_separated := h_chain.rel_head? hb_mapped_head α
        apply h_separated
        constructor
        · exact ⟨a, ha⟩
        · dsimp only at hαβ
          subst α
          exact Set.mem_range_self b
      refine ⟨Word.cons a v h_fstIdx ha_ne_one, ?_⟩
      -- Prepending the chosen source letter realizes the ambient head and preserves the tail map.
      rw [Word.cons_toList, List.map_cons, hv, ha]

/-- Helper for Definition 68.5: the canonical and ambient reduced-word products agree whenever
their underlying lists correspond letterwise. -/
private lemma word_prod_eq_reducedWord_prod_of_map_eq
    (v : Word G)
    (w : Subgroup.ReducedWord
      (fun α ↦ (of : G α →* Monoid.CoprodI G).range))
    (h_map : v.toList.map (fun p ↦ of p.2) = w.toList) :
    v.prod = w.prod := by
  -- Both evaluations are the ordered product of the same ambient list.
  rw [Word.prod, Subgroup.ReducedWord.prod_def, h_map]

/-- Helper for Definition 68.5: project reduced words with equal underlying lists are equal. -/
private lemma reducedWord_eq_of_toList_eq
    {H : ι → Subgroup (Monoid.CoprodI G)} {w₁ w₂ : Subgroup.ReducedWord H}
    (h : w₁.toList = w₂.toList) : w₁ = w₂ := by
  -- The remaining fields of both nested word structures are proof-valued.
  cases w₁ with
  | mk toWord₁ ne_one₁ chain₁ =>
      cases w₂ with
      | mk toWord₂ ne_one₂ chain₂ =>
          cases toWord₁ with
          | mk list₁ mem₁ =>
              cases toWord₂ with
              | mk list₂ mem₂ =>
                  dsimp only at h
                  subst list₂
                  rfl

/-- Helper for Definition 68.5: evaluation of reduced words in the canonical factor ranges is a
bijection onto the indexed coproduct. -/
private lemma reducedWordProd_bijective_range_of :
    Function.Bijective (fun w : Subgroup.ReducedWord
      (fun α ↦ (of : G α →* Monoid.CoprodI G).range) ↦ w.prod) := by
  classical
  constructor
  · intro w₁ w₂ h_prod
    obtain ⟨v₁, hv₁⟩ := existsWordMappingToReducedList G w₁.toList
      w₁.toWord.mem_subgroup w₁.ne_one w₁.chain_separated
    obtain ⟨v₂, hv₂⟩ := existsWordMappingToReducedList G w₂.toList
      w₂.toWord.mem_subgroup w₂.ne_one w₂.chain_separated
    have hv_prod : v₁.prod = v₂.prod := by
      rw [word_prod_eq_reducedWord_prod_of_map_eq G v₁ w₁ hv₁,
        word_prod_eq_reducedWord_prod_of_map_eq G v₂ w₂ hv₂]
      exact h_prod
    have hv_eq : v₁ = v₂ := Word.equiv.symm.injective hv_prod
    have hw_list : w₁.toList = w₂.toList := by
      calc
        w₁.toList = v₁.toList.map (fun p ↦ of p.2) := hv₁.symm
        _ = v₂.toList.map (fun p ↦ of p.2) :=
          congrArg (fun v : Word G ↦ v.toList.map (fun p ↦ of p.2)) hv_eq
        _ = w₂.toList := hv₂
    exact reducedWord_eq_of_toList_eq G hw_list
  · intro x
    -- Generation supplies an ambient reduced word representing every coproduct element.
    exact Subgroup.ReducedWord.exists_prod_eq_of_iSup_eq_top _
      (iSup_range_of_eq_top G) x

/-- Helper for Definition 68.5: the canonical inclusions exhibit `Monoid.CoprodI G` as the
external free product of `G`. -/
theorem canonicalIsExternalFreeProduct :
    MonoidHom.IsExternalFreeProduct (fun α ↦ (of : G α →* Monoid.CoprodI G)) := by
  -- Injectivity is canonical; the two helper invariants assemble the internal free product.
  refine ⟨of_injective, ?_⟩
  exact ⟨pairwiseDisjoint_range_of G, reducedWordProd_bijective_range_of G⟩

end Monoid.CoprodI
