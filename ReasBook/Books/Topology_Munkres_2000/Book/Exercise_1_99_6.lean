module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelClasses

import Topology_Munkres_2000.Book.Exercise_1_99_1
import Topology_Munkres_2000.Book.Exercise_1_99_5

public section

universe u

open Set
open scoped WellOrderedSubset

/-- Helper for Exercise 1.99.6: recursive selection by earlier comparability produces a
maximal chain. -/
private lemma recursiveComparableSet_isMaxChain {α : Type u} {r s : α → α → Prop}
    [IsStrictOrder α r] [IsWellOrder α s] (p : α → Prop)
    (hp : ∀ a, p a ↔ ∀ b, s b a → p b → Relation.SymmGen r b a) :
    IsMaxChain r {a | p a} := by
  -- Earlier selected elements are comparable by the defining recursion equation.
  have chain : IsChain r {a | p a} := by
    intro a ha b hb hab
    rcases trichotomous_of s a b with habs | habs | hbas
    · rcases hp b |>.mp hb a habs ha with hr | hr
      · exact Or.inl hr
      · exact Or.inr hr
    · exact (hab habs).elim
    · rcases hp a |>.mp ha b hbas hb with hr | hr
      · exact Or.inr hr
      · exact Or.inl hr
  refine ⟨chain, ?_⟩
  intro t ht hpt
  apply Set.Subset.antisymm hpt
  intro a ha
  by_contra hpa
  have hnotall : ¬ ∀ b, s b a → p b → Relation.SymmGen r b a := by
    intro hall
    exact hpa ((hp a).mpr hall)
  push Not at hnotall
  obtain ⟨b, hba, hpb, hnotcomp⟩ := hnotall
  have hbt : b ∈ t := hpt hpb
  have hab : a ≠ b := by
    intro hab
    subst b
    exact IsWellFounded.wf.irrefl.irrefl a hba
  exact hnotcomp (Relation.SymmGen.symm (ht ha hbt hab))

/-- Helper for Exercise 1.99.6: every member of a chain is either its union or a
proper initial section of its union. -/
private lemma WellOrderedSubset.eq_or_isProperSection_chainUnion {X : Type u}
    {C : Set (WellOrderedSubset X)} (hC : IsChain (· ≺ ·) C)
    {W : WellOrderedSubset X} (hW : W ∈ C) :
    W = WellOrderedSubset.chainUnion C hC ∨ W ≺ WellOrderedSubset.chainUnion C hC := by
  -- A new point in the union supplies a larger chain member and hence a cut for `W`.
  by_cases hcarrier : W.carrier = (WellOrderedSubset.chainUnion C hC).carrier
  · left
    rw [WellOrderedSubset.mk.injEq]
    refine ⟨hcarrier, funext fun x ↦ funext fun y ↦ propext ?_⟩
    constructor
    · intro hxy
      exact ⟨W, hW, hxy⟩
    · intro hxy
      have hyW : y ∈ W.carrier := by
        rw [hcarrier]
        exact (WellOrderedSubset.chainUnion C hC).rel_supported hxy |>.2
      exact (WellOrderedSubset.unionRel_below_mem hC hW hyW hxy).2
  · right
    have hproper : ∃ x, x ∈ (WellOrderedSubset.chainUnion C hC).carrier ∧ x ∉ W.carrier := by
      by_contra hall
      push Not at hall
      apply hcarrier
      ext x
      constructor
      · intro hxW
        exact WellOrderedSubset.carrier_subset_unionCarrier hW hxW
      · intro hx
        exact hall x hx
    obtain ⟨x, hxU, hxW⟩ := hproper
    obtain ⟨V, hV, hxV⟩ := hxU
    have hWV : W ≺ V := by
      by_cases hEq : W = V
      · subst V
        exact (hxW hxV).elim
      · rcases hC hW hV hEq with hWV | hVW
        · exact hWV
        · exact (hxW (WellOrderedSubset.IsProperSection.carrier_subset hVW hxV)).elim
    obtain ⟨cut, hcutV, hcarrierW, hagreeWV⟩ := hWV
    refine ⟨cut, ⟨V, hV, hcutV⟩, ?_, ?_⟩
    · ext y
      constructor
      · intro hyW
        exact ⟨V, hV, (Set.ext_iff.mp hcarrierW y).mp hyW⟩
      · intro hycut
        exact (Set.ext_iff.mp hcarrierW y).mpr
          (WellOrderedSubset.unionRel_below_mem hC hV hcutV hycut).2
    · intro y z hyW hzW
      constructor
      · intro hyz
        exact ⟨W, hW, hyz⟩
      · intro hyz
        exact (WellOrderedSubset.unionRel_below_mem hC hW hzW hyz).2

/-- Helper for Exercise 1.99.6: adjoining a fresh greatest point preserves a well-order. -/
private lemma adjoinGreatest_isWellOrder {X : Type u} (W : WellOrderedSubset X)
    {x : X} (hx : x ∉ W.carrier) :
    IsWellOrder (Set.insert x W.carrier)
      (Subrel (fun a b ↦ W.rel a b ∨ (a ∈ W.carrier ∧ b = x)) (Set.insert x W.carrier)) := by
  -- Old elements inherit accessibility; the new point sits above all of them.
  have oldAcc : ∀ y : W.carrier,
      Acc (Subrel (fun a b ↦ W.rel a b ∨ (a ∈ W.carrier ∧ b = x))
        (Set.insert x W.carrier)) ⟨y, Set.mem_insert_of_mem x y.property⟩ := by
    intro y
    induction y using W.wellOrder.wf.induction with
    | h y ih =>
        apply Acc.intro
        intro z hz
        rcases hz with hzy | ⟨hzW, hyx⟩
        · have hzW := (W.rel_supported hzy).1
          exact ih ⟨z, hzW⟩ hzy
        · exact (hx (hyx ▸ y.property)).elim
  refine { wf := ⟨?_⟩, trichotomous := ?_ }
  · intro y
    rcases y.property with hyx | hyW
    · apply Acc.intro
      intro z hz
      rcases hz with hzx | ⟨hzW, hzx⟩
      · exact (hx (hyx ▸ (W.rel_supported hzx).2)).elim
      · exact oldAcc ⟨z, hzW⟩
    · exact oldAcc ⟨y, hyW⟩
  · exact (Std.trichotomous_of_rel_or_eq_or_rel_swap (fun {a b} ↦ by
      rcases a.property with hax | haW
      · rcases b.property with hbx | hbW
        · exact Or.inr (Or.inl (Subtype.ext (hax.trans hbx.symm)))
        · exact Or.inr (Or.inr (Or.inr ⟨hbW, hax⟩))
      · rcases b.property with hbx | hbW
        · exact Or.inl (Or.inr ⟨haW, hbx⟩)
        · rcases (show Subrel W.rel W.carrier ⟨a, haW⟩ ⟨b, hbW⟩ ∨
              (⟨a, haW⟩ : W.carrier) = ⟨b, hbW⟩ ∨
              Subrel W.rel W.carrier ⟨b, hbW⟩ ⟨a, haW⟩ by
            by_cases hab : W.rel a b
            · exact Or.inl hab
            · by_cases hba : W.rel b a
              · exact Or.inr (Or.inr hba)
              · exact Or.inr (Or.inl (W.wellOrder.trichotomous _ _ hab hba))) with h | h | h
          · exact Or.inl (Or.inl h)
          · have hab : (a.val : X) = b.val := congrArg (fun z : W.carrier ↦ (z.val : X)) h
            exact Or.inr (Or.inl (Subtype.ext hab))
          · exact Or.inr (Or.inr (Or.inl h)))).trichotomous

/-- Helper for Exercise 1.99.6: adjoining a point outside a well-ordered subset as a
new greatest element gives a proper-section extension containing that point. -/
private lemma WellOrderedSubset.existsProperSectionExtension {X : Type u}
    (W : WellOrderedSubset X) {x : X} (hx : x ∉ W.carrier) :
    ∃ T : WellOrderedSubset X, W ≺ T ∧ x ∈ T.carrier := by
  -- Package the inserted carrier and greatest-point relation behind the proved interface.
  have supported {a b : X}
      (hab : W.rel a b ∨ (a ∈ W.carrier ∧ b = x)) :
      a ∈ Set.insert x W.carrier ∧ b ∈ Set.insert x W.carrier := by
    rcases hab with hab | ⟨haW, hbx⟩
    · exact ⟨Set.mem_insert_of_mem x (W.rel_supported hab).1,
        Set.mem_insert_of_mem x (W.rel_supported hab).2⟩
    · exact ⟨Set.mem_insert_of_mem x haW, hbx ▸ Set.mem_insert x W.carrier⟩
  let T : WellOrderedSubset X :=
    { carrier := Set.insert x W.carrier
      rel := fun a b ↦ W.rel a b ∨ (a ∈ W.carrier ∧ b = x)
      rel_supported := supported
      wellOrder := adjoinGreatest_isWellOrder W hx }
  refine ⟨T, ?_, Set.mem_insert x W.carrier⟩
  refine ⟨x, Set.mem_insert x W.carrier, ?_, ?_⟩
  · ext y
    simp only [T, Set.mem_setOf_eq]
    constructor
    · intro hyW
      exact Or.inr ⟨hyW, trivial⟩
    · intro hy
      rcases hy with hy | ⟨hyW, hxx⟩
      · exact (hx (W.rel_supported hy).2).elim
      · exact hyW
  · intro y z hyW hzW
    simp only [T]
    constructor
    · exact Or.inl
    · intro hyz
      rcases hyz with hyz | ⟨hyW, hzx⟩
      · exact hyz
      · exact (hx (hzx ▸ hzW)).elim

/-- Helper for Exercise 1.99.6: a supported well-order whose carrier is universal
well-orders the ambient type. -/
private lemma WellOrderedSubset.wellOrder_rel_of_carrier_eq_univ {X : Type u}
    (W : WellOrderedSubset X) (hW : W.carrier = Set.univ) : IsWellOrder X W.rel := by
  -- Pull the subtype well-order back along the canonical inclusion into the universal carrier.
  let inclusion : X → W.carrier := fun x ↦ ⟨x, hW.symm ▸ Set.mem_univ x⟩
  have hinjective : Function.Injective inclusion := by
    intro x y hxy
    exact congrArg Subtype.val hxy
  letI wellOrderCarrier : IsWellOrder W.carrier (Subrel W.rel W.carrier) := W.wellOrder
  have hpull := @Function.Injective.isWellOrder X W.carrier (Subrel W.rel W.carrier)
    inclusion hinjective wellOrderCarrier
  exact hpull

/-- Exercise 1.99.6: The Hausdorff maximum principle for strict partial orders is
equivalent to the well-ordering theorem. -/
theorem maximumPrinciple_iff_wellOrderingTheorem :
    (∀ (α : Type u) (r : α → α → Prop) [IsStrictOrder α r],
      ∃ s : Set α, IsMaxChain r s) ↔
    (∀ α : Type u, ∃ r : α → α → Prop, IsWellOrder α r) := by
  constructor
  · intro maximumPrinciple X
    classical
    obtain ⟨C, hC⟩ := maximumPrinciple (WellOrderedSubset X) (· ≺ ·)
    let U := WellOrderedSubset.chainUnion C hC.isChain
    have hcarrier : U.carrier = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      obtain ⟨T, hUT, hxT⟩ := U.existsProperSectionExtension hx
      have hinsert : IsChain (· ≺ ·) (insert T C) := by
        apply hC.isChain.insert
        intro W hW hTW
        rcases W.eq_or_isProperSection_chainUnion hC.isChain hW with hWU | hWU
        · subst W
          exact Or.inr hUT
        · exact Or.inr (WellOrderedSubset.isProperSection_trans hWU hUT)
      have heq : insert T C = C := (hC.2 hinsert (Set.subset_insert T C)).symm
      have hTC : T ∈ C := by
        rw [← heq]
        exact Set.mem_insert T C
      exact hx ⟨T, hTC, hxT⟩
    exact ⟨U.rel, U.wellOrder_rel_of_carrier_eq_univ hcarrier⟩
  · intro wellOrdering α r inst
    classical
    obtain ⟨s, hs⟩ := wellOrdering α
    letI : IsWellOrder α s := hs
    letI : LinearOrder α := IsWellOrder.linearOrder s
    letI : WellFoundedLT α := ⟨hs.wf⟩
    let rule : {a : α} → (Set.Iio a → Prop) → Prop :=
      fun {a} previous ↦ ∀ b : Set.Iio a, previous b → Relation.SymmGen r b a
    obtain ⟨p, hp, hp_unique⟩ := existsUniqueRecursiveDefinition rule
    have hprecise (a : α) :
        p a ↔ ∀ b, s b a → p b → Relation.SymmGen r b a := by
      rw [hp]
      constructor
      · intro hall b hba hpb
        exact hall ⟨b, hba⟩ hpb
      · intro hall b hpb
        exact hall b b.property hpb
    exact ⟨{a | p a}, recursiveComparableSet_isMaxChain p hprecise⟩

end
