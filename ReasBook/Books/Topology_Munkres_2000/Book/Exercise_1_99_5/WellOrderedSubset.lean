module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelIso.Set

@[expose] public section

open Set

universe u

/-- A subset of an ambient type equipped with a supported well-ordering relation. -/
structure WellOrderedSubset (X : Type u) where
  carrier : Set X
  rel : X → X → Prop
  rel_supported {x y} : rel x y → x ∈ carrier ∧ y ∈ carrier
  wellOrder : IsWellOrder carrier (Subrel rel carrier)

namespace WellOrderedSubset

/-- A well-ordered subset coerces to its carrier subtype. -/
instance instCoeSort {X : Type u} : CoeSort (WellOrderedSubset X) (Type u) where
  coe W := W.carrier

/-- The strict order on a well-ordered subset is its stored ambient relation. -/
instance instLT {X : Type u} (W : WellOrderedSubset X) : LT W where
  lt x y := W.rel x y

/-- The stored relation restricts to a well-order on the carrier subtype. -/
instance instIsWellOrder {X : Type u} (W : WellOrderedSubset X) :
    IsWellOrder W (· < ·) := W.wellOrder

/-- The support and well-order conditions defining a well-ordered subset. -/
theorem spec {X : Type u} (W : WellOrderedSubset X) :
    (∀ {x y}, W.rel x y → x ∈ W.carrier ∧ y ∈ W.carrier) ∧
      IsWellOrder W (· < ·) :=
  ⟨W.rel_supported, W.wellOrder⟩

/-- `S` is a proper initial section of `T` when its carrier is exactly the set of
strict predecessors of an element of `T`, and both relations agree on that carrier. -/
def IsProperSection {X : Type u} (S T : WellOrderedSubset X) : Prop :=
  ∃ x ∈ T.carrier,
    S.carrier = {y | T.rel y x} ∧
      ∀ {y z}, y ∈ S.carrier → z ∈ S.carrier → (S.rel y z ↔ T.rel y z)

scoped[WellOrderedSubset] infix:50 " ≺ " => WellOrderedSubset.IsProperSection

open scoped WellOrderedSubset

/-- The defining characterization of proper initial-section inclusion. -/
theorem isProperSection_iff {X : Type u} (S T : WellOrderedSubset X) :
    S ≺ T ↔ ∃ x ∈ T.carrier,
      S.carrier = {y | T.rel y x} ∧
        ∀ {y z}, y ∈ S.carrier → z ∈ S.carrier → (S.rel y z ↔ T.rel y z) := Iff.rfl

/-- Helper for Exercise 1.99.5: the ambient relation of a well-ordered subset is transitive. -/
lemma rel_trans {X : Type u} (W : WellOrderedSubset X) {x y z : X}
    (hxy : W.rel x y) (hyz : W.rel y z) : W.rel x z := by
  -- Restrict the three supported points to the carrier and use its stored well-order.
  have hx := (W.rel_supported hxy).1
  have hy := (W.rel_supported hxy).2
  have hz := (W.rel_supported hyz).2
  exact trans_of (fun a b : W ↦ a < b) (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    (c := ⟨z, hz⟩) hxy hyz

/-- Helper for Exercise 1.99.5: a proper section's carrier lies in the larger carrier. -/
lemma IsProperSection.carrier_subset {X : Type u} {S T : WellOrderedSubset X}
    (hST : S ≺ T) : S.carrier ⊆ T.carrier := by
  -- Every member of the section is a predecessor of its cut point, hence is supported in `T`.
  obtain ⟨cut, hcut, hcarrier, hagree⟩ := hST
  intro x hx
  have hxcut : T.rel x cut := by
    exact (Set.ext_iff.mp hcarrier x).mp hx
  exact (T.rel_supported hxcut).1

/-- Helper for Exercise 1.99.5: no well-ordered subset is a proper section of itself. -/
lemma isProperSection_irrefl {X : Type u} (S : WellOrderedSubset X) : ¬ S ≺ S := by
  -- A self-section would make its cut point strictly precede itself.
  intro hSS
  obtain ⟨cut, hcut, hcarrier, hagree⟩ := hSS
  have hcutcut : S.rel cut cut := by
    exact (Set.ext_iff.mp hcarrier cut).mp hcut
  exact (S.wellOrder.wf.irrefl).irrefl ⟨cut, hcut⟩ hcutcut

/-- Helper for Exercise 1.99.5: proper initial-section inclusion is transitive. -/
lemma isProperSection_trans {X : Type u} {S T U : WellOrderedSubset X}
    (hST : S ≺ T) (hTU : T ≺ U) : S ≺ U := by
  -- Use the first cut point as the composite cut and translate both carrier descriptions.
  have hSTsubset := IsProperSection.carrier_subset hST
  have hTUsubset := IsProperSection.carrier_subset hTU
  obtain ⟨cutST, hcutST, hcarrierST, hagreeST⟩ := hST
  obtain ⟨cutTU, hcutTU, hcarrierTU, hagreeTU⟩ := hTU
  refine ⟨cutST, hTUsubset hcutST, ?_, ?_⟩
  · ext x
    constructor
    · intro hxS
      have hxT := hSTsubset hxS
      have hTrel : T.rel x cutST := by
        exact (Set.ext_iff.mp hcarrierST x).mp hxS
      exact (hagreeTU hxT hcutST).mp hTrel
    · intro hUrel
      have hcutSTcutTU : U.rel cutST cutTU := by
        exact (Set.ext_iff.mp hcarrierTU cutST).mp hcutST
      have hxT : x ∈ T.carrier := by
        exact (Set.ext_iff.mp hcarrierTU x).mpr (U.rel_trans hUrel hcutSTcutTU)
      have hTrel : T.rel x cutST := (hagreeTU hxT hcutST).mpr hUrel
      exact (Set.ext_iff.mp hcarrierST x).mpr hTrel
  · intro x y hxS hyS
    have hxT := hSTsubset hxS
    have hyT := hSTsubset hyS
    exact (hagreeST hxS hyS).trans (hagreeTU hxT hyT)

/-- Helper for Exercise 1.99.5: proper initial-section inclusion satisfies the strict-order laws. -/
lemma isStrictOrder_isProperSection {X : Type u} :
    IsStrictOrder (WellOrderedSubset X) (· ≺ ·) where
  -- Irreflexivity and transitivity are exactly the two section lemmas above.
  irrefl := isProperSection_irrefl
  trans := fun _ _ _ ↦ isProperSection_trans

/-- The union of the carriers in a collection of well-ordered subsets. -/
def unionCarrier {X : Type u} (C : Set (WellOrderedSubset X)) : Set X :=
  {x | ∃ W ∈ C, x ∈ W.carrier}

/-- Membership in the union carrier is membership in one carrier from the collection. -/
theorem mem_unionCarrier_iff {X : Type u} {C : Set (WellOrderedSubset X)} {x : X} :
    x ∈ unionCarrier C ↔ ∃ W ∈ C, x ∈ W.carrier := Iff.rfl

/-- The union of the ambient relations in a collection of well-ordered subsets. -/
def unionRel {X : Type u} (C : Set (WellOrderedSubset X)) (x y : X) : Prop :=
  ∃ W ∈ C, W.rel x y

/-- The union relation holds exactly when one relation in the collection holds. -/
theorem unionRel_iff {X : Type u} {C : Set (WellOrderedSubset X)} {x y : X} :
    unionRel C x y ↔ ∃ W ∈ C, W.rel x y := Iff.rfl

/-- The union relation is supported on the union carrier. -/
theorem unionRel_supported {X : Type u} (C : Set (WellOrderedSubset X))
    {x y : X} (hxy : unionRel C x y) :
    x ∈ unionCarrier C ∧ y ∈ unionCarrier C := by
  -- A witnessing member supports both endpoints and therefore witnesses union membership.
  obtain ⟨W, hW, hxy⟩ := hxy
  exact ⟨⟨W, hW, (W.rel_supported hxy).1⟩, ⟨W, hW, (W.rel_supported hxy).2⟩⟩

/-- Helper for Exercise 1.99.5: each member carrier includes into the union carrier. -/
lemma carrier_subset_unionCarrier {X : Type u} {C : Set (WellOrderedSubset X)}
    {W : WellOrderedSubset X} (hW : W ∈ C) : W.carrier ⊆ unionCarrier C := by
  -- The same member supplies the existential witness for every one of its points.
  intro x hx
  exact ⟨W, hW, hx⟩

/-- Helper for Exercise 1.99.5: a union predecessor of a point in a chain member
already lies in that member, where the two relations agree. -/
lemma unionRel_below_mem {X : Type u} {C : Set (WellOrderedSubset X)}
    (hC : IsChain (· ≺ ·) C) {W : WellOrderedSubset X} (hW : W ∈ C)
    {x y : X} (hyW : y ∈ W.carrier) (hxy : unionRel C x y) :
    x ∈ W.carrier ∧ W.rel x y := by
  -- Compare the relation witness with `W`; initiality handles the only nontrivial orientation.
  obtain ⟨V, hV, hVxy⟩ := hxy
  by_cases hVW : V = W
  · subst V
    exact ⟨(W.rel_supported hVxy).1, hVxy⟩
  · rcases hC hV hW hVW with hVWsection | hWVsection
    · have hVsubset := IsProperSection.carrier_subset hVWsection
      obtain ⟨cut, hcut, hcarrier, hagree⟩ := hVWsection
      have hxV := (V.rel_supported hVxy).1
      have hyV := (V.rel_supported hVxy).2
      have hxW := hVsubset hxV
      have hyW := hVsubset hyV
      exact ⟨hxW, (hagree hxV hyV).mp hVxy⟩
    · obtain ⟨cut, hcut, hcarrier, hagree⟩ := hWVsection
      have hycut : V.rel y cut := by
        exact (Set.ext_iff.mp hcarrier y).mp hyW
      have hxcut : V.rel x cut := V.rel_trans hVxy hycut
      have hxW : x ∈ W.carrier := by
        exact (Set.ext_iff.mp hcarrier x).mpr hxcut
      exact ⟨hxW, (hagree hxW hyW).mpr hVxy⟩

/-- Helper for Exercise 1.99.5: two points lying in one chain member satisfy union trichotomy. -/
lemma unionRel_trichotomy_of_mem {X : Type u} {C : Set (WellOrderedSubset X)}
    {W : WellOrderedSubset X} (hW : W ∈ C) {x y : X}
    (hxW : x ∈ W.carrier) (hyW : y ∈ W.carrier) :
    unionRel C x y ∨ x = y ∨ unionRel C y x := by
  -- Apply trichotomy in `W` and retain `W` as the witness for either strict union relation.
  rcases trichotomous_of (fun a b : W ↦ a < b) ⟨x, hxW⟩ ⟨y, hyW⟩ with hxy | hxy | hyx
  · exact Or.inl ⟨W, hW, hxy⟩
  · exact Or.inr (Or.inl (congrArg Subtype.val hxy))
  · exact Or.inr (Or.inr ⟨W, hW, hyx⟩)

/-- Helper for Exercise 1.99.5: the relation on a chain union is well-founded. -/
lemma chainUnion_wellFounded {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) :
    WellFounded (Subrel (unionRel C) (unionCarrier C)) := by
  -- Choose a member containing each point and lift its accessibility along the carrier inclusion.
  refine ⟨?_⟩
  intro x
  obtain ⟨W, hW, hxW⟩ := x.property
  let inclusion : W.carrier → unionCarrier C := Set.inclusion (carrier_subset_unionCarrier hW)
  have hfib : Relation.Fibration (Subrel W.rel W.carrier)
      (Subrel (unionRel C) (unionCarrier C)) inclusion := by
    intro a b hba
    have hnormalized := unionRel_below_mem hC hW a.property hba
    let bW : W.carrier := ⟨b, hnormalized.1⟩
    refine ⟨bW, hnormalized.2, ?_⟩
    exact Set.inclusion_right (carrier_subset_unionCarrier hW) b hnormalized.1
  have hxAcc : Acc (Subrel W.rel W.carrier) ⟨x, hxW⟩ := W.wellOrder.wf.apply ⟨x, hxW⟩
  exact hxAcc.of_fibration inclusion hfib

/-- Helper for Exercise 1.99.5: the relation on a chain union is trichotomous. -/
lemma chainUnion_trichotomous {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) :
    Std.Trichotomous (Subrel (unionRel C) (unionCarrier C)) := by
  -- Compare carrier witnesses, move both points into the larger member, and use its trichotomy.
  refine Std.trichotomous_of_rel_or_eq_or_rel_swap ?_
  intro x y
  obtain ⟨W, hW, hxW⟩ := x.property
  obtain ⟨V, hV, hyV⟩ := y.property
  by_cases hWV : W = V
  · subst V
    rcases unionRel_trichotomy_of_mem hW hxW hyV with hxy | hxy | hyx
    · exact Or.inl hxy
    · exact Or.inr (Or.inl (Subtype.ext hxy))
    · exact Or.inr (Or.inr hyx)
  · rcases hC hW hV hWV with hWVsection | hVWsection
    · have hxV := IsProperSection.carrier_subset hWVsection hxW
      rcases unionRel_trichotomy_of_mem hV hxV hyV with hxy | hxy | hyx
      · exact Or.inl hxy
      · exact Or.inr (Or.inl (Subtype.ext hxy))
      · exact Or.inr (Or.inr hyx)
    · have hyW := IsProperSection.carrier_subset hVWsection hyV
      rcases unionRel_trichotomy_of_mem hW hxW hyW with hxy | hxy | hyx
      · exact Or.inl hxy
      · exact Or.inr (Or.inl (Subtype.ext hxy))
      · exact Or.inr (Or.inr hyx)

/-- Helper for Exercise 1.99.5: a chain's union relation well-orders its union carrier. -/
theorem chainUnionWellOrder {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) :
    IsWellOrder (unionCarrier C) (Subrel (unionRel C) (unionCarrier C)) where
  -- Assemble the well-order from the separately normalized well-foundedness and trichotomy fields.
  wf := chainUnion_wellFounded C hC
  trichotomous := (chainUnion_trichotomous C hC).trichotomous

/-- The well-ordered subset obtained by taking the literal unions along a chain. -/
def chainUnion {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) : WellOrderedSubset X where
  carrier := unionCarrier C
  rel := unionRel C
  rel_supported := unionRel_supported C
  wellOrder := chainUnionWellOrder C hC

/-- The carrier of a chain union is the literal union of the carriers. -/
theorem chainUnion_carrier {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) :
    (chainUnion C hC).carrier = unionCarrier C := rfl

/-- The relation of a chain union is the literal union of the relations. -/
theorem chainUnion_rel {X : Type u} (C : Set (WellOrderedSubset X))
    (hC : IsChain (· ≺ ·) C) :
    (chainUnion C hC).rel = unionRel C := rfl

end WellOrderedSubset
