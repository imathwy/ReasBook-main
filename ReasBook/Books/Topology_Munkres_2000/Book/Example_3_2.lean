module

public import Topology_Munkres_2000.Book.Example_3_1

public section

open scoped SetRel

namespace Kinship

/-- Example 3.2 (1): A person who is not their own descendant witnesses that
the descendant relation is not reflexive. -/
theorem descendant_not_reflexive {P : Type*} (descendant : SetRel P P) (person : P)
    (not_self_descendant : ¬ person ~[descendant] person) : ¬ descendant.IsRefl := by
  rintro ⟨hrefl⟩
  exact not_self_descendant (hrefl person)

/-- Example 3.2 (2): A descendant and ancestor for which the reverse relation
fails witness that the descendant relation is not symmetric. -/
theorem descendant_not_isSymm {P : Type*} (descendant : SetRel P P) (person ancestor : P)
    (person_descendant_ancestor : person ~[descendant] ancestor)
    (ancestor_not_descendant_person : ¬ ancestor ~[descendant] person) : ¬ descendant.IsSymm := by
  rintro ⟨hsymm⟩
  exact ancestor_not_descendant_person (hsymm person ancestor person_descendant_ancestor)

/-- Example 3.2 (3): A husband and wife with no common ancestor, together with
a child sharing an ancestor with each, witness that the blood relation is not
transitive. -/
theorem blood_not_transitive {P : Type*} (descendant : SetRel P P)
    (husband child wife husbandAncestor wifeAncestor : P)
    (husband_descendant_husbandAncestor : husband ~[descendant] husbandAncestor)
    (child_descendant_husbandAncestor : child ~[descendant] husbandAncestor)
    (child_descendant_wifeAncestor : child ~[descendant] wifeAncestor)
    (wife_descendant_wifeAncestor : wife ~[descendant] wifeAncestor)
    (husband_not_blood_wife : ¬ husband ~[blood descendant] wife) :
    ¬ (blood descendant).IsTrans := by
  rintro ⟨htrans⟩
  have husbandChild : husband ~[blood descendant] child :=
    mem_blood descendant husband child |>.2
      ⟨husbandAncestor, husband_descendant_husbandAncestor, child_descendant_husbandAncestor⟩
  have childWife : child ~[blood descendant] wife :=
    mem_blood descendant child wife |>.2
      ⟨wifeAncestor, child_descendant_wifeAncestor, wife_descendant_wifeAncestor⟩
  exact husband_not_blood_wife (htrans husband child wife husbandChild childWife)

/-- The sibling relation determined by any parent relation is reflexive,
symmetric, and transitive. -/
instance sibling.instIsEquiv {P : Type*} (parent : SetRel P P) :
    IsEquiv P (· ~[sibling parent] ·) where
  refl x := mem_sibling parent x x |>.2 fun _ ↦ Iff.rfl
  symm x y hxy := mem_sibling parent y x |>.2 fun z ↦ (mem_sibling parent x y |>.1 hxy z).symm
  trans x y z hxy hyz := mem_sibling parent x z |>.2 fun w ↦
    (mem_sibling parent x y |>.1 hxy w).trans (mem_sibling parent y z |>.1 hyz w)

/- Example 3.2 (4): The sibling relation is an equivalence relation. -/
#check sibling.instIsEquiv

end Kinship
