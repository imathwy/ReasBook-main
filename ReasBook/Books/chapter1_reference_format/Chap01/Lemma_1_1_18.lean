import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u}

/-- Lemma 1.1.18 (1): every partial order relation on `S` induces a strict partial order relation
by removing the reflexive comparisons, i.e. by declaring `a < b` to mean `a ≤ b` and `¬ b ≤ a`. -/
-- Proof sketch: irreflexivity is immediate from the negated reverse comparison, and transitivity
-- follows from transitivity of `≤`; antisymmetry of `≤` rules out the reverse comparison.
theorem strict_relation_of_partial_order_isStrictOrder (le : S → S → Prop) [IsPartialOrder S le] :
    IsStrictOrder S (fun a b ↦ le a b ∧ ¬ le b a) := by
  let _ : PartialOrder S :=
    { le := le
      le_refl := fun a ↦ refl_of le a
      le_trans := fun _ _ _ hab hbc ↦ trans_of le hab hbc
      le_antisymm := fun _ _ hab hba ↦ antisymm_of le hab hba }
  simpa [lt_iff_le_not_ge] using (inferInstance : IsStrictOrder S (· < ·))

/-- Lemma 1.1.18 (2): every strict partial order relation on `S` induces a partial order relation
by adjoining all reflexive pairs, i.e. by passing to the reflexive closure `Relation.ReflGen lt`. -/
-- Proof sketch: `Relation.ReflGen lt` adds exactly the diagonal relations to `lt`; reflexivity is
-- built in, transitivity comes from transitivity of `lt`, and antisymmetry follows from the
-- irreflexivity of `lt`.
theorem reflClosure_of_strictOrder_isPartialOrder (lt : S → S → Prop) [IsStrictOrder S lt] :
    IsPartialOrder S (Relation.ReflGen lt) := by
  let _ : PartialOrder S :=
    { le := Relation.ReflGen lt
      le_refl := fun _ ↦ Relation.ReflGen.refl
      le_trans := fun _ _ _ hab hbc ↦ by
        rw [← Relation.reflTransGen_eq_reflGen] at hab hbc ⊢
        exact Relation.ReflTransGen.trans hab hbc
      le_antisymm := fun a b hab hba ↦ by
        rw [Relation.reflGen_iff] at hab hba
        rcases hab with rfl | hab
        · exact Or.elim hba (fun h ↦ h) (fun h ↦ False.elim ((irrefl_of lt b) h))
        · exact Or.elim hba (fun h ↦ h)
            (fun hba ↦ False.elim ((irrefl_of lt a) (trans_of lt hab hba))) }
  simpa using (inferInstance : IsPartialOrder S (· ≤ ·))
