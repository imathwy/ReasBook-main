import chapter1_reference_format.Chap01.Lemma_1_1_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u}

/- Lemma 1.7.18 (1): this source-facing bridge from a partial order relation to its strict part
is already owned earlier in the chapter by the canonical theorem
`strict_relation_of_partial_order_isStrictOrder`. -/
recall strict_relation_of_partial_order_isStrictOrder (le : S → S → Prop) [IsPartialOrder S le] :
    IsStrictOrder S (fun a b ↦ le a b ∧ ¬ le b a)

/- Lemma 1.7.18 (2): the converse bridge from a strict order relation to its reflexive closure is
already owned earlier in the chapter by `reflClosure_of_strictOrder_isPartialOrder`. -/
recall reflClosure_of_strictOrder_isPartialOrder (lt : S → S → Prop) [IsStrictOrder S lt] :
    IsPartialOrder S (Relation.ReflGen lt)
