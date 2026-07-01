import chapter1_reference_format.Chap01.Definition_1_1_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (S : Type u) (lt : S → S → Prop)

/- Definition 1.7.16 (1): this repeats the standard strict-order notion already recalled earlier
in the chapter, so we reuse the canonical owner directly. -/
#check IsStrictOrder S lt

/- Definition 1.7.16 (2): this likewise reuses the canonical strict-total-order owner already
fixed earlier in the chapter. -/
#check IsStrictTotalOrder S lt
