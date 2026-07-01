import chapter1_reference_format.Chap01.Definition_1_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (S : Type u)

/- Definition 1.7.4 is `bridge/view`: an internal law on `S` is the product-map presentation
`S × S → S` of the earlier chapter notion of a binary operation on `S`. -/
#check (S × S → S)

/- The bridge from an internal law to the chapter's canonical curried binary-operation owner is
`Function.curry`. -/
#check (Function.curry : (S × S → S) → S → S → S)
