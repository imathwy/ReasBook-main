import chapter1_reference_format.Chap01.Definition_1_7_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 1.7.5 (1): addition on `ℕ` is an internal law on `ℕ`. Following
Definition 1.7.4, we use the product-map presentation obtained by uncurrying the canonical
binary operation `((· + ·) : ℕ → ℕ → ℕ)`. -/
#check (Function.uncurry ((· + ·) : ℕ → ℕ → ℕ) : ℕ × ℕ → ℕ)

/- Example 1.7.5 (2): multiplication on `ℕ` is an internal law on `ℕ`, via the same bridge from
the canonical curried binary operation to its product-map presentation. -/
#check (Function.uncurry ((· * ·) : ℕ → ℕ → ℕ) : ℕ × ℕ → ℕ)
