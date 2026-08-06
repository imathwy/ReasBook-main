import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_3_3

noncomputable section

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch`: the source-facing owner here is the canonical morphism
-- `kroneckerPairing` from Construction 17.3.3, and the corollary asserts that this map is an
-- isomorphism when the coefficient ring is a field.

/-- Corollary 17.3.5. If `R` is a field, then in each degree `n` there is an isomorphism
`H^n(X; M) ≅ Hom(H_n(X), M)`, formalized by asserting that the canonical Kronecker pairing
`kroneckerPairing R X M n` is an isomorphism. -/
theorem kroneckerPairing_isIso_of_field
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    IsIso (kroneckerPairing R X M n) := sorry

instance instIsIsoKroneckerPairingOfField
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    IsIso (kroneckerPairing R X M n) :=
  kroneckerPairing_isIso_of_field R X M n
