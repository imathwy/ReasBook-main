import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.ModTwoCohomologyTheory

open CategoryTheory

noncomputable section

section

variable (H2 : ModTwoCohomologyTheory)
variable (suspension : TopCat ⥤ TopCat)
variable (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)

/-- Theorem 22.5.5. For the chosen ambient ordinary mod-`2` cohomology theory together with the
chosen suspension-compatibility datum from Definition 22.5.3, there exists a stable family of
Steenrod square operations `Sq^n : H^q(X; ZMod 2) → H^(q + n)(X; ZMod 2)` satisfying
normalization, naturality, the Cartan formula, and the Adem relations. -/
theorem exists_steenrodSquareFamily :
    Nonempty (SteenrodSquareFamily H2 suspension suspensionIso) := sorry

end
