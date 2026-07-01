import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

/-- The constant abelian sheaf on `X` with value `ℤ`. -/
abbrev constantIntegerAbelianSheaf (X : TopCat) : X.Sheaf AddCommGrpCat :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The constant abelian sheaf on the open subspace `U` with value `dℤ`. -/
abbrev integerMultiplesAbelianSheaf {X : TopCat} (U : Opens X) (d : ℤ) :
    ((Opens.toTopCat X).obj U).Sheaf AddCommGrpCat :=
  (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat).obj
    (AddCommGrpCat.of ↑(AddSubgroup.zmultiples d))

-- Proof sketch: on an irreducible space, every nonempty open subset has only constant sections in
-- the ambient constant sheaf `\underline{\mathbf Z}`. The subgroup cut out by `ℋ` on a nonempty
-- open is therefore some `n\mathbf Z`, and if this subgroup is not yet locally constant one can
-- shrink to a smaller nonempty open with strictly smaller positive generator; well-foundedness of
-- the positive integers forces this process to stop.
/-- Lemma 20.20.6: for a subobject `ℋ` of the constant abelian sheaf
`\underline{\mathbf Z}` on an irreducible space, there is a nonempty open subset on which `ℋ`
is isomorphic to the constant abelian sheaf with value `d\mathbf Z` for some integer `d`. -/
theorem exists_nonempty_open_restrictIso_integerMultiplesAbelianSheaf
    {X : TopCat} [IrreducibleSpace X]
    (ℋ : Subobject (constantIntegerAbelianSheaf X)) :
    ∃ (U : Opens X) (_ : (U : Set X).Nonempty) (d : ℤ),
      Nonempty (((TopCat.Sheaf.pullback AddCommGrpCat (Opens.inclusion' U)).obj
          (((ℋ : Subobject (constantIntegerAbelianSheaf X)) : X.Sheaf AddCommGrpCat))) ≅
        integerMultiplesAbelianSheaf U d) := sorry
