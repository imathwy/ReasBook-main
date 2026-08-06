import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWType

open scoped ContinuousMap

universe u

-- Source/core/bridge triage: the homotopy-retract hypothesis is source-facing, while the reusable
-- conclusion owner is `TopCat.HasCWType`. The source-facing existential witness package remains as
-- a companion theorem via `TopCat.hasCWType_iff`.

/-- Problem 10.8.3: if maps `f : X ⟶ Y` and `g : Y ⟶ X` satisfy
`(g.comp f).Homotopic (ContinuousMap.id X)` and `Y` is a CW complex, then `X` has the homotopy
type of a CW complex. -/
theorem hasCWType_of_homotopyRetract
    {X Y : TopCat.{u}} (f : C(X, Y)) (g : C(Y, X)) (hY : TopCat.CWComplex Y)
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X)) :
    TopCat.HasCWType X := sorry

/-- Source-facing existential form of Problem 10.8.3. -/
theorem exists_cwComplex_homotopyEquiv_of_homotopyRetract
    {X Y : TopCat.{u}} (f : C(X, Y)) (g : C(Y, X)) (hY : TopCat.CWComplex Y)
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X)) :
    ∃ Z : TopCat.{u}, Nonempty (TopCat.CWComplex Z) ∧ Nonempty (X ≃ₕ Z) :=
  (TopCat.hasCWType_iff).mp (hasCWType_of_homotopyRetract f g hY hgf)
