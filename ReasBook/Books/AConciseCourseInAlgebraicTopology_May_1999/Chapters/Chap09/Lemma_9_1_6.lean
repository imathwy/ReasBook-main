import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: mathlib already supplies the canonical `Group` and
-- `CommGroup` instances for `π_ (n + 1)` and `π_ (n + 2)`. Combined with the shifted owner
-- `relativeHomotopyGroup` from Definition 9.1.5, Lemma 9.1.6 is best exposed as shifted
-- instance declarations.

/-- Lemma 9.1.6 (1): for every `n : ℕ`, the relative homotopy group `π_(n + 2)(X, A)` based at
`x : A` carries its canonical group structure. -/
noncomputable instance relativeHomotopyGroupGroup (n : ℕ) (A : Set X) (x : A) :
    Group (relativeHomotopyGroup (n + 1).succPNat A x) := by
  simpa using
    (inferInstance :
      Group (HomotopyGroup.Pi (n + 1) (PathToSet A x.1) (PathToSet.refl x)))

/-- Lemma 9.1.6 (2): for every `n : ℕ`, the relative homotopy group `π_(n + 3)(X, A)` based at
`x : A` carries its canonical commutative group structure. -/
noncomputable instance relativeHomotopyGroupCommGroup (n : ℕ) (A : Set X) (x : A) :
    CommGroup (relativeHomotopyGroup (n + 2).succPNat A x) := by
  simpa using
    (inferInstance :
      CommGroup (HomotopyGroup.Pi (n + 2) (PathToSet A x.1) (PathToSet.refl x)))
