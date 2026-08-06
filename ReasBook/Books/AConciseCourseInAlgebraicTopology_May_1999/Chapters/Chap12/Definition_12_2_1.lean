import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Tactic.Recall

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable {X X' : ChainComplex (ModuleCat R) ℕ}

-- Semantic recall via `lean_leansearch`: `HomologicalComplex.Hom` is the canonical mathlib owner
-- for chain maps; its field `f` gives the degreewise component maps, and `comm'` records
-- compatibility with the differentials.

/- Definition 12.2.1. For chain complexes `X X' : ChainComplex (ModuleCat R) ℕ`, a chain map
`f : X ⟶ X'` is exactly a morphism in the canonical mathlib structure `HomologicalComplex.Hom`:
its components `f.f n : X.X n ⟶ X'.X n` are degreewise `R`-linear maps in `ModuleCat R`, and
`f.comm'` states that they commute with the differentials. -/
#check (X ⟶ X')

/- A chain map has a degreewise component in every degree. -/
recall HomologicalComplex.Hom.f

/- The components of a chain map commute with the differentials. -/
recall HomologicalComplex.Hom.comm'

/- Conversely, degreewise maps satisfying the differential-compatibility relation assemble into a
chain map via the canonical constructor `HomologicalComplex.Hom.mk`. -/
recall HomologicalComplex.Hom.mk
