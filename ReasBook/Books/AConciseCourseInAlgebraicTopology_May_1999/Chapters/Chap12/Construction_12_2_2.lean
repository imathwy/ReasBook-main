import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.Recall

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable {X X' : ChainComplex (ModuleCat R) ℕ} (f : X ⟶ X') (i : ℕ)

-- `HomologicalComplex.cyclesMap` and `HomologicalComplex.homologyMap` are the canonical maps
-- induced by a chain map, while `ShortComplex.toCycles_naturality` yields the chain-complex
-- boundary compatibility recorded below as `HomologicalComplex.toCycles_naturality`.

namespace HomologicalComplex

theorem toCycles_naturality (f : X ⟶ X') (i : ℕ) :
    X.toCycles (i + 1) i ≫ cyclesMap f i = f.f (i + 1) ≫ X'.toCycles (i + 1) i := by
  apply (cancel_mono (X'.iCycles i)).1
  rw [Category.assoc, cyclesMap_i, ← Category.assoc, toCycles_i, Category.assoc, toCycles_i]
  exact (f.comm' (i + 1) i (ComplexShape.down_mk (i + 1) i rfl)).symm

attribute [reassoc, simp] toCycles_naturality
attribute [simp] toCycles_naturality_assoc

end HomologicalComplex

/- Construction 12.2.2. For a chain map `f : X ⟶ X'`, the canonical morphism
`HomologicalComplex.cyclesMap f i : X.cycles i ⟶ X'.cycles i` sends cycles to cycles.
Compatibility of the boundary maps is the chain-complex naturality statement
`HomologicalComplex.toCycles_naturality`, and the induced homology morphism is the canonical
map `HomologicalComplex.homologyMap f i : X.homology i ⟶ X'.homology i`, i.e. the textbook
`H_i(f) : H_i(X) ⟶ H_i(X')`. -/
#check HomologicalComplex.cyclesMap f i
recall HomologicalComplex.toCycles_naturality
#check HomologicalComplex.homologyMap f i
