import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Homotopy

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable {X X' : ChainComplex (ModuleCat R) ℕ}
variable {f g : X ⟶ X'}

-- Bridge/view item: this records the `ChainComplex (ModuleCat R) ℕ` specialization of the
-- canonical mathlib theorem `Homotopy.homologyMap_eq`.

/-- Lemma 12.2.4. Chain homotopic chain maps induce the same morphism on homology:
if `s : Homotopy f g`, then the degree-`i` maps on homology are equal.
-/
theorem homologyMap_eq_of_chainHomotopy (s : Homotopy f g) (i : ℕ) :
    HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i :=
  s.homologyMap_eq i
